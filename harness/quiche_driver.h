/*
 * quiche_driver.h -- the engine half of conn_driver.h for Cloudflare's quiche.
 *
 * Included by conn_driver.h in place of its ngtcp2 step functions when
 * DRIVER_QUICHE is defined.  The script grammar, the binary fuzz format, the
 * trace vocabulary and the MH_* model hooks are conn_driver.h's and unchanged,
 * so the same input drives either implementation and the model side
 * (endpoint_diff.c) does not know which one it is looking at.
 *
 * ===========================================================================
 * What is different about quiche
 * ===========================================================================
 *
 * The handshake is real.  quiche has no way to install keys by hand, so the
 *   endpoint under test and a second quiche connection (the "peer") perform a
 *   TLS handshake in memory at ts = 0.  After it the peer is discarded and the
 *   harness forges the peer's packets itself, as conn_driver.h does.
 *
 * The crypto stub is quiche's.  Built with its `fuzzing` feature quiche leaves
 *   payloads in the clear, writes no tag and uses an all-zero header-protection
 *   mask.  The model and endpoint_diff.c's parse_out speak the other stub
 *   (Quic.Protection.stub: mask = first five bytes of the sample, tag = 16 x
 *   0xA5).  This driver converts at the boundary, both ways, so the *model
 *   sees the same bytes it would see from ngtcp2*:
 *
 *     script step --build_peer_pkt--> model-format packet --> MH_RECV
 *                  \-- same plaintext, quiche format ------> quiche_conn_recv
 *     quiche_conn_send --> quiche format --q_to_model--> MH_OUT
 *
 * Packet numbers are relative.  The handshake uses up application packet
 *   numbers on both sides, so `recv app <pn>` means "<pn> past what the peer
 *   used in the handshake"; the model is given the real number.  The 1-RTT
 *   packets of the handshake are replayed into the model (MH_SYNTH_RECV for
 *   the peer's, MH_OUT for ours) so that its ACK and packet-number state is
 *   the endpoint's.
 *
 * The clock is mocked.  quiche reads clock::CLOCK (the fuzz-mock-clock patch);
 *   quiche_fuzz_set_clock(h->ts) precedes every call.
 *
 * There are no callbacks.  After every receive the driver polls what quiche
 *   exposes and prints it in ngtcp2's `CB  name ...` vocabulary:
 *     recv_stream_data   quiche_conn_readable + quiche_conn_stream_recv
 *     stream_reset       QUICHE_ERR_STREAM_RESET from quiche_conn_stream_recv
 *   Everything else the model can produce is unobservable through quiche's
 *   API and is excluded from the comparison (drv_cb_observable).
 *
 * Return codes handed to the MH_* hooks (drv_obs_error decodes them):
 *     0            no connection error
 *     -1           closed, but not with a QUIC transport error (idle timeout,
 *                  application error)
 *     1 + code     closed with transport error |code|
 *
 * Not supported: `extend_*` steps (quiche extends flow-control credit by
 *   itself when the application reads) -- accepted and ignored, so that inputs
 *   stay interchangeable.
 */
#ifndef QUICHE_DRIVER_H
#define QUICHE_DRIVER_H

#include <quiche.h>

extern void quiche_fuzz_set_clock(uint64_t nanos);

#define Q_MAX_FLIGHT 32

static struct sockaddr_in g_q_local, g_q_remote;

/* Length of the connection ID the endpoint under test addresses its peer
   with.  It changes when the peer issues one of another length and retires the
   old (WP13-15); short headers do not carry it. */
static size_t g_q_dcidlen = CIDLEN;

static void q_refresh_dcidlen(quiche_conn *q) {
  const uint8_t *id = NULL;
  size_t len = CIDLEN;
  quiche_conn_destination_id(q, &id, &len);
  g_q_dcidlen = len <= NGTCP2_MAX_CIDLEN ? len : CIDLEN;
}

static void q_addrs(void) {
  memset(&g_q_local, 0, sizeof(g_q_local));
  memset(&g_q_remote, 0, sizeof(g_q_remote));
  g_q_local.sin_family = AF_INET;
  g_q_local.sin_port = htons(4433);
  g_q_local.sin_addr.s_addr = htonl(0x7f000001u);
  g_q_remote.sin_family = AF_INET;
  g_q_remote.sin_port = htons(12345);
  g_q_remote.sin_addr.s_addr = htonl(0x7f000001u);
}

/* -------------------------------------------------- the two crypto stubs */

/* Length of the first packet in |p|, its packet-number offset, and whether it
   has a long header.  Returns 0 on success. */
static int q_pkt_extent_cid(const uint8_t *p, size_t left, size_t dcidlen,
                            size_t *pktend, size_t *pnoff, int *is_long);

static int q_pkt_extent(const uint8_t *p, size_t left, size_t *pktend,
                        size_t *pnoff, int *is_long) {
  return q_pkt_extent_cid(p, left, g_q_dcidlen, pktend, pnoff, is_long);
}

static int q_pkt_extent_cid(const uint8_t *p, size_t left, size_t dcidlen,
                            size_t *pktend, size_t *pnoff, int *is_long) {
  ngtcp2_pkt_hd hd;
  ngtcp2_ssize hdlen;
  if (left == 0) return -1;
  if (p[0] & NGTCP2_HEADER_FORM_BIT) {
    hdlen = ngtcp2_pkt_decode_hd_long(&hd, p, left);
    if (hdlen < 0) return -1;
    if (hd.type == NGTCP2_PKT_VERSION_NEGOTIATION || hd.type == NGTCP2_PKT_RETRY)
      return -1;
    if (hd.len > left - (size_t)hdlen) return -1;
    *pktend = (size_t)hdlen + hd.len;
    *is_long = 1;
  } else {
    hdlen = ngtcp2_pkt_decode_hd_short(&hd, p, left, dcidlen);
    if (hdlen < 0) return -1;
    *pktend = left;
    *is_long = 0;
  }
  *pnoff = (size_t)hdlen;
  return 0;
}

/* quiche pads a datagram that carries an Initial with raw zero bytes *after*
   the last packet (quiche/src/lib.rs, `out[done..done + pad_len].fill(0)`).  On
   a real path they fail decryption and are dropped; the `fuzzing` stub decrypts
   anything, so they would arrive as a 1-RTT packet for connection ID 00..00 and
   close the connection.  (quiche's own fuzz targets use all-zero connection IDs,
   which hides this.)  Returns the length without that tail: everything from
   the first "packet" whose fixed bit is clear. */
static size_t q_trim(const uint8_t *buf, size_t len) {
  size_t in = 0;
  while (in < len) {
    size_t pktend, pnoff;
    int is_long;
    if (!(buf[in] & 0x40)) break;
    if (q_pkt_extent(buf + in, len - in, &pktend, &pnoff, &is_long) != 0) break;
    in += pktend;
  }
  return in;
}

/* quiche format -> model format, packet by packet, in place.  With
   |short_only| long-header packets are dropped (the model starts after the
   handshake and has no keys for them).  Returns the new length; 0 if nothing
   is left or the datagram does not parse. */
static size_t q_to_model(uint8_t *buf, size_t len, int short_only) {
  size_t in = 0, out = 0;
  while (in < len) {
    size_t pktend, pnoff, pnlen, i;
    int is_long;
    uint8_t *p = buf + in;
    uint8_t mask[5];
    if (q_pkt_extent(p, len - in, &pktend, &pnoff, &is_long) != 0) break;
    pnlen = (size_t)(p[0] & 0x03) + 1;
    if (pktend < pnoff + pnlen + TAGLEN || pktend < pnoff + 4 + 16) break;
    if (!(is_long && short_only)) {
      memset(p + pktend - TAGLEN, 0xa5, TAGLEN);
      memcpy(mask, p + pnoff + 4, 5);
      p[0] ^= (uint8_t)(mask[0] & (is_long ? 0x0f : 0x1f));
      for (i = 0; i < pnlen; ++i) p[pnoff + i] ^= mask[1 + i];
      memmove(buf + out, p, pktend);
      out += pktend;
    }
    in += pktend;
  }
  return out;
}

/* The largest 1-RTT packet number in a quiche-format datagram, or -1. */
static int64_t q_max_short_pn(const uint8_t *buf, size_t len) {
  size_t in = 0;
  int64_t best = -1;
  while (in < len) {
    size_t pktend, pnoff, pnlen, i;
    int is_long;
    const uint8_t *p = buf + in;
    if (q_pkt_extent(p, len - in, &pktend, &pnoff, &is_long) != 0) break;
    pnlen = (size_t)(p[0] & 0x03) + 1;
    if (!is_long && pktend >= pnoff + pnlen) {
      int64_t v = 0;
      for (i = 0; i < pnlen; ++i) v = (v << 8) | p[pnoff + i];
      if (v > best) best = v; /* handshake-era numbers fit their encoding */
    }
    in += pktend;
  }
  return best;
}

/* The packet the forged peer sends, in quiche's format: the plaintext
   build_peer_pkt just produced (g_build_plain), a four-byte packet number, a
   tag that is not the header (crypto/mod.rs: `open` fails on tag == ad). */
static size_t q_build_peer_pkt(int space, int64_t pn, uint8_t *out, size_t cap) {
  size_t n = 0, i, paylen = g_build_plainlen;
  size_t bodylen = 4 + paylen + TAGLEN;
  if (cap < 64 + bodylen) return 0;
  if (space == 2) {
    out[n++] = 0x43;
    memcpy(out + n, g_cid_local, CIDLEN); n += CIDLEN;
  } else {
    out[n++] = (uint8_t)(0xc3 | ((space == 0 ? 0 : 2) << 4));
    out[n++] = 0; out[n++] = 0; out[n++] = 0; out[n++] = 1;
    out[n++] = CIDLEN; memcpy(out + n, g_cid_local, CIDLEN); n += CIDLEN;
    out[n++] = CIDLEN; memcpy(out + n, g_cid_remote, CIDLEN); n += CIDLEN;
    if (space == 0) out[n++] = 0; /* token length */
    out[n++] = (uint8_t)(0x40 | (bodylen >> 8));
    out[n++] = (uint8_t)(bodylen & 0xff);
  }
  for (i = 0; i < 4; ++i) out[n++] = (uint8_t)((uint64_t)pn >> (8 * (3 - i)));
  memcpy(out + n, g_build_plain, paylen); n += paylen;
  memset(out + n, 0xa5, TAGLEN); n += TAGLEN;
  return n;
}

/* ------------------------------------------------------------ observing */

/* The QUIC-level result of the last call, in the encoding described above. */
static int q_conn_rv(harness *h) {
  bool is_app = false;
  uint64_t code = 0;
  const uint8_t *reason;
  size_t reason_len;
  if (quiche_conn_local_error(h->q, &is_app, &code, &reason, &reason_len))
    return is_app ? -1 : (int)(1 + code);
  if (quiche_conn_is_timed_out(h->q)) return -1;
  return 0;
}

static int drv_obs_error(int rv, uint64_t *code) {
  if (rv == 0) return 0;
  if (rv < 0) return -1;
  *code = (uint64_t)(rv - 1);
  return 1;
}

static int drv_cb_observable(const char *n) {
  return strcmp(n, "recv_stream_data") == 0 || strcmp(n, "stream_reset") == 0;
}

static uint64_t *q_rd_off(harness *h, uint64_t sid) {
  size_t i;
  for (i = 0; i < h->q_nstreams; ++i)
    if (h->q_sid[i] == sid) return &h->q_off[i];
  if (h->q_nstreams == sizeof(h->q_sid) / sizeof(h->q_sid[0])) return NULL;
  h->q_sid[h->q_nstreams] = sid;
  h->q_off[h->q_nstreams] = 0;
  return &h->q_off[h->q_nstreams++];
}

/* What an application learns after a receive, in ngtcp2's trace words. */
static void q_poll_events(harness *h) {
  uint64_t sid;
  uint8_t sink[4096];
  quiche_stream_iter *it = quiche_conn_readable(h->q);
  if (!it) return;
  while (quiche_stream_iter_next(it, &sid)) {
    int guard;
    for (guard = 0; guard < 64; ++guard) {
      bool fin = false;
      uint64_t err = 0;
      uint64_t *off = q_rd_off(h, sid);
      ssize_t n = quiche_conn_stream_recv(h->q, sid, sink, sizeof(sink), &fin, &err);
      if (n == QUICHE_ERR_STREAM_RESET) {
        TR(h, "CB  stream_reset id=%" PRIu64 " app_error_code=%" PRIu64 "\n", sid, err);
        break;
      }
      if (n < 0) break;
      TR(h, "CB  recv_stream_data id=%" PRIu64 " off=%" PRIu64 " len=%zd fin=%d early=0\n",
         sid, off ? *off : 0, n, fin ? 1 : 0);
      if (off) *off += (uint64_t)n;
      if (fin || n == 0) break;
    }
  }
  quiche_stream_iter_free(it);
}

static void tr_time(harness *h) {
  uint64_t t = quiche_conn_timeout_as_nanos(h->q);
  if (t == UINT64_MAX) TR(h, "TIME now=%" PRIu64 " expiry=none\n", h->ts);
  else TR(h, "TIME now=%" PRIu64 " expiry=%" PRIu64 "\n", h->ts, h->ts + t);
  MH_TICK(h);
}

static void q_note_error(harness *h, int rv) {
  if (rv == 0) return;
  if (rv > 0) TR(h, "ERR type=transport code=%d\n", rv - 1);
  else TR(h, "ERR type=other\n");
  h->fatal = 1;
}

/* Everything quiche wants to send now, shown to the model.  |check| = 0 only
   while the handshake is being replayed and long headers must be dropped. */
static void q_flush(harness *h) {
  uint8_t buf[PKTBUF];
  int iter;
  for (iter = 0; iter < 16; ++iter) {
    quiche_send_info si;
    size_t n;
    ssize_t w;
    quiche_fuzz_set_clock(h->ts);
    w = quiche_conn_send(h->q, buf, sizeof(buf), &si);
    if (w <= 0) break;
    q_refresh_dcidlen(h->q);
    if (getenv("QDRV_DEBUG")) {
      int k;
      fprintf(stderr, "qdrv: out len=%zd api_dcidlen=%zu hdr=", w, g_q_dcidlen);
      for (k = 0; k < 24 && k < w; ++k) fprintf(stderr, "%02x", buf[k]);
      fprintf(stderr, "\n");
    }
    n = q_to_model(buf, q_trim(buf, (size_t)w), 1);
    if (n == 0) continue;
    dump_out_datagram(h, buf, n);
    MH_OUT(h, buf, n);
  }
}

/* ---------------------------------------------------------------- setup */

static quiche_config *q_config(void) {
  quiche_config *c = quiche_config_new(QUICHE_PROTOCOL_VERSION);
  const char *crt = getenv("QUICHE_FUZZ_CRT"), *key = getenv("QUICHE_FUZZ_KEY");
  if (!c) return NULL;
  if (!crt) crt = "../quiche/fuzz/cert.crt";
  if (!key) key = "../quiche/fuzz/cert.key";
  if (quiche_config_load_cert_chain_from_pem_file(c, crt) != 0 ||
      quiche_config_load_priv_key_from_pem_file(c, key) != 0) {
    fprintf(stderr, "quiche_driver: cannot load %s / %s "
                    "(set QUICHE_FUZZ_CRT / QUICHE_FUZZ_KEY)\n", crt, key);
    quiche_config_free(c);
    return NULL;
  }
  quiche_config_verify_peer(c, false);
  quiche_config_set_application_protos(c, (const uint8_t *)"\x04" "diff", 5);
  /* conn_driver.h's fill_params, item for item. */
  quiche_config_set_initial_max_data(c, 4096);
  quiche_config_set_initial_max_stream_data_bidi_local(c, 1024);
  quiche_config_set_initial_max_stream_data_bidi_remote(c, 1024);
  quiche_config_set_initial_max_stream_data_uni(c, 1024);
  quiche_config_set_initial_max_streams_bidi(c, 4);
  quiche_config_set_initial_max_streams_uni(c, 2);
  quiche_config_set_max_idle_timeout(c, 30000);
  quiche_config_set_max_recv_udp_payload_size(c, 1200);
  quiche_config_set_max_send_udp_payload_size(c, 1200);
  quiche_config_set_active_connection_id_limit(c, 4);
  quiche_config_set_ack_delay_exponent(c, 3);
  quiche_config_set_max_ack_delay(c, 25);
  quiche_config_enable_dgram(c, true, 16, 16);
  quiche_config_set_disable_active_migration(c, false);
  quiche_config_grease(c, false);
  quiche_config_discover_pmtu(c, false);
  quiche_config_set_cc_algorithm(c, QUICHE_CC_RENO);
  quiche_config_enable_pacing(c, false);
  return c;
}

static void q_debug_log(const char *line, void *argp) {
  (void)argp;
  fprintf(stderr, "quiche: %s\n", line);
}

static int setup_conn(harness *h, int server) {
  static quiche_config *cfg;
  static int logging;
  quiche_conn *peer, *srv, *cli;
  struct { uint8_t b[PKTBUF]; size_t n; int from_us; } fl[Q_MAX_FLIGHT];
  int nfl = 0, round, i;
  quiche_recv_info to_us, to_peer;
  int64_t peer_max = -1;

  if (!logging && getenv("QDRV_DEBUG")) {
    quiche_enable_debug_logging(q_debug_log, NULL);
    logging = 1;
  }
  q_addrs();
  g_q_dcidlen = CIDLEN;
  if (!cfg) cfg = q_config();
  if (!cfg) return -1;
  h->ts = 0;
  quiche_fuzz_set_clock(0);

  /* We are 127.0.0.1:4433 with connection ID a0.., the peer :12345 with b0..,
     whichever role we play -- the addresses and IDs of conn_driver.h. */
  srv = quiche_accept(server ? g_cid_local : g_cid_remote, CIDLEN, NULL, 0,
                      (struct sockaddr *)(server ? &g_q_local : &g_q_remote),
                      sizeof(g_q_local),
                      (struct sockaddr *)(server ? &g_q_remote : &g_q_local),
                      sizeof(g_q_local), cfg);
  cli = quiche_connect("quic.tech", server ? g_cid_remote : g_cid_local, CIDLEN,
                       (struct sockaddr *)(server ? &g_q_remote : &g_q_local),
                       sizeof(g_q_local),
                       (struct sockaddr *)(server ? &g_q_local : &g_q_remote),
                       sizeof(g_q_local), cfg);
  if (!srv || !cli) {
    fprintf(stderr, "quiche_driver: accept=%p connect=%p\n", (void *)srv, (void *)cli);
    return -1;
  }
  h->q = server ? srv : cli;
  peer = server ? cli : srv;

  to_us.from = (struct sockaddr *)&g_q_remote; to_us.from_len = sizeof(g_q_remote);
  to_us.to = (struct sockaddr *)&g_q_local;    to_us.to_len = sizeof(g_q_local);
  to_peer.from = (struct sockaddr *)&g_q_local; to_peer.from_len = sizeof(g_q_local);
  to_peer.to = (struct sockaddr *)&g_q_remote;  to_peer.to_len = sizeof(g_q_remote);

  for (round = 0; round < 16; ++round) {
    int moved = 0, side;
    /* the client speaks first */
    for (side = 0; side < 2; ++side) {
      int from_us = (side == 0) ? !server : server;
      quiche_conn *tx = from_us ? h->q : peer, *rx = from_us ? peer : h->q;
      for (;;) {
        quiche_send_info si;
        uint8_t tmp[PKTBUF];
        ssize_t w = quiche_conn_send(tx, tmp, sizeof(tmp), &si);
        if (w <= 0) break;
        w = (ssize_t)q_trim(tmp, (size_t)w);
        if (w == 0) continue;
        moved = 1;
        if (nfl < Q_MAX_FLIGHT) {
          memcpy(fl[nfl].b, tmp, (size_t)w);
          fl[nfl].n = (size_t)w;
          fl[nfl].from_us = from_us;
          ++nfl;
        }
        if (!from_us) {
          int64_t m = q_max_short_pn(tmp, (size_t)w);
          if (m > peer_max) peer_max = m;
        }
        {
          ssize_t r = quiche_conn_recv(rx, tmp, (size_t)w, from_us ? &to_peer : &to_us);
          if (getenv("QDRV_DEBUG"))
            fprintf(stderr, "hs round=%d from_us=%d sent=%zd recv=%zd\n", round, from_us, w, r);
        }
      }
    }
    if (!moved) break;
  }
  if (!quiche_conn_is_established(h->q) || !quiche_conn_is_established(peer)) {
    fprintf(stderr, "quiche_driver: handshake incomplete (us=%d peer=%d, %d datagrams)\n",
            quiche_conn_is_established(h->q), quiche_conn_is_established(peer), nfl);
    quiche_conn_free(peer);
    return -1;
  }
  quiche_conn_free(peer);
  h->q_peer_pn_base = peer_max + 1;
  h->q_next_bidi = server ? 1 : 0;
  h->q_next_uni = server ? 3 : 2;

  /* The 1-RTT packets of the handshake, in order, so that the model's packet
     numbers and ACK state are the endpoint's. */
  TR(h, "HS  peer_pn_base=%" PRId64 "\n", h->q_peer_pn_base);
  for (i = 0; i < nfl; ++i) {
    size_t n = q_to_model(fl[i].b, fl[i].n, 1);
    if (n == 0) continue;
    if (fl[i].from_us) {
      dump_out_datagram(h, fl[i].b, n);
      MH_OUT(h, fl[i].b, n);
    } else {
      MH_SYNTH_RECV(h, fl[i].b, n);
    }
  }
  q_poll_events(h);
  return 0;
}

static void drv_free(harness *h) {
  if (h->q) quiche_conn_free(h->q);
  h->q = NULL;
}

/* ---------------------------------------------------------------- steps */

static void step_recv(harness *h, int space, int64_t pn, const uint8_t *fb,
                      size_t fblen) {
  uint8_t mpkt[PKTBUF], qpkt[PKTBUF];
  quiche_recv_info ri;
  ngtcp2_ssize mlen;
  size_t qlen;
  int rv;

  if (space == 2) pn += h->q_peer_pn_base;
  mlen = build_peer_pkt(space, pn, fb, fblen, mpkt, sizeof(mpkt));
  if (mlen < 0) {
    TR(h, "IN  space=%s pn=%" PRId64 " frames=[] build=failed\n", space_name(space), pn);
    tr_time(h);
    return;
  }
  qlen = q_build_peer_pkt(space, pn, qpkt, sizeof(qpkt));
  TR(h, "IN  space=%s pn=%" PRId64 " len=%zu frames=[", space_name(space), pn,
     (size_t)mlen);
  dump_frames_joined(&h->tr, g_build_plain, g_build_plainlen);
  TR(h, "]\n");

  ri.from = (struct sockaddr *)&g_q_remote; ri.from_len = sizeof(g_q_remote);
  ri.to = (struct sockaddr *)&g_q_local;    ri.to_len = sizeof(g_q_local);
  MH_MARK(h);
  quiche_fuzz_set_clock(h->ts);
  (void)quiche_conn_recv(h->q, qpkt, qlen, &ri);
  q_poll_events(h);
  rv = q_conn_rv(h);
  TR(h, "RET recv=%d\n", rv);
  MH_RECV(h, mpkt, (size_t)mlen, rv);
  q_note_error(h, rv);
  tr_time(h);
}

static void step_time(harness *h, uint64_t d) {
  int rv;
  h->ts += d;
  MH_MARK(h);
  quiche_fuzz_set_clock(h->ts);
  if (quiche_conn_timeout_as_nanos(h->q) == 0) quiche_conn_on_timeout(h->q);
  rv = q_conn_rv(h);
  TR(h, "RET on_timeout=%d\n", rv);
  MH_TIME(h, rv);
  q_note_error(h, rv);
  tr_time(h);
}

static void step_open(harness *h, int uni) {
  /* quiche has no "open": a stream exists from the first stream_send, and
     quiche_conn_peer_streams_left_* only counts streams that exist.  A
     zero-length send without fin creates the stream, puts nothing on the wire,
     and fails with STREAM_LIMIT exactly when the peer's limit is reached. */
  int64_t sid = uni ? h->q_next_uni : h->q_next_bidi;
  uint64_t err = 0;
  ssize_t w;
  int rv;
  MH_MARK(h);
  quiche_fuzz_set_clock(h->ts);
  w = quiche_conn_stream_send(h->q, (uint64_t)sid, (const uint8_t *)"", 0, false, &err);
  rv = (w < 0 && w != QUICHE_ERR_DONE) ? (int)w : 0;
  MH_OPEN(h, uni, rv, rv == 0 ? sid : -1);
  if (rv == 0) {
    h->last_stream = sid;
    if (uni) h->q_next_uni += 4; else h->q_next_bidi += 4;
    TR(h, "RET open_%s_stream=OK id=%" PRId64 "\n", uni ? "uni" : "bidi", sid);
  } else {
    TR(h, "RET open_%s_stream=%d\n", uni ? "uni" : "bidi", rv);
  }
  tr_time(h);
}

static uint8_t g_write_data[1024];

static void init_write_data(void) {
  size_t i;
  for (i = 0; i < sizeof(g_write_data); ++i)
    g_write_data[i] = (uint8_t)('a' + (i % 26));
}

static void step_write(harness *h, int64_t sid, size_t n, int fin) {
  uint64_t err = 0;
  ssize_t w;
  if (n > sizeof(g_write_data)) n = sizeof(g_write_data);
  /* quiche would open a locally-initiated stream on this write; ngtcp2 answers
     STREAM_NOT_FOUND for one that was never opened and writes nothing.  The
     model takes ngtcp2's view (a stream exists once `open` created it), so the
     driver does too, and inputs mean the same thing to both engines. */
  if (sid >= 0 && ((sid & 1) == (h->server ? 1 : 0)) &&
      sid >= ((sid & 2) ? h->q_next_uni : h->q_next_bidi)) {
    MH_MARK(h);
    TR(h, "RET stream_send=STREAM_NOT_FOUND\n");
    tr_time(h);
    return;
  }
  MH_MARK(h);
  MH_WRITE(h, sid, n, fin);
  quiche_fuzz_set_clock(h->ts);
  w = quiche_conn_stream_send(h->q, (uint64_t)sid, g_write_data, n, fin != 0, &err);
  TR(h, "RET stream_send=%zd\n", w);
  q_flush(h);
  tr_time(h);
}

static void step_drain(harness *h) {
  MH_MARK(h);
  q_flush(h);
  tr_time(h);
}

enum { SHUT_RD_ = 0, SHUT_WR_ = 1, SHUT_RDWR_ = 2 };

static void step_shutdown(harness *h, int which, int64_t sid, uint64_t err) {
  int rv = 0, r;
  MH_MARK(h);
  quiche_fuzz_set_clock(h->ts);
  if (which != SHUT_WR_) {
    r = quiche_conn_stream_shutdown(h->q, (uint64_t)sid, QUICHE_SHUTDOWN_READ, err);
    if (r != 0 && r != QUICHE_ERR_DONE) rv = r;
  }
  if (which != SHUT_RD_) {
    r = quiche_conn_stream_shutdown(h->q, (uint64_t)sid, QUICHE_SHUTDOWN_WRITE, err);
    if (r != 0 && r != QUICHE_ERR_DONE) rv = r;
  }
  TR(h, "RET stream_shutdown=%d\n", rv);
  MH_SHUTDOWN(h, which, sid, err, rv);
  tr_time(h);
}

enum { EXT_STREAM = 0, EXT_CONN = 1, EXT_STREAMS_BIDI = 2, EXT_STREAMS_UNI = 3 };

static void step_extend(harness *h, int which, int64_t sid, uint64_t n) {
  (void)which; (void)sid; (void)n;
  TR(h, "RET extend=UNSUPPORTED\n");
  tr_time(h);
}

#endif /* QUICHE_DRIVER_H */
