/*
 * gquiche_driver.h -- the engine half of conn_driver.h for Google QUICHE, the
 * QUIC implementation of Chrome.
 *
 * Included by conn_driver.h in place of its ngtcp2 step functions when
 * DRIVER_GQUICHE is defined (which implies DRIVER_QUICHE, "the engine is not
 * ngtcp2").  The script grammar, the binary fuzz format, the trace vocabulary
 * and the MH_* model hooks are conn_driver.h's and unchanged, so the same input
 * drives ngtcp2, Cloudflare quiche or Google QUICHE.
 *
 * QUICHE is C++; harness/gquiche/gquiche_shim.cc puts it behind the C calls of
 * gquiche_shim.h and is linked, with QUICHE, into libgquiche_shim.so.
 *
 * ===========================================================================
 * What is different about Google QUICHE
 * ===========================================================================
 *
 * Nothing is converted.  QUICHE's packet protection is an interface, so the
 *   shim installs the model's own stub (Quic.Protection.stub) and the bytes
 *   QUICHE reads and writes are the bytes the model and ngtcp2 see.  There is
 *   no handshake either: keys and transport parameters are installed by hand,
 *   as conn_driver.h does for ngtcp2, and 1-RTT packet numbers are absolute.
 *   (QUICHE numbers its own packets from 1, ngtcp2 from 0.)
 *
 * QUICHE writes when it likes.  ngtcp2 and quiche produce a datagram only when
 *   asked (`write`, `drain`); QUICHE calls its packet writer from inside
 *   ProcessUdpPacket, an alarm or a stream write.  The shim queues what is
 *   written and the driver hands it to MH_OUT at the end of the step, *after*
 *   the step's own hook, so that the model has processed the datagram that
 *   provoked the response before it judges the response.
 *
 * Setup already sends.  A server is given the Handshake packet the model is
 *   primed with (it validates the peer's address; without it QUICHE stays
 *   under the anti-amplification limit for good).  Completing the handshake
 *   then makes a server write HANDSHAKE_DONE and NEW_CONNECTION_ID; setup_conn
 *   flushes them to MH_OUT.
 *
 * Time is alarms.  `time <d>` advances the clock and fires every alarm that is
 *   due, earliest first; `drain` fires what is due and calls OnCanWrite.
 *
 * Callbacks are QuicStream / QuicSession virtuals, printed in ngtcp2's words:
 *     stream_open         QuicSession::CreateIncomingStream
 *     recv_stream_data    QuicStream::OnDataAvailable (the application reads
 *                         everything at once)
 *     stream_reset        QuicStream::OnStreamReset
 *     recv_stop_sending   QuicStream::OnStopSending
 *     recv_crypto_data    CryptoMessageParser::ProcessInput
 *   Everything else is excluded from the comparison (drv_cb_observable).
 *
 * Return codes handed to the MH_* hooks are quiche_driver.h's:
 *     0 no connection error; -1 closed, but not by a transport error of ours;
 *     1 + code closed with transport error |code|.
 *
 * Not supported: `extend_*` steps -- QUICHE extends credit by itself as the
 *   application reads.  Accepted and ignored, so inputs stay interchangeable.
 */
#ifndef GQUICHE_DRIVER_H
#define GQUICHE_DRIVER_H

#include "gquiche/gquiche_shim.h"

static int drv_obs_error(int rv, uint64_t *code) {
  if (rv == 0) return 0;
  if (rv < 0) return -1;
  *code = (uint64_t)(rv - 1);
  return 1;
}

static int drv_cb_observable(const char *n) {
  return strcmp(n, "recv_stream_data") == 0 || strcmp(n, "stream_reset") == 0 ||
         strcmp(n, "stream_open") == 0 || strcmp(n, "recv_stop_sending") == 0 ||
         strcmp(n, "recv_crypto_data") == 0;
}

static void gq_poll_events(harness *h) {
  char line[256];
  while (gq_pop_event(h->gq, line, sizeof(line))) TR(h, "CB  %s\n", line);
}

static void tr_time(harness *h) {
  uint64_t e = gq_next_deadline(h->gq);
  if (e == UINT64_MAX) TR(h, "TIME now=%" PRIu64 " expiry=none\n", h->ts);
  else TR(h, "TIME now=%" PRIu64 " expiry=%" PRIu64 "\n", h->ts, e);
  MH_TICK(h);
}

static void gq_note_error(harness *h, int rv) {
  if (rv == 0 || h->fatal) return;
  /* %.160s: sb_printf's line buffer is 256 bytes and QUICHE's reasons quote
     peer-controlled values. */
  if (rv > 0) TR(h, "ERR type=transport code=%d detail=\"%.160s\"\n", rv - 1,
                 gq_close_detail(h->gq));
  else TR(h, "ERR type=other detail=\"%.160s\"\n", gq_close_detail(h->gq));
  h->fatal = 1;
}

/* Everything QUICHE has written since the last call, shown to the model.
   The datagram a closing connection writes is traced but not checked unless
   DIFF_GQ_CHECK_CLOSE is set: the other two drivers never show theirs to the
   model (conn_driver.h's tr_fatal writes it outside MH_OUT, quiche_driver.h
   stops flushing), and the model rejects QUICHE's, which bundles an ACK with
   the CONNECTION_CLOSE -- see endpoint_diff.md, "Google QUICHE". */
static void gq_flush(harness *h) {
  uint8_t buf[PKTBUF];
  size_t n;
  int check = gq_status(h->gq) == 0 || getenv("DIFF_GQ_CHECK_CLOSE") != NULL;
  while ((n = gq_pop_out(h->gq, buf, sizeof(buf), &g_q_dcidlen)) != 0) {
    dump_out_datagram(h, buf, n);
    if (check) MH_OUT(h, buf, n);
  }
}

static int setup_conn(harness *h, int server) {
  h->ts = 0;
  g_q_dcidlen = CIDLEN;
  h->gq = gq_new(server, g_cid_local, g_cid_remote, CIDLEN, h->ts);
  if (!h->gq) return -1;
  if (server) {
    /* The Handshake packet carrying only PADDING that endpoint_diff.c primes
       the model with (endpoint_diff.md section 2, item 3), for the same
       reason: it is what validates the client's address. */
    static const uint8_t pad[4] = {0, 0, 0, 0};
    uint8_t pkt[PKTBUF];
    ngtcp2_ssize n = build_peer_pkt(1, 0, pad, sizeof(pad), pkt, sizeof(pkt));
    if (n < 0) return -1;
    gq_recv(h->gq, pkt, (size_t)n);
  }
  if (gq_handshake_done(h->gq) != 0) return -1;
  gq_poll_events(h);
  gq_flush(h);
  return 0;
}

static void drv_free(harness *h) {
  if (h->gq) gq_free(h->gq);
  h->gq = NULL;
}

/* ---------------------------------------------------------------- steps */

static void step_recv(harness *h, int space, int64_t pn, const uint8_t *fb,
                      size_t fblen) {
  uint8_t pkt[PKTBUF];
  ngtcp2_ssize pktlen;
  int rv;

  pktlen = build_peer_pkt(space, pn, fb, fblen, pkt, sizeof(pkt));
  if (pktlen < 0) {
    TR(h, "IN  space=%s pn=%" PRId64 " frames=[] build=failed\n", space_name(space), pn);
    tr_time(h);
    return;
  }
  TR(h, "IN  space=%s pn=%" PRId64 " len=%zu frames=[", space_name(space), pn,
     (size_t)pktlen);
  dump_frames_joined(&h->tr, g_build_plain, g_build_plainlen);
  TR(h, "]\n");

  MH_MARK(h);
  gq_set_clock(h->gq, h->ts);
  h->recv_space = space;
  gq_recv_meta(h->gq, pkt, (size_t)pktlen, h->recv_ecn, h->recv_alt);
  /* QUICHE defers part of a packet's processing to alarms set for "now"
     (retiring a connection ID the peer asked to retire, for one); an event
     loop runs them before it reads the next datagram. */
  gq_fire_alarms(h->gq);
  gq_poll_events(h);
  rv = gq_status(h->gq);
  TR(h, "RET recv=%d\n", rv);
  MH_RECV(h, pkt, (size_t)pktlen, rv);
  gq_flush(h);
  gq_note_error(h, rv);
  tr_time(h);
}

static void step_time(harness *h, uint64_t d) {
  int rv;
  h->ts += d;
  MH_MARK(h);
  gq_set_clock(h->gq, h->ts);
  gq_fire_alarms(h->gq);
  gq_poll_events(h);
  rv = gq_status(h->gq);
  TR(h, "RET fire_alarms=%d\n", rv);
  MH_TIME(h, rv);
  gq_flush(h);
  gq_note_error(h, rv);
  tr_time(h);
}

static void step_open(harness *h, int uni) {
  int64_t sid;
  int rv;
  MH_MARK(h);
  gq_set_clock(h->gq, h->ts);
  sid = gq_open(h->gq, uni);
  rv = sid < 0 ? -1 : 0;
  MH_OPEN(h, uni, rv, sid);
  if (rv == 0) {
    h->last_stream = sid;
    TR(h, "RET open_%s_stream=OK id=%" PRId64 "\n", uni ? "uni" : "bidi", sid);
  } else {
    TR(h, "RET open_%s_stream=STREAM_ID_BLOCKED\n", uni ? "uni" : "bidi");
  }
  gq_flush(h); /* STREAMS_BLOCKED */
  tr_time(h);
}

static uint8_t g_write_data[1024];

static void init_write_data(void) {
  size_t i;
  for (i = 0; i < sizeof(g_write_data); ++i)
    g_write_data[i] = (uint8_t)('a' + (i % 26));
}

static const char *gq_rc_name(int rv) {
  switch (rv) {
  case GQ_OK:               return "OK";
  case GQ_STREAM_NOT_FOUND: return "STREAM_NOT_FOUND";
  case GQ_STREAM_SHUT_WR:   return "STREAM_SHUT_WR";
  case GQ_STREAM_STATE:     return "STREAM_STATE";
  }
  return "?";
}

static void step_write(harness *h, int64_t sid, size_t n, int fin) {
  int rv;
  if (n > sizeof(g_write_data)) n = sizeof(g_write_data);
  MH_MARK(h);
  MH_WRITE(h, sid, n, fin);
  gq_set_clock(h->gq, h->ts);
  rv = gq_write(h->gq, sid, g_write_data, n, fin);
  TR(h, "RET stream_write=%s\n", gq_rc_name(rv));
  gq_poll_events(h);
  gq_flush(h);
  gq_note_error(h, gq_status(h->gq));
  tr_time(h);
}

static void step_drain(harness *h) {
  MH_MARK(h);
  gq_set_clock(h->gq, h->ts);
  gq_fire_alarms(h->gq);
  gq_can_write(h->gq);
  gq_poll_events(h);
  gq_flush(h);
  gq_note_error(h, gq_status(h->gq));
  tr_time(h);
}

enum { SHUT_RD_ = 0, SHUT_WR_ = 1, SHUT_RDWR_ = 2 };

static void step_shutdown(harness *h, int which, int64_t sid, uint64_t err) {
  int rv, rd = GQ_OK, wr = GQ_OK;
  MH_MARK(h);
  gq_set_clock(h->gq, h->ts);
  if (which != SHUT_WR_) rd = gq_shutdown_read(h->gq, sid, err);
  if (which != SHUT_RD_) wr = gq_shutdown_write(h->gq, sid, err);
  /* `shutdown` of a unidirectional stream acts on the half that exists, as
     ngtcp2_conn_shutdown_stream does. */
  if (which == SHUT_RDWR_ && (rd == GQ_STREAM_STATE) != (wr == GQ_STREAM_STATE))
    rv = rd == GQ_STREAM_STATE ? wr : rd;
  else
    rv = rd != GQ_OK ? rd : wr;
  TR(h, "RET stream_shutdown=%s\n", gq_rc_name(rv));
  MH_SHUTDOWN(h, which, sid, err, rv);
  gq_poll_events(h);
  gq_flush(h);
  gq_note_error(h, gq_status(h->gq));
  tr_time(h);
}

enum { EXT_STREAM = 0, EXT_CONN = 1, EXT_STREAMS_BIDI = 2, EXT_STREAMS_UNI = 3 };

static void step_extend(harness *h, int which, int64_t sid, uint64_t n) {
  (void)which; (void)sid; (void)n;
  TR(h, "RET extend=UNSUPPORTED\n");
  tr_time(h);
}

#endif /* GQUICHE_DRIVER_H */
