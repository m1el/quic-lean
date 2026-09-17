/*
 * Differential harness for the packet layer.  The first input byte picks a mode:
 *
 *   0  headers    ngtcp2_pkt_decode_hd_long/_short and
 *                 ngtcp2_pkt_decode_version_cid on raw bytes vs Quic.header /
 *                 Quic.versionCid.
 *   1  pktnum     ngtcp2_pkt_adjust_pkt_num vs Quic.decodePacketNumber.
 *   2  roundtrip  ngtcp2's packet writer (ngtcp2_ppe) builds a protected packet
 *                 with stub crypto; Quic.decodePacket must take it apart again
 *                 and recover the same header, packet number and frames.
 *
 * Stub crypto (same as Quic.Protection.stub): plaintext payload, tag = 0xA5
 * repeated, header-protection mask = first 5 bytes of the sample.
 */
#include "diff_common.h"

extern lean_object *quic_model_dump_header(lean_object *, uint32_t);
extern lean_object *quic_model_dump_packet(lean_object *, uint32_t, uint32_t,
                                           uint64_t, uint8_t);
extern uint64_t quic_model_decode_pn(uint64_t, uint64_t, uint8_t);

#define TAGLEN 16

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  (void)argc;
  (void)argv;
  model_init();
  return 0;
}

static const char *long_type_str(uint8_t type) {
  switch (type) {
  case NGTCP2_PKT_INITIAL:
    return "INITIAL";
  case NGTCP2_PKT_0RTT:
    return "0RTT";
  case NGTCP2_PKT_HANDSHAKE:
    return "HANDSHAKE";
  case NGTCP2_PKT_RETRY:
    return "RETRY";
  default:
    return "?";
  }
}

/* Returns header length or -1. */
static ngtcp2_ssize c_dump_hd(sbuf *sb, const uint8_t *pkt, size_t pktlen,
                              size_t short_dcidlen) {
  ngtcp2_pkt_hd hd;
  ngtcp2_ssize n;

  if (pkt[0] & NGTCP2_HEADER_FORM_BIT) {
    n = ngtcp2_pkt_decode_hd_long(&hd, pkt, pktlen);
    if (n < 0) {
      sb_printf(sb, "HD ERR\n");
      return -1;
    }
    if (hd.type == NGTCP2_PKT_VERSION_NEGOTIATION) {
      sb_printf(sb, "VN dcid=");
      sb_hex(sb, hd.dcid.data, hd.dcid.datalen);
      sb_printf(sb, " scid=");
      sb_hex(sb, hd.scid.data, hd.scid.datalen);
    } else {
      sb_printf(sb, "LONG type=%s ver=%u fixed=%d dcid=", long_type_str(hd.type),
                hd.version, (hd.flags & NGTCP2_PKT_FLAG_FIXED_BIT_CLEAR) ? 0 : 1);
      sb_hex(sb, hd.dcid.data, hd.dcid.datalen);
      sb_printf(sb, " scid=");
      sb_hex(sb, hd.scid.data, hd.scid.datalen);
      sb_printf(sb, " token=");
      if (hd.tokenlen) sb_hex(sb, hd.token, hd.tokenlen);
      sb_printf(sb, " len=%zu", hd.len);
    }
  } else {
    n = ngtcp2_pkt_decode_hd_short(&hd, pkt, pktlen, short_dcidlen);
    if (n < 0) {
      sb_printf(sb, "HD ERR\n");
      return -1;
    }
    sb_printf(sb, "SHORT fixed=%d dcid=",
              (hd.flags & NGTCP2_PKT_FLAG_FIXED_BIT_CLEAR) ? 0 : 1);
    sb_hex(sb, hd.dcid.data, hd.dcid.datalen);
  }
  sb_printf(sb, " hdlen=%td\n", (ptrdiff_t)n);
  return n;
}

static void mode_headers(const uint8_t *data, size_t size) {
  sbuf sb = {0};
  size_t short_dcidlen;
  uint8_t *pkt;
  size_t pktlen;
  ngtcp2_version_cid vc;
  int rv;

  if (size < 2) return;
  short_dcidlen = data[0] % (NGTCP2_MAX_CIDLEN + 1);
  pktlen = size - 1;
  pkt = malloc(pktlen);
  memcpy(pkt, data + 1, pktlen);

  sb_reserve(&sb, 16);
  sb.p[0] = 0;
  c_dump_hd(&sb, pkt, pktlen, short_dcidlen);

  rv = ngtcp2_pkt_decode_version_cid(&vc, pkt, pktlen, short_dcidlen);
  if (rv == 0 || rv == NGTCP2_ERR_VERSION_NEGOTIATION) {
    sb_printf(&sb, "VCID rc=%s ver=%u dcid=", rv == 0 ? "OK" : "VN", vc.version);
    sb_hex(&sb, vc.dcid, vc.dcidlen);
    sb_printf(&sb, " scid=");
    if (vc.scidlen) sb_hex(&sb, vc.scid, vc.scidlen);
    sb_printf(&sb, "\n");
  } else {
    sb_printf(&sb, "VCID ERR\n");
  }

  expect_same("headers", &sb,
              quic_model_dump_header(model_bytes(pkt, pktlen),
                                     (uint32_t)short_dcidlen),
              data, size);
  free(pkt);
  free(sb.p);
}

static uint64_t get_u64(const uint8_t *p) {
  uint64_t v = 0;
  int i;
  for (i = 0; i < 8; ++i) v = (v << 8) | p[i];
  return v;
}

static void mode_pktnum(const uint8_t *data, size_t size) {
  uint64_t expected, truncated, model;
  size_t len;
  int64_t c;

  if (size < 13) return;
  /* ngtcp2 asserts (instead of taking RFC 9000 A.3's `candidate_pn <
     (1 << 62) - pn_win` guard) once the expected packet number is within one
     window of 2^62; keep clear of that so the rest of the domain gets fuzzed.
     See FINDINGS.md. */
  expected = get_u64(data) % ((1ULL << 62) - (1ULL << 33));
  len = (size_t)(data[8] % 4) + 1;
  truncated = (get_u64(data + 5) & 0xffffffffULL) &
              (len == 4 ? 0xffffffffULL : ((1ULL << (8 * len)) - 1));

  c = ngtcp2_pkt_adjust_pkt_num((int64_t)expected - 1, (int64_t)truncated, len);
  model = quic_model_decode_pn(expected, truncated, (uint8_t)len);
  if ((uint64_t)c != model) {
    fprintf(stderr,
            "MISMATCH (pktnum) expected=%" PRIu64 " truncated=%" PRIu64
            " len=%zu: ngtcp2=%" PRId64 " model=%" PRIu64 "\n",
            expected, truncated, len, c, model);
    save_input("mismatch", data, size);
    abort();
  }
}

/* --- roundtrip ---------------------------------------------------------- */

static uint8_t g_plain[2048];
static size_t g_plainlen;

static int stub_encrypt(uint8_t *dest, const ngtcp2_crypto_aead *aead,
                        const ngtcp2_crypto_aead_ctx *aead_ctx,
                        const uint8_t *plaintext, size_t plaintextlen,
                        const uint8_t *nonce, size_t noncelen,
                        const uint8_t *aad, size_t aadlen) {
  (void)aead_ctx;
  (void)nonce;
  (void)noncelen;
  (void)aad;
  (void)aadlen;
  if (plaintextlen > sizeof(g_plain)) abort();
  memcpy(g_plain, plaintext, plaintextlen);
  g_plainlen = plaintextlen;
  if (plaintextlen && dest != plaintext) memmove(dest, plaintext, plaintextlen);
  memset(dest + plaintextlen, 0xa5, aead->max_overhead);
  return 0;
}

static int stub_hp_mask(uint8_t *dest, const ngtcp2_crypto_cipher *hp,
                        const ngtcp2_crypto_cipher_ctx *hp_ctx,
                        const uint8_t *sample) {
  (void)hp;
  (void)hp_ctx;
  memcpy(dest, sample, NGTCP2_HP_MASKLEN);
  return 0;
}

static void mode_roundtrip(const uint8_t *data, size_t size) {
  static const uint8_t iv[12] = {0};
  static const uint8_t types[] = {NGTCP2_PKT_INITIAL, NGTCP2_PKT_0RTT,
                                  NGTCP2_PKT_HANDSHAKE, NGTCP2_PKT_1RTT};
  ngtcp2_crypto_cc cc;
  ngtcp2_crypto_km *ckm = NULL;
  ngtcp2_crypto_aead_ctx aead_ctx = {0};
  ngtcp2_ppe ppe;
  ngtcp2_pkt_hd hd;
  ngtcp2_cid dcid, scid;
  ngtcp2_frame_decoder frd;
  uint8_t out[1500];
  uint8_t ctl, type, flags = 0;
  size_t pnlen, dcidlen, scidlen, tokenlen, need, nframes = 0;
  uint64_t pn, expected, back;
  uint32_t version;
  const uint8_t *p, *token;
  uint8_t *payload;
  size_t payloadlen;
  ngtcp2_ssize pktlen;
  sbuf sb = {0};
  int rv;

  if (size < 12) return;
  ctl = data[0];
  type = types[ctl & 3];
  version = (ctl & 4) ? NGTCP2_PROTO_VER_V2 : NGTCP2_PROTO_VER_V1;
  pnlen = (size_t)((ctl >> 3) & 3) + 1;
  if (type == NGTCP2_PKT_1RTT) {
    if (ctl & 0x20) flags |= NGTCP2_PKT_FLAG_KEY_PHASE;
  } else {
    flags |= NGTCP2_PKT_FLAG_LONG_FORM;
  }
  if (ctl & 0x40) flags |= NGTCP2_PKT_FLAG_FIXED_BIT_CLEAR;
  dcidlen = data[1] % (NGTCP2_MAX_CIDLEN + 1);
  scidlen = type == NGTCP2_PKT_1RTT ? 0 : data[2] % (NGTCP2_MAX_CIDLEN + 1);
  tokenlen = type == NGTCP2_PKT_INITIAL ? data[3] : 0;
  pn = get_u64(data + 4) % ((1ULL << 62) - (1ULL << 33));
  /* The receiver has seen up to `back` packets fewer than the sender assumes;
     stay inside the half-window so the truncation is decodable. */
  back = data[0] ^ data[11];
  back %= (1ULL << (8 * pnlen - 1)) > 120 ? 120 : (1ULL << (8 * pnlen - 1));
  expected = pn >= back ? pn - back : 0;

  need = 12 + dcidlen + scidlen + tokenlen;
  if (size < need) return;
  p = data + 12;
  ngtcp2_cid_init(&dcid, p, dcidlen);
  p += dcidlen;
  ngtcp2_cid_init(&scid, p, scidlen);
  p += scidlen;
  token = p;
  p += tokenlen;

  payloadlen = size - need;
  payload = malloc(payloadlen ? payloadlen : 1);
  if (payloadlen) memcpy(payload, p, payloadlen);

  memset(&cc, 0, sizeof(cc));
  cc.encrypt = stub_encrypt;
  cc.hp_mask = stub_hp_mask;
  cc.aead.max_overhead = TAGLEN;
  rv = ngtcp2_crypto_km_new(&ckm, NULL, 0, &aead_ctx, iv, sizeof(iv),
                            ngtcp2_mem_default());
  if (rv != 0) abort();
  cc.ckm = ckm;

  ngtcp2_pkt_hd_init(&hd, flags, type, &dcid,
                     type == NGTCP2_PKT_1RTT ? NULL : &scid, (int64_t)pn, pnlen,
                     version);
  hd.token = tokenlen ? token : NULL;
  hd.tokenlen = tokenlen;

  ngtcp2_ppe_init(&ppe, out, sizeof(out), 0, &cc);
  rv = ngtcp2_ppe_encode_hd(&ppe, &hd);
  if (rv != 0) goto done;

  /* Frames: whatever the C decoder makes of the fuzz bytes, re-encoded by the
     C encoder. */
  {
    const uint8_t *q = payload;
    size_t left = payloadlen;
    while (left) {
      ngtcp2_frame fr;
      ngtcp2_ssize n;
      memset(&fr, 0, sizeof(fr));
      n = ngtcp2_frame_decoder_decode(&frd, &fr, q, left);
      if (n <= 0) break;
      q += n;
      left -= (size_t)n;
      /* The encoder asserts a non-empty token. */
      if (fr.hd.type == NGTCP2_FRAME_NEW_TOKEN && fr.new_token.tokenlen == 0)
        continue;
      if (ngtcp2_ppe_encode_frame(&ppe, &fr) != 0) break;
      ++nframes;
    }
  }
  if (nframes == 0) {
    ngtcp2_frame fr;
    memset(&fr, 0, sizeof(fr));
    fr.hd.type = NGTCP2_FRAME_PING;
    if (ngtcp2_ppe_encode_frame(&ppe, &fr) != 0) goto done;
  }
  ngtcp2_ppe_padding_size(&ppe, 0);
  pktlen = ngtcp2_ppe_final(&ppe, NULL);
  if (pktlen < 0) abort();

  /* What ngtcp2 itself says about the packet it just wrote. */
  sb_reserve(&sb, 16);
  sb.p[0] = 0;
  if (c_dump_hd(&sb, out, (size_t)pktlen, dcidlen) < 0) abort();
  sb_printf(&sb, "PN pn=%" PRId64 " pnlen=%zu keyphase=%d\n",
            ngtcp2_pkt_adjust_pkt_num(
              (int64_t)expected - 1,
              (int64_t)(pn & (pnlen == 4 ? 0xffffffffULL
                                         : ((1ULL << (8 * pnlen)) - 1))),
              pnlen),
            pnlen, (flags & NGTCP2_PKT_FLAG_KEY_PHASE) ? 1 : 0);
  if (c_dump_frames(&sb, g_plain, g_plainlen) < 0) {
    fprintf(stderr, "ngtcp2 cannot decode the payload it encoded\n");
    save_input("selfdecode", data, size);
    abort();
  }
  sb_printf(&sb, "NEXT %td\n", (ptrdiff_t)pktlen);

  expect_same("roundtrip", &sb,
              quic_model_dump_packet(model_bytes(out, (size_t)pktlen),
                                     (uint32_t)dcidlen, TAGLEN, expected,
                                     /* grease_quic_bit negotiated iff the
                                        writer was told to clear the bit */
                                     (flags & NGTCP2_PKT_FLAG_FIXED_BIT_CLEAR)
                                       ? 1 : 0),
              data, size);

done:
  ngtcp2_crypto_km_del(ckm, ngtcp2_mem_default());
  free(payload);
  free(sb.p);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size < 1) return 0;
  switch (data[0] % 3) {
  case 0:
    mode_headers(data + 1, size - 1);
    break;
  case 1:
    mode_pktnum(data + 1, size - 1);
    break;
  case 2:
    mode_roundtrip(data + 1, size - 1);
    break;
  }
  return 0;
}
