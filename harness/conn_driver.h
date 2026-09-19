/*
 * conn_driver.h -- the ngtcp2 driver of WP8's conn_trace, factored out so that
 * WP13's harness/endpoint_diff.c drives *the same* connection, the same way,
 * and produces the same trace text.
 *
 * The full documentation of the setup, the script grammar and the trace
 * grammar is the block comment at the top of harness/conn_trace.c.
 *
 * The only thing added here is a set of no-op hook macros.  conn_trace.c leaves
 * them empty and its output is byte-for-byte what it always was; endpoint_diff.c
 * defines MODEL_HOOKS and fills them in, which is how the Lean endpoint is
 * driven in lockstep with ngtcp2.  Nothing in the driver looks at the model.
 */
#ifndef CONN_DRIVER_H
#define CONN_DRIVER_H


/* ------------------------------------------------------------------ hooks */

#ifndef MODEL_HOOKS
/* WP8's conn_trace: no model, every hook vanishes. */
#define MH_START(h, server)               ((void)0)
#define MH_MARK(h)                        ((void)0)
#define MH_RECV(h, pkt, len, rv)          ((void)0)
#define MH_TIME(h, rv)                    ((void)0)
#define MH_OPEN(h, uni, rv, sid)          ((void)0)
#define MH_WRITE(h, sid, n, fin)          ((void)0)
#define MH_SHUTDOWN(h, which, sid, err, rv) ((void)0)
#define MH_OUT(h, buf, len)               ((void)0)
#define MH_TICK(h)                        ((void)0)
#define MH_FINISH(h)                      ((void)0)
#endif
#ifndef MH_SYNTH_RECV
/* A datagram the model must process without the outcome being compared:
   quiche_driver.h's replay of the handshake's 1-RTT packets. */
#define MH_SYNTH_RECV(h, pkt, len)        ((void)0)
#endif

#include <sys/socket.h>
#include <netinet/in.h>

#include "diff_common.h"

#include "ngtcp2_ppe.h"
#include "ngtcp2_conv.h"
#include "ngtcp2_cid.h"
#include "ngtcp2_ksl.h"
#include "ngtcp2_pq.h"

#ifdef DRIVER_QUICHE
static size_t g_q_dcidlen; /* quiche_driver.h: the endpoint's current DCID length */
#endif

#define TAGLEN 16
#define MAX_STEPS 64
#define PKTBUF 1500
#define CIDLEN 8

/* ------------------------------------------------------------------ state */

typedef struct harness_s {
  sbuf tr;
  ngtcp2_conn *conn;
  ngtcp2_tstamp ts;
  ngtcp2_path_storage path;
  int server;
  int fatal;      /* a fatal library error was seen; stop stepping */
  int64_t last_stream;
  int64_t out_max_pn[3]; /* largest pn seen per space, for OUT pn recovery */
  size_t cb_mark; /* h->tr.len when the current step began (WP13) */
  void *model;    /* the Lean endpoint running beside it (WP13), or NULL */
#ifdef DRIVER_QUICHE
  struct quiche_conn *q;    /* the endpoint under test (quiche_driver.h) */
  int64_t q_peer_pn_base;   /* first 1-RTT packet number the forged peer may use */
  int64_t q_next_bidi, q_next_uni;
  uint64_t q_sid[64], q_off[64]; /* read offset per stream, for the trace */
  size_t q_nstreams;
#endif
} harness;

static const uint8_t g_cid_local[CIDLEN] = {0xa0, 0xa1, 0xa2, 0xa3,
                                            0xa4, 0xa5, 0xa6, 0xa7};
static const uint8_t g_cid_remote[CIDLEN] = {0xb0, 0xb1, 0xb2, 0xb3,
                                             0xb4, 0xb5, 0xb6, 0xb7};
static const uint8_t g_null_secret[32] = {0};
static const uint8_t g_null_iv[16] = {0};

static uint32_t g_rand_state;

static uint8_t next_rand(void) {
  g_rand_state = g_rand_state * 1103515245u + 12345u;
  return (uint8_t)(g_rand_state >> 16);
}

#define TR(h, ...) sb_printf(&(h)->tr, __VA_ARGS__)

static void tr_hex(harness *h, const uint8_t *p, size_t n) {
  sb_hex(&h->tr, p, n);
}

/* ------------------------------------------------------------- rc names */

static const char *rc_name(int rv) {
  switch (rv) {
  case 0:                                     return "OK";
  case NGTCP2_ERR_INVALID_ARGUMENT:           return "INVALID_ARGUMENT";
  case NGTCP2_ERR_NOBUF:                      return "NOBUF";
  case NGTCP2_ERR_PROTO:                      return "PROTO";
  case NGTCP2_ERR_INVALID_STATE:              return "INVALID_STATE";
  case NGTCP2_ERR_ACK_FRAME:                  return "ACK_FRAME";
  case NGTCP2_ERR_STREAM_ID_BLOCKED:          return "STREAM_ID_BLOCKED";
  case NGTCP2_ERR_STREAM_IN_USE:              return "STREAM_IN_USE";
  case NGTCP2_ERR_STREAM_DATA_BLOCKED:        return "STREAM_DATA_BLOCKED";
  case NGTCP2_ERR_FLOW_CONTROL:               return "FLOW_CONTROL";
  case NGTCP2_ERR_CONNECTION_ID_LIMIT:        return "CONNECTION_ID_LIMIT";
  case NGTCP2_ERR_STREAM_LIMIT:               return "STREAM_LIMIT";
  case NGTCP2_ERR_FINAL_SIZE:                 return "FINAL_SIZE";
  case NGTCP2_ERR_CRYPTO:                     return "CRYPTO";
  case NGTCP2_ERR_PKT_NUM_EXHAUSTED:          return "PKT_NUM_EXHAUSTED";
  case NGTCP2_ERR_REQUIRED_TRANSPORT_PARAM:   return "REQUIRED_TRANSPORT_PARAM";
  case NGTCP2_ERR_MALFORMED_TRANSPORT_PARAM:  return "MALFORMED_TRANSPORT_PARAM";
  case NGTCP2_ERR_FRAME_ENCODING:             return "FRAME_ENCODING";
  case NGTCP2_ERR_DECRYPT:                    return "DECRYPT";
  case NGTCP2_ERR_STREAM_SHUT_WR:             return "STREAM_SHUT_WR";
  case NGTCP2_ERR_STREAM_NOT_FOUND:           return "STREAM_NOT_FOUND";
  case NGTCP2_ERR_STREAM_STATE:               return "STREAM_STATE";
  case NGTCP2_ERR_RECV_VERSION_NEGOTIATION:   return "RECV_VERSION_NEGOTIATION";
  case NGTCP2_ERR_CLOSING:                    return "CLOSING";
  case NGTCP2_ERR_DRAINING:                   return "DRAINING";
  case NGTCP2_ERR_TRANSPORT_PARAM:            return "TRANSPORT_PARAM";
  case NGTCP2_ERR_DISCARD_PKT:                return "DISCARD_PKT";
  case NGTCP2_ERR_CONN_ID_BLOCKED:            return "CONN_ID_BLOCKED";
  case NGTCP2_ERR_INTERNAL:                   return "INTERNAL";
  case NGTCP2_ERR_CRYPTO_BUFFER_EXCEEDED:     return "CRYPTO_BUFFER_EXCEEDED";
  case NGTCP2_ERR_WRITE_MORE:                 return "WRITE_MORE";
  case NGTCP2_ERR_RETRY:                      return "RETRY";
  case NGTCP2_ERR_DROP_CONN:                  return "DROP_CONN";
  case NGTCP2_ERR_AEAD_LIMIT_REACHED:         return "AEAD_LIMIT_REACHED";
  case NGTCP2_ERR_NO_VIABLE_PATH:             return "NO_VIABLE_PATH";
  case NGTCP2_ERR_VERSION_NEGOTIATION:        return "VERSION_NEGOTIATION";
  case NGTCP2_ERR_HANDSHAKE_TIMEOUT:          return "HANDSHAKE_TIMEOUT";
  case NGTCP2_ERR_VERSION_NEGOTIATION_FAILURE: return "VERSION_NEGOTIATION_FAILURE";
  case NGTCP2_ERR_IDLE_CLOSE:                 return "IDLE_CLOSE";
  case NGTCP2_ERR_FATAL:                      return "FATAL";
  case NGTCP2_ERR_NOMEM:                      return "NOMEM";
  case NGTCP2_ERR_CALLBACK_FAILURE:           return "CALLBACK_FAILURE";
  default:                                    return "UNKNOWN";
  }
}

static const char *space_name(int s) {
  return s == 0 ? "initial" : s == 1 ? "handshake" : "app";
}

static const char *level_name(ngtcp2_encryption_level l) {
  switch (l) {
  case NGTCP2_ENCRYPTION_LEVEL_INITIAL:   return "initial";
  case NGTCP2_ENCRYPTION_LEVEL_HANDSHAKE: return "handshake";
  case NGTCP2_ENCRYPTION_LEVEL_1RTT:      return "1rtt";
  case NGTCP2_ENCRYPTION_LEVEL_0RTT:      return "0rtt";
  default:                                return "?";
  }
}

static const char *ccerr_type_name(ngtcp2_ccerr_type t) {
  switch (t) {
  case NGTCP2_CCERR_TYPE_TRANSPORT:            return "transport";
  case NGTCP2_CCERR_TYPE_APPLICATION:          return "application";
  case NGTCP2_CCERR_TYPE_VERSION_NEGOTIATION:  return "version_negotiation";
  case NGTCP2_CCERR_TYPE_IDLE_CLOSE:           return "idle_close";
  case NGTCP2_CCERR_TYPE_DROP_CONN:            return "drop_conn";
  case NGTCP2_CCERR_TYPE_RETRY:                return "retry";
  default:                                     return "?";
  }
}

/* ------------------------------------------------------------ stub crypto */

/* Plaintext of the last packet the *peer-side builder* encrypted, so that the
   IN record shows exactly what went on the wire (padding included). */
static uint8_t g_build_plain[2048];
static size_t g_build_plainlen;

static int build_encrypt(uint8_t *dest, const ngtcp2_crypto_aead *aead,
                         const ngtcp2_crypto_aead_ctx *aead_ctx,
                         const uint8_t *plaintext, size_t plaintextlen,
                         const uint8_t *nonce, size_t noncelen,
                         const uint8_t *aad, size_t aadlen) {
  (void)aead_ctx; (void)nonce; (void)noncelen; (void)aad; (void)aadlen;
  if (plaintextlen > sizeof(g_build_plain)) abort();
  memcpy(g_build_plain, plaintext, plaintextlen);
  g_build_plainlen = plaintextlen;
  if (plaintextlen && dest != plaintext) memmove(dest, plaintext, plaintextlen);
  memset(dest + plaintextlen, 0xa5, aead->max_overhead);
  return 0;
}

static int stub_encrypt(uint8_t *dest, const ngtcp2_crypto_aead *aead,
                        const ngtcp2_crypto_aead_ctx *aead_ctx,
                        const uint8_t *plaintext, size_t plaintextlen,
                        const uint8_t *nonce, size_t noncelen,
                        const uint8_t *aad, size_t aadlen) {
  (void)aead_ctx; (void)nonce; (void)noncelen; (void)aad; (void)aadlen;
  if (plaintextlen && dest != plaintext) memmove(dest, plaintext, plaintextlen);
  memset(dest + plaintextlen, 0xa5, aead->max_overhead);
  return 0;
}

static int stub_decrypt(uint8_t *dest, const ngtcp2_crypto_aead *aead,
                        const ngtcp2_crypto_aead_ctx *aead_ctx,
                        const uint8_t *ciphertext, size_t ciphertextlen,
                        const uint8_t *nonce, size_t noncelen,
                        const uint8_t *aad, size_t aadlen) {
  (void)aead_ctx; (void)nonce; (void)noncelen; (void)aad; (void)aadlen;
  if (ciphertextlen < aead->max_overhead) return NGTCP2_ERR_DECRYPT;
  if (ciphertextlen > aead->max_overhead)
    memmove(dest, ciphertext, ciphertextlen - aead->max_overhead);
  return 0;
}

static int stub_hp_mask(uint8_t *dest, const ngtcp2_crypto_cipher *hp,
                        const ngtcp2_crypto_cipher_ctx *hp_ctx,
                        const uint8_t *sample) {
  (void)hp; (void)hp_ctx;
  memcpy(dest, sample, NGTCP2_HP_MASKLEN);
  return 0;
}

/* --------------------------------------------------------- frame dumping */

/* Canonical dump of a frame payload, joined with ';'. */
static void dump_frames_joined(sbuf *sb, const uint8_t *p, size_t size) {
  ngtcp2_frame_decoder frd;
  int first = 1;
  memset(&frd, 0, sizeof(frd));
  while (size) {
    ngtcp2_frame fr;
    ngtcp2_ssize n;
    memset(&fr, 0, sizeof(fr));
    n = ngtcp2_frame_decoder_decode(&frd, &fr, p, size);
    if (n <= 0 || (size_t)n > size) {
      sb_printf(sb, "%sBADFRAME", first ? "" : ";");
      return;
    }
    if (!first) sb_printf(sb, ";");
    first = 0;
    dump_frame(sb, &fr);
    p += n;
    size -= (size_t)n;
  }
}

/* --------------------------------------------------------------- callbacks */

#define H(user_data) ((harness *)(user_data))

static int cb_client_initial(ngtcp2_conn *conn, void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  client_initial\n");
  return 0;
}

static int cb_recv_client_initial(ngtcp2_conn *conn, const ngtcp2_cid *dcid,
                                  void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  recv_client_initial dcid=");
  tr_hex(H(user_data), dcid->data, dcid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_recv_crypto_data(ngtcp2_conn *conn,
                               ngtcp2_encryption_level level, uint64_t offset,
                               const uint8_t *data, size_t datalen,
                               void *user_data) {
  (void)conn; (void)data;
  TR(H(user_data), "CB  recv_crypto_data level=%s off=%" PRIu64 " len=%zu\n",
     level_name(level), offset, datalen);
  return 0;
}

static int cb_handshake_completed(ngtcp2_conn *conn, void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  handshake_completed\n");
  return 0;
}

static int cb_handshake_confirmed(ngtcp2_conn *conn, void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  handshake_confirmed\n");
  return 0;
}

static int cb_recv_version_negotiation(ngtcp2_conn *conn,
                                       const ngtcp2_pkt_hd *hd,
                                       const uint32_t *sv, size_t nsv,
                                       void *user_data) {
  size_t i;
  (void)conn; (void)hd;
  TR(H(user_data), "CB  recv_version_negotiation versions=[");
  for (i = 0; i < nsv; ++i)
    TR(H(user_data), "%s%u", i ? "," : "", sv[i]);
  TR(H(user_data), "]\n");
  return 0;
}

static int cb_recv_stream_data(ngtcp2_conn *conn, uint32_t flags,
                               int64_t stream_id, uint64_t offset,
                               const uint8_t *data, size_t datalen,
                               void *user_data, void *stream_user_data) {
  (void)conn; (void)data; (void)stream_user_data;
  TR(H(user_data),
     "CB  recv_stream_data id=%" PRId64 " off=%" PRIu64
     " len=%zu fin=%d early=%d\n",
     stream_id, offset, datalen, (flags & NGTCP2_STREAM_DATA_FLAG_FIN) ? 1 : 0,
     (flags & NGTCP2_STREAM_DATA_FLAG_0RTT) ? 1 : 0);
  return 0;
}

static int cb_acked_stream_data_offset(ngtcp2_conn *conn, int64_t stream_id,
                                       uint64_t offset, uint64_t datalen,
                                       void *user_data,
                                       void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  acked_stream_data_offset id=%" PRId64 " off=%" PRIu64
     " len=%" PRIu64 "\n",
     stream_id, offset, datalen);
  return 0;
}

static int cb_stream_open(ngtcp2_conn *conn, int64_t stream_id,
                          void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  stream_open id=%" PRId64 "\n", stream_id);
  return 0;
}

static int cb_stream_close(ngtcp2_conn *conn, uint32_t flags,
                           int64_t stream_id, uint64_t app_error_code,
                           void *user_data, void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  stream_close id=%" PRId64 " app_error_code=%" PRIu64 " set=%d\n",
     stream_id, app_error_code,
     (flags & NGTCP2_STREAM_CLOSE_FLAG_APP_ERROR_CODE_SET) ? 1 : 0);
  return 0;
}

static int cb_stream_close2(ngtcp2_conn *conn, uint32_t flags,
                            int64_t stream_id, uint64_t rx_app_error_code,
                            uint64_t tx_app_error_code, void *user_data,
                            void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  stream_close2 id=%" PRId64 " rx_app_error_code=%" PRIu64
     " tx_app_error_code=%" PRIu64 " set=%d\n",
     stream_id, rx_app_error_code, tx_app_error_code,
     (flags & NGTCP2_STREAM_CLOSE_FLAG_APP_ERROR_CODE_SET) ? 1 : 0);
  return 0;
}

static int cb_stream_reset(ngtcp2_conn *conn, int64_t stream_id,
                           uint64_t final_size, uint64_t app_error_code,
                           void *user_data, void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  stream_reset id=%" PRId64 " final_size=%" PRIu64
     " app_error_code=%" PRIu64 "\n",
     stream_id, final_size, app_error_code);
  return 0;
}

static int cb_stream_stop_sending(ngtcp2_conn *conn, int64_t stream_id,
                                  uint64_t app_error_code, void *user_data,
                                  void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  stream_stop_sending id=%" PRId64 " app_error_code=%" PRIu64 "\n",
     stream_id, app_error_code);
  return 0;
}

static int cb_recv_stop_sending(ngtcp2_conn *conn, int64_t stream_id,
                                uint64_t app_error_code, void *user_data,
                                void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data),
     "CB  recv_stop_sending id=%" PRId64 " app_error_code=%" PRIu64 "\n",
     stream_id, app_error_code);
  return 0;
}

static int cb_extend_max_local_streams_bidi(ngtcp2_conn *conn,
                                            uint64_t max_streams,
                                            void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  extend_max_local_streams_bidi max_streams=%" PRIu64 "\n",
     max_streams);
  return 0;
}

static int cb_extend_max_local_streams_uni(ngtcp2_conn *conn,
                                           uint64_t max_streams,
                                           void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  extend_max_local_streams_uni max_streams=%" PRIu64 "\n",
     max_streams);
  return 0;
}

static int cb_extend_max_remote_streams_bidi(ngtcp2_conn *conn,
                                             uint64_t max_streams,
                                             void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  extend_max_remote_streams_bidi max_streams=%" PRIu64 "\n",
     max_streams);
  return 0;
}

static int cb_extend_max_remote_streams_uni(ngtcp2_conn *conn,
                                            uint64_t max_streams,
                                            void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  extend_max_remote_streams_uni max_streams=%" PRIu64 "\n",
     max_streams);
  return 0;
}

static int cb_extend_max_stream_data(ngtcp2_conn *conn, int64_t stream_id,
                                     uint64_t max_data, void *user_data,
                                     void *stream_user_data) {
  (void)conn; (void)stream_user_data;
  TR(H(user_data), "CB  extend_max_stream_data id=%" PRId64
     " max_data=%" PRIu64 "\n", stream_id, max_data);
  return 0;
}

static int cb_extend_max_data(ngtcp2_conn *conn, uint64_t max_data,
                              void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  extend_max_data max_data=%" PRIu64 "\n", max_data);
  return 0;
}

static int cb_recv_stateless_reset(ngtcp2_conn *conn,
                                   const ngtcp2_pkt_stateless_reset *sr,
                                   void *user_data) {
  (void)conn; (void)sr;
  TR(H(user_data), "CB  recv_stateless_reset\n");
  return 0;
}

static int cb_recv_stateless_reset2(ngtcp2_conn *conn,
                                    const ngtcp2_pkt_stateless_reset2 *sr,
                                    void *user_data) {
  (void)conn; (void)sr;
  TR(H(user_data), "CB  recv_stateless_reset2\n");
  return 0;
}

static int cb_recv_retry(ngtcp2_conn *conn, const ngtcp2_pkt_hd *hd,
                         void *user_data) {
  (void)conn; (void)hd;
  TR(H(user_data), "CB  recv_retry\n");
  return 0;
}

static int cb_recv_new_token(ngtcp2_conn *conn, const uint8_t *token,
                             size_t tokenlen, void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  recv_new_token token=");
  tr_hex(H(user_data), token, tokenlen);
  TR(H(user_data), "\n");
  return 0;
}

static void cb_rand(uint8_t *dest, size_t destlen,
                    const ngtcp2_rand_ctx *rand_ctx) {
  size_t i;
  (void)rand_ctx;
  for (i = 0; i < destlen; ++i) dest[i] = next_rand();
}

static int cb_get_new_connection_id(ngtcp2_conn *conn, ngtcp2_cid *cid,
                                    uint8_t *token, size_t cidlen,
                                    void *user_data) {
  memset(cid, 0, sizeof(*cid));
  cid->datalen = cidlen;
  if (cidlen) cid->data[0] = (uint8_t)(conn->scid.last_seq + 1);
  memset(token, 0, NGTCP2_STATELESS_RESET_TOKENLEN);
  TR(H(user_data), "CB  get_new_connection_id cidlen=%zu -> cid=", cidlen);
  tr_hex(H(user_data), cid->data, cid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_get_new_connection_id2(ngtcp2_conn *conn, ngtcp2_cid *cid,
                                     ngtcp2_stateless_reset_token *token,
                                     size_t cidlen, void *user_data) {
  memset(cid, 0, sizeof(*cid));
  cid->datalen = cidlen;
  if (cidlen) cid->data[0] = (uint8_t)(conn->scid.last_seq + 1);
  memset(token, 0, sizeof(*token));
  TR(H(user_data), "CB  get_new_connection_id2 cidlen=%zu -> cid=", cidlen);
  tr_hex(H(user_data), cid->data, cid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_remove_connection_id(ngtcp2_conn *conn, const ngtcp2_cid *cid,
                                   void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  remove_connection_id cid=");
  tr_hex(H(user_data), cid->data, cid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static const char *cid_status_name(ngtcp2_connection_id_status_type t) {
  return t == NGTCP2_CONNECTION_ID_STATUS_TYPE_ACTIVATE ? "activate"
                                                        : "deactivate";
}

static int cb_dcid_status(ngtcp2_conn *conn,
                          ngtcp2_connection_id_status_type type, uint64_t seq,
                          const ngtcp2_cid *cid, const uint8_t *token,
                          void *user_data) {
  (void)conn; (void)token;
  TR(H(user_data), "CB  dcid_status type=%s seq=%" PRIu64 " cid=",
     cid_status_name(type), seq);
  tr_hex(H(user_data), cid->data, cid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_dcid_status2(ngtcp2_conn *conn,
                           ngtcp2_connection_id_status_type type, uint64_t seq,
                           const ngtcp2_cid *cid,
                           const ngtcp2_stateless_reset_token *token,
                           void *user_data) {
  (void)conn; (void)token;
  TR(H(user_data), "CB  dcid_status2 type=%s seq=%" PRIu64 " cid=",
     cid_status_name(type), seq);
  tr_hex(H(user_data), cid->data, cid->datalen);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_update_key(ngtcp2_conn *conn, uint8_t *rx_secret,
                         uint8_t *tx_secret, ngtcp2_crypto_aead_ctx *rx_aead_ctx,
                         uint8_t *rx_iv, ngtcp2_crypto_aead_ctx *tx_aead_ctx,
                         uint8_t *tx_iv, const uint8_t *current_rx_secret,
                         const uint8_t *current_tx_secret, size_t secretlen,
                         void *user_data) {
  (void)conn; (void)current_rx_secret; (void)current_tx_secret;
  memset(rx_secret, 0xff, secretlen);
  memset(tx_secret, 0xff, secretlen);
  rx_aead_ctx->native_handle = NULL;
  tx_aead_ctx->native_handle = NULL;
  memset(rx_iv, 0xff, sizeof(g_null_iv));
  memset(tx_iv, 0xff, sizeof(g_null_iv));
  TR(H(user_data), "CB  update_key\n");
  return 0;
}

static const char *pv_result_name(ngtcp2_path_validation_result r) {
  switch (r) {
  case NGTCP2_PATH_VALIDATION_RESULT_SUCCESS: return "success";
  case NGTCP2_PATH_VALIDATION_RESULT_FAILURE: return "failure";
  default:                                    return "aborted";
  }
}

static int cb_path_validation(ngtcp2_conn *conn, uint32_t flags,
                              const ngtcp2_path *path,
                              const ngtcp2_path *old_path,
                              ngtcp2_path_validation_result res,
                              void *user_data) {
  (void)conn; (void)path; (void)old_path;
  TR(H(user_data), "CB  path_validation flags=%u res=%s\n", flags,
     pv_result_name(res));
  return 0;
}

static int cb_begin_path_validation(ngtcp2_conn *conn, uint32_t flags,
                                    const ngtcp2_path *path,
                                    const ngtcp2_path *fallback_path,
                                    void *user_data) {
  (void)conn; (void)path; (void)fallback_path;
  TR(H(user_data), "CB  begin_path_validation flags=%u\n", flags);
  return 0;
}

static int cb_select_preferred_addr(ngtcp2_conn *conn, ngtcp2_path *dest,
                                    const ngtcp2_preferred_addr *paddr,
                                    void *user_data) {
  (void)conn; (void)dest; (void)paddr;
  TR(H(user_data), "CB  select_preferred_addr\n");
  return 0;
}

static void cb_delete_crypto_aead_ctx(ngtcp2_conn *conn,
                                      ngtcp2_crypto_aead_ctx *aead_ctx,
                                      void *user_data) {
  (void)conn; (void)aead_ctx; (void)user_data;
}

static void cb_delete_crypto_cipher_ctx(ngtcp2_conn *conn,
                                        ngtcp2_crypto_cipher_ctx *cipher_ctx,
                                        void *user_data) {
  (void)conn; (void)cipher_ctx; (void)user_data;
}

static int cb_recv_datagram(ngtcp2_conn *conn, uint32_t flags,
                            const uint8_t *data, size_t datalen,
                            void *user_data) {
  (void)conn; (void)data;
  TR(H(user_data), "CB  recv_datagram len=%zu early=%d\n", datalen,
     (flags & NGTCP2_DATAGRAM_FLAG_0RTT) ? 1 : 0);
  return 0;
}

static int cb_ack_datagram(ngtcp2_conn *conn, uint64_t dgram_id,
                           void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  ack_datagram dgram_id=%" PRIu64 "\n", dgram_id);
  return 0;
}

static int cb_lost_datagram(ngtcp2_conn *conn, uint64_t dgram_id,
                            void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  lost_datagram dgram_id=%" PRIu64 "\n", dgram_id);
  return 0;
}

static int cb_get_path_challenge_data(ngtcp2_conn *conn, uint8_t *data,
                                      void *user_data) {
  size_t i;
  (void)conn;
  for (i = 0; i < NGTCP2_PATH_CHALLENGE_DATALEN; ++i) data[i] = next_rand();
  TR(H(user_data), "CB  get_path_challenge_data -> data=");
  tr_hex(H(user_data), data, NGTCP2_PATH_CHALLENGE_DATALEN);
  TR(H(user_data), "\n");
  return 0;
}

static int cb_get_path_challenge_data2(ngtcp2_conn *conn,
                                       ngtcp2_path_challenge_data *data,
                                       void *user_data) {
  size_t i;
  (void)conn;
  for (i = 0; i < sizeof(data->data); ++i) data->data[i] = next_rand();
  TR(H(user_data), "CB  get_path_challenge_data2 -> data=");
  tr_hex(H(user_data), data->data, sizeof(data->data));
  TR(H(user_data), "\n");
  return 0;
}

static int cb_version_negotiation(ngtcp2_conn *conn, uint32_t version,
                                  const ngtcp2_cid *client_dcid,
                                  void *user_data) {
  ngtcp2_crypto_aead_ctx aead_ctx;
  ngtcp2_crypto_cipher_ctx hp_ctx;
  (void)client_dcid;
  memset(&aead_ctx, 0, sizeof(aead_ctx));
  memset(&hp_ctx, 0, sizeof(hp_ctx));
  TR(H(user_data), "CB  version_negotiation version=%u\n", version);
  ngtcp2_conn_install_vneg_initial_key(conn, version, &aead_ctx, g_null_iv,
                                       &hp_ctx, &aead_ctx, g_null_iv, &hp_ctx,
                                       sizeof(g_null_iv));
  return 0;
}

static int cb_recv_rx_key(ngtcp2_conn *conn, ngtcp2_encryption_level level,
                          void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  recv_rx_key level=%s\n", level_name(level));
  return 0;
}

static int cb_recv_tx_key(ngtcp2_conn *conn, ngtcp2_encryption_level level,
                          void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  recv_tx_key level=%s\n", level_name(level));
  return 0;
}

static int cb_tls_early_data_rejected(ngtcp2_conn *conn, void *user_data) {
  (void)conn;
  TR(H(user_data), "CB  tls_early_data_rejected\n");
  return 0;
}

/* ---------------------------------------------------------------- setup */

static void init_path(ngtcp2_path_storage *ps) {
  struct sockaddr_in local, remote;
  memset(&local, 0, sizeof(local));
  memset(&remote, 0, sizeof(remote));
  local.sin_family = AF_INET;
  local.sin_port = htons(4433);
  local.sin_addr.s_addr = htonl(0x7f000001u);
  remote.sin_family = AF_INET;
  remote.sin_port = htons(12345);
  remote.sin_addr.s_addr = htonl(0x7f000001u);
  ngtcp2_path_storage_init(ps, (struct sockaddr *)&local, sizeof(local),
                           (struct sockaddr *)&remote, sizeof(remote), NULL);
}

static void fill_params(ngtcp2_transport_params *params) {
  ngtcp2_transport_params_default(params);
  params->initial_max_stream_data_bidi_local = 1024;
  params->initial_max_stream_data_bidi_remote = 1024;
  params->initial_max_stream_data_uni = 1024;
  params->initial_max_data = 4096;
  params->initial_max_streams_bidi = 4;
  params->initial_max_streams_uni = 2;
  params->max_idle_timeout = 30 * NGTCP2_SECONDS;
  params->max_udp_payload_size = NGTCP2_MAX_UDP_PAYLOAD_SIZE;
  params->active_connection_id_limit = 4;
  params->ack_delay_exponent = 3;
  params->max_ack_delay = 25 * NGTCP2_MILLISECONDS;
  params->max_datagram_frame_size = 1200;
  params->disable_active_migration = 0;
  params->grease_quic_bit = 0;
}

#ifndef DRIVER_QUICHE
/* Builds the connection exactly the way ngtcp2's own read_write_pkt fuzzer
   does: install all three key sets by hand, then force the post-handshake
   state.  Returns 0 on success. */
static int setup_conn(harness *h, int server) {
  ngtcp2_callbacks cb;
  ngtcp2_settings settings;
  ngtcp2_transport_params params, remote_params;
  ngtcp2_crypto_ctx crypto_ctx;
  ngtcp2_crypto_aead_ctx aead_ctx;
  ngtcp2_crypto_cipher_ctx hp_ctx;
  ngtcp2_cid dcid, scid;
  ngtcp2_ksl_it it;
  ngtcp2_scid *s;
  int rv;

  memset(&cb, 0, sizeof(cb));
  cb.client_initial = cb_client_initial;
  cb.recv_client_initial = cb_recv_client_initial;
  cb.recv_crypto_data = cb_recv_crypto_data;
  cb.handshake_completed = cb_handshake_completed;
  cb.recv_version_negotiation = cb_recv_version_negotiation;
  cb.encrypt = stub_encrypt;
  cb.decrypt = stub_decrypt;
  cb.hp_mask = stub_hp_mask;
  cb.recv_stream_data = cb_recv_stream_data;
  cb.acked_stream_data_offset = cb_acked_stream_data_offset;
  cb.stream_open = cb_stream_open;
  cb.stream_close = cb_stream_close;
  cb.recv_stateless_reset = cb_recv_stateless_reset;
  cb.recv_retry = cb_recv_retry;
  cb.extend_max_local_streams_bidi = cb_extend_max_local_streams_bidi;
  cb.extend_max_local_streams_uni = cb_extend_max_local_streams_uni;
  cb.rand = cb_rand;
  cb.get_new_connection_id = cb_get_new_connection_id;
  cb.remove_connection_id = cb_remove_connection_id;
  cb.update_key = cb_update_key;
  cb.path_validation = cb_path_validation;
  cb.select_preferred_addr = cb_select_preferred_addr;
  cb.stream_reset = cb_stream_reset;
  cb.extend_max_remote_streams_bidi = cb_extend_max_remote_streams_bidi;
  cb.extend_max_remote_streams_uni = cb_extend_max_remote_streams_uni;
  cb.extend_max_stream_data = cb_extend_max_stream_data;
  cb.dcid_status = cb_dcid_status;
  cb.handshake_confirmed = cb_handshake_confirmed;
  cb.recv_new_token = cb_recv_new_token;
  cb.delete_crypto_aead_ctx = cb_delete_crypto_aead_ctx;
  cb.delete_crypto_cipher_ctx = cb_delete_crypto_cipher_ctx;
  cb.recv_datagram = cb_recv_datagram;
  cb.ack_datagram = cb_ack_datagram;
  cb.lost_datagram = cb_lost_datagram;
  cb.get_path_challenge_data = cb_get_path_challenge_data;
  cb.stream_stop_sending = cb_stream_stop_sending;
  cb.version_negotiation = cb_version_negotiation;
  cb.recv_rx_key = cb_recv_rx_key;
  cb.recv_tx_key = cb_recv_tx_key;
  cb.tls_early_data_rejected = cb_tls_early_data_rejected;
  cb.begin_path_validation = cb_begin_path_validation;
  cb.recv_stateless_reset2 = cb_recv_stateless_reset2;
  cb.get_new_connection_id2 = cb_get_new_connection_id2;
  cb.dcid_status2 = cb_dcid_status2;
  cb.get_path_challenge_data2 = cb_get_path_challenge_data2;
  cb.recv_stop_sending = cb_recv_stop_sending;
  cb.stream_close2 = cb_stream_close2;
  cb.extend_max_data = cb_extend_max_data;

  ngtcp2_cid_init(&scid, g_cid_local, CIDLEN);
  ngtcp2_cid_init(&dcid, g_cid_remote, CIDLEN);

  init_path(&h->path);

  ngtcp2_settings_default(&settings);
  settings.initial_ts = 0;
  settings.initial_rtt = 100 * NGTCP2_MILLISECONDS;
  settings.cc_algo = NGTCP2_CC_ALGO_RENO;
  settings.no_pmtud = 1;
  settings.initial_pkt_num = 0;
  settings.handshake_timeout = UINT64_MAX;
  settings.log_write = NULL;
  settings.qlog_write = NULL;

  fill_params(&params);
  if (server) {
    params.original_dcid = dcid;
    params.original_dcid_present = 1;
  }

  if (server) {
    rv = ngtcp2_conn_server_new(&h->conn, &dcid, &scid, &h->path.path,
                                NGTCP2_PROTO_VER_V1, &cb, &settings, &params,
                                NULL, h);
  } else {
    rv = ngtcp2_conn_client_new(&h->conn, &dcid, &scid, &h->path.path,
                                NGTCP2_PROTO_VER_V1, &cb, &settings, &params,
                                NULL, h);
  }
  if (rv != 0) return -1;

  memset(&crypto_ctx, 0, sizeof(crypto_ctx));
  crypto_ctx.aead.max_overhead = TAGLEN;
  crypto_ctx.max_encryption = UINT64_MAX;
  crypto_ctx.max_decryption_failure = UINT64_MAX;

  memset(&aead_ctx, 0, sizeof(aead_ctx));
  memset(&hp_ctx, 0, sizeof(hp_ctx));

  ngtcp2_conn_set_initial_crypto_ctx(h->conn, &crypto_ctx);
  rv = ngtcp2_conn_install_initial_key(h->conn, &aead_ctx, g_null_iv, &hp_ctx,
                                       &aead_ctx, g_null_iv, &hp_ctx,
                                       sizeof(g_null_iv));
  if (rv != 0) goto fail;

  ngtcp2_conn_set_crypto_ctx(h->conn, &crypto_ctx);
  rv = ngtcp2_conn_install_rx_handshake_key(h->conn, &aead_ctx, g_null_iv,
                                            sizeof(g_null_iv), &hp_ctx);
  if (rv != 0) goto fail;
  rv = ngtcp2_conn_install_tx_handshake_key(h->conn, &aead_ctx, g_null_iv,
                                            sizeof(g_null_iv), &hp_ctx);
  if (rv != 0) goto fail;
  rv = ngtcp2_conn_install_rx_key(h->conn, g_null_secret, sizeof(g_null_secret),
                                  &aead_ctx, g_null_iv, sizeof(g_null_iv),
                                  &hp_ctx);
  if (rv != 0) goto fail;
  rv = ngtcp2_conn_install_tx_key(h->conn, g_null_secret, sizeof(g_null_secret),
                                  &aead_ctx, g_null_iv, sizeof(g_null_iv),
                                  &hp_ctx);
  if (rv != 0) goto fail;

  ngtcp2_conn_discard_initial_state(h->conn, 0);
  ngtcp2_conn_discard_handshake_state(h->conn, 0);

  h->conn->state = NGTCP2_CS_POST_HANDSHAKE;
  h->conn->flags |= NGTCP2_CONN_FLAG_INITIAL_PKT_PROCESSED |
                    NGTCP2_CONN_FLAG_TLS_HANDSHAKE_COMPLETED |
                    NGTCP2_CONN_FLAG_HANDSHAKE_COMPLETED |
                    NGTCP2_CONN_FLAG_HANDSHAKE_CONFIRMED;
  h->conn->dcid.current.flags |= NGTCP2_DCID_FLAG_PATH_VALIDATED;

  it = ngtcp2_ksl_begin(&h->conn->scid.set);
  s = ngtcp2_ksl_it_get(&it);
  s->flags |= NGTCP2_SCID_FLAG_USED;
  rv = ngtcp2_pq_push(&h->conn->scid.used, &s->pe);
  if (rv != 0) goto fail;

  h->conn->negotiated_version = h->conn->client_chosen_version;
  h->conn->handshake_confirmed_ts = 0;

  /* The peer's transport parameters.  initial_scid must be the CID we address
     the peer with; a client additionally checks original_dcid. */
  fill_params(&remote_params);
  remote_params.initial_scid = dcid;
  remote_params.initial_scid_present = 1;
  if (!server) {
    remote_params.original_dcid = dcid;
    remote_params.original_dcid_present = 1;
  }
  rv = ngtcp2_conn_set_remote_transport_params(h->conn, &remote_params);
  if (rv != 0) goto fail;

  return 0;

fail:
  ngtcp2_conn_del(h->conn);
  h->conn = NULL;
  return -1;
}

#endif /* !DRIVER_QUICHE */

/* ------------------------------------------------------- packet building */

/* Builds a protected packet in |space| with packet number |pn| carrying the
   frames ngtcp2's decoder makes of |fb|.  Returns the packet length or -1. */
static ngtcp2_ssize build_peer_pkt(int space, int64_t pn, const uint8_t *fb,
                                   size_t fblen, uint8_t *out, size_t outcap) {
  ngtcp2_crypto_cc cc;
  ngtcp2_crypto_km *ckm = NULL;
  ngtcp2_crypto_aead_ctx aead_ctx;
  ngtcp2_ppe ppe;
  ngtcp2_pkt_hd hd;
  ngtcp2_cid dcid, scid;
  ngtcp2_frame_decoder frd;
  static const uint8_t iv[12] = {0};
  size_t nframes = 0;
  uint8_t flags = 0;
  uint8_t type;
  ngtcp2_ssize pktlen;
  int rv;

  memset(&aead_ctx, 0, sizeof(aead_ctx));
  memset(&frd, 0, sizeof(frd));
  ngtcp2_cid_init(&dcid, g_cid_local, CIDLEN);
  ngtcp2_cid_init(&scid, g_cid_remote, CIDLEN);

  switch (space) {
  case 0: type = NGTCP2_PKT_INITIAL; flags = NGTCP2_PKT_FLAG_LONG_FORM; break;
  case 1: type = NGTCP2_PKT_HANDSHAKE; flags = NGTCP2_PKT_FLAG_LONG_FORM; break;
  default: type = NGTCP2_PKT_1RTT; flags = 0; break;
  }

  memset(&cc, 0, sizeof(cc));
  cc.encrypt = build_encrypt;
  cc.hp_mask = stub_hp_mask;
  cc.aead.max_overhead = TAGLEN;
  rv = ngtcp2_crypto_km_new(&ckm, NULL, 0, &aead_ctx, iv, sizeof(iv),
                            ngtcp2_mem_default());
  if (rv != 0) abort();
  cc.ckm = ckm;

  ngtcp2_pkt_hd_init(&hd, flags, type, &dcid,
                     type == NGTCP2_PKT_1RTT ? NULL : &scid, pn, 4,
                     NGTCP2_PROTO_VER_V1);
  hd.token = NULL;
  hd.tokenlen = 0;

  g_build_plainlen = 0;
  ngtcp2_ppe_init(&ppe, out, outcap, 0, &cc);
  if (ngtcp2_ppe_encode_hd(&ppe, &hd) != 0) {
    pktlen = -1;
    goto done;
  }

  while (fblen) {
    ngtcp2_frame fr;
    ngtcp2_ssize n;
    memset(&fr, 0, sizeof(fr));
    n = ngtcp2_frame_decoder_decode(&frd, &fr, fb, fblen);
    if (n <= 0 || (size_t)n > fblen) break;
    fb += n;
    fblen -= (size_t)n;
    /* The encoder asserts a non-empty token. */
    if (fr.hd.type == NGTCP2_FRAME_NEW_TOKEN && fr.new_token.tokenlen == 0)
      continue;
    if (ngtcp2_ppe_encode_frame(&ppe, &fr) != 0) break;
    ++nframes;
  }
  if (nframes == 0) {
    ngtcp2_frame fr;
    memset(&fr, 0, sizeof(fr));
    fr.hd.type = NGTCP2_FRAME_PING;
    if (ngtcp2_ppe_encode_frame(&ppe, &fr) != 0) {
      pktlen = -1;
      goto done;
    }
  }
  /* A client Initial datagram must be at least 1200 bytes or a server drops
     it; everything else is padded only as far as the HP sample needs. */
  ngtcp2_ppe_padding_size(&ppe, space == 0 ? 1200 : 0);
  pktlen = ngtcp2_ppe_final(&ppe, NULL);

done:
  ngtcp2_crypto_km_del(ckm, ngtcp2_mem_default());
  return pktlen;
}

/* ------------------------------------------------------- packet dumping */

static uint64_t get_be(const uint8_t *p, size_t n) {
  uint64_t v = 0;
  size_t i;
  for (i = 0; i < n; ++i) v = (v << 8) | p[i];
  return v;
}

/* Takes a datagram the connection wrote apart with the stub crypto and emits
   one OUT record per packet in it. */
static void dump_out_datagram(harness *h, const uint8_t *pkt, size_t pktlen) {
  const uint8_t *p = pkt;
  size_t left = pktlen;

  while (left > 0) {
    ngtcp2_pkt_hd hd;
    ngtcp2_ssize hdlen;
    size_t pktend, pnoff, pnlen, i;
    const uint8_t *sample;
    uint8_t mask[NGTCP2_HP_MASKLEN], b0, pnbuf[4];
    int space;
    int64_t pn;

    if (p[0] & NGTCP2_HEADER_FORM_BIT) {
      hdlen = ngtcp2_pkt_decode_hd_long(&hd, p, left);
      if (hdlen < 0) { TR(h, "OUT parse=hd_long_err\n"); return; }
      if (hd.type == NGTCP2_PKT_VERSION_NEGOTIATION) {
        TR(h, "OUT space=none type=version_negotiation\n");
        return;
      }
      if (hd.type == NGTCP2_PKT_RETRY) {
        TR(h, "OUT space=none type=retry\n");
        return;
      }
      if (hd.len > left - (size_t)hdlen) {
        TR(h, "OUT parse=len_err\n");
        return;
      }
      pktend = (size_t)hdlen + hd.len;
      space = hd.type == NGTCP2_PKT_INITIAL     ? 0
              : hd.type == NGTCP2_PKT_HANDSHAKE ? 1
                                                : 2;
    } else {
      /* The Destination Connection ID of a packet we write is the one the peer
         told us to use, which need not be CIDLEN bytes long: a NEW_CONNECTION_ID
         with a longer CID and a Retire Prior To that retires the current one
         makes ngtcp2 switch to it.  Assuming CIDLEN then reads the packet number,
         the header-protection sample and the payload at the wrong offset, and
         the OUT record is noise (WP13-15). */
#ifdef DRIVER_QUICHE
      hdlen = ngtcp2_pkt_decode_hd_short(&hd, p, left, g_q_dcidlen);
#else
      hdlen = ngtcp2_pkt_decode_hd_short(&hd, p, left,
                                         h->conn->dcid.current.cid.datalen);
#endif
      if (hdlen < 0) { TR(h, "OUT parse=hd_short_err\n"); return; }
      pktend = left;
      space = 2;
    }
    pnoff = (size_t)hdlen;
    if (pnoff + 4 + NGTCP2_HP_SAMPLELEN > pktend) {
      TR(h, "OUT parse=sample_err\n");
      return;
    }
    sample = p + pnoff + 4;
    memcpy(mask, sample, NGTCP2_HP_MASKLEN);
    b0 = (uint8_t)(p[0] ^ (mask[0] & (uint8_t)((p[0] & NGTCP2_HEADER_FORM_BIT)
                                                 ? 0x0f
                                                 : 0x1f)));
    pnlen = (size_t)(b0 & 0x03) + 1;
    for (i = 0; i < pnlen; ++i) pnbuf[i] = (uint8_t)(p[pnoff + i] ^ mask[1 + i]);
    pn = ngtcp2_pkt_adjust_pkt_num(h->out_max_pn[space],
                                   (int64_t)get_be(pnbuf, pnlen), pnlen);
    if (pn > h->out_max_pn[space]) h->out_max_pn[space] = pn;

    if (pktend < pnoff + pnlen + TAGLEN) {
      TR(h, "OUT parse=short_payload\n");
      return;
    }
    TR(h, "OUT space=%s pn=%" PRId64 " len=%zu frames=[", space_name(space), pn,
       pktend);
    dump_frames_joined(&h->tr, p + pnoff + pnlen,
                       pktend - pnoff - pnlen - TAGLEN);
    TR(h, "]\n");

    p += pktend;
    left -= pktend;
  }
}

/* ---------------------------------------------------------------- steps */

#ifdef DRIVER_QUICHE
/* The engine: setup_conn, tr_time and the step_* functions, for quiche. */
#include "quiche_driver.h"
#else
static void tr_time(harness *h) {
  ngtcp2_tstamp e = ngtcp2_conn_get_expiry(h->conn);
  if (e == UINT64_MAX) TR(h, "TIME now=%" PRIu64 " expiry=none\n", h->ts);
  else TR(h, "TIME now=%" PRIu64 " expiry=%" PRIu64 "\n", h->ts, e);
  MH_TICK(h);
}

/* Reports a library error the way an application would: the QUIC error code
   ngtcp2_ccerr_set_liberr derives, then the CONNECTION_CLOSE it would send. */
static void tr_fatal(harness *h, int rv) {
  ngtcp2_ccerr ccerr;
  ngtcp2_pkt_info pi;
  ngtcp2_path_storage ps;
  uint8_t buf[PKTBUF];
  ngtcp2_ssize n;

  ngtcp2_ccerr_default(&ccerr);
  ngtcp2_ccerr_set_liberr(&ccerr, rv, NULL, 0);
  TR(h, "ERR type=%s code=%" PRIu64 " frame_type=%" PRIu64 " reason=",
     ccerr_type_name(ccerr.type), ccerr.error_code, ccerr.frame_type);
  if (ccerr.reasonlen) tr_hex(h, ccerr.reason, ccerr.reasonlen);
  TR(h, "\n");

  h->fatal = 1;

  memset(&pi, 0, sizeof(pi));
  ngtcp2_path_storage_zero(&ps);
  n = ngtcp2_conn_write_connection_close(h->conn, &ps.path, &pi, buf,
                                         sizeof(buf), &ccerr, h->ts);
  if (n < 0) {
    TR(h, "RET write_connection_close=%s\n", rc_name((int)n));
  } else {
    /* n == 0 is normal for an idle close or a drop: nothing goes on the wire. */
    TR(h, "RET write_connection_close=OK n=%td\n", (ptrdiff_t)n);
    if (n > 0) dump_out_datagram(h, buf, (size_t)n);
  }
}

static void step_recv(harness *h, int space, int64_t pn, const uint8_t *fb,
                      size_t fblen) {
  uint8_t pkt[PKTBUF];
  ngtcp2_pkt_info pi;
  ngtcp2_ssize pktlen;
  int rv;

  pktlen = build_peer_pkt(space, pn, fb, fblen, pkt, sizeof(pkt));
  if (pktlen < 0) {
    TR(h, "IN  space=%s pn=%" PRId64 " frames=[] build=failed\n",
       space_name(space), pn);
    tr_time(h);
    return;
  }
  TR(h, "IN  space=%s pn=%" PRId64 " len=%zu frames=[", space_name(space), pn,
     (size_t)pktlen);
  dump_frames_joined(&h->tr, g_build_plain, g_build_plainlen);
  TR(h, "]\n");

  memset(&pi, 0, sizeof(pi));
  MH_MARK(h);
  rv = ngtcp2_conn_read_pkt(h->conn, &h->path.path, &pi, pkt, (size_t)pktlen,
                            h->ts);
  TR(h, "RET read_pkt=%s\n", rc_name(rv));
  MH_RECV(h, pkt, (size_t)pktlen, rv);
  if (rv != 0) tr_fatal(h, rv);
  tr_time(h);
}

static void step_time(harness *h, uint64_t d) {
  int rv;
  h->ts += d;
  MH_MARK(h);
  rv = ngtcp2_conn_handle_expiry(h->conn, h->ts);
  TR(h, "RET handle_expiry=%s\n", rc_name(rv));
  MH_TIME(h, rv);
  if (rv != 0) tr_fatal(h, rv);
  tr_time(h);
}

static void step_open(harness *h, int uni) {
  int64_t sid = -1;
  int rv;
  MH_MARK(h);
  rv = uni ? ngtcp2_conn_open_uni_stream(h->conn, &sid, NULL)
           : ngtcp2_conn_open_bidi_stream(h->conn, &sid, NULL);
  MH_OPEN(h, uni, rv, sid);
  if (rv == 0) {
    h->last_stream = sid;
    TR(h, "RET open_%s_stream=OK id=%" PRId64 "\n", uni ? "uni" : "bidi", sid);
  } else {
    TR(h, "RET open_%s_stream=%s\n", uni ? "uni" : "bidi", rc_name(rv));
  }
  tr_time(h);
}

/* ngtcp2_conn_writev_stream keeps a pointer into the caller's buffer until the
   data is acknowledged, for retransmission ("the caller must keep the portion
   of data covered by *pdatalen in tact until acked_stream_data_offset ... or
   the stream is closed").  A stack buffer here is a stack-use-after-return.
   The filler is the same for every stream and offset, so one buffer with a
   fixed content serves all of them. */
static uint8_t g_write_data[1024];

static void init_write_data(void) {
  size_t i;
  for (i = 0; i < sizeof(g_write_data); ++i)
    g_write_data[i] = (uint8_t)('a' + (i % 26));
}

static void step_write(harness *h, int64_t sid, size_t n, int fin) {
  uint8_t buf[PKTBUF];
  ngtcp2_pkt_info pi;
  ngtcp2_path_storage ps;
  ngtcp2_vec vec;
  size_t off = 0;
  int iter;

  if (n > sizeof(g_write_data)) n = sizeof(g_write_data);

  MH_MARK(h);
  MH_WRITE(h, sid, n, fin);

  for (iter = 0; iter < 16; ++iter) {
    ngtcp2_ssize ndatalen = 0, spktlen;
    uint32_t flags = fin ? NGTCP2_WRITE_STREAM_FLAG_FIN
                         : NGTCP2_WRITE_STREAM_FLAG_NONE;
    vec.base = g_write_data + off;
    vec.len = n - off;
    memset(&pi, 0, sizeof(pi));
    ngtcp2_path_storage_zero(&ps);
    spktlen = ngtcp2_conn_writev_stream(h->conn, &ps.path, &pi, buf,
                                        sizeof(buf), &ndatalen, flags, sid,
                                        &vec, 1, h->ts);
    if (spktlen < 0) {
      TR(h, "RET writev_stream=%s\n", rc_name((int)spktlen));
      if (spktlen != NGTCP2_ERR_STREAM_DATA_BLOCKED &&
          spktlen != NGTCP2_ERR_STREAM_NOT_FOUND &&
          spktlen != NGTCP2_ERR_STREAM_SHUT_WR &&
          spktlen != NGTCP2_ERR_WRITE_MORE)
        tr_fatal(h, (int)spktlen);
      break;
    }
    if (ndatalen > 0) off += (size_t)ndatalen;
    if (spktlen == 0) {
      TR(h, "RET writev_stream=OK spktlen=0\n");
      break;
    }
    dump_out_datagram(h, buf, (size_t)spktlen);
    MH_OUT(h, buf, (size_t)spktlen);
    if (off >= n) break;
  }
  tr_time(h);
}

static void step_drain(harness *h) {
  uint8_t buf[PKTBUF];
  int iter;
  MH_MARK(h);
  for (iter = 0; iter < 16; ++iter) {
    ngtcp2_pkt_info pi;
    ngtcp2_path_storage ps;
    ngtcp2_ssize spktlen;
    memset(&pi, 0, sizeof(pi));
    ngtcp2_path_storage_zero(&ps);
    spktlen = ngtcp2_conn_write_pkt(h->conn, &ps.path, &pi, buf, sizeof(buf),
                                    h->ts);
    if (spktlen < 0) {
      TR(h, "RET write_pkt=%s\n", rc_name((int)spktlen));
      tr_fatal(h, (int)spktlen);
      break;
    }
    if (spktlen == 0) break;
    dump_out_datagram(h, buf, (size_t)spktlen);
    MH_OUT(h, buf, (size_t)spktlen);
  }
  tr_time(h);
}

enum { SHUT_RD_ = 0, SHUT_WR_ = 1, SHUT_RDWR_ = 2 };

static void step_shutdown(harness *h, int which, int64_t sid, uint64_t err) {
  int rv;
  const char *name;
  MH_MARK(h);
  switch (which) {
  case SHUT_RD_:
    rv = ngtcp2_conn_shutdown_stream_read(h->conn, 0, sid, err);
    name = "shutdown_stream_read";
    break;
  case SHUT_WR_:
    rv = ngtcp2_conn_shutdown_stream_write(h->conn, 0, sid, err);
    name = "shutdown_stream_write";
    break;
  default:
    rv = ngtcp2_conn_shutdown_stream(h->conn, 0, sid, err);
    name = "shutdown_stream";
    break;
  }
  TR(h, "RET %s=%s\n", name, rc_name(rv));
  MH_SHUTDOWN(h, which, sid, err, rv);
  if (rv != 0 && rv != NGTCP2_ERR_STREAM_NOT_FOUND &&
      rv != NGTCP2_ERR_INVALID_ARGUMENT)
    tr_fatal(h, rv);
  tr_time(h);
}

enum { EXT_STREAM = 0, EXT_CONN = 1, EXT_STREAMS_BIDI = 2, EXT_STREAMS_UNI = 3 };

static void step_extend(harness *h, int which, int64_t sid, uint64_t n) {
  int rv;
  switch (which) {
  case EXT_STREAM:
    rv = ngtcp2_conn_extend_max_stream_offset(h->conn, sid, n);
    TR(h, "RET extend_max_stream_offset=%s\n", rc_name(rv));
    break;
  case EXT_CONN:
    ngtcp2_conn_extend_max_offset(h->conn, n);
    TR(h, "RET extend_max_offset=OK\n");
    break;
  case EXT_STREAMS_BIDI:
    ngtcp2_conn_extend_max_streams_bidi(h->conn, (size_t)n);
    TR(h, "RET extend_max_streams_bidi=OK\n");
    break;
  default:
    ngtcp2_conn_extend_max_streams_uni(h->conn, (size_t)n);
    TR(h, "RET extend_max_streams_uni=OK\n");
    break;
  }
  tr_time(h);
}

/* --------------------------------------------------------------- driver */

#endif /* DRIVER_QUICHE */

static void harness_start(harness *h, int server) {
  memset(h, 0, sizeof(*h));
  h->server = server;
  h->last_stream = -1;
  h->out_max_pn[0] = h->out_max_pn[1] = h->out_max_pn[2] = -1;
  g_rand_state = 0x12345678u;
  init_write_data();
  sb_reserve(&h->tr, 4096);
  h->tr.p[0] = 0;
  TR(h, "CONN role=%s scid=", server ? "server" : "client");
  tr_hex(h, g_cid_local, CIDLEN);
  TR(h, " dcid=");
  tr_hex(h, g_cid_remote, CIDLEN);
  TR(h, "\n");
  MH_START(h, server);
}

static uint64_t trace_hash(const sbuf *sb) {
  uint64_t v = 1469598103934665603ULL;
  size_t i;
  for (i = 0; i < sb->len; ++i) v = (v ^ (uint8_t)sb->p[i]) * 1099511628211ULL;
  return v;
}

static volatile uint64_t g_sink;

static void harness_finish(harness *h, int show) {
  uint64_t v;
  MH_FINISH(h);
  TR(h, "SUM %016" PRIx64 "\n", trace_hash(&h->tr));
  v = trace_hash(&h->tr);
  g_sink = v;
  if (show) fputs(h->tr.p, stdout);
#ifdef DRIVER_QUICHE
  drv_free(h);
#else
  if (h->conn) ngtcp2_conn_del(h->conn);
  h->conn = NULL;
#endif
  free(h->tr.p);
  h->tr.p = NULL;
}

/* ------------------------------------------------------ binary step input */

typedef struct {
  const uint8_t *p;
  size_t len, pos;
} cursor;

static int cur_done(const cursor *c) { return c->pos >= c->len; }

static uint8_t cur_u8(cursor *c) {
  return c->pos < c->len ? c->p[c->pos++] : 0;
}

static uint64_t cur_u16(cursor *c) {
  uint64_t a = cur_u8(c);
  return (a << 8) | cur_u8(c);
}

static int64_t cur_sid(cursor *c, harness *h) {
  uint8_t b = cur_u8(c);
  if (b & 0x80) return h->last_stream;
  return (int64_t)(b & 0x3f);
}

static void run_binary(harness *h, const uint8_t *data, size_t size) {
  cursor c;
  int steps;

  c.p = data;
  c.len = size;
  c.pos = 0;

  for (steps = 0; steps < MAX_STEPS && !cur_done(&c) && !h->fatal; ++steps) {
    uint8_t op = cur_u8(&c);
    switch (op % 11) {
    case 0:
    case 1:
    case 10: {
      int space = cur_u8(&c) % 3;
      int64_t pn = (int64_t)cur_u16(&c);
      size_t n = cur_u8(&c);
      uint8_t fb[256];
      size_t i;
      for (i = 0; i < n; ++i) fb[i] = cur_u8(&c);
      step_recv(h, space, pn, fb, n);
      break;
    }
    case 2:
      step_time(h, (uint64_t)cur_u16(&c) * NGTCP2_MILLISECONDS);
      break;
    case 3:
      step_open(h, cur_u8(&c) & 1);
      break;
    case 4: {
      int64_t sid = cur_sid(&c, h);
      size_t n = cur_u8(&c) * 4u;
      int fin = cur_u8(&c) & 1;
      step_write(h, sid, n, fin);
      break;
    }
    case 5: {
      int which = cur_u8(&c) % 3;
      int64_t sid = cur_sid(&c, h);
      uint64_t err = cur_u16(&c);
      step_shutdown(h, which, sid, err);
      break;
    }
    case 6: {
      int which = cur_u8(&c) % 4;
      int64_t sid = cur_sid(&c, h);
      uint64_t n = cur_u16(&c);
      step_extend(h, which, sid, n);
      break;
    }
    case 7:
    case 8:
      step_drain(h);
      break;
    default: {
      int uni = cur_u8(&c) & 1;
      size_t n = cur_u8(&c) * 4u;
      int fin = cur_u8(&c) & 1;
      step_open(h, uni);
      if (!h->fatal) step_write(h, h->last_stream, n, fin);
      break;
    }
    }
  }
}

/* -------------------------------------------------------- text script input */

static char *skip_ws(char *s) {
  while (*s == ' ' || *s == '\t') ++s;
  return s;
}

static char *token(char **s) {
  char *b;
  *s = skip_ws(*s);
  if (**s == 0) return NULL;
  b = *s;
  while (**s && **s != ' ' && **s != '\t') ++*s;
  if (**s) { **s = 0; ++*s; }
  return b;
}

static uint64_t parse_u64(const char *s) {
  if (!s) return 0;
  if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X'))
    return strtoull(s + 2, NULL, 16);
  return strtoull(s, NULL, 10);
}

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static size_t parse_hex(const char *s, uint8_t *out, size_t cap) {
  size_t n = 0;
  if (!s) return 0;
  while (s[0] && s[1] && n < cap) {
    int a = hexval(s[0]), b = hexval(s[1]);
    if (a < 0 || b < 0) break;
    out[n++] = (uint8_t)((a << 4) | b);
    s += 2;
  }
  return n;
}

static int64_t parse_sid(const char *s, harness *h) {
  if (!s) return -1;
  if (strcmp(s, "last") == 0) return h->last_stream;
  return (int64_t)strtoll(s, NULL, 10);
}

static int parse_space(const char *s) {
  if (!s) return 2;
  if (strcmp(s, "initial") == 0) return 0;
  if (strcmp(s, "handshake") == 0) return 1;
  return 2;
}

static int run_script(const char *path) {
  FILE *f = fopen(path, "r");
  char line[8192];
  harness h;
  int started = 0, server = 1, rc = 0;

  if (!f) {
    fprintf(stderr, "conn_trace: cannot open %s\n", path);
    return 1;
  }
  harness_start(&h, server);

  while (fgets(line, sizeof(line), f)) {
    char *s = line, *op;
    char *hash;
    size_t l;
    hash = strchr(s, '#');
    if (hash) *hash = 0;
    l = strlen(s);
    while (l && (s[l - 1] == '\n' || s[l - 1] == '\r')) s[--l] = 0;
    op = token(&s);
    if (!op) continue;

    if (strcmp(op, "role") == 0) {
      char *v = token(&s);
      if (started) {
        fprintf(stderr, "conn_trace: `role` must precede every other step\n");
        rc = 1;
        break;
      }
      server = !(v && strcmp(v, "client") == 0);
      free(h.tr.p);
      harness_start(&h, server);
      continue;
    }

    if (!started) {
      if (setup_conn(&h, server) != 0) {
        fprintf(stderr, "conn_trace: setup_conn failed\n");
        rc = 1;
        break;
      }
      started = 1;
      tr_time(&h);
    }
    if (h.fatal) {
      TR(&h, "SKIP %s\n", op);
      continue;
    }

    if (strcmp(op, "recv") == 0) {
      char *sp = token(&s), *pn = token(&s), *hex = token(&s);
      uint8_t fb[1024];
      size_t n = parse_hex(hex, fb, sizeof(fb));
      step_recv(&h, parse_space(sp), (int64_t)parse_u64(pn), fb, n);
    } else if (strcmp(op, "time") == 0) {
      step_time(&h, parse_u64(token(&s)));
    } else if (strcmp(op, "open") == 0) {
      char *d = token(&s);
      step_open(&h, d && strcmp(d, "uni") == 0);
    } else if (strcmp(op, "write") == 0) {
      char *sid = token(&s), *n = token(&s), *fin = token(&s);
      step_write(&h, parse_sid(sid, &h), (size_t)parse_u64(n),
                 (int)parse_u64(fin));
    } else if (strcmp(op, "shutdown_read") == 0) {
      char *sid = token(&s), *e = token(&s);
      step_shutdown(&h, SHUT_RD_, parse_sid(sid, &h), parse_u64(e));
    } else if (strcmp(op, "shutdown_write") == 0) {
      char *sid = token(&s), *e = token(&s);
      step_shutdown(&h, SHUT_WR_, parse_sid(sid, &h), parse_u64(e));
    } else if (strcmp(op, "shutdown") == 0) {
      char *sid = token(&s), *e = token(&s);
      step_shutdown(&h, SHUT_RDWR_, parse_sid(sid, &h), parse_u64(e));
    } else if (strcmp(op, "extend_stream") == 0) {
      char *sid = token(&s), *n = token(&s);
      step_extend(&h, EXT_STREAM, parse_sid(sid, &h), parse_u64(n));
    } else if (strcmp(op, "extend_conn") == 0) {
      step_extend(&h, EXT_CONN, -1, parse_u64(token(&s)));
    } else if (strcmp(op, "extend_streams") == 0) {
      char *d = token(&s), *n = token(&s);
      step_extend(&h, (d && strcmp(d, "uni") == 0) ? EXT_STREAMS_UNI
                                                   : EXT_STREAMS_BIDI,
                  -1, parse_u64(n));
    } else if (strcmp(op, "drain") == 0) {
      step_drain(&h);
    } else {
      fprintf(stderr, "conn_trace: unknown step `%s`\n", op);
      rc = 1;
      break;
    }
  }
  fclose(f);
  if (!started && rc == 0) {
    if (setup_conn(&h, server) != 0) rc = 1;
    else tr_time(&h);
  }
  harness_finish(&h, 1);
  return rc;
}

#endif /* CONN_DRIVER_H */
