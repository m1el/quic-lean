/* Shared by the differential harnesses: string buffer, canonical frame
   rendering (must match QuicModel/Dump.lean) and Lean runtime start-up. */
#ifndef DIFF_COMMON_H
#define DIFF_COMMON_H

#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#include "ngtcp2_conn.h"

extern lean_object *initialize_QuicModel_QuicModel(uint8_t builtin);
extern void lean_initialize_runtime_module(void);

typedef struct {
  char *p;
  size_t len, cap;
} sbuf;

static void sb_reserve(sbuf *sb, size_t extra) {
  if (sb->len + extra + 1 > sb->cap) {
    sb->cap = (sb->len + extra + 1) * 2;
    sb->p = realloc(sb->p, sb->cap);
    if (!sb->p) abort();
  }
}

static void sb_printf(sbuf *sb, const char *fmt, ...) {
  va_list ap;
  char tmp[256];
  int n;
  va_start(ap, fmt);
  n = vsnprintf(tmp, sizeof(tmp), fmt, ap);
  va_end(ap);
  if (n < 0 || (size_t)n >= sizeof(tmp)) abort();
  sb_reserve(sb, (size_t)n);
  memcpy(sb->p + sb->len, tmp, (size_t)n + 1);
  sb->len += (size_t)n;
}

static void sb_hex(sbuf *sb, const uint8_t *d, size_t n) {
  static const char H[] = "0123456789abcdef";
  size_t i;
  sb_reserve(sb, n * 2);
  for (i = 0; i < n; ++i) {
    sb->p[sb->len++] = H[d[i] >> 4];
    sb->p[sb->len++] = H[d[i] & 15];
  }
  sb->p[sb->len] = 0;
}

static void dump_frame(sbuf *sb, const ngtcp2_frame *fr) {
  size_t i;
  switch (fr->hd.type) {
  case NGTCP2_FRAME_PADDING:
    sb_printf(sb, "PADDING len=%zu", fr->padding.len);
    break;
  case NGTCP2_FRAME_PING:
    sb_printf(sb, "PING");
    break;
  case NGTCP2_FRAME_ACK:
  case NGTCP2_FRAME_ACK_ECN:
    sb_printf(sb, "ACK largest=%" PRId64 " delay=%" PRIu64 " first=%" PRIu64
                  " ranges=[",
              fr->ack.largest_ack, fr->ack.ack_delay, fr->ack.first_ack_range);
    for (i = 0; i < fr->ack.rangecnt; ++i) {
      sb_printf(sb, "%s%" PRIu64 ":%" PRIu64, i ? "," : "",
                fr->ack.ranges[i].gap, fr->ack.ranges[i].len);
    }
    sb_printf(sb, "]");
    if (fr->hd.type == NGTCP2_FRAME_ACK_ECN) {
      sb_printf(sb, " ecn=%" PRIu64 ",%" PRIu64 ",%" PRIu64, fr->ack.ecn.ect0,
                fr->ack.ecn.ect1, fr->ack.ecn.ce);
    }
    break;
  case NGTCP2_FRAME_RESET_STREAM:
    sb_printf(sb, "RESET_STREAM id=%" PRId64 " err=%" PRIu64 " final=%" PRIu64,
              fr->reset_stream.stream_id, fr->reset_stream.app_error_code,
              fr->reset_stream.final_size);
    break;
  case NGTCP2_FRAME_STOP_SENDING:
    sb_printf(sb, "STOP_SENDING id=%" PRId64 " err=%" PRIu64,
              fr->stop_sending.stream_id, fr->stop_sending.app_error_code);
    break;
  case NGTCP2_FRAME_CRYPTO:
    sb_printf(sb, "CRYPTO off=%" PRIu64 " data=", fr->stream.offset);
    if (fr->stream.datacnt)
      sb_hex(sb, fr->stream.data[0].base, fr->stream.data[0].len);
    break;
  case NGTCP2_FRAME_NEW_TOKEN:
    sb_printf(sb, "NEW_TOKEN token=");
    sb_hex(sb, fr->new_token.token, fr->new_token.tokenlen);
    break;
  case NGTCP2_FRAME_STREAM:
    sb_printf(sb, "STREAM id=%" PRId64 " off=%" PRIu64 " fin=%d data=",
              fr->stream.stream_id, fr->stream.offset, fr->stream.fin ? 1 : 0);
    if (fr->stream.datacnt)
      sb_hex(sb, fr->stream.data[0].base, fr->stream.data[0].len);
    break;
  case NGTCP2_FRAME_MAX_DATA:
    sb_printf(sb, "MAX_DATA v=%" PRIu64, fr->max_data.max_data);
    break;
  case NGTCP2_FRAME_MAX_STREAM_DATA:
    sb_printf(sb, "MAX_STREAM_DATA id=%" PRId64 " v=%" PRIu64,
              fr->max_stream_data.stream_id,
              fr->max_stream_data.max_stream_data);
    break;
  case NGTCP2_FRAME_MAX_STREAMS_BIDI:
  case NGTCP2_FRAME_MAX_STREAMS_UNI:
    sb_printf(sb, "MAX_STREAMS dir=%s v=%" PRIu64,
              fr->hd.type == NGTCP2_FRAME_MAX_STREAMS_BIDI ? "bidi" : "uni",
              fr->max_streams.max_streams);
    break;
  case NGTCP2_FRAME_DATA_BLOCKED:
    sb_printf(sb, "DATA_BLOCKED v=%" PRIu64, fr->data_blocked.max_data);
    break;
  case NGTCP2_FRAME_STREAM_DATA_BLOCKED:
    sb_printf(sb, "STREAM_DATA_BLOCKED id=%" PRId64 " v=%" PRIu64,
              fr->stream_data_blocked.stream_id,
              fr->stream_data_blocked.max_stream_data);
    break;
  case NGTCP2_FRAME_STREAMS_BLOCKED_BIDI:
  case NGTCP2_FRAME_STREAMS_BLOCKED_UNI:
    sb_printf(sb, "STREAMS_BLOCKED dir=%s v=%" PRIu64,
              fr->hd.type == NGTCP2_FRAME_STREAMS_BLOCKED_BIDI ? "bidi" : "uni",
              fr->streams_blocked.max_streams);
    break;
  case NGTCP2_FRAME_NEW_CONNECTION_ID:
    sb_printf(sb, "NEW_CONNECTION_ID seq=%" PRIu64 " rpt=%" PRIu64 " cid=",
              fr->new_connection_id.seq, fr->new_connection_id.retire_prior_to);
    sb_hex(sb, fr->new_connection_id.cid.data, fr->new_connection_id.cid.datalen);
    sb_printf(sb, " token=");
    sb_hex(sb, fr->new_connection_id.token.data,
           sizeof(fr->new_connection_id.token.data));
    break;
  case NGTCP2_FRAME_RETIRE_CONNECTION_ID:
    sb_printf(sb, "RETIRE_CONNECTION_ID seq=%" PRIu64,
              fr->retire_connection_id.seq);
    break;
  case NGTCP2_FRAME_PATH_CHALLENGE:
    sb_printf(sb, "PATH_CHALLENGE data=");
    sb_hex(sb, fr->path_challenge.data.data, 8);
    break;
  case NGTCP2_FRAME_PATH_RESPONSE:
    sb_printf(sb, "PATH_RESPONSE data=");
    sb_hex(sb, fr->path_response.data.data, 8);
    break;
  case NGTCP2_FRAME_CONNECTION_CLOSE:
  case NGTCP2_FRAME_CONNECTION_CLOSE_APP:
    sb_printf(sb, "CONNECTION_CLOSE kind=%s err=%" PRIu64 " ftype=%" PRIu64
                  " reason=",
              fr->hd.type == NGTCP2_FRAME_CONNECTION_CLOSE ? "transport" : "app",
              fr->connection_close.error_code, fr->connection_close.frame_type);
    if (fr->connection_close.reasonlen)
      sb_hex(sb, fr->connection_close.reason, fr->connection_close.reasonlen);
    break;
  case NGTCP2_FRAME_HANDSHAKE_DONE:
    sb_printf(sb, "HANDSHAKE_DONE");
    break;
  case NGTCP2_FRAME_DATAGRAM:
  case NGTCP2_FRAME_DATAGRAM_LEN:
    sb_printf(sb, "DATAGRAM len=%d data=",
              fr->hd.type == NGTCP2_FRAME_DATAGRAM_LEN ? 1 : 0);
    if (fr->datagram.datacnt)
      sb_hex(sb, fr->datagram.data[0].base, fr->datagram.data[0].len);
    break;
  default:
    sb_printf(sb, "UNKNOWN type=%" PRIu64, (uint64_t)fr->hd.type);
  }
}

/* libFuzzer's own artifact writer does not always get to run once the Lean
   runtime is loaded, so keep a copy of the offending input ourselves. */
static void save_input(const char *kind, const uint8_t *data, size_t size) {
  uint64_t h = 1469598103934665603ULL;
  char path[256];
  const char *dir = getenv("DIFF_OUT");
  FILE *f;
  size_t i;
  for (i = 0; i < size; ++i) h = (h ^ data[i]) * 1099511628211ULL;
  snprintf(path, sizeof(path), "%s/%s-%016" PRIx64, dir ? dir : ".", kind, h);
  f = fopen(path, "wb");
  if (!f) return;
  fwrite(data, 1, size, f);
  fclose(f);
  fprintf(stderr, "input saved to %s\n", path);
}

static void model_init(void) {
  lean_object *res;
  lean_initialize_runtime_module();
  res = initialize_QuicModel_QuicModel(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    abort();
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
}

static lean_object *model_bytes(const uint8_t *data, size_t size) {
  lean_object *arr = lean_alloc_sarray(1, size, size);
  if (size) memcpy(lean_sarray_cptr(arr), data, size);
  return arr;
}

/* Compares and consumes |model|. */
static void expect_same(const char *what, const sbuf *c, lean_object *model,
                        const uint8_t *data, size_t size) {
  const char *m = lean_string_cstr(model);
  if (getenv("DIFF_SHOW")) {
    printf("--- ngtcp2 (%s)\n%s--- model\n%s", what, c->p, m);
  }
  if (strcmp(c->p, m) != 0) {
    fprintf(stderr, "MISMATCH (%s)\n--- ngtcp2\n%s--- model\n%s", what, c->p, m);
    save_input("mismatch", data, size);
    abort();
  }
  lean_dec(model);
}

/* Runs the C frame decoder over a payload the way fuzz/decode_frame.cc does.
   Returns the number of frames decoded, or -1 if one failed. */
/* Whether c_dump_frames prints each frame's encoded length. */
static int g_show_n = 1;

static int c_dump_frames(sbuf *sb, const uint8_t *p, size_t size) {
  ngtcp2_frame_decoder frd;
  int cnt = 0;
  while (size) {
    ngtcp2_frame fr;
    ngtcp2_ssize n;
    memset(&fr, 0, sizeof(fr));
    n = ngtcp2_frame_decoder_decode(&frd, &fr, p, size);
    if (n < 0) return -1;
    if (n == 0 || (size_t)n > size) {
      sb_printf(sb, "BADLEN %td\n", (ptrdiff_t)n);
      return -1;
    }
    dump_frame(sb, &fr);
    if (g_show_n) sb_printf(sb, " n=%td", (ptrdiff_t)n);
    sb_printf(sb, "\n");
    ++cnt;
    p += n;
    size -= (size_t)n;
  }
  return cnt;
}

#endif /* DIFF_COMMON_H */
