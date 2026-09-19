/*
 * api_misuse -- an application that misuses the ngtcp2 API on purpose, run
 * under the Lean usage monitor (QuicModel/Api/Usage.lean).
 *
 * The question is not "what does ngtcp2 do when misused" but "does the
 * contract *detect* the misuse".  Every call to one of the four functions of
 * the trial goes through a wrapper (M_read_pkt, ...) that
 *
 *   1. asks the monitor which clauses the call breaks (quic_api_check) and
 *      prints them -- before the call, because the call may not return;
 *   2. makes the real call;
 *   3. tells the monitor the return value (quic_api_post), and compares the
 *      monitor's idea of "a packet is pending" with ngtcp2's own
 *      NGTCP2_CONN_FLAG_PPE_PENDING.  That comparison tests the postconditions.
 *
 * Each case runs in a forked child, because the library's reaction to misuse
 * is often an abort.  The parent records what the library did (returned,
 * assert, AddressSanitizer report) next to what the monitor said, and the
 * verdict is about the monitor alone:
 *
 *   DETECTED  the expected clause was flagged (whatever ngtcp2 did)
 *   MISSED    it was not
 *   CLEAN     a control case, and nothing was flagged
 *   FALSE+    a control case, and something was
 *
 * Build it twice (build_api_misuse.sh): against build-c/ (asserts live, which
 * is how ngtcp2 ships -- CMakeLists.txt:102 strips -DNDEBUG from Release) and
 * against build-c-ndebug/ (-DNDEBUG), which shows what each assert protects.
 *
 * The connection is the one conn_driver.h sets up: stub crypto, forced past
 * the handshake.  That setup is itself outside any API contract, so the
 * monitor starts at the first call made after it.
 */
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "conn_driver.h"

const char *__asan_default_options(void) { return "detect_leaks=0"; }

extern lean_object *quic_api_init(uint8_t);
extern uint32_t quic_api_check(lean_object *, uint8_t, uint8_t, uint64_t,
                               uint64_t, uint64_t, uint64_t, uint64_t);
extern lean_object *quic_api_post(lean_object *, uint8_t, uint8_t, uint64_t,
                                  uint64_t, uint64_t, uint64_t, uint64_t,
                                  uint64_t, uint8_t);
extern lean_object *quic_api_enter_callback(lean_object *);
extern lean_object *quic_api_exit_callback(lean_object *);
extern uint8_t quic_api_is_pending(lean_object *);
extern uint8_t quic_api_clause_count(uint8_t);
extern lean_object *quic_api_clause_name(uint8_t);

/* Bits of quic_api_check's mask: Quic.Api.Clause.all, in order. */
enum {
  CL_TS_MONOTONIC = 1u << 0,
  CL_NOT_IN_CALLBACK = 1u << 1,
  CL_NO_CALL_WHILE_PENDING = 1u << 2,
  CL_NO_CALL_WHILE_PENDING_UNGUARDED = 1u << 3,
  CL_PENDING_SAME_ARGS = 1u << 4,
  CL_PATH_NON_NULL = 1u << 5,
  CL_DESTLEN_MIN = 1u << 6,
  CL_NOT_WHEN_CLOSED = 1u << 7,
  CL_NOT_AFTER_TERMINAL = 1u << 8,
};

enum { K_READ_PKT, K_WRITEV_STREAM, K_HANDLE_EXPIRY, K_EXTEND };

/* What a child tells its parent. */
typedef struct {
  uint32_t flagged;       /* every clause the monitor flagged */
  int post_mismatches;    /* monitor's pending != PPE_PENDING after a call */
  int finished;           /* the case ran to its end */
} report;

static report *g_rep;

typedef struct {
  harness h;
  lean_object *mon;
} app;

static app *g_app; /* for callbacks */

/* ------------------------------------------------------------- the shim */

static void say_mask(uint32_t mask) {
  uint8_t i, n = quic_api_clause_count(0);
  for (i = 0; i < n; ++i) {
    if (mask & (1u << i)) {
      lean_object *s = quic_api_clause_name(i);
      printf("    MONITOR  violation: %s\n", lean_string_cstr(s));
      lean_dec(s);
    }
  }
}

static void mon_before(app *a, const char *fn, uint8_t kind, uint8_t path_null,
                       uint64_t path, uint64_t pi, uint64_t dest,
                       uint64_t destlen, uint64_t ts) {
  uint32_t mask;
  lean_inc(a->mon);
  mask = quic_api_check(a->mon, kind, path_null, path, pi, dest, destlen, ts);
  printf("  call %s ts=%" PRIu64 "\n", fn, ts);
  if (mask) say_mask(mask);
  g_rep->flagged |= mask;
  fflush(stdout);
}

static void mon_after(app *a, uint8_t kind, uint8_t path_null, uint64_t path,
                      uint64_t pi, uint64_t dest, uint64_t destlen, uint64_t ts,
                      int64_t code, int more) {
  int lib_pending, mon_pending;
  a->mon = quic_api_post(a->mon, kind, path_null, path, pi, dest, destlen, ts,
                         (uint64_t)code, (uint8_t)more);
  lean_inc(a->mon);
  mon_pending = quic_api_is_pending(a->mon);
  lib_pending = (a->h.conn->flags & NGTCP2_CONN_FLAG_PPE_PENDING) != 0;
  printf("    -> %s%s\n", code < 0 ? rc_name((int)code) : "ok",
         lib_pending ? "  [packet pending]" : "");
  if (mon_pending != lib_pending) {
    printf("    POST     mismatch: monitor pending=%d, ngtcp2 PPE_PENDING=%d\n",
           mon_pending, lib_pending);
    ++g_rep->post_mismatches;
  }
  fflush(stdout);
}

static int M_read_pkt(app *a, const ngtcp2_path *path, const uint8_t *pkt,
                      size_t pktlen, ngtcp2_tstamp ts) {
  ngtcp2_pkt_info pi;
  int rv;
  memset(&pi, 0, sizeof(pi));
  mon_before(a, "read_pkt", K_READ_PKT, path == NULL, 0, 0, 0, 0, ts);
  rv = ngtcp2_conn_read_pkt(a->h.conn, path, &pi, pkt, pktlen, ts);
  mon_after(a, K_READ_PKT, path == NULL, 0, 0, 0, 0, ts, rv, 0);
  return rv;
}

static ngtcp2_ssize M_writev_stream(app *a, ngtcp2_path *path,
                                    ngtcp2_pkt_info *pi, uint8_t *dest,
                                    size_t destlen, uint32_t flags, int64_t sid,
                                    const uint8_t *data, size_t datalen,
                                    ngtcp2_tstamp ts) {
  ngtcp2_vec vec;
  ngtcp2_ssize ndatalen = -1, rv;
  int more = (flags & NGTCP2_WRITE_STREAM_FLAG_MORE) != 0;
  vec.base = (uint8_t *)data;
  vec.len = datalen;
  mon_before(a, "writev_stream", K_WRITEV_STREAM, 0, (uintptr_t)path,
             (uintptr_t)pi, (uintptr_t)dest, destlen, ts);
  rv = ngtcp2_conn_writev_stream(a->h.conn, path, pi, dest, destlen, &ndatalen,
                                 flags, sid, sid == -1 ? NULL : &vec,
                                 sid == -1 ? 0 : 1, ts);
  mon_after(a, K_WRITEV_STREAM, 0, (uintptr_t)path, (uintptr_t)pi,
            (uintptr_t)dest, destlen, ts, rv, more);
  return rv;
}

static int M_handle_expiry(app *a, ngtcp2_tstamp ts) {
  int rv;
  mon_before(a, "handle_expiry", K_HANDLE_EXPIRY, 0, 0, 0, 0, 0, ts);
  rv = ngtcp2_conn_handle_expiry(a->h.conn, ts);
  mon_after(a, K_HANDLE_EXPIRY, 0, 0, 0, 0, 0, ts, rv, 0);
  return rv;
}

static int M_extend(app *a, int64_t sid, uint64_t n) {
  int rv;
  mon_before(a, "extend_max_stream_offset", K_EXTEND, 0, 0, 0, 0, 0, 0);
  rv = ngtcp2_conn_extend_max_stream_offset(a->h.conn, sid, n);
  mon_after(a, K_EXTEND, 0, 0, 0, 0, 0, 0, rv, 0);
  return rv;
}

/* The callback side of the shim: recv_stream_data is wrapped so the monitor
   knows a callback is on the stack, and so a case can misbehave inside it. */
static void (*g_in_callback)(app *a, int64_t sid, size_t datalen);

static int shim_recv_stream_data(ngtcp2_conn *conn, uint32_t flags,
                                 int64_t stream_id, uint64_t offset,
                                 const uint8_t *data, size_t datalen,
                                 void *user_data, void *stream_user_data) {
  app *a = g_app;
  (void)conn; (void)flags; (void)offset; (void)data; (void)user_data;
  (void)stream_user_data;
  a->mon = quic_api_enter_callback(a->mon);
  printf("  callback recv_stream_data id=%" PRId64 " len=%zu {\n", stream_id,
         datalen);
  if (g_in_callback) g_in_callback(a, stream_id, datalen);
  printf("  }\n");
  a->mon = quic_api_exit_callback(a->mon);
  return 0;
}

/* ------------------------------------------------------------ fixtures */

#define SEC NGTCP2_SECONDS

static const uint8_t F_STREAM0[] = {0x0a, 0x00, 0x03, 'a', 'b', 'c'};
static const uint8_t F_PING[] = {0x01};
static const uint8_t F_CONN_CLOSE[] = {0x1c, 0x00, 0x00, 0x00};
static const uint8_t DATA[10] = "0123456789";

static int app_start(app *a, int server) {
  memset(a, 0, sizeof(*a));
  harness_start(&a->h, server);
  if (setup_conn(&a->h, server) != 0) return -1;
  a->h.conn->callbacks.recv_stream_data = shim_recv_stream_data;
  a->mon = quic_api_init(0);
  g_app = a;
  g_in_callback = NULL;
  return 0;
}

static size_t peer_pkt(int64_t pn, const uint8_t *fb, size_t fblen,
                       uint8_t *out, size_t cap) {
  ngtcp2_ssize n = build_peer_pkt(2, pn, fb, fblen, out, cap);
  if (n < 0) { printf("  (could not build peer packet)\n"); exit(2); }
  return (size_t)n;
}

/* Opens a stream and starts a packet that is left pending.  Returns the
   stream, or -1 if ngtcp2 did not answer WRITE_MORE. */
static int64_t start_pending(app *a, ngtcp2_path_storage *ps,
                             ngtcp2_pkt_info *pi, uint8_t *dest, size_t destlen,
                             ngtcp2_tstamp ts) {
  int64_t sid;
  ngtcp2_ssize rv;
  if (ngtcp2_conn_open_bidi_stream(a->h.conn, &sid, NULL) != 0) return -1;
  ngtcp2_path_storage_zero(ps);
  memset(pi, 0, sizeof(*pi));
  rv = M_writev_stream(a, &ps->path, pi, dest, destlen,
                       NGTCP2_WRITE_STREAM_FLAG_MORE, sid, DATA, sizeof(DATA),
                       ts);
  if (rv != NGTCP2_ERR_WRITE_MORE) {
    printf("  (fixture: expected WRITE_MORE, got %td)\n", rv);
    return -1;
  }
  return sid;
}

/* --------------------------------------------------------------- cases */

/* C1: the loop h:5324 describes, then a read and a timer. */
static void case_control_loop(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF], pkt[PKTBUF];
  size_t n;
  if (start_pending(a, &ps, &pi, dest, sizeof(dest), 1 * SEC) < 0) return;
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 1 * SEC);
  n = peer_pkt(0, F_PING, sizeof(F_PING), pkt, sizeof(pkt));
  M_read_pkt(a, &a->h.path.path, pkt, n, 2 * SEC);
  M_handle_expiry(a, 3 * SEC);
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 3 * SEC);
}

/* C2: extend_max_stream_offset from inside recv_stream_data is legal
   (examples/sim.cc:102 does exactly this). */
static void in_cb_extend(app *a, int64_t sid, size_t datalen) {
  M_extend(a, sid, datalen);
}
static void case_control_extend_in_callback(app *a) {
  uint8_t pkt[PKTBUF];
  size_t n = peer_pkt(0, F_STREAM0, sizeof(F_STREAM0), pkt, sizeof(pkt));
  g_in_callback = in_cb_extend;
  M_read_pkt(a, &a->h.path.path, pkt, n, 1 * SEC);
}

/* M1: a datagram arrives in the middle of a WRITE_MORE loop. */
static void case_read_pkt_while_pending(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF], pkt[PKTBUF];
  size_t n = peer_pkt(0, F_PING, sizeof(F_PING), pkt, sizeof(pkt));
  if (start_pending(a, &ps, &pi, dest, sizeof(dest), 1 * SEC) < 0) return;
  M_read_pkt(a, &a->h.path.path, pkt, n, 1 * SEC);
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 1 * SEC);
}

/* M2: a timer fires in the middle of a WRITE_MORE loop. */
static void case_handle_expiry_while_pending(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF];
  if (start_pending(a, &ps, &pi, dest, sizeof(dest), 1 * SEC) < 0) return;
  M_handle_expiry(a, 1 * SEC);
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 1 * SEC);
}

/* M3: the loop is resumed in a new buffer and the first one is freed --
   a send queue that recycles buffers between calls. */
static void case_resume_in_other_buffer(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t *d1 = malloc(PKTBUF), *d2 = malloc(PKTBUF);
  if (start_pending(a, &ps, &pi, d1, PKTBUF, 1 * SEC) < 0) return;
  free(d1);
  M_writev_stream(a, &ps.path, &pi, d2, PKTBUF, 0, -1, NULL, 0, 1 * SEC);
  free(d2);
}

/* M4: the loop is resumed with a fresh clock reading. */
static void case_resume_with_other_ts(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF];
  if (start_pending(a, &ps, &pi, dest, sizeof(dest), 1 * SEC) < 0) return;
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0,
                  1 * SEC + 5);
}

/* M5: the clock goes backwards (a wall clock stepped by NTP). */
static void case_ts_backwards(app *a) {
  uint8_t pkt[PKTBUF], pkt2[PKTBUF];
  size_t n = peer_pkt(0, F_PING, sizeof(F_PING), pkt, sizeof(pkt));
  size_t n2 = peer_pkt(1, F_PING, sizeof(F_PING), pkt2, sizeof(pkt2));
  M_read_pkt(a, &a->h.path.path, pkt, n, 5 * SEC);
  M_read_pkt(a, &a->h.path.path, pkt2, n2, 4 * SEC);
}

/* M6: no path. */
static void case_path_null(app *a) {
  uint8_t pkt[PKTBUF];
  size_t n = peer_pkt(0, F_PING, sizeof(F_PING), pkt, sizeof(pkt));
  M_read_pkt(a, NULL, pkt, n, 1 * SEC);
}

/* M7: extend_max_stream_offset in the middle of a WRITE_MORE loop: forbidden
   by h:5324, unguarded in the code. */
static void case_extend_while_pending(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF];
  int64_t sid = start_pending(a, &ps, &pi, dest, sizeof(dest), 1 * SEC);
  if (sid < 0) return;
  M_extend(a, sid, 100);
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 1 * SEC);
}

/* M8: the connection is used after handle_expiry said IDLE_CLOSE. */
static void case_use_after_idle_close(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF];
  int rv = M_handle_expiry(a, 40 * SEC);
  if (rv != NGTCP2_ERR_IDLE_CLOSE) {
    printf("  (fixture: expected IDLE_CLOSE, got %s)\n", rc_name(rv));
    return;
  }
  ngtcp2_path_storage_zero(&ps);
  memset(&pi, 0, sizeof(pi));
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 40 * SEC);
}

/* M9: read_pkt re-entered from inside recv_stream_data. */
static uint8_t g_inner_pkt[PKTBUF];
static size_t g_inner_len;
static void in_cb_read_pkt(app *a, int64_t sid, size_t datalen) {
  (void)sid; (void)datalen;
  g_in_callback = NULL;
  M_read_pkt(a, &a->h.path.path, g_inner_pkt, g_inner_len, 1 * SEC);
}
static void case_read_pkt_in_callback(app *a) {
  uint8_t pkt[PKTBUF];
  size_t n = peer_pkt(0, F_STREAM0, sizeof(F_STREAM0), pkt, sizeof(pkt));
  g_inner_len = peer_pkt(1, F_PING, sizeof(F_PING), g_inner_pkt,
                         sizeof(g_inner_pkt));
  g_in_callback = in_cb_read_pkt;
  M_read_pkt(a, &a->h.path.path, pkt, n, 1 * SEC);
}

/* M10: a buffer under NGTCP2_MAX_UDP_PAYLOAD_SIZE. */
static void case_small_dest(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[100];
  int64_t sid;
  if (ngtcp2_conn_open_bidi_stream(a->h.conn, &sid, NULL) != 0) return;
  ngtcp2_path_storage_zero(&ps);
  memset(&pi, 0, sizeof(pi));
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, sid, DATA,
                  sizeof(DATA), 1 * SEC);
}

/* M11: writing after the peer closed (read_pkt said DRAINING). */
static void case_write_when_draining(app *a) {
  ngtcp2_path_storage ps; ngtcp2_pkt_info pi;
  uint8_t dest[PKTBUF], pkt[PKTBUF];
  size_t n = peer_pkt(0, F_CONN_CLOSE, sizeof(F_CONN_CLOSE), pkt, sizeof(pkt));
  M_read_pkt(a, &a->h.path.path, pkt, n, 1 * SEC);
  ngtcp2_path_storage_zero(&ps);
  memset(&pi, 0, sizeof(pi));
  M_writev_stream(a, &ps.path, &pi, dest, sizeof(dest), 0, -1, NULL, 0, 1 * SEC);
}

typedef struct {
  const char *name;
  int server;
  uint32_t expect; /* 0 for a control */
  void (*run)(app *);
} misuse_case;

static const misuse_case CASES[] = {
  {"C1 control: WRITE_MORE loop, read, timer", 0, 0, case_control_loop},
  {"C2 control: extend inside recv_stream_data", 1, 0,
   case_control_extend_in_callback},
  {"M1 read_pkt while a packet is pending", 0, CL_NO_CALL_WHILE_PENDING,
   case_read_pkt_while_pending},
  {"M2 handle_expiry while a packet is pending", 0, CL_NO_CALL_WHILE_PENDING,
   case_handle_expiry_while_pending},
  {"M3 resume WRITE_MORE in another buffer, first freed", 0,
   CL_PENDING_SAME_ARGS, case_resume_in_other_buffer},
  {"M4 resume WRITE_MORE with another ts", 0, CL_PENDING_SAME_ARGS,
   case_resume_with_other_ts},
  {"M5 timestamp goes backwards", 0, CL_TS_MONOTONIC, case_ts_backwards},
  {"M6 read_pkt with path == NULL", 0, CL_PATH_NON_NULL, case_path_null},
  {"M7 extend_max_stream_offset while pending", 0,
   CL_NO_CALL_WHILE_PENDING_UNGUARDED, case_extend_while_pending},
  {"M8 writev_stream after IDLE_CLOSE", 0, CL_NOT_AFTER_TERMINAL,
   case_use_after_idle_close},
  {"M9 read_pkt from inside a callback", 1, CL_NOT_IN_CALLBACK,
   case_read_pkt_in_callback},
  {"M10 destlen below 1200", 0, CL_DESTLEN_MIN, case_small_dest},
  {"M11 writev_stream after DRAINING", 0, CL_NOT_WHEN_CLOSED,
   case_write_when_draining},
};
#define NCASES (sizeof(CASES) / sizeof(CASES[0]))

/* -------------------------------------------------------------- runner */

/* The first line of |path| that says how the library died. */
static void lib_reaction(const char *path, int status, char *out, size_t cap) {
  FILE *f = fopen(path, "r");
  char line[512];
  out[0] = 0;
  if (f) {
    while (fgets(line, sizeof(line), f)) {
      char *p;
      if ((p = strstr(line, "Assertion")) || (p = strstr(line, "AddressSanitizer:"))) {
        size_t n = strcspn(p, "\n");
        if (n >= cap) n = cap - 1;
        memcpy(out, p, n);
        out[n] = 0;
        break;
      }
    }
    fclose(f);
  }
  if (out[0]) return;
  if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
    snprintf(out, cap, "returned normally");
  else if (WIFSIGNALED(status))
    snprintf(out, cap, "killed by signal %d", WTERMSIG(status));
  else
    snprintf(out, cap, "exit status %d", WEXITSTATUS(status));
}

int main(void) {
  size_t i;
  int bad = 0;
  report *reps = mmap(NULL, sizeof(report) * NCASES, PROT_READ | PROT_WRITE,
                      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  char reaction[NCASES][256];
  const char *dir = "out/api_misuse";
  char cmd[64];

  snprintf(cmd, sizeof(cmd), "mkdir -p %s", dir);
  if (system(cmd) != 0) return 2;
#ifdef NDEBUG
  printf("library: asserts compiled out (-DNDEBUG)\n\n");
#else
  printf("library: asserts live (the standard build)\n\n");
#endif

  for (i = 0; i < NCASES; ++i) {
    char errpath[128];
    pid_t pid;
    int status = 0;
    snprintf(errpath, sizeof(errpath), "%s/case%02zu.err", dir, i);
    printf("=== %s\n", CASES[i].name);
    fflush(stdout);
    pid = fork();
    if (pid == 0) {
      app a;
      if (!freopen(errpath, "w", stderr)) _exit(2);
      g_rep = &reps[i];
      model_init();
      if (app_start(&a, CASES[i].server) != 0) _exit(2);
      CASES[i].run(&a);
      g_rep->finished = 1;
      fflush(stdout);
      _exit(0);
    }
    waitpid(pid, &status, 0);
    lib_reaction(errpath, status, reaction[i], sizeof(reaction[i]));
    printf("  LIBRARY  %s\n\n", reaction[i]);
  }

  printf("%-52s %-10s %s\n", "case", "monitor", "library");
  for (i = 0; i < NCASES; ++i) {
    const char *v;
    if (CASES[i].expect == 0)
      v = reps[i].flagged == 0 ? "CLEAN" : "FALSE+";
    else
      v = (reps[i].flagged & CASES[i].expect) ? "DETECTED" : "MISSED";
    if (v[0] == 'F' || v[0] == 'M') bad = 1;
    if (reps[i].post_mismatches) bad = 1;
    printf("%-52s %-10s %s%s\n", CASES[i].name, v, reaction[i],
           reps[i].post_mismatches ? "  [POST mismatch]" : "");
  }
  return bad;
}
