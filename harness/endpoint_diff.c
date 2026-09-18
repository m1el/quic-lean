/*
 * endpoint_diff -- WP13 "DiffHarness".
 *
 * The same ngtcp2 connection as harness/conn_trace.c (same stub crypto, same
 * transport parameters, same script grammar, same trace text: the driver is
 * literally the same file, harness/conn_driver.h), with the Lean endpoint model
 * of QuicModel/Spec/Endpoint running beside it and every observable outcome
 * checked against what the spec permits.
 *
 * ===========================================================================
 * What is compared
 * ===========================================================================
 *
 * The model is not deterministic: `Endpoint.outcomes` is the *list* of every
 * outcome the text permits, and ngtcp2 shows us only a return code and a few
 * application callbacks.  So the harness keeps a *set* of candidate model
 * states (PLAN Sec. 4a; `Core.Component.trackSet`) and narrows it after every
 * step with `quic_endpoint_track_trace`.  A violation is the set becoming
 * empty: nothing the spec permits looks like what ngtcp2 just did.
 *
 *   receive   for every `recv` step the datagram bytes go to
 *             `quic_endpoint_recv_datagram` through `Event.datagram`, and the
 *             observation is (did read_pkt fail, with which QUIC error code,
 *             which CB lines did it print).
 *   clock     `time` steps drive `Event.timer`.
 *   app       `open`, `write`, `shutdown*` drive `Event.app`; their callbacks
 *             are *not* compared (see "What is not compared").
 *   send      every packet ngtcp2 writes is unprotected, parsed into
 *             `OutPacket`s and offered to `quic_endpoint_may_send_datagram`.
 *             A `false` from every candidate is "ngtcp2 sent what the spec
 *             forbids".  Then the frames are fed back as
 *             `LocalAction.sentFrameIn` / `sentPacket` / `sentDatagram`, which
 *             is the bookkeeping the components need (Sec. 13.2.1's discharge of
 *             the ACK obligation, Sec. 3.1's "sending the first STREAM frame",
 *             Sec. 17.2.2's first CRYPTO offset).
 *   liveness  at every TIME record `quic_endpoint_obligations` is evaluated.
 *             An obligation overdue in *every* candidate is "ngtcp2 failed to
 *             do what the spec requires".
 *
 * ===========================================================================
 * What is not compared, and why
 * ===========================================================================
 *
 * - Effects ngtcp2 does not surface.  `Effect.cbName` is `none` for them and
 *   `observedCbs` drops them before the comparison; the harness drops the
 *   mirror image -- ngtcp2 callbacks with no model effect -- in `map_cb`.
 * - Callbacks fired during a *send* step.  ngtcp2 asks for new connection IDs
 *   and rotates keys while writing; the model has no event for either
 *   (`LocalAction.issueCid` is a decision the harness would have to invent, and
 *   it would then be comparing its own invention).  Send steps therefore
 *   compare the packets, not the callbacks.
 * - `extend_stream` / `extend_conn` / `extend_streams`: ngtcp2's API is
 *   *relative* ("extend by n") and the model's event is the *absolute* limit a
 *   MAX_DATA / MAX_STREAM_DATA / MAX_STREAMS frame carries.  Driving the app
 *   event would need the harness to track ngtcp2's limits itself; instead the
 *   frame is picked up on the wire, where its value is visible, as
 *   `LocalAction.sentFrameIn`.
 * - An error whose `ngtcp2_ccerr` type is not `transport` (idle close, drop
 *   connection, version negotiation): there is no QUIC error code to compare,
 *   so the step is tracked loosely and counted as "not compared".
 * - On an error only the code is compared, never the callbacks that preceded
 *   it (PLAN Sec. 4a: ngtcp2 fires `stream_open` and then fails the same frame).
 *   `Obs.matchesSpec` also lets a generic code (PROTOCOL_VIOLATION,
 *   INTERNAL_ERROR) stand in for a specific one (Sec. 11, line 4434).
 *
 * ===========================================================================
 * After a mismatch
 * ===========================================================================
 *
 * The run does not stop.  The mismatch is reported once per distinct signature
 * (kind + step + error code + callback list + what the model offered), the
 * offending input is saved under $DIFF_OUT, and the candidate set is
 * *resynchronised*: it is rebuilt from the previous set by keeping every
 * permitted successor, so that the rest of the run still tests something.  A
 * summary of every distinct mismatch is printed at exit.  This is what makes
 * a ten-minute fuzz run produce a triage list rather than one crash.
 *
 * ===========================================================================
 * Usage
 * ===========================================================================
 *
 *   ./out/endpoint_diff --script harness/scripts/01-stream-in-order.txt
 *   ./out/endpoint_diff corpus/conn_trace -max_total_time=600
 *   DIFF_SHOW=1 ./out/endpoint_diff some_input     # print the trace as well
 *   DIFF_ACK_TOLERANCE=<us>                        # obligation slack, default 25000
 *   DIFF_MAX_CANDS=<n>                             # candidate cap, default 12
 */
#include "diff_common.h"

/* --------------------------------------------------- forward declarations */

typedef struct harness_s harness;

static void md_start(harness *h, int server);
static void md_mark(harness *h);
static void md_recv(harness *h, const uint8_t *pkt, size_t len, int rv);
static void md_time(harness *h, int rv);
static void md_open(harness *h, int uni, int rv, int64_t sid);
static void md_write(harness *h, int64_t sid, size_t n, int fin);
static void md_shutdown(harness *h, int which, int64_t sid, uint64_t err, int rv);
static void md_out(harness *h, const uint8_t *buf, size_t len);
static void md_tick(harness *h);
static void md_finish(harness *h);

#define MODEL_HOOKS
#define MH_START(h, server)                 md_start((h), (server))
#define MH_MARK(h)                          md_mark(h)
#define MH_RECV(h, pkt, len, rv)            md_recv((h), (pkt), (len), (rv))
#define MH_TIME(h, rv)                      md_time((h), (rv))
#define MH_OPEN(h, uni, rv, sid)            md_open((h), (uni), (rv), (sid))
#define MH_WRITE(h, sid, n, fin)            md_write((h), (sid), (n), (fin))
#define MH_SHUTDOWN(h, which, sid, err, rv) md_shutdown((h), (which), (sid), (err), (rv))
#define MH_OUT(h, buf, len)                 md_out((h), (buf), (len))
#define MH_TICK(h)                          md_tick(h)
#define MH_FINISH(h)                        md_finish(h)

#include "conn_driver.h"

/* ====================================================================== */
/* The Lean entry points                                                   */
/* ====================================================================== */

/* QuicModel/Spec/Endpoint/Exports.lean */
extern lean_object *quic_endpoint_init(uint8_t is_server, lean_object *local_cid,
                                       lean_object *peer_cid, uint64_t max_data,
                                       uint64_t max_stream_data,
                                       uint64_t max_streams_bidi,
                                       uint64_t max_streams_uni, uint64_t max_idle,
                                       uint64_t max_ack_delay, uint64_t cid_limit,
                                       uint64_t pto);
extern lean_object *quic_endpoint_recv_datagram(lean_object *s, uint64_t src,
                                                uint64_t dest, lean_object *buf,
                                                uint64_t now);
extern lean_object *quic_endpoint_app_event(lean_object *s, lean_object *a,
                                            uint64_t now);
extern lean_object *quic_endpoint_tls_event(lean_object *s, lean_object *e);
extern lean_object *quic_endpoint_tick(lean_object *s, uint64_t now);
extern lean_object *quic_endpoint_local_event(lean_object *s, lean_object *a,
                                              uint64_t now);
extern uint64_t quic_endpoint_outcome_error(lean_object *o);
extern uint8_t quic_endpoint_outcome_is_drop(lean_object *o);
extern lean_object *quic_endpoint_outcome_state(lean_object *s, lean_object *o);
extern lean_object *quic_endpoint_outcome_render(lean_object *o);
extern lean_object *quic_endpoint_outcome_cbs(lean_object *o);
extern lean_object *quic_endpoint_track_trace(lean_object *ss, lean_object *e,
                                              uint8_t is_error, uint64_t code,
                                              lean_object *cbs);
extern uint8_t quic_endpoint_may_send_datagram(lean_object *s, uint64_t src,
                                               uint64_t dest, uint64_t size,
                                               uint8_t is_pmtu_probe,
                                               uint8_t is_ecn_marked,
                                               lean_object *dcid, lean_object *scid,
                                               lean_object *packets);
extern uint8_t quic_endpoint_obligations(lean_object *s, uint64_t now,
                                         uint64_t tolerance);
extern lean_object *quic_endpoint_state_render(lean_object *s);
extern uint64_t quic_endpoint_repair_owed(lean_object *s);

/* QuicModel/Harness.lean */
extern lean_object *quic_h_ev_datagram(uint64_t src, uint64_t dest, lean_object *buf,
                                       uint64_t now);
extern lean_object *quic_h_ev_app(lean_object *a, uint64_t now);
extern lean_object *quic_h_ev_tls(lean_object *e);
extern lean_object *quic_h_ev_timer(uint64_t now);
extern lean_object *quic_h_ev_local(lean_object *a, uint64_t now);
extern lean_object *quic_h_tls_keys(uint8_t is_write, uint8_t level);
extern lean_object *quic_h_tls_complete(uint8_t dummy);
extern lean_object *quic_h_app_open_stream(uint8_t dir);
extern lean_object *quic_h_app_write(uint64_t id, uint64_t len);
extern lean_object *quic_h_app_fin(uint64_t id);
extern lean_object *quic_h_app_reset(uint64_t id, uint64_t code);
extern lean_object *quic_h_app_stop_sending(uint64_t id, uint64_t code);
extern lean_object *quic_h_local_sent_packet(uint8_t ptype, uint64_t pn, uint8_t ae);
extern lean_object *quic_h_local_sent_frame_in(uint8_t ptype, uint64_t src,
                                               uint64_t dest, lean_object *f);
extern lean_object *quic_h_local_sent_datagram(uint64_t dest, uint64_t n);
extern lean_object *quic_h_frames_of_bytes(lean_object *buf);
extern uint64_t quic_h_frames_length(lean_object *fs);
extern lean_object *quic_h_frames_get(lean_object *fs, uint64_t i);
extern lean_object *quic_h_out_packet(uint8_t ptype, lean_object *fs);
extern uint8_t quic_h_ack_eliciting(lean_object *fs);
extern lean_object *quic_h_frames_dump(lean_object *fs);
extern lean_object *quic_h_presend_actions(lean_object *fs);
extern lean_object *quic_h_advance_all(lean_object *ss, lean_object *e, uint8_t only_ok,
                                       uint64_t cap);
extern uint64_t quic_h_states_length(lean_object *ss);
extern uint64_t quic_h_frames_max_stream_index(lean_object *fs);
extern uint64_t quic_h_actions_length(lean_object *as);
extern lean_object *quic_h_actions_get(lean_object *as, uint64_t i);

/* ====================================================================== */
/* Lean list helpers                                                       */
/* ====================================================================== */

static lean_object *l_nil(void) { return lean_box(0); }

static lean_object *l_cons(lean_object *head, lean_object *tail) {
  lean_object *c = lean_alloc_ctor(1, 2, 0);
  lean_ctor_set(c, 0, head);
  lean_ctor_set(c, 1, tail);
  return c;
}

static int l_len(lean_object *l) {
  int n = 0;
  while (!lean_is_scalar(l)) {
    ++n;
    l = lean_ctor_get(l, 1);
  }
  return n;
}

static lean_object *l_head(lean_object *l) { return lean_ctor_get(l, 0); }
static lean_object *l_tail(lean_object *l) { return lean_ctor_get(l, 1); }

/* A fresh list holding (references to) the first |max| elements of |l|; |l| is
   consumed.  The candidate set is capped so that a pathological branch cannot
   make the run quadratic; the cap keeps the *preferred* outcomes, which are
   `outcomes`' head, so a cap can only ever cost a later match, never invent
   one. */
static lean_object *l_take(lean_object *l, int max) {
  lean_object *out = l_nil(), **tailp = &out;
  lean_object *p = l;
  int n = 0;
  if (l_len(l) <= max) return l;
  while (!lean_is_scalar(p) && n < max) {
    lean_object *c = lean_alloc_ctor(1, 2, 0);
    lean_object *hd = l_head(p);
    lean_inc(hd);
    lean_ctor_set(c, 0, hd);
    lean_ctor_set(c, 1, l_nil());
    *tailp = c;
    tailp = (lean_object **)lean_ctor_obj_cptr(c) + 1;
    p = l_tail(p);
    ++n;
  }
  lean_dec(l);
  return out;
}

/* ====================================================================== */
/* Configuration: the connection conn_trace.c sets up                      */
/* ====================================================================== */

/* conn_trace.c's fill_params(), as harnessConfig's arguments. */
#define CFG_MAX_DATA          4096
#define CFG_MAX_STREAM_DATA   1024
#define CFG_MAX_STREAMS_BIDI  4
#define CFG_MAX_STREAMS_UNI   2
#define CFG_MAX_IDLE          (30ULL * 1000000ULL)  /* 30 s, in us */
#define CFG_MAX_ACK_DELAY     25000ULL              /* 25 ms, in us */
#define CFG_CID_LIMIT         4
#define CFG_PTO               100000ULL             /* initial_rtt = 100 ms   */

/* harnessConfig fixes localAddr = 0 and peerAddr = 1. */
#define ADDR_SELF 0
#define ADDR_PEER 1

/* Endpoint.PacketType, as QuicModel/Harness.lean numbers it. */
enum { PT_INITIAL = 0, PT_0RTT = 1, PT_HANDSHAKE = 2, PT_1RTT = 3 };

/* ====================================================================== */
/* Mismatch bookkeeping                                                    */
/* ====================================================================== */

#define MAX_MISMATCH_KINDS 512

typedef struct {
  uint64_t sig;
  unsigned long count;
} mm_entry;

static mm_entry g_mm[MAX_MISMATCH_KINDS];
static int g_summary_done;
static int g_nmm;
static unsigned long g_mm_total;
static unsigned long g_steps_compared, g_steps_skipped, g_send_checks;
static unsigned long g_steps_loose;
static unsigned long g_runs;
static const uint8_t *g_input;
static size_t g_inputlen;
static int g_summary_registered;

static uint64_t fnv(const char *s) {
  uint64_t v = 1469598103934665603ULL;
  while (*s) v = (v ^ (uint8_t)*s++) * 1099511628211ULL;
  return v;
}

static void mm_summary(void) {
  int i;
  if (g_summary_done) return;
  g_summary_done = 1;
  fprintf(stderr,
          "\n=== endpoint_diff summary ===\n"
          "runs=%lu  steps compared=%lu (%lu only after excluding "
          "stream_close/acked_stream_data_offset)  steps not compared=%lu  "
          "send checks=%lu\n"
          "distinct mismatches=%d  total mismatches=%lu\n",
          g_runs, g_steps_compared, g_steps_loose, g_steps_skipped, g_send_checks,
          g_nmm, g_mm_total);
  for (i = 0; i < g_nmm; ++i)
    fprintf(stderr, "  sig=%016" PRIx64 " x%lu\n", g_mm[i].sig, g_mm[i].count);
}

/* Returns 1 the first time this signature is seen. */
static int mm_seen(uint64_t sig) {
  int i;
  ++g_mm_total;
  if (!g_summary_registered) {
    g_summary_registered = 1;
    atexit(mm_summary);
  }
  for (i = 0; i < g_nmm; ++i) {
    if (g_mm[i].sig == sig) {
      ++g_mm[i].count;
      return 0;
    }
  }
  if (g_nmm < MAX_MISMATCH_KINDS) {
    g_mm[g_nmm].sig = sig;
    g_mm[g_nmm].count = 1;
    ++g_nmm;
  }
  return 1;
}

/* ====================================================================== */
/* The model state carried beside the connection                           */
/* ====================================================================== */

typedef struct {
  lean_object *cands; /* List Endpoint.State, owned */
  int server;
  int alive;
  uint64_t tolerance;
  int max_cands;
  uint64_t max_stream_index;
  int64_t out_max_pn[3];
} mstate;

static int g_model_ready;

static void model_ready(void) {
  if (!g_model_ready) {
    model_init();
    g_model_ready = 1;
  }
}

static mstate *M(harness *h) { return (mstate *)h->model; }

/* ====================================================================== */
/* Events, as a description the harness can both build and enumerate       */
/* ====================================================================== */

enum { EV_DATAGRAM, EV_APP, EV_TLS, EV_TIMER, EV_LOCAL };

typedef struct {
  int kind;
  lean_object *arg; /* ByteArray | AppAction | TlsEvent | LocalAction, owned by
                       the caller for the whole lifetime of the evspec */
  uint64_t now;
  const char *name; /* for reports */
} evspec;

static lean_object *ev_build(const evspec *e) {
  switch (e->kind) {
  case EV_DATAGRAM:
    lean_inc(e->arg);
    return quic_h_ev_datagram(ADDR_PEER, ADDR_SELF, e->arg, e->now);
  case EV_APP:
    lean_inc(e->arg);
    return quic_h_ev_app(e->arg, e->now);
  case EV_TLS:
    lean_inc(e->arg);
    return quic_h_ev_tls(e->arg);
  case EV_TIMER:
    return quic_h_ev_timer(e->now);
  default:
    lean_inc(e->arg);
    return quic_h_ev_local(e->arg, e->now);
  }
}

/* Every outcome the spec permits for |s| (borrowed) under |e|.  Owned result. */
static lean_object *ev_outcomes(const evspec *e, lean_object *s) {
  lean_inc(s);
  switch (e->kind) {
  case EV_DATAGRAM:
    lean_inc(e->arg);
    return quic_endpoint_recv_datagram(s, ADDR_PEER, ADDR_SELF, e->arg, e->now);
  case EV_APP:
    lean_inc(e->arg);
    return quic_endpoint_app_event(s, e->arg, e->now);
  case EV_TLS:
    lean_inc(e->arg);
    return quic_endpoint_tls_event(s, e->arg);
  case EV_TIMER:
    return quic_endpoint_tick(s, e->now);
  default:
    lean_inc(e->arg);
    return quic_endpoint_local_event(s, e->arg, e->now);
  }
}

/* ====================================================================== */
/* ngtcp2 callback names -> the model's effect names                       */
/* ====================================================================== */

/* The range of `Effect.cbName` (Exports.lean) is twenty-one names.  ngtcp2
   prints a few of them under a versioned name (`..._2`) and prints a dozen more
   for which the model has no effect at all; those are dropped, exactly as
   `observedCbs` drops the effects ngtcp2 does not surface.  The pair of
   filters is the mapping table of endpoint_diff.md. */
static const char *map_cb(const char *name) {
  /* same name on both sides */
  static const char *keep[] = {
      "recv_stream_data", "acked_stream_data_offset", "stream_open",
      "stream_close",     "stream_reset",             "recv_stop_sending",
      "extend_max_stream_data", "extend_max_data",
      "extend_max_local_streams_bidi", "extend_max_local_streams_uni",
      "handshake_completed", "handshake_confirmed", "recv_crypto_data",
      "recv_new_token", "recv_retry", "path_validation", "dcid_status",
      "remove_connection_id", "recv_version_negotiation", "version_negotiation",
      NULL};
  size_t i;
  for (i = 0; keep[i]; ++i)
    if (strcmp(name, keep[i]) == 0) return keep[i];
  /* ngtcp2's versioned callbacks are the same model effect */
  if (strcmp(name, "stream_close2") == 0) return "stream_close";
  if (strcmp(name, "dcid_status2") == 0) return "dcid_status";
  /* everything else: no model effect (update_key, recv_rx_key, recv_tx_key,
     tls_early_data_rejected, client_initial, recv_client_initial,
     recv_datagram, ack_datagram, lost_datagram, begin_path_validation,
     get_path_challenge_data[2], select_preferred_addr, recv_stateless_reset[2],
     stream_stop_sending, extend_max_remote_streams_*) */
  return NULL;
}

/* Collects the mapped CB names printed since h->cb_mark, in order, into a Lean
   List String (owned) and, for the report, into |text| (which must already be
   an initialised sbuf, or NULL). */
static lean_object *collect_cbs(harness *h, sbuf *text) {
  lean_object *out = l_nil(), **tailp = &out;
  const char *p = h->tr.p + h->cb_mark;
  const char *end = h->tr.p + h->tr.len;
  int first = 1;

  while (p < end) {
    const char *eol = strchr(p, '\n');
    if (!eol || eol > end) eol = end;
    if ((size_t)(eol - p) > 4 && strncmp(p, "CB  ", 4) == 0) {
      char name[64];
      const char *b = p + 4, *e = b;
      const char *mapped;
      while (e < eol && *e != ' ' && *e != '\n') ++e;
      if ((size_t)(e - b) < sizeof(name)) {
        memcpy(name, b, (size_t)(e - b));
        name[e - b] = 0;
        mapped = map_cb(name);
        if (mapped) {
          lean_object *c = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(c, 0, lean_mk_string(mapped));
          lean_ctor_set(c, 1, l_nil());
          *tailp = c;
          tailp = (lean_object **)lean_ctor_obj_cptr(c) + 1;
          if (text) {
            sb_printf(text, "%s%s", first ? "" : ", ", mapped);
            first = 0;
          }
        }
      }
    }
    p = eol + 1;
  }
  return out;
}

/* ====================================================================== */
/* Reporting                                                               */
/* ====================================================================== */

/* Prints, for every candidate state, the state and every outcome the spec
   permits for |e|.  Both are what Exports.lean renders. */
static void report_candidates(sbuf *sb, mstate *m, const evspec *e) {
  lean_object *p = m->cands;
  int i = 0;
  while (!lean_is_scalar(p) && i < 8) {
    lean_object *s = l_head(p);
    lean_object *r, *os, *q;
    lean_inc(s);
    r = quic_endpoint_state_render(s);
    sb_printf(sb, "  candidate %d: ", i);
    sb_puts(sb, lean_string_cstr(r));
    sb_puts(sb, "\n");
    lean_dec(r);
    if (e) {
      os = ev_outcomes(e, s);
      q = os;
      while (!lean_is_scalar(q)) {
        lean_object *o = l_head(q);
        lean_inc(o);
        r = quic_endpoint_outcome_render(o);
        sb_puts(sb, "      permits ");
        sb_puts(sb, lean_string_cstr(r));
        sb_puts(sb, "\n");
        lean_dec(r);
        q = l_tail(q);
      }
      lean_dec(os);
    }
    p = l_tail(p);
    ++i;
  }
  if (!lean_is_scalar(p)) sb_printf(sb, "  ... (%d more)\n", l_len(p));
}

/* One mismatch: dedup, print once, save the input. */
static void report(harness *h, mstate *m, const char *kind, const char *sigkey,
                   const char *detail, const evspec *e) {
  char key[1024];
  sbuf sb = {0};
  uint64_t sig;

  snprintf(key, sizeof(key), "%s|%s", kind, sigkey);
  sig = fnv(key);
  if (!mm_seen(sig)) return;

  sb_reserve(&sb, 256);
  sb.p[0] = 0;
  sb_printf(&sb, "\n=== MISMATCH %s (sig %016" PRIx64 ") ===\n", kind, sig);
  sb_puts(&sb, "observed: ");
  sb_puts(&sb, detail);
  sb_puts(&sb, "\n");
  if (m) {
    sb_printf(&sb, "model candidates: %d\n", l_len(m->cands));
    report_candidates(&sb, m, e);
  }
  sb_puts(&sb, "--- ngtcp2 trace so far ---\n");
  sb_puts(&sb, h->tr.p);
  fputs(sb.p, stderr);
  free(sb.p);

  if (g_input) save_input("endpoint", g_input, g_inputlen);
}

/* ====================================================================== */
/* Driving the model                                                       */
/* ====================================================================== */

/* Every permitted successor of every candidate, as the resynchronisation after
   a mismatch and as the way a synthesised event (one ngtcp2 never reports) is
   applied.  `quic_h_advance_all` is `trackSet` with a pattern that accepts
   everything, so duplicate states collapse -- which matters: without it the
   candidate set doubles at every branch and the run exhausts memory.
   |only_ok| drops the outcomes that are connection errors. */
static lean_object *advance_all(mstate *m, const evspec *e, int only_ok) {
  lean_inc(m->cands);
  return quic_h_advance_all(m->cands, ev_build(e), (uint8_t)(only_ok != 0),
                            (uint64_t)m->max_cands);
}

static void set_cands(mstate *m, lean_object *next) {
  lean_dec(m->cands);
  m->cands = next;
}

/* ------------------------------------------------ the loose second chance */

/* Callback names the two sides *have* and that name the same transport state,
   but at different moments of the trace, so a per-step comparison of the lists
   is meaningless.  Both entries have a TRIAGE.md number and neither hides an
   error code or a frame:
     stream_close              TRIAGE WP13-1 (the model's Stream.Recv
                               allDataReceived is the receive half reaching Data
                               Recvd; ngtcp2 waits for both halves)
     acked_stream_data_offset  TRIAGE WP13-6 (nothing in Endpoint routes a
                               received ACK to StreamTable, so the model can
                               never produce Stream.Send.allDataAcked) */
static int cb_excluded(const char *n) {
  return strcmp(n, "stream_close") == 0 ||
         strcmp(n, "acked_stream_data_offset") == 0;
}

/* The observed names, filtered; returns how many were kept (at most |cap|). */
static int observed_names(harness *h, const char **out, int cap) {
  const char *p = h->tr.p + h->cb_mark, *end = h->tr.p + h->tr.len;
  int n = 0;
  static char pool[64][64];
  while (p < end && n < cap) {
    const char *eol = strchr(p, '\n');
    if (!eol || eol > end) eol = end;
    if ((size_t)(eol - p) > 4 && strncmp(p, "CB  ", 4) == 0) {
      char name[64];
      const char *b = p + 4, *q = b, *mapped;
      while (q < eol && *q != ' ' && *q != '\n') ++q;
      if ((size_t)(q - b) < sizeof(name)) {
        memcpy(name, b, (size_t)(q - b));
        name[q - b] = 0;
        mapped = map_cb(name);
        if (mapped && !cb_excluded(mapped) && n < 64) {
          snprintf(pool[n], sizeof(pool[n]), "%s", mapped);
          out[n] = pool[n];
          ++n;
        }
      }
    }
    p = eol + 1;
  }
  return n;
}

/* `Obs.matchesSpec`, re-stated in C so that the excluded names can be dropped
   from *both* sides.  Returns 1 when the outcome |o| looks like what ngtcp2
   did. */
static int outcome_matches(lean_object *o, int is_error, uint64_t code,
                           const char **names, int nnames) {
  uint64_t err;
  uint8_t isdrop;
  lean_inc(o);
  err = quic_endpoint_outcome_error(o);
  if (is_error) {
    /* §11, line 4434: a generic code may stand in for a specific one. */
    return err != 0xffffffffULL && (err == code || code == 0xa || code == 0x1);
  }
  if (err != 0xffffffffULL) return 0;
  lean_inc(o);
  isdrop = quic_endpoint_outcome_is_drop(o);
  if (isdrop) return nnames == 0;
  {
    lean_object *cbs;
    int i = 0;
    lean_inc(o);
    cbs = quic_endpoint_outcome_cbs(o);
    {
      lean_object *q = cbs;
      while (!lean_is_scalar(q)) {
        const char *nm = lean_string_cstr(l_head(q));
        if (!cb_excluded(nm)) {
          if (i >= nnames || strcmp(nm, names[i]) != 0) {
            lean_dec(cbs);
            return 0;
          }
          ++i;
        }
        q = l_tail(q);
      }
    }
    lean_dec(cbs);
    return i == nnames;
  }
}

/* The candidates that survive the loose comparison.  Owned result, possibly
   the empty list. */
static lean_object *track_loose(harness *h, mstate *m, const evspec *e,
                                int is_error, uint64_t code) {
  const char *names[64];
  int nnames = observed_names(h, names, 64);
  lean_object *out = l_nil(), **tailp = &out;
  lean_object *p = m->cands;
  int kept = 0;

  while (!lean_is_scalar(p)) {
    lean_object *s = l_head(p);
    lean_object *os = ev_outcomes(e, s), *q = os;
    while (!lean_is_scalar(q)) {
      lean_object *o = l_head(q);
      if (kept < m->max_cands && outcome_matches(o, is_error, code, names, nnames)) {
        lean_object *c;
        lean_inc(s);
        lean_inc(o);
        c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, quic_endpoint_outcome_state(s, o));
        lean_ctor_set(c, 1, l_nil());
        *tailp = c;
        tailp = (lean_object **)lean_ctor_obj_cptr(c) + 1;
        ++kept;
      }
      q = l_tail(q);
    }
    lean_dec(os);
    p = l_tail(p);
  }
  return out;
}

/* A step ngtcp2 reported on: narrow the candidate set with the model's own
   `trackSet` + `Obs.matchesSpec` (Exports.lean's `quic_endpoint_track_trace`).
   |is_error| < 0 means "the error is not a QUIC transport error", which is not
   comparable; the step is then only advanced. */
static void track_step(harness *h, const evspec *e, int is_error, uint64_t code,
                       lean_object *cbs, const char *cbtext, const char *what) {
  mstate *m = M(h);
  lean_object *next;
  char detail[768], sigkey[512];

  if (!m || !m->alive) {
    if (cbs) lean_dec(cbs);
    return;
  }

  if (is_error < 0) {
    ++g_steps_skipped;
    if (cbs) lean_dec(cbs);
    set_cands(m, advance_all(m, e, 0));
    return;
  }

  ++g_steps_compared;
  lean_inc(m->cands);
  next = quic_endpoint_track_trace(m->cands, ev_build(e), (uint8_t)is_error, code,
                                   cbs ? cbs : l_nil());
  if (!lean_is_scalar(next)) {
    set_cands(m, l_take(next, m->max_cands));
    return;
  }
  lean_dec(next);

  /* Second chance: the same comparison with the two callbacks that name the
     same transport state at a different moment of the trace removed from both
     sides (TRIAGE WP13-1, WP13-6). */
  next = track_loose(h, m, e, is_error, code);
  if (!lean_is_scalar(next)) {
    ++g_steps_loose;
    set_cands(m, next);
    return;
  }
  lean_dec(next);

  /* The candidate set is empty: nothing the spec permits looks like this. */
  if (is_error) {
    snprintf(detail, sizeof(detail), "%s -> ERR code=%" PRIu64 " [%s]", what, code,
             cbtext);
    snprintf(sigkey, sizeof(sigkey), "%s|ERR=%" PRIu64, e->name, code);
  } else {
    snprintf(detail, sizeof(detail), "%s -> OK cbs=[%s]", what, cbtext);
    snprintf(sigkey, sizeof(sigkey), "%s|OK|%.300s", e->name, cbtext);
  }

  report(h, m, "outcome", sigkey, detail, e);
  /* resynchronise so the rest of the run still tests something */
  set_cands(m, advance_all(m, e, 0));
}

/* A step ngtcp2 does not report on (a synthesised event).  Keep every non-error
   successor; if the spec permits nothing but errors, that is itself a finding:
   the model refuses something ngtcp2 just did. */
static void synth_step(harness *h, const evspec *e) {
  mstate *m = M(h);
  lean_object *next;
  char detail[512];

  if (!m || !m->alive) return;
  next = advance_all(m, e, 1);
  if (lean_is_scalar(next)) {
    lean_dec(next);
    snprintf(detail, sizeof(detail), "synthesised %s is a connection error in the model",
             e->name ? e->name : "?");
    report(h, m, "synth", e->name ? e->name : "?", detail, e);
    set_cands(m, advance_all(m, e, 0)); /* keep going with the error states */
    return;
  }
  set_cands(m, next);
}

/* ====================================================================== */
/* Hooks                                                                   */
/* ====================================================================== */

static void md_mark(harness *h) { h->cb_mark = h->tr.len; }

static void tls_prime(harness *h, uint8_t is_write, uint8_t level) {
  evspec e;
  e.kind = EV_TLS;
  e.arg = quic_h_tls_keys(is_write, level);
  e.now = 0;
  e.name = "tlsKeys";
  synth_step(h, &e);
  lean_dec(e.arg);
}

static void md_start(harness *h, int server) {
  mstate *m;
  lean_object *s0;
  const char *env;
  evspec e;

  model_ready();
  if (h->model) md_finish(h);

  m = calloc(1, sizeof(*m));
  if (!m) abort();
  m->server = server;
  m->alive = 1;
  m->tolerance = CFG_MAX_ACK_DELAY;
  m->max_cands = 12;
  m->max_stream_index = 1u << 14;
  m->out_max_pn[0] = m->out_max_pn[1] = m->out_max_pn[2] = -1;
  env = getenv("DIFF_ACK_TOLERANCE");
  if (env) m->tolerance = strtoull(env, NULL, 10);
  env = getenv("DIFF_MAX_STREAM_INDEX");
  if (env) m->max_stream_index = strtoull(env, NULL, 10);
  env = getenv("DIFF_MAX_CANDS");
  if (env) {
    m->max_cands = atoi(env);
    if (m->max_cands < 1) m->max_cands = 1;
  }

  s0 = quic_endpoint_init((uint8_t)(server != 0), model_bytes(g_cid_local, CIDLEN),
                          model_bytes(g_cid_remote, CIDLEN), CFG_MAX_DATA,
                          CFG_MAX_STREAM_DATA, CFG_MAX_STREAMS_BIDI,
                          CFG_MAX_STREAMS_UNI, CFG_MAX_IDLE, CFG_MAX_ACK_DELAY,
                          CFG_CID_LIMIT, CFG_PTO);
  m->cands = l_cons(s0, l_nil());
  h->model = m;
  ++g_runs;

  /* conn_trace.c installs the Handshake and 1-RTT keys by hand and forces
     NGTCP2_CS_POST_HANDSHAKE; the model gets there through WP11's own events,
     which is what `CB recv_rx_key` / `recv_tx_key` record in every expected
     trace.  Handshake.Level: 2 = handshake, 3 = 1-RTT. */
  tls_prime(h, 0, 2);
  tls_prime(h, 1, 2);
  tls_prime(h, 0, 3);
  tls_prime(h, 1, 3);
  e.kind = EV_TLS;
  e.arg = quic_h_tls_complete(0);
  e.now = 0;
  e.name = "tlsComplete";
  synth_step(h, &e);
  lean_dec(e.arg);

  /* §8.1, line 2757: "the successful use of Handshake packets indicates that
     ... the peer's address is validated".  conn_driver.h forces ngtcp2 into
     NGTCP2_CS_POST_HANDSHAKE and marks the path validated, which can only have
     happened by Handshake packets having been exchanged; the model has no
     event by which the harness could simply assert the fact, so the harness
     replays the packet instead: one Handshake packet carrying PADDING only.
     PADDING is not ack-eliciting (§13.2, line 5018), so this leaves no
     acknowledgment obligation behind, and the datagram's bytes count towards
     the anti-amplification budget exactly as the real one would have. */
  {
    static const uint8_t padding_frame[1] = {0x00};
    uint8_t pkt[PKTBUF];
    ngtcp2_ssize n = build_peer_pkt(1, 0, padding_frame, sizeof(padding_frame), pkt,
                                    sizeof(pkt));
    if (n > 0) {
      evspec d;
      d.kind = EV_DATAGRAM;
      d.arg = model_bytes(pkt, (size_t)n);
      d.now = 0;
      d.name = "handshake packet (synthesised)";
      synth_step(h, &d);
      lean_dec(d.arg);
    }
  }
}

static void md_finish(harness *h) {
  mstate *m = M(h);
  if (!m) return;
  lean_dec(m->cands);
  free(m);
  h->model = NULL;
}

/* The QUIC error code ngtcp2 would close with, the way conn_trace's tr_fatal
   derives it.  1 = a transport error with *code, 0 = no error, -1 = an error
   that is not a QUIC transport error (idle close, drop connection, ...). */
static int obs_error(int rv, uint64_t *code) {
  ngtcp2_ccerr ccerr;
  if (rv == 0) return 0;
  ngtcp2_ccerr_default(&ccerr);
  ngtcp2_ccerr_set_liberr(&ccerr, rv, NULL, 0);
  if (ccerr.type != NGTCP2_CCERR_TYPE_TRANSPORT) return -1;
  *code = ccerr.error_code;
  return 1;
}

static void md_recv(harness *h, const uint8_t *pkt, size_t len, int rv) {
  mstate *m = M(h);
  evspec e;
  uint64_t code = 0;
  int is_err;
  lean_object *cbs;
  char what[64];
  sbuf cbtext = {0};

  if (!m || !m->alive) return;

  /* `StreamTable.openedEffects` is linear in the stream index, so a frame that
     names stream 2^60 makes the executable `outcomes` unevaluable.  ngtcp2
     answers STREAM_LIMIT in constant time; the harness skips the comparison
     rather than the whole run.  g_build_plain is the plaintext conn_driver's
     builder encrypted, so this is the packet's own frame list. */
  {
    lean_object *fs = quic_h_frames_of_bytes(
        model_bytes(g_build_plain, g_build_plainlen));
    uint64_t idx;
    lean_inc(fs);
    idx = quic_h_frames_max_stream_index(fs);
    lean_dec(fs);
    if (idx > m->max_stream_index) {
      ++g_steps_skipped;
      return;
    }
  }

  is_err = obs_error(rv, &code);
  e.kind = EV_DATAGRAM;
  e.arg = model_bytes(pkt, len);
  e.now = h->ts;
  e.name = "recv";
  sb_reserve(&cbtext, 64);
  cbtext.p[0] = 0;
  cbs = collect_cbs(h, &cbtext);
  snprintf(what, sizeof(what), "read_pkt len=%zu", len);
  track_step(h, &e, is_err, code, cbs, cbtext.p, what);
  free(cbtext.p);
  lean_dec(e.arg);
}

static void md_time(harness *h, int rv) {
  mstate *m = M(h);
  evspec e;
  uint64_t code = 0;
  int is_err;
  lean_object *cbs;
  char what[64];
  sbuf cbtext = {0};

  if (!m || !m->alive) return;
  is_err = obs_error(rv, &code);
  e.kind = EV_TIMER;
  e.arg = NULL;
  e.now = h->ts;
  e.name = "timer";
  sb_reserve(&cbtext, 64);
  cbtext.p[0] = 0;
  cbs = collect_cbs(h, &cbtext);
  snprintf(what, sizeof(what), "handle_expiry now=%" PRIu64, (uint64_t)h->ts);
  track_step(h, &e, is_err, code, cbs, cbtext.p, what);
  free(cbtext.p);
}

/* An application event: ngtcp2 reports a return code but the callbacks it fires
   on the way belong to the send side, so only the "the model must permit this
   at all" half is checked. */
static void app_step(harness *h, lean_object *action, const char *name, int ok) {
  mstate *m = M(h);
  evspec e;
  char detail[256];

  if (!m || !m->alive) {
    lean_dec(action);
    return;
  }
  e.kind = EV_APP;
  e.arg = action;
  e.now = h->ts;
  e.name = name;

  if (ok) {
    /* ngtcp2 did it, so the spec must permit something other than a refusal. */
    lean_object *p = m->cands;
    int permits = 0;
    while (!lean_is_scalar(p) && !permits) {
      lean_object *os = ev_outcomes(&e, l_head(p)), *q = os;
      while (!lean_is_scalar(q)) {
        lean_object *o = l_head(q);
        uint64_t err;
        uint8_t isdrop;
        lean_inc(o);
        err = quic_endpoint_outcome_error(o);
        lean_inc(o);
        isdrop = quic_endpoint_outcome_is_drop(o);
        if (err == 0xffffffffULL && !isdrop) {
          permits = 1;
          break;
        }
        q = l_tail(q);
      }
      lean_dec(os);
      p = l_tail(p);
    }
    if (!permits) {
      snprintf(detail, sizeof(detail), "ngtcp2 performed %s; the model permits only drop/error",
               name);
      report(h, m, "app", name, detail, &e);
    }
  }
  synth_step(h, &e);
  lean_dec(action);
}

static void md_open(harness *h, int uni, int rv, int64_t sid) {
  (void)sid;
  if (rv != 0) return; /* ngtcp2 refused; the model's `.drop` agrees */
  app_step(h, quic_h_app_open_stream((uint8_t)(uni ? 1 : 0)), "openStream", 1);
}

static void md_write(harness *h, int64_t sid, size_t n, int fin) {
  if (sid < 0) return;
  app_step(h, quic_h_app_write((uint64_t)sid, n), "write", 0);
  if (fin) app_step(h, quic_h_app_fin((uint64_t)sid), "fin", 0);
}

static void md_shutdown(harness *h, int which, int64_t sid, uint64_t err, int rv) {
  if (rv != 0 || sid < 0) return;
  if (which != 0) app_step(h, quic_h_app_reset((uint64_t)sid, err), "reset", 1);
  if (which != 1) app_step(h, quic_h_app_stop_sending((uint64_t)sid, err), "stopSending", 1);
}

/* ---------------------------------------------------------- the send side */

/* One packet of a datagram ngtcp2 wrote, as the send-side rules see it. */
typedef struct {
  int ptype;           /* PT_* */
  int space;           /* 0 initial, 1 handshake, 2 app */
  int64_t pn;
  lean_object *frames; /* List Frame, owned */
  uint8_t dcid[NGTCP2_MAX_CIDLEN];
  size_t dcidlen;
  uint8_t scid[NGTCP2_MAX_CIDLEN];
  size_t scidlen;
} outpkt;

/* Unprotects the datagram with the stub crypto, exactly as conn_trace's
   dump_out_datagram does, and fills |ps| with up to |cap| packets.  Returns the
   number found, or -1 if the datagram does not parse. */
static int parse_out(mstate *m, const uint8_t *pkt, size_t pktlen, outpkt *ps,
                     int cap) {
  const uint8_t *p = pkt;
  size_t left = pktlen;
  int n = 0;

  while (left > 0 && n < cap) {
    ngtcp2_pkt_hd hd;
    ngtcp2_ssize hdlen;
    size_t pktend, pnoff, pnlen, i;
    const uint8_t *sample;
    uint8_t mask[NGTCP2_HP_MASKLEN], b0, pnbuf[4];
    int space, ptype;
    int64_t pn;

    if (p[0] & NGTCP2_HEADER_FORM_BIT) {
      hdlen = ngtcp2_pkt_decode_hd_long(&hd, p, left);
      if (hdlen < 0) return n ? n : -1;
      if (hd.type == NGTCP2_PKT_VERSION_NEGOTIATION || hd.type == NGTCP2_PKT_RETRY)
        return n; /* not a protected packet; no OutPacket rule applies */
      if (hd.len > left - (size_t)hdlen) return n ? n : -1;
      pktend = (size_t)hdlen + hd.len;
      space = hd.type == NGTCP2_PKT_INITIAL ? 0 : hd.type == NGTCP2_PKT_HANDSHAKE ? 1 : 2;
      ptype = hd.type == NGTCP2_PKT_INITIAL     ? PT_INITIAL
              : hd.type == NGTCP2_PKT_HANDSHAKE ? PT_HANDSHAKE
              : hd.type == NGTCP2_PKT_0RTT      ? PT_0RTT
                                                : PT_1RTT;
    } else {
      hdlen = ngtcp2_pkt_decode_hd_short(&hd, p, left, CIDLEN);
      if (hdlen < 0) return n ? n : -1;
      pktend = left;
      space = 2;
      ptype = PT_1RTT;
    }
    pnoff = (size_t)hdlen;
    if (pnoff + 4 + NGTCP2_HP_SAMPLELEN > pktend) return n ? n : -1;
    sample = p + pnoff + 4;
    memcpy(mask, sample, NGTCP2_HP_MASKLEN);
    b0 = (uint8_t)(p[0] ^ (mask[0] & (uint8_t)((p[0] & NGTCP2_HEADER_FORM_BIT) ? 0x0f
                                                                              : 0x1f)));
    pnlen = (size_t)(b0 & 0x03) + 1;
    for (i = 0; i < pnlen; ++i) pnbuf[i] = (uint8_t)(p[pnoff + i] ^ mask[1 + i]);
    {
      uint64_t v = 0;
      for (i = 0; i < pnlen; ++i) v = (v << 8) | pnbuf[i];
      pn = ngtcp2_pkt_adjust_pkt_num(m->out_max_pn[space], (int64_t)v, pnlen);
    }
    if (pn > m->out_max_pn[space]) m->out_max_pn[space] = pn;
    if (pktend < pnoff + pnlen + TAGLEN) return n ? n : -1;

    ps[n].ptype = ptype;
    ps[n].space = space;
    ps[n].pn = pn;
    ps[n].frames = quic_h_frames_of_bytes(
        model_bytes(p + pnoff + pnlen, pktend - pnoff - pnlen - TAGLEN));
    ps[n].dcidlen = hd.dcid.datalen <= NGTCP2_MAX_CIDLEN ? hd.dcid.datalen : 0;
    memcpy(ps[n].dcid, hd.dcid.data, ps[n].dcidlen);
    ps[n].scidlen = (p[0] & NGTCP2_HEADER_FORM_BIT) &&
                            hd.scid.datalen <= NGTCP2_MAX_CIDLEN
                        ? hd.scid.datalen
                        : 0;
    memcpy(ps[n].scid, hd.scid.data, ps[n].scidlen);
    ++n;

    p += pktend;
    left -= pktend;
  }
  return n;
}

static void md_out(harness *h, const uint8_t *buf, size_t len) {
  mstate *m = M(h);
  outpkt ps[8];
  int np, i, allowed = 0;
  lean_object *packets = l_nil();
  lean_object *p;

  if (!m || !m->alive) return;
  np = parse_out(m, buf, len, ps, 8);
  if (np <= 0) return;
  ++g_send_checks;

  /* Sec. 12.2: one datagram, so one dcid/scid; take the first packet's. */
  for (i = np - 1; i >= 0; --i) {
    lean_object *fs = ps[i].frames;
    lean_inc(fs);
    packets = l_cons(quic_h_out_packet((uint8_t)ps[i].ptype, fs), packets);
  }

  /* §5.1.1 / §5.1.2: ngtcp2 issues and retires connection IDs inside the
     writer, so the decision is only visible as the frame announcing it.  It has
     to reach `ConnIds` before the frame may be sent, or every NEW_CONNECTION_ID
     would look like one the endpoint never issued. */
  for (i = 0; i < np; ++i) {
    lean_object *acts;
    uint64_t na, k;
    lean_inc(ps[i].frames);
    acts = quic_h_presend_actions(ps[i].frames);
    lean_inc(acts);
    na = quic_h_actions_length(acts);
    for (k = 0; k < na; ++k) {
      evspec e;
      lean_inc(acts);
      e.kind = EV_LOCAL;
      e.arg = quic_h_actions_get(acts, k);
      e.now = h->ts;
      e.name = "issueCid/retireCid";
      synth_step(h, &e);
      lean_dec(e.arg);
    }
    lean_dec(acts);
  }

  p = m->cands;
  while (!lean_is_scalar(p)) {
    lean_object *s = l_head(p);
    lean_inc(s);
    lean_inc(packets);
    if (quic_endpoint_may_send_datagram(
            s, ADDR_SELF, ADDR_PEER, len, 0, 0,
            model_bytes(ps[0].dcid, ps[0].dcidlen),
            model_bytes(ps[0].scid, ps[0].scidlen), packets)) {
      allowed = 1;
      break;
    }
    p = l_tail(p);
  }
  lean_dec(packets);

  if (!allowed) {
    char detail[1024], sigkey[512];
    lean_object *d;
    const char *dump;
    size_t k = 0;
    lean_inc(ps[0].frames);
    d = quic_h_frames_dump(ps[0].frames);
    dump = lean_string_cstr(d);
    /* the signature is the frame *kinds*, so that a thousand STREAM frames
       differing only in offset are one entry in the triage list */
    {
      const char *q = dump;
      sigkey[0] = 0;
      while (*q && k + 32 < sizeof(sigkey)) {
        const char *w = q;
        while (*q && *q != ' ' && *q != ';') ++q;
        k += (size_t)snprintf(sigkey + k, sizeof(sigkey) - k, "%.*s,", (int)(q - w), w);
        while (*q && *q != ';') ++q;
        if (*q == ';') q += 2;
      }
    }
    snprintf(detail, sizeof(detail), "OUT len=%zu packets=%d first=[%.700s]", len, np,
             dump);
    lean_dec(d);
    report(h, m, "maysend", sigkey, detail, NULL);
  }

  /* The bookkeeping the components need once a frame really travelled. */
  for (i = 0; i < np; ++i) {
    uint64_t nfr = 0, k;
    evspec e;
    lean_inc(ps[i].frames);
    nfr = quic_h_frames_length(ps[i].frames);
    for (k = 0; k < nfr; ++k) {
      lean_object *f;
      lean_inc(ps[i].frames);
      f = quic_h_frames_get(ps[i].frames, k);
      e.kind = EV_LOCAL;
      e.arg = quic_h_local_sent_frame_in((uint8_t)ps[i].ptype, ADDR_SELF, ADDR_PEER, f);
      e.now = h->ts;
      e.name = "sentFrameIn";
      synth_step(h, &e);
      lean_dec(e.arg);
    }
    lean_inc(ps[i].frames);
    e.kind = EV_LOCAL;
    e.arg = quic_h_local_sent_packet((uint8_t)ps[i].ptype, (uint64_t)ps[i].pn,
                                     quic_h_ack_eliciting(ps[i].frames));
    e.now = h->ts;
    e.name = "sentPacket";
    synth_step(h, &e);
    lean_dec(e.arg);
  }
  {
    evspec e;
    e.kind = EV_LOCAL;
    e.arg = quic_h_local_sent_datagram(ADDR_PEER, len);
    e.now = h->ts;
    e.name = "sentDatagram";
    synth_step(h, &e);
    lean_dec(e.arg);
  }

  for (i = 0; i < np; ++i) lean_dec(ps[i].frames);
}

/* ------------------------------------------------------- the obligations */

static void md_tick(harness *h) {
  mstate *m = M(h);
  lean_object *p;
  int met = 0;

  if (!m || !m->alive) return;
  p = m->cands;
  while (!lean_is_scalar(p)) {
    lean_object *s = l_head(p);
    lean_inc(s);
    if (quic_endpoint_obligations(s, h->ts, m->tolerance)) {
      met = 1;
      break;
    }
    p = l_tail(p);
  }
  if (!met && !lean_is_scalar(m->cands)) {
    char detail[256];
    snprintf(detail, sizeof(detail),
             "acknowledgment overdue in every candidate at now=%" PRIu64
             " (tolerance %" PRIu64 ")",
             (uint64_t)h->ts, m->tolerance);
    report(h, m, "obligation", "ack overdue", detail, NULL);
    /* report once per run: otherwise every later TIME repeats it */
    m->tolerance = UINT64_MAX;
  }
}

/* ====================================================================== */
/* Entry points                                                            */
/* ====================================================================== */

int LLVMFuzzerInitialize(int *argc, char ***argv) {
  int i;
  model_ready();
  for (i = 1; i < *argc; ++i) {
    if (strcmp((*argv)[i], "--script") == 0) {
      int rc;
      if (i + 1 >= *argc) {
        fprintf(stderr, "endpoint_diff: --script needs a file\n");
        exit(2);
      }
      rc = run_script((*argv)[i + 1]);
      mm_summary();
      if (rc == 0 && g_nmm && getenv("DIFF_FAIL_ON_MISMATCH")) rc = 3;
      exit(rc);
    }
  }
  return 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  harness h;
  int server;

  if (size < 2) return 0;
  g_input = data;
  g_inputlen = size;
  server = !(data[0] & 1);
  harness_start(&h, server);
  if (setup_conn(&h, server) != 0) {
    md_finish(&h);
    free(h.tr.p);
    g_input = NULL;
    return 0;
  }
  tr_time(&h);
  run_binary(&h, data + 1, size - 1);
  harness_finish(&h, getenv("TRACE_SHOW") != NULL);
  g_input = NULL;
  return 0;
}
