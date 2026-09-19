# The application's contract with ngtcp2 — trial on four functions

Date: 2026-09-18.  ngtcp2 `v1.25.0-92-g3c23148e`.
`h:N` is `lib/includes/ngtcp2/ngtcp2.h` line N, `c:N` is `lib/ngtcp2_conn.c`
line N, `pg:N` is `doc/source/programmers-guide.rst` line N.

The goal is to **detect misuse of the ngtcp2 API by an application**, not to
see how ngtcp2 behaves under it.  That needs a contract, and the contract has
two sources that do not always agree:

* the **implementation's assumptions** — asserts, and things it relies on with
  no check at all.  Primary: this is what this version actually needs;
* the **header's prose** — what the maintainers promise across versions.

A clause is in the contract if *either* source needs it, and carries where it
came from and what the code does when it is broken.  The contract is
`QuicModel/Api/Usage.lean` (typestate, preconditions `check`, postconditions
`post`, five theorems); `QuicModel/Api/Exports.lean` is its C interface;
`harness/api_misuse.c` is an application that breaks each clause on purpose
with the monitor beside it.

Trial scope: `ngtcp2_conn_read_pkt`, `ngtcp2_conn_writev_stream`,
`ngtcp2_conn_handle_expiry`, `ngtcp2_conn_extend_max_stream_offset`.

## 1. A fact about the asserts

ngtcp2 has 293 `assert`s in `ngtcp2_conn.c` and its `CMakeLists.txt:102`
**strips `-DNDEBUG` from Release flags on purpose** ("Do not disable assertions
based on CMAKE_BUILD_TYPE").  So in a standard build an assert-backed
precondition is enforced — by aborting the process.  Only an embedder who
defines `NDEBUG` themselves loses the check.  Both builds are tested below
(`build-c/`, and `build-c-ndebug/` via `EXTRA_CFLAGS=-DNDEBUG ./build_ngtcp2.sh`).

## 2. Typestate

```
            writev_stream -> WRITE_MORE
            (or STREAM_DATA_BLOCKED under FLAG_MORE)
   ready ------------------------------------------> pending(ctx)
     ^                                                  |  only writev_stream, with the
     |        writev_stream -> >= 0                     |  same path, pi, dest, destlen, ts
     +--------------------------------------------------+
     |
     |  any call -> CLOSING / DRAINING        any call -> IDLE_CLOSE, DROP_CONN, RETRY,
     v                                                    or any other negative code
   closed                                     terminal   (absorbing: nothing is legal)
```

plus two counters that cut across the phases: `lastTs` (largest timestamp so
far) and `cbDepth` (application callbacks on the stack).

`STREAM_NOT_FOUND`, `STREAM_SHUT_WR` and `INVALID_ARGUMENT` are returned by
`writev_stream` *before the packet is touched* (c:12177–12195), so they leave
whatever was pending still pending.  The header's "4 outcomes" paragraph
(h:5288–5322) does not say this; it follows from the code, and the harness
checks it against ngtcp2's own `NGTCP2_CONN_FLAG_PPE_PENDING` after every call.

## 3. Clauses

Enforcement: **error** = checked, error code returned; **assert** = `assert`
only; **none** = relied on with no check; **prose** = the header demands it and
the code does not need it.

| Clause | Applies to | Code | Header | Enforcement |
|---|---|---|---|---|
| `tsMonotonic` — `ts` never decreases | all three that take `ts` | c:88 `assert(conn->log.last_ts <= ts)` in `conn_update_timestamp` | **silent**; only pg:122 "any timestamp which increases monotonically" | assert |
| `noCallWhilePending` — nothing but `writev_stream` while a packet is pending | `read_pkt`, `handle_expiry` | c:10379, c:11432 `assert(!(conn->flags & NGTCP2_CONN_FLAG_PPE_PENDING))` | h:5324 "must not call other ngtcp2 API functions" — stated at `writev_stream`, not at the two functions that assert it | assert |
| `noCallWhilePendingUnguarded` — the same | `extend_max_stream_offset` | no check; it only moves `rx.unsent_max_offset` and may queue the stream (c:13136–13151) | forbidden by h:5324: not in the list of exceptions (h:5326–5329) | prose |
| `pendingSameArgs` — resume with the same `path`, `pi`, `dest`, `destlen`, `ts` | `writev_stream` | none.  `conn->pkt.ppe` keeps a pointer into the *first* `dest` (c:3557); on resume `dest`/`destlen` are ignored ("already adjusted in ppe", c:12494) | h:5304 "otherwise the behaviour is undefined" | none |
| `notInCallback` | `read_pkt`, `writev_stream` | none | h:4286, h:5348 "must not be called from inside the callback functions" | none |
| `pathNonNull` | `read_pkt` | dereferenced at c:10391 (`ngtcp2_path_eq`) | h:4282 "must not be NULL" | none |
| `destlenMin` — `destlen` ≥ 1200 | `writev_stream` | tolerant: returns 0 under `conn_min_pktlen` (c:3598), else writes what fits | h:5238 "It must be at least NGTCP2_MAX_UDP_PAYLOAD_SIZE" | prose |
| `notWhenClosed` — after CLOSING / DRAINING | `read_pkt`, `writev_stream` | returns the same error again (c:10455, c:12462) | h:4301–4308 "no further packet transmission is allowed" | error |
| `notAfterTerminal` — after IDLE_CLOSE / DROP_CONN / RETRY / any other negative code | all four | none | h:4741 "drop the connection", h:4295 "discard connection state", h:4313 only `write_connection_close` remains | none |

Assumptions looked at and **not** made clauses:

* `extend_max_stream_offset` by more than the application consumed — neither
  the code nor the header forbids it (it is only flow-control credit).
* `read_pkt` with `pktlen == 0` — returns 0 (c:10386); legal.
* the asserts at c:10417 / c:10448 (`conn->pktns.crypto.rx.ckm` after the
  handshake read) are reached through the TLS glue, not through these
  arguments: a key-installation clause, outside the four functions.

## 4. Where code and prose disagree

| Kind | Instances |
|---|---|
| Code assumes, header silent | `tsMonotonic` (documented only in the programmer's guide) |
| Documented, but not where the check is | `noCallWhilePending`: a reader of `handle_expiry`'s or `read_pkt`'s documentation never meets it; h:4746 even says the application "may call any number of additional `ngtcp2_conn_read_pkt` and `ngtcp2_conn_handle_expiry` before calling `ngtcp2_conn_writev_stream`" |
| Header stricter than code | `noCallWhilePendingUnguarded`, `destlenMin` |
| Header says "undefined", code is memory-unsafe | `pendingSameArgs` |

## 5. Results (`./build_api_misuse.sh && ./out/api_misuse_assert; ./out/api_misuse_ndebug`)

The monitor's verdict is printed *before* the call is made.

| Case | Monitor | Library, asserts live | Library, `-DNDEBUG` |
|---|---|---|---|
| C1 control: WRITE_MORE loop, read, timer | clean | ok | ok |
| C2 control: `extend` inside `recv_stream_data` | clean | ok | ok |
| M1 `read_pkt` while a packet is pending | detected | abort: assert c:10379 | **returns 0, silently** |
| M2 `handle_expiry` while a packet is pending | detected | abort: assert c:11432 | **returns 0, silently** |
| M3 resume in another buffer, first one freed | detected | **heap-use-after-free** (ASan) | **heap-use-after-free** (ASan) |
| M4 resume with another `ts` | detected | returns normally | returns normally |
| M5 timestamp goes backwards | detected | abort: assert c:88 | **returns 0, silently** |
| M6 `read_pkt` with `path == NULL` | detected | SEGV | SEGV |
| M7 `extend_max_stream_offset` while pending | detected | returns normally | returns normally |
| M8 `writev_stream` after IDLE_CLOSE | detected | returns ≥ 0 | returns ≥ 0 |
| M9 `read_pkt` from inside a callback | detected | returns 0 | returns 0 |
| M10 `destlen` 100 | detected | returns normally | returns normally |
| M11 `writev_stream` after DRAINING | detected | `NGTCP2_ERR_DRAINING` | `NGTCP2_ERR_DRAINING` |

11 of 11 misuses detected, 0 false positives on the two controls, and the
monitor's `pending` agreed with `NGTCP2_CONN_FLAG_PPE_PENDING` after every
call in every case (no `POST mismatch`).

What the table says about ngtcp2 itself: of the eleven, the library reports
**one** to the caller (M11).  Three abort the process in a standard build and
are invisible under `NDEBUG`.  M3 is memory-unsafe in both builds — it is what
an application does if its send queue recycles buffers between two calls of the
WRITE_MORE loop.  The remaining six return as if nothing had happened.

## 6. Limits

* Eleven hand-written cases show the monitor *can* see each clause, not that
  the clause list is complete.  Completeness is the assert inventory for the
  remaining functions plus an API-sequence fuzzer whose oracle is "the library
  aborted or ASan fired ⇒ the monitor had flagged it first".
* The connection is `conn_driver.h`'s: stub crypto, forced past the handshake
  by writing `conn->state`.  That setup is outside any contract; the monitor
  starts after it.  Key installation and the handshake calls need a driver that
  performs a real handshake.
* Pointer *lifetimes* are not tracked (the stream data that must stay intact
  until acknowledged, h:5276).  `pendingSameArgs` compares addresses, which
  catches M3 because the application passes a different buffer — it would not
  catch freeing and re-allocating the same address.
* No false-positive run against a real application yet.  ngtcp2's own
  `examples/` under the shim is the next check.
* Line numbers are for the revision above.
