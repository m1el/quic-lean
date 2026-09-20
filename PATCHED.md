# Patches for the implementation findings

Date: 2026-09-19.  One branch per finding of [DIFFERENCES.md](DIFFERENCES.md)
section A, each a single commit on top of the upstream default branch, each
with a regression test.  The branches are checked out as worktrees under
`../patches-wt/`; the `../ngtcp2` and `../quiche` checkouts are untouched
(`../quiche` stays on `fuzz-mock-clock`).  Nothing is pushed and no pull request
is open.

| Finding | Repository | Branch | Commit | Base | Worktree | Change |
|---|---|---|---|---|---|---|
| A1 | quiche | `fix/pad-path-response` | `776fcca3` | `master` `1c8e9761` | `../patches-wt/quiche-pad-path-response` | A 1-RTT packet carrying PATH_RESPONSE or PATH_CHALLENGE on a validated path is padded up to 1200 bytes (§8.2.1 line 3154, §8.2.2 line 3197) — to 1200, not to the whole remaining budget.  The unvalidated-path and coalesced-Initial cases are unchanged |
| A6 | quiche | `fix/stream-data-blocked-checks` | `b3e94a0a` | `master` `1c8e9761` | `../patches-wt/quiche-sdb` | STREAM_DATA_BLOCKED is handled like MAX_STREAM_DATA: refused on one of our own unidirectional streams (STREAM_STATE_ERROR, §19.13), and passed through `get_or_create_stream` so the stream limit is enforced (STREAM_LIMIT_ERROR, §4.6 line 1546).  A frame for an already collected stream is still ignored |
| A2 | ngtcp2 | `fix/ncid-retire-prior-to-check` | `4c7d96b0` | `main` `3c23148e` | `../patches-wt/ngtcp2-ncid` | In `conn_recv_new_connection_id`, Retire Prior To > Sequence Number (FRAME_ENCODING_ERROR, §19.15 line 7993) is checked before the early return for a repeated sequence number |
| A3 | ngtcp2 | `fix/coalesced-pkt-after-discard` | `bcab5e5a` | `main` `3c23148e` | `../patches-wt/ngtcp2-cpkt` | `conn_recv_cpkt` skips a discarded long-header packet by its Length field and goes on with the rest of the datagram (§12.2 line 4619).  A short-header packet, or a long-header packet that cannot be delimited, still ends the datagram; the stateless-reset check is unchanged; the handshake path (`conn_recv_handshake_cpkt`) is left as it is |
| A5 | ngtcp2 | `fix/adjust-pkt-num-no-assert` | `ecd9732a` | `main` `3c23148e` | `../patches-wt/ngtcp2-pktnum` | The assert in `ngtcp2_pkt_adjust_pkt_num` becomes the guard of RFC 9000 Appendix A.3; callers already discard a result above `NGTCP2_MAX_PKT_NUM` |

A4 (FINAL_SIZE_ERROR for a STREAM_DATA_BLOCKED past the final size) has no
patch: its conformance is unresolved.

## Regression tests

| Finding | Test | Fails without the fix |
|---|---|---|
| A1 | `tests::path_challenge` (extended): the datagram carrying the PATH_RESPONSE is exactly 1200 bytes and ends in PADDING | not checked separately |
| A6 | `tests::stream_data_blocked_send_uni`, `tests::stream_data_blocked_stream_limit` | not checked separately |
| A2 | `test_ngtcp2_conn_recv_new_connection_id`, new last case: sequence 1 accepted, then sequence 1 again with Retire Prior To 2 | yes (`-217 == 0`) |
| A3 | `test_ngtcp2_conn_recv_compound_pkt`, new last case: a Handshake packet that fails decryption (`fail_once_decrypt`) in front of a 1-RTT packet.  This is the first reproduction of A3 — the harness's stub AEAD cannot fail | yes (`pkt_recv` stays 0) |
| A5 | `test_ngtcp2_pkt_adjust_pkt_num`: `(NGTCP2_MAX_PKT_NUM - 1, 0x00, 1)` gives `0x3FFFFFFFFFFFFF00` | yes (the assert aborts) |

Suites: ngtcp2 `tests/main` 266/266 on each of its three branches; quiche
`cargo test --lib` all passing on both (1140 and 1144 tests).  `cargo fmt
--check` reports two comment-wrapping diffs that are already on `master`, none
in the patched lines.  Building ngtcp2's unit tests needs
`git submodule update --init tests/munit` (done in `ngtcp2-ncid`; the other two
worktrees have an untracked copy of the sources).

## End-to-end check

Harness binaries were linked against all five patches at once, in throwaway
trees (ngtcp2 `main` plus its three commits; quiche `fuzz-mock-clock` plus its
two) that have since been removed; the binaries under `out/` were not replaced.
The five commits apply together without conflicts.

| | before | after |
|---|---|---|
| A1 script, quiche | one `maysend` mismatch, 40-byte datagram | zero, 1200-byte datagram |
| A2 script, ngtcp2 | one `outcome` mismatch, `read_pkt=OK` | zero, `FRAME_ENCODING`, error 7 |
| A6 script, quiche | two mismatches, `recv=0` | zero, error 4 |
| eight `harness/scripts` | zero on both engines | zero on both engines |
| corpus replay, ngtcp2 | 27 signatures / 138 steps | 26 / 137 |
| corpus replay, quiche | 24 signatures / 323 steps | 11 / 230 (A1 was 13 of 19 `maysend` signatures) |

No crash or ASan report in either replay.  Scripts are the ones in
`DIFFERENCES.md` ("Focused validation evidence" and A6).
