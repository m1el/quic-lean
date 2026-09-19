# Differences found between the Lean model, ngtcp2 and quiche

Date: 2026-09-19.  Model: working tree on top of `b66e902`.  ngtcp2
`v1.25.0-92-g3c23148e`.  quiche `1c8e9761` + the local `fuzz-mock-clock` patch.
Text: `draft-ietf-quic-transport-34.txt` (line numbers are that file's).

This is every difference seen so far, from four sources: `TRIAGE.md` (the
ngtcp2 campaign, WP13-1 … 18), `FINDINGS.md` (the wire-format diff), the
replay of `corpus/conn_trace` (2 458 inputs) through `out/endpoint_diff`
(ngtcp2) and `out/quiche_diff` (quiche) on 2026-09-19, and the join of their
step digests (`harness/scripts/digest_diff.py`).

**How to read the verdicts.**  A "difference" is a step where what an
implementation did is not among the outcomes the model permits, or a datagram
it sent that the model forbids — plus, from the digest join, steps where the two
implementations disagree while the model accepts both.  Each entry says whose
fault it is and how sure that is:

* **confirmed** — reduced to a minimal script *and* explained from the source
  and the text;
* **traced** — explained from one fuzz input and the source, no minimal script;
* **classified** — grouped by symptom (refusing conjunct, error code, callback
  list), cause inferred, not traced;
* **open** — unexplained.

Counts are *signatures* (distinct kind + frame-type or callback combination),
not occurrences and not bugs: one cause usually appears under several.

## Summary

| | ngtcp2 | quiche |
|---|---|---|
| signatures in the corpus replay | 44 (36 outcome, 7 maysend, 1 obligation) | 26 (21 maysend, 4 outcome, 1 obligation) |
| implementation deviates from the text | 3 (A2, A3, A4) + 1 latent assert (A5) | 1 (A1) |
| model wrong, too narrow, or not executable | B1–B9, shared | B1–B9, shared |
| API events the text does not govern | C1–C6 | C5 only (no callbacks) |
| harness artefact | D1–D5 | D5–D11 |

Both implementations agree with each other and disagree with the model on B5
and B6; by the replay rule that makes the model the suspect, and in both cases
it is.

---

## A. An implementation deviates from the text

### A1. quiche does not expand a PATH_RESPONSE datagram on a validated path — confirmed

* **Text:** §8.2.2, line 3197: "An endpoint MUST expand datagrams that contain a
  PATH_RESPONSE frame to at least the smallest allowed maximum datagram size of
  1200 bytes."  The exception (line 3200, anti-amplification) does not apply to
  a validated address.
* **Script:** `role server` / `recv app 0 1a0102030405060708` / `drain`.
* **ngtcp2:** one 1200-byte datagram.  **quiche:** one 41-byte datagram
  (`[ACK; PATH_RESPONSE]`).  **Model:** the best candidate refuses quiche's by
  `PathValidation.maySendDatagramOn` alone.
* **Source:** quiche pads a 1-RTT packet only
  `if (has_initial || !path.validated()) && pkt_type == Type::Short`
  (`quiche/src/lib.rs:5389`).  Not behind the `fuzzing` feature.
* **Extent:** 14 of quiche's 21 maysend signatures.  One of them is a *full*
  packet of 1180 bytes carrying two PATH_RESPONSEs — still under 1200; why
  quiche's ceiling is 1180 there is not traced.
* **Impact:** low — the padding exists to prove the path carries 1200 bytes, and
  this path already has.  By the letter it is a MUST.

### A2. ngtcp2 skips the Retire-Prior-To check for a repeated sequence number — confirmed

* **Text:** §19.15, line 7993: "Receiving a value in the Retire Prior To field
  that is greater than that in the Sequence Number field MUST be treated as a
  connection error of type FRAME_ENCODING_ERROR."
* **Script:** `role client` / `recv app 0 18 00 02 08 <8-byte cid> <16-byte token>`
  (NEW_CONNECTION_ID seq=0, Retire Prior To=2), with the connection's own
  sequence-0 ID or with any other.
* **ngtcp2:** `read_pkt=OK`, nothing happens.  **quiche:** FRAME_ENCODING_ERROR.
  With a *fresh* sequence number (seq=1, rpt=2) both close with
  FRAME_ENCODING_ERROR.
* **Source:** `conn_recv_new_connection_id` returns 0 at
  `ngtcp2_gaptr_is_pushed(&conn->dcid.seqgap, fr->seq, 1)` (`ngtcp2_conn.c:8176`)
  before it reaches `if (fr->retire_prior_to > fr->seq)` (line 8191).
* **The harness does not report it.**  ngtcp2's silent `OK` looks like a dropped
  datagram, which the model always permits (B3), so `endpoint_diff` shows 0
  mismatches on the minimal script.  It surfaced only because a fuzz input
  carried a later frame that ngtcp2 rejected with a different code than the
  model (`bebccdddc002175a`: ngtcp2 ERR 5, model ERR 7 or drop), and the two
  implementations disagree on it in the digest join.
* **Impact:** low; the frame is ignored.

### A3. ngtcp2 stops at an undecryptable coalesced packet — traced (source only)

`TRIAGE.md` WP13-5.  §12.2, line 4619: the receiver "MUST attempt to process
the remaining packets".  `conn_recv_cpkt` leaves its loop on
`NGTCP2_ERR_DISCARD_PKT`.  Not reproducible in the harness: the ngtcp2 stub
AEAD cannot fail.  (quiche's `fuzzing` stub *can* — tag equal to the header
fails — so this is now testable there; not done.)  The model had the same
defect and a fabricated citation; fixed.

### A4. ngtcp2 answers a STREAM_DATA_BLOCKED past a final size with FINAL_SIZE_ERROR — confirmed, text ambiguous

`TRIAGE.md` WP13-11.  §4.5, lines 1517–1520 attach FINAL_SIZE_ERROR to "a
RESET_STREAM or STREAM frame" and to "receipt of data"; a STREAM_DATA_BLOCKED is
neither.  Harmless over-strictness; the model does not permit the error.
Signature `bebcccddc00215a7` (ERR 6).

### A5. ngtcp2: `ngtcp2_pkt_adjust_pkt_num` asserts where RFC 9000 A.3 has a guard — confirmed, latent

`FINDINGS.md` §1.  **Correction to that file:** it says "release builds are
fine" because the assert is compiled out.  It is not: ngtcp2's
`CMakeLists.txt:102` strips `-DNDEBUG` from Release flags, so the assert is live
in a standard build.  Still not practically reachable (needs a packet number
within 2^31 of 2^62).

---

## B. The model is wrong, too narrow, or not executable

### B1. CRYPTO_BUFFER_EXCEEDED is not among the permitted outcomes — open since WP13-9

§7.5, lines 2713–2716 make the error a permitted alternative.  Both engines
produce it (`1cdbc0cd43827127`, ERR 13, under ngtcp2 *and* quiche).  The third
audit noted `Handshake/Basic.lean` now has buffer-error alternatives; the
signature is still there, so either they do not cover this input or the replay
was never re-adjudicated.

### B2. Blocked frames naming a limit never granted — open, WP13-10

DATA_BLOCKED / STREAMS_BLOCKED above the advertised limit: ngtcp2 closes with
FLOW_CONTROL_ERROR / STREAM_LIMIT_ERROR (`bebcc7ddc0020d28` ERR 3,
`bebcceddc002190d` ERR 4); the model encodes the wide reading of §4.1 line 1368
for STREAM_DATA_BLOCKED only.  The digest join shows quiche does **not** raise
these (A: err=4 / B: ok, 12 inputs; A: err=3 / B: ok, 4), so the two
implementations read the text differently — evidence that both readings must
stay permitted, which is the fix WP13-10 already proposes.

### B3. The model permits discarding any datagram — open, WP13-3

Safe direction for soundness, but it **masks** implementation defects whose
symptom is "nothing happened": A2 is invisible to the harness because of it.
Also implicated in D11.

### B4. `outcomes` is not evaluable for a large stream ID — open, WP13-7

`StreamTable.openedEffects` enumerates every implicitly opened stream.  The
harness skips such steps.

### B5. ACK frames refused by `ackPacketOk` — classified, both engines

The model refuses an ACK naming a packet number not in its `received`
(`Ack.AckFrameSendable`, §13.1 line 5026 — the rule is right).  6 ngtcp2
signatures and 2 quiche ones (`892de5bdb790c40d` and frame-combination
variants).  Since both engines send these ACKs, the model's `received` is
missing packets the engines processed.  Root cause not traced; the candidates
are B3 (the tracked candidate took the "drop" branch for a packet the engine
processed) and the 12-candidate cap.

### B6. An empty STREAM frame with FIN produces no `recv_stream_data` in the model — traced, both engines

`9aceb441f00f0b87`, identical under ngtcp2 and quiche: `STREAM id=7 off=0 fin=1
data=` — both hand the application a zero-length read with fin; the model emits
`stream_open` and `stream_close` but no data event.  API-level (§2.4 leaves it
open), but two independent implementations agree.

### B7. Frames for a stream the model has not seen opened are unsendable — classified

`StreamTable.streamMaySend` requires `s.has id` — a modelling conjunct, not a
sentence of the text (review finding S-5).  1 ngtcp2 signature
(`2f54b591a2287416`), 5 quiche ones: RESET_STREAM / STOP_SENDING / STREAM on
streams the engine knows and the model does not.

### B8. `acked_stream_data_offset` can never be produced — open, WP13-6

Nothing routes a received ACK to `StreamTable`.  Excluded from the comparison.

### B9. Found by the quiche harness, fixed the same day

* The model lets a CRYPTO frame out only for bytes TLS has handed over
  (`TlsEvent.tlsSend`); the harness never fired that event because ngtcp2's
  stubbed handshake sends no CRYPTO.  quiche's real one sends a session ticket
  in 1-RTT.  Now read back off the wire (`Harness.cryptoEnd`).
* TLS alerts are outside the model: `82cd84c9b16a2f33`, quiche closes with 0x10a
  (CRYPTO_ERROR + alert 10) on fuzzed post-handshake CRYPTO bytes that its real
  TLS rejects; ngtcp2's stub TLS accepts anything.  Not a model defect — a
  scope limit — but it will recur under fuzzing.

(Fixed earlier and not repeated here: WP13-4, WP13-5's model half, and the seven
audit defects D34-1 … D34-7, which were differences between the model and the
*text*, found by review rather than by either implementation.)

---

## C. API events the text does not govern

All ngtcp2, except C5.  None is a conformance difference; each costs triage time.

| | What | Signatures |
|---|---|---|
| C1 | `stream_close` fires when one direction finishes (model) vs both (ngtcp2) — WP13-1 | excluded from comparison |
| C2 | `stream_stop_sending` / `recv_stop_sending` at a different moment, or for a stream the model has no callback for — WP13-2 | 7 (`421431d4…`, `584229a3…`, `73d96ee5…`, `a073af85…`, `1ecd677b…`, `82b509b3…`, `ee5d73e7…`) |
| C3 | ngtcp2 does not announce implicitly opened streams; or announces one the model already considers open — WP13-8 | 5 of the `stream_open, …` family (`91d69bb8…` etc.); soft "subsequence" findings otherwise |
| C4 | callback multiplicity: `recv_crypto_data` once per frame in ngtcp2, once per contiguous delivery in the model; `recv_stream_data` twice for retransmitted data | 6 (`f565d890…`, `4036bb62…`, `dd084b59…`, `d4e74519…`, `6c020a91…`, `3180074e…`) |
| C5 | connection-ID callbacks deferred to the timer: ngtcp2 fires `dcid_status` / `remove_connection_id` from `handle_expiry`, the model at the frame | 6 (`6a152ea1…`, `68826271…`, `5689cb8a…`, `2b43bbe0…`, `f34ae195…`, `8babe7e8…`) |
| C6 | mixed lists combining the above | 6 (`2eb22dad…`, `22f03ea2…`, `b1f45c16…`, `36892f23…`, `3d7a7a79…`, `69315488…`) |

quiche has no callbacks, so only `recv_stream_data` and `stream_reset` are
compared for it and this whole class is absent — which is most of why quiche has
4 outcome signatures and ngtcp2 36.

---

## D. Harness artefacts

| | What | Status |
|---|---|---|
| D1 | idle timer: ngtcp2's harness forces `POST_HANDSHAKE` with `idle_ts = 0`, so its timer starts from a moment that never happened — WP13-12, was "undecided" | **resolved by quiche**: 49 inputs where quiche (real handshake) closes on idle exactly when the model does and ngtcp2 runs on |
| D2 | callback mapping for retired connection IDs — WP13-13 | fixed |
| D3 | `NGTCP2_ERR_DRAINING` read as PROTOCOL_VIOLATION — WP13-14 | fixed |
| D4 | unprotection assumed an 8-byte connection ID — WP13-15 | worked around (ngtcp2); fixed for quiche (D8) |
| D5 | "acknowledgment overdue": the driver does not drain after a clock step, so the ACK the engine owes is never written | open, both engines (`bfd34bc6b6895906`) |
| D6 | quiche pads an Initial datagram with raw zeros after the last packet; the `fuzzing` stub decrypts them as a packet for connection ID 00…00 and the client closes.  quiche's own fuzz targets use all-zero IDs, which hides it | driver trims (`q_trim`) |
| D7 | quiche opens a stream on first write; ngtcp2 refuses writes to unopened streams | driver refuses, for parity |
| D8 | quiche switches to a peer-issued connection ID of another length | driver asks quiche for the current length |
| D9 | the exact-match pass sees effects quiche cannot report and so prefers the "dropped" outcome | exclusion-aware pass first, for quiche |
| D10 | ACK frames in scripts name absolute packet numbers; the handshake shifts quiche's, so the same bytes acknowledge different packets in the two engines | open |
| D12 | quiche closes with PROTOCOL_VIOLATION on `RETIRE_CONNECTION_ID seq=2` (§19.16 line 8046: a sequence number it never sent) where ngtcp2 accepts it: ngtcp2 issues connection IDs by itself while writing, quiche only when the application calls `new_scid`, and the driver never does.  Both correct; the engines are in different states.  58 inputs in the join | open — the driver should issue IDs for parity |
| D11 | `dcidOk` refusals (4 quiche signatures): quiche had received packet 60932, so it discards packet 5 as below its duplicate window and never sees the NEW_CONNECTION_ID in it; the model processed it and retired the ID.  quiche is within its rights (§12.3); why *every* candidate, including the "dropped" ones, then refuses is B3/B5's problem | traced |

---

## E. The two implementations against each other (digest join)

2 306 inputs in common, 1 855 identical up to the last step, 451 with a first
difference; 280 of those are "latitude" (both accepted by the model, behaviour
differs).  One representative of each of the larger buckets was run on both
engines; the rest are untraced, and D10 inflates all of them.

| Inputs | ngtcp2 | quiche | Cause |
|---|---|---|---|
| 92 | ok, `recv_stream_data` | ok, nothing | **traced — genuine latitude.**  After a packet numbered ~16 000, a packet numbered 5 arrives.  ngtcp2 processes it; quiche drops it ("ignored duplicate packet"): its duplicate detection is a fixed window below the largest number seen (`packet.rs` `PktNumWindow`, a 128-bit map) and anything older counts as a duplicate.  §12.3, lines 4716–4719 allow exactly this: "The data required for detecting duplicates can be limited by maintaining a minimum packet number below which all packets are immediately dropped."  Same root as D11 |
| 85 + 28 | ok | ok, model verdict differs | same behaviour, the model judged the two runs differently: state drift (B5, D10) |
| 58 | ok | PROTOCOL_VIOLATION | **traced — D12**, different connection-ID state, both correct |
| 49 | ok | idle close | D1 |
| 12 | PROTOCOL_VIOLATION | ok | **traced — genuine latitude.**  `ACK largest=0` for an application packet never sent.  §13.1, line 5030: "An endpoint SHOULD treat receipt of an acknowledgment for a packet it did not send as a connection error of type PROTOCOL_VIOLATION, if it is able to detect the condition."  ngtcp2 does; quiche detects only its deliberately skipped number (`recovery.rs:142`, `OptimisticAckDetected`) |
| 12 + 4 | STREAM_LIMIT / FLOW_CONTROL error | ok | B2 — the two readings of §4.1 line 1368, one per implementation |
| 12 + 4 | ok, `stream_reset` | ok, nothing | untraced; quiche reports a reset only when the application reads |
| 7 | ok | FRAME_ENCODING_ERROR | includes A2 |
| 6 | STREAM_STATE_ERROR | ok | untraced |
| 5 | FRAME_ENCODING_ERROR | ok | untraced |
| 5 + 5 | ok, `stream_reset` | FINAL_SIZE / PROTOCOL_VIOLATION | untraced |

So far the join has produced one implementation finding the pairwise diff
hides (A2), settled one verdict that was undecided (D1), and shown three places
where the text really does leave the choice open (the duplicate window, ACKs
for unsent packets, B2).  It has not yet produced a rule the model is missing.

## What is not covered

Migration and second paths; loss recovery and congestion control; Retry and
version negotiation against a live peer; 0-RTT; key update; receive-side
coalescing under ngtcp2 (its stub AEAD cannot fail); any input found under
quiche's own coverage — `quiche_diff` has only replayed a corpus evolved under
ngtcp2.
