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

**Validation pass (2026-09-19).** Rechecked the local draft and current source
at Lean `4448547`, ngtcp2 `3c23148e`, and quiche `d3e21813` (the local patched
checkout), and ran the focused scripts listed below against the existing
`out/endpoint_diff` and `out/quiche_diff` binaries. The binaries were not rebuilt
in this pass. The campaign counts below are historical reports, not newly
recomputed totals. Source-confirmed, reproduced, and inferred findings are
separated below; implementation agreement alone does not establish conformance.
This validates against the checked-in draft-34, not every subsequent RFC or
erratum.

**Fixes pass (2026-09-19, later the same day).**  The four recommendations of
`TRANSPORT_AUDIT_2026-09-19_1.md` (B3, B1, B4, B6) and its §6 harness items
were implemented, both harnesses rebuilt, and the corpus replayed on both
engines.  Entries below say "fixed" where that happened; the summary has a
before/after row.  Narrowing B3 exposed one new implementation finding (A6) and
made A2 visible to the pairwise harness.

Counts are *signatures* (distinct kind + frame-type or callback combination),
not occurrences and not bugs: one cause usually appears under several.

## Summary

| | ngtcp2 | quiche |
|---|---|---|
| signatures in the corpus replay, before the fixes pass | 44 (36 outcome, 7 maysend, 1 obligation); 649 mismatching steps | 26 (21 maysend, 4 outcome, 1 obligation); 571 steps |
| … after it | 27 (23 outcome, 4 maysend, 0 obligation); 138 steps, 65 of them after candidate loss | 24 (19 maysend, 4 outcome, 1 obligation); 323 steps, 233 of them after candidate loss |
| implementation deviations supported by validation | A2 reproduced (now a pairwise mismatch); A3 source-supported; A5 latent assert; A4 interpretation unresolved | A1 reproduced; A6 reproduced |
| model limitations or suspected tracking issues | B1, B3, B4, B6 fixed; B2, B5, B7, B8 open (see individual qualifications) | the same |
| API events the text does not govern | C1–C6, B6 | B6 (read results synthesized as callbacks) |
| harness artefact | D1–D5, D10, D12 | D5–D12 |
| corpus replay, 2026-09-21 (section F) | 29 signatures / 145 steps; 72 after candidate loss.  Three confirmed spec deviations (A2, A3, A5); A4 and B2 still unresolved | not re-run |
| SHOULDs ignored on that corpus (section G) | 7 kinds, all still accepted.  Largest: ACK of an unsent number ×340, `RESET_STREAM` code ×97, final-size change ×58 | not re-run |

Both implementations produce B5 and B6 symptoms. B5 remains an untraced
state-tracking discrepancy, not a proven model-rule defect. B6 is a reproduced
API observation mismatch, not a transport-spec violation.

---

## A. Implementation findings and suspected deviations

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

**After the B3 fix** the pairwise harness sees A2 on its own: the script above
is one `outcome` mismatch under ngtcp2 (`405f42ebc91f5bc1`: observed OK, every
candidate permits only ERR 7) and zero under quiche.  `Endpoint/Examples.lean`
section B3 is the model-side guard.

### A3. ngtcp2 stops at an undecryptable coalesced packet — source-supported, not reproduced

`TRIAGE.md` WP13-5.  §12.2, line 4619: the receiver "MUST attempt to process
the remaining packets".  `conn_recv_cpkt` leaves its loop on
`NGTCP2_ERR_DISCARD_PKT`.  Not reproducible in the harness: the ngtcp2 stub
AEAD cannot fail.  (quiche's `fuzzing` stub *can* — tag equal to the header
fails — but a receive-side coalescing test is still needed; not done.)  The model had the same
defect and a fabricated citation; fixed.

### A4. ngtcp2 answers a STREAM_DATA_BLOCKED past a final size with FINAL_SIZE_ERROR — behavior reproduced, conformance unresolved

`TRIAGE.md` WP13-11.  §4.5, lines 1517–1520 attach FINAL_SIZE_ERROR to "a
RESET_STREAM or STREAM frame" and to "receipt of data"; a STREAM_DATA_BLOCKED is
neither. The model does not permit the error. The two-frame WP13-11 script
still produces error 6 in ngtcp2 and succeeds in quiche. However, the cited
paragraph specifies situations in which the error SHOULD be sent; its silence
about this frame alone is not a prohibition. §11 also permits any applicable
error code. Whether this blocked offset constitutes a final-size inconsistency
needs a separate argument; do not count this as an established spec violation.
Signature `bebcccddc00215a7` (ERR 6).

### A5. ngtcp2: `ngtcp2_pkt_adjust_pkt_num` asserts where RFC 9000 A.3 has a guard — confirmed, latent

`FINDINGS.md` §1.  **Correction to that file:** it says "release builds are
fine" because the assert is compiled out.  It is not: ngtcp2's
`CMakeLists.txt:102–108` strips `-DNDEBUG` from Release flags, so the assert is live
in a standard build.  Still not practically reachable (needs a packet number
within 2^31 of 2^62).

### A6. quiche ignores STREAM_DATA_BLOCKED, so a stream ID over the limit raises nothing — confirmed

Found by the fixes pass: it was masked by B3.  §4.6, line 1546: "An endpoint
that receives a frame with a stream ID exceeding the limit it has sent MUST
treat this as a connection error of type STREAM_LIMIT_ERROR."  §19.13 adds
STREAM_STATE_ERROR for a send-only stream.

* **Script:** `role server` / `recv app 0 15401400` / `drain`
  (STREAM_DATA_BLOCKED id=20 — client-initiated bidirectional stream 5, limit 4).
* **ngtcp2:** `RET read_pkt=STREAM_LIMIT`, error 4, zero mismatches.
* **quiche:** processes the packet and acknowledges it; one `outcome` mismatch
  (every candidate permits only ERR 4) and the `maysend` that follows from it.
* **Cause:** the receive handler (`quiche/src/lib.rs:8735` on `master`) only
  increments `stream_data_blocked_recv_count`; the stream ID is never looked
  at, so neither the limit nor the stream's direction is checked.  (Line 4373,
  cited here earlier, is the *send*-side acknowledgment handler.)
* **Extent:** 8 of the 13 steps left under `405f42ebc91f5bc1` in the quiche
  replay.  The other five are untraced singles (CONNECTION_CLOSE, STOP_SENDING
  and DATA_BLOCKED packets where the model permits only an error).
* **Impact:** low — the frame is informational — but it is a MUST.

---

## B. The model is wrong, too narrow, or not executable

### B1. CRYPTO buffer policy is too narrow — fixed (`Handshake.BufferPolicy`)

The title in WP13-9 was stale: `Handshake/Basic.lean` already permitted
CRYPTO_BUFFER_EXCEEDED for offset overflow, a discarded CRYPTO stream, or
buffered payload exceeding the limit.  The mismatch was the **accounting**:
`bufferedBytes` counts payload bytes held, so CRYPTO offset 196611 length 16 cost
16 bytes, while both engines answer error 13 — ngtcp2 bounds the end offset
minus the delivered offset (`ngtcp2_conn.c:7456`,
`NGTCP2_MAX_REORDERED_CRYPTO_DATA`) and has absolute per-level limits
(7375–7393); quiche rejects `max_off() >= MAX_CRYPTO_STREAM_OFFSET`
(`lib.rs:8573`).

* **Fix:** `Handshake/Crypto.lean` has `BufferPolicy` — a limit per accounting,
  payload bytes and reordering span (`Crypto.span`: highest buffered byte minus
  the delivered offset) — with `Exceeded` as §7.5's "unable to buffer" and
  `Admissible` as line 2703's 4096-byte floor under both.  `cryptoOutcomes` and
  `CryptoStep` ask `s.bufPolicy.Exceeded`; the phase-dependent outcomes are
  unchanged (during the handshake: expand or close; after it also discard,
  which is an `.ok`, so the packet is still acknowledged).
* **What the text was read to fix:** out-of-order data ending within 4096 bytes
  of the delivered offset is never a buffer error
  (`BufferPolicy.not_exceeded_of_minimum`); in-order data occupies no buffer, so
  an **absolute offset cutoff is not admitted** (`not_exceeded_in_order`).
  Neither engine's constant was copied.  An engine that refuses a contiguous
  CRYPTO stream for its length alone would still be a mismatch; the corpus has
  one candidate, under quiche only (`1cdbc0cd43827127`, CRYPTO offset
  271060402572361728 with no data, after candidate loss — untraced).
* **Validation:** `Handshake.lean` examples (sparse high offset in both phases,
  4095 vs 4096 bytes past the delivered offset, contiguous delivery, delivery at
  a high absolute offset); `Endpoint/Examples.lean` section B1 (error 13
  accepted, the discard leaves packet 0 in `ackAppData.received`, no `.drop`).
  The script below: zero mismatches on both engines (was one each).
  `1cdbc0cd43827127`: ngtcp2 3 → 0 steps, quiche 5 → 1.

### B2. Blocked frames naming a limit never granted — open, WP13-10

DATA_BLOCKED / STREAMS_BLOCKED above the advertised limit: ngtcp2 closes with
FLOW_CONTROL_ERROR / STREAM_LIMIT_ERROR (`bebcc7ddc0020d28` ERR 3,
`bebcceddc002190d` ERR 4); the model encodes the wide reading of §4.1 line 1368
for STREAM_DATA_BLOCKED only.  The digest join shows quiche does **not** raise
these (A: err=4 / B: ok, 12 inputs; A: err=3 / B: ok, 4), so the two
implementations behave differently. Both minimal WP13-10 scripts reproduce.
The source confirms that `StreamTable/Step.lean:208–216` lacks these error
alternatives. However, differing implementations do not prove that both are
conformant. §4.1 concerns data limits; STREAMS_BLOCKED additionally needs the
separate §4.6 stream-count argument. Whether a reported blocked limit alone
constitutes a violation remains unresolved. Adding alternatives is a proposed
modelling choice, not a spec requirement established by this comparison.

### B3. The model permitted discarding any datagram — fixed, WP13-3

`DatagramSize.Step.datagramDiscard` gave every `.recvDatagram n` a `.drop`,
which the endpoint composition preserved; §14 lines 5695–5697 permit dropping
datagrams **that fail size constraints**.  It masked every defect whose symptom
is "nothing happened" (A2, A6).

* **Fix:** the event is `.recvDatagram size required` and the discard needs
  `DatagramSize.FailsSizeConstraint`: smaller than the text required of its
  sender (1200 for a datagram carrying PATH_CHALLENGE or PATH_RESPONSE, §8.2.1
  line 3154 / §8.2.2 line 3197, read off the frames by `Pipeline.requiredSize`)
  or larger than our own `max_udp_payload_size` (§18.2).  Proved:
  `datagram_drop_iff`, `datagram_delivered_of_size_ok`.  `initialDiscard`
  (§5.2 line 1878, §11.1 line 4485) is unchanged.
* **Discards kept at their own layers:** failed decryption and §12.2
  (`recvParsed`), §12.3 duplicates (`Ack`), §9 (`Migration`), §5.2 (`VersionNeg`),
  §11.1 (`packetErrOutcomes`).  One was *missing* and had been riding on the
  blanket discard: §12.3 line 4717's minimum packet number — `Ack` modelled it
  but no endpoint event could raise it.  `Pipeline.minimumRaised` now offers
  "the minimum moved past this packet" for a non-duplicate packet older than
  the largest processed in its space, and for no other (D11's case).
* **Harness consequences** (audit §6, not model latitude): the model is now
  told that both engines have discarded their Initial and Handshake keys
  (`tlsDiscardKeys`, see `endpoint_diff.md` §2) — without that, ~150 steps in
  which the engine cannot even decrypt the packet became mismatches.
* **Validation:** `Endpoint/Examples.lean` section B3 — A2's malformed
  NEW_CONNECTION_ID has error 7 as its only outcome; an undersized
  PATH_CHALLENGE datagram may still be dropped and never closes; an expanded
  one may not; a duplicate is still ignored; an old packet may be dropped, the
  newest may not; D34-3/D34-4 (skipping a coalesced packet) still pass.

### B4. `outcomes` was impractical to evaluate for a large stream ID — fixed, WP13-7

`StreamTable.openedEffects` enumerated every implicitly opened stream with
`List.range'`; the harness skipped such steps and stopped tracking the run.

* **Fix:** the state already was a counter (`State.opened`); the effects are now
  one range, `Effect.streamsOpenedBelow first count`, then `streamOpened` for
  the stream the frame names, and the STREAM_LIMIT_ERROR branch builds no
  effects at all.  `no_reuse` is restated over `Effect.opens`, which covers the
  range.  ngtcp2 announces an implicitly opened stream the first time a frame
  names it, so `Effect.streamFirstUsed` marks that moment (observation only).
* **Validation:** `StreamTable.lean` examples at stream 2^62 − 4 (limit error;
  with a limit of 2^60, all lower streams exist afterwards; none is opened
  twice).  Script `recv app 0 0bfffffffffffffffc0161`: 32 ms, error 4, zero
  mismatches on both engines.  The harness skip is off by default
  (`DIFF_MAX_STREAM_INDEX` restores it): steps not compared 133 → 86 (ngtcp2),
  190 → 142 (quiche); the rest are non-transport error codes.  Side effect:
  steps needing the subsequence rule 148 → 43 under ngtcp2, because one
  `stream_open` per frame is what ngtcp2 reports.

### B5. ACK frames refused by `ackPacketOk` — classified, both engines

The model refuses an ACK naming a packet number not in its `received`
(`Ack.AckFrameSendable`, §13.1 line 5026 — the rule is right).  6 ngtcp2
signatures and 2 quiche ones (`892de5bdb790c40d` and frame-combination
variants).  The refusal establishes a mismatch with the retained candidates' `received`
sets, not why those sets differ from the engine. Root cause remains untraced;
possibilities include a retained drop branch, the 12-candidate cap, handshake
state/packet-number mapping, or other harness state drift. The cap can remove
a valid execution and cause a false-positive mismatch; agreement between the
engines does not prove that `AckFrameSendable` itself is wrong.

### B6. An empty STREAM frame with FIN produced no `recv_stream_data` in the model — fixed in the observation layer

`9aceb441f00f0b87`, identical under both engines: `STREAM id=7 off=0 fin=1
data=` — both hand the application a zero-length read with fin.  API-level
(§2.4 leaves it open), not a transport-spec defect: `Stream/Recv.lean` keeps
"new bytes available" (`dataAvailable`) and "final size reached"
(`allDataReceived`) apart, and only the harness mapping was wrong.

* **Fix:** `Exports.Effect.cbNames` — a step that reaches the final size of a
  stream *without* delivering new bytes of it is observed as `recv_stream_data`
  followed by `stream_close`; with new bytes, as before.  The model's effects
  are untouched: no `dataAvailable` is invented, and completion is not erased.
* **Validation:** `Endpoint/Examples.lean` section B6 and four scripts on both
  engines, all zero mismatches: empty FIN (`0f070000`), data plus FIN
  (`0f070003616263`), FIN after the data (`0e07…` then `0f070300`), repeated
  empty FIN (no second read, no second completion).  `9aceb441f00f0b87`:
  4 → 0 steps (ngtcp2), 20 → 0 (quiche).

### B7. Frames for a stream the model has not seen opened are unsendable — classified

`StreamTable.streamMaySend` requires `s.has id` — a modelling conjunct, not a
sentence of the text (review finding S-5).  1 ngtcp2 signature
(`2f54b591a2287416`), 5 quiche ones: RESET_STREAM / STOP_SENDING / STREAM on
streams the engine knows and the model does not. The conjunct is confirmed
in `StreamTable/Send.lean:48`, but the signature causes are not traced.
The same source explicitly requires the harness to synthesize `appOpenStream`
before local first use. Missing that event or losing a candidate can also
explain rejection; the conjunct alone is not proof of a spec defect.

### B8. `acked_stream_data_offset` could never be produced — fixed, WP13-6

Fixed 2026-09-20 (PLAN §4p).  `Pipeline.recvAckFrame`: after `Ack`'s own rules,
every in-flight packet an ACK frame covers is acknowledged to `Retransmission`
(§13.3, line 5333), and a stream whose acknowledged segments reach its final
size with the FIN moves "Data Sent" → "Data Recvd" (§3.1, line 975); an
acknowledged RESET_STREAM moves "Reset Sent" → "Reset Recvd" (line 990).  The
harness now reports what each sent packet carried
(`LocalAction.sentPacketFrames`), which it never had.  43 ngtcp2 replay steps
that needed the callback exclusion match exactly.  It exposed one API
difference: ngtcp2 and Google QUICHE tell the application about a STOP_SENDING
that arrives in "Data Recvd"; the text is silent, so `Step.stopSendingLateTold`
permits it (section C).

### B9. quiche harness integration and TLS scope limitations

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

The quiche driver synthesizes `recv_stream_data` and `stream_reset` observations
from reads and compares those; it does not compare connection-ID callbacks.
Consequently C1–C6 are absent for quiche — which is most of why quiche has
4 outcome signatures and ngtcp2 36.

---

## D. Harness artefacts

| | What | Status |
|---|---|---|
| D1 | idle timer: ngtcp2's harness forces `POST_HANDSHAKE` with `idle_ts = 0` — WP13-12 | harness-state explanation supported by source; the reported 49 quiche comparisons support it but do not independently prove the cause for every input |
| D2 | callback mapping for retired connection IDs — WP13-13 | fixed |
| D3 | `NGTCP2_ERR_DRAINING` read as PROTOCOL_VIOLATION — WP13-14 | fixed |
| D4 | unprotection assumed an 8-byte connection ID — WP13-15 | worked around (ngtcp2); fixed for quiche (D8) |
| D5 | "acknowledgment overdue": the driver does not drain after a clock step, so the ACK the engine owes is never written | **fixed for ngtcp2** (435 → 0 steps): `md_tick` gives the engine one `step_drain` before reporting, and an engine that has closed is not checked.  quiche 421 → 201, all under one signature and mostly after candidate loss; untraced |
| D13 | the candidate cap (12) can cut the execution the engine is on; a later empty set is then not an exhaustive rejection | reports now say "exhaustive" or "after candidate loss" and the summary counts the latter: 65 of 138 (ngtcp2), 233 of 323 (quiche).  `DIFF_MAX_CANDS=64` takes quiche to 262 / 146 in the same minute; ngtcp2 stays at 27 signatures / 138 steps (17 after loss) and takes 13 minutes instead of 2, so the cap explains part of quiche's residue and none of ngtcp2's |
| D14 | the model was never told the engines had discarded their Initial and Handshake keys; hidden by B3 | fixed (`tlsDiscardKeys` in `md_start`) |
| D6 | quiche pads an Initial datagram with raw zeros after the last packet; the `fuzzing` stub decrypts them as a packet for connection ID 00…00 and the client closes.  quiche's own fuzz targets use all-zero IDs, which hides it | driver trims (`q_trim`) |
| D7 | quiche opens a stream on first write; ngtcp2 refuses writes to unopened streams | driver refuses, for parity |
| D8 | quiche switches to a peer-issued connection ID of another length | driver asks quiche for the current length |
| D9 | the exact-match pass sees effects quiche cannot report and so prefers the "dropped" outcome | exclusion-aware pass first, for quiche |
| D10 | ACK frames in scripts name absolute packet numbers; the handshake shifts quiche's, so the same bytes acknowledge different packets in the two engines | open |
| D12 | quiche closes with PROTOCOL_VIOLATION on `RETIRE_CONNECTION_ID seq=2` (§19.16 line 8046: a sequence number it never sent) where ngtcp2 accepts it: ngtcp2 issues connection IDs by itself while writing, quiche only when the application calls `new_scid`, and the driver never does.  Both correct; the engines are in different states.  58 inputs in the join | open — the driver should issue IDs for parity |
| D11 | `dcidOk` refusals (4 quiche signatures): quiche had received packet 60932, so it discards packet 5 as below its duplicate window and never sees the NEW_CONNECTION_ID in it; the model processed it and retired the ID.  quiche is within its rights (§12.3); why *every* candidate, including the "dropped" ones, then refuses is B3/B5's problem | traced; the discard is now `Pipeline.minimumRaised` (see B3) |

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
| 12 | PROTOCOL_VIOLATION | ok | **traced — SHOULD-level difference.**  `ACK largest=0` for an application packet never sent.  §13.1, line 5030: "An endpoint SHOULD treat receipt of an acknowledgment for a packet it did not send as a connection error of type PROTOCOL_VIOLATION, if it is able to detect the condition."  ngtcp2 does; quiche detects only its deliberately skipped number (`recovery.rs:142`, `OptimisticAckDetected`) |
| 12 + 4 | STREAM_LIMIT / FLOW_CONTROL error | ok | B2 — interpretation unresolved (§4.1 and §4.6) |
| 12 + 4 | ok, `stream_reset` | ok, nothing | untraced; quiche reports a reset only when the application reads |
| 7 | ok | FRAME_ENCODING_ERROR | includes A2 |
| 6 | STREAM_STATE_ERROR | ok | untraced |
| 5 | FRAME_ENCODING_ERROR | ok | untraced |
| 5 + 5 | ok, `stream_reset` | FINAL_SIZE / PROTOCOL_VIOLATION | untraced |

So far the join has produced one implementation finding the pairwise diff
hides (A2), supported a harness explanation for D1, and identified permitted duplicate-window latitude. The unsent-ACK rule is a
SHOULD, not unconditional permission to ignore a detectable error: omitting
such a check needs the usual justification for departing from a SHOULD.
B2 remains an interpretation question. No additional missing model rule has
been established by the join alone.

## Focused validation evidence

The following scripts were each run on both existing binaries (16 runs total)
with `ASAN_OPTIONS=detect_leaks=0 DIFF_SHOW=1 ./out/<engine> --script <file>`.
A zero process exit status does not mean agreement: these harnesses report
mismatch counts and continue. Each row below denotes a separate script;
semicolons separate script lines. `CID` is `c1c1c1c1c1c1c1c1` and `TOKEN` is
`11111111111111111111111111111111`; concatenate the frame hex without spaces.

| Finding | Script | Result in this pass |
|---|---|---|
| A1 | `role server; recv app 0 1a0102030405060708; drain` | ngtcp2 response datagram 1200 bytes; quiche 41 bytes, one send mismatch |
| A2 | `role client; recv app 0 18000208<CID><TOKEN>; drain` | ngtcp2 OK, quiche error 7; both have zero model mismatches |
| A2 control | `role client; recv app 0 18010208<CID><TOKEN>; drain` | both error 7, zero model mismatches |
| A4 | `role server; recv app 0 0b0003616263; recv app 1 15001e; drain` | ngtcp2 error 6 and one mismatch; quiche accepts |
| B1 | `role client; recv app 0 06800300031000000000000000000000000000000000` | both error 13, one mismatch each |
| B2 data | `role server; recv app 0 145008` | ngtcp2 error 3 and one mismatch; quiche accepts |
| B2 streams | `role server; recv app 0 1703` | ngtcp2 error 4 and one mismatch; quiche accepts |
| B6 | `role client; recv app 0 0f070000; drain` | both report an empty FIN read, one outcome mismatch each |

The B1 accounting explanation was also checked with `lake env lean` using:

```lean
import QuicModel.Spec.Handshake.Basic
open Quic.Spec Quic.Spec.Handshake
def probeState : State := { initClient [] [] with complete := true }
#eval bufferedBytes ((probeState.stream .oneRtt).recv 196611 16).buf
-- 16
#eval (cryptoOutcomes probeState .oneRtt 196611 16).any
  (fun o => match o with
    | .error .cryptoBufferExceeded => true
    | _ => false)
-- false
```

A3 and A5 were checked against source, without new runtime reproducers. B3,
B4, B7, and B8 were checked in the model source (received ACKs route to `Ack`,
not `StreamTable`). B9's CRYPTO handover synthesis is present in the harness.
The historical corpus counts, signature-to-cause assignments, C-family callback
buckets, D-family per-input explanations, and digest-join totals were not
independently replayed in this pass. Those remain campaign evidence at their
stated confidence levels, not newly validated conformance conclusions.

## After the fixes pass

Commands as before (`-runs=0 corpus/conn_trace`, 2 458 inputs, default cap 12),
both binaries rebuilt from the fixed model.  Eight scripts: zero mismatches on
both engines; `harness/scripts/run.sh` (the `conn_trace` recordings): unchanged.

| Script | ngtcp2 | quiche |
|---|---|---|
| A2 `recv app 0 18000208<CID><TOKEN>` | one mismatch (was hidden) | zero |
| A6 `recv app 0 15401400` | zero | two (outcome, then maysend) |
| B1 `recv app 0 0680030003100000…` | zero (was one) | zero (was one) |
| B4 `recv app 0 0bfffffffffffffffc0161` | zero, compared (was skipped) | zero, compared |
| B6 empty FIN / data+FIN / late FIN / repeated FIN | zero ×4 (empty FIN was one) | zero ×4 |

No signature is new under ngtcp2.  Under quiche `405f42ebc91f5bc1` (13 steps,
A6 and five singles) and one single-step signature (`ceaff8b58ae25eeb`) are
new, and three grew by one step (`2f54b591…`, `b75a6a4c…`, `fec5b6db…`);
everything else shrank or is unchanged.  The digest join (section E) was **not** re-run and its
totals are from before this pass.

## Patches for the implementation findings

One branch per finding, each one commit on top of the upstream default branch
(`main` `3c23148e` for ngtcp2, `master` `1c8e9761` for quiche), each with a
regression test that fails without the fix.  They live in worktrees under
`../patches-wt/`; nothing is pushed.  ngtcp2's own suite: 266/266 on every
branch; quiche `cargo test --lib`: all pass on both.

| Finding | Repository / branch | Change |
|---|---|---|
| A1 | quiche `fix/pad-path-response` | a 1-RTT packet carrying PATH_CHALLENGE or PATH_RESPONSE on a validated path is padded up to 1200 bytes |
| A6 | quiche `fix/stream-data-blocked-checks` | STREAM_DATA_BLOCKED goes through `get_or_create_stream` (stream limit) and is refused on our own unidirectional streams |
| A2 | ngtcp2 `fix/ncid-retire-prior-to-check` | Retire Prior To > Sequence Number is checked before the repeated-sequence early return |
| A3 | ngtcp2 `fix/coalesced-pkt-after-discard` | `conn_recv_cpkt` skips a discarded long-header packet by its Length and goes on; the handshake path is untouched.  The unit test (a Handshake packet that fails decryption in front of a 1-RTT packet) is the first reproduction of A3 |
| A5 | ngtcp2 `fix/adjust-pkt-num-no-assert` | the assert becomes RFC 9000 A.3's guard |

A4 has no patch: its conformance is unresolved.

Checked end to end with harness binaries linked against all the patches at once
(throwaway trees, `out/` untouched): A1, A2 and A6's scripts go to zero
mismatches on the engine that had one, the eight scripts stay at zero on both,
and the corpus replay goes from 27 signatures / 138 steps to 26 / 137 (ngtcp2)
and from 24 / 323 to 11 / 230 (quiche — A1 was 13 of its 19 `maysend`
signatures).

## F. ngtcp2 against the text, corpus replay of 2026-09-21

Replay of `corpus/conn_trace` (2456 inputs) through `out/endpoint_diff_cov`,
rebuilt the same day from the current tree (post-error stop restored).  Log:
`out/spec-coverage-run/endpoint_diff.log`.  ngtcp2 `3c23148e`.  18512 steps
compared (348 needed the `stream_close` / `acked_stream_data_offset`
exclusion, 45 the subsequence rule), 86 not compared, 10109 send checks, 28
runs abandoned after the model closed.  **29 distinct signatures, 145
mismatching steps, 72 of them after the candidate cap had already cut a
state.**  Transport-parameter wire checks: 2456, of which 59 disagree with
`ngtcp2_transport_params_decode`; those are a separate counter and are not
among the 29.  The 27 / 138 figure above is the 2026-09-19 fixes-pass replay,
not this one.

Three of these are departures from RFC 9000.  Two more are reproduced and
still open.  The other 26 signatures are callback timing, model-state drift,
or a harness check.

### Confirmed

**A2 — §19.15, Retire Prior To greater than Sequence Number.**  A
`NEW_CONNECTION_ID` with Retire Prior To greater than Sequence Number must be
`FRAME_ENCODING_ERROR` (draft-34 line 7993).  `conn_recv_new_connection_id`
returns success at `ngtcp2_conn.c:8176` when that sequence is already in the
gap tracker, before the comparison at line 8191.  A fresh sequence number is
rejected; a repeat of sequence 0 is ignored.  This replay shows the
consequence as one exhaustive step, `bebccdddc002175a`: the packet starts
with `NEW_CONNECTION_ID seq=0 rpt=2` and also carries a `STREAM` on a
send-only stream, and ngtcp2 closes with `STREAM_STATE_ERROR` (5).  Both
candidates permit only error 7.  The illegal connection-ID frame was skipped,
so the later frame determined the code.

**A3 — §12.2, coalesced packets after one that cannot be decrypted.**  The
receiver must try to process the remaining packets (draft-34 line 4619).
`conn_recv_cpkt` leaves its loop on `NGTCP2_ERR_DISCARD_PKT` and returns 0
(`ngtcp2_conn.c:10115`).  Discarding the undecryptable packet is allowed;
stopping there is not.  The harness stub AEAD cannot fail, so this replay
does not hit it.  The unit test on `fix/coalesced-pkt-after-discard` does
(section "Patches" above).

**A5 — Appendix A.3, packet-number reconstruction.**  The algorithm rejects a
candidate that would land at or above 2^62.  `ngtcp2_pkt_adjust_pkt_num`
asserts that case (`ngtcp2_pkt.c:2197`).  ngtcp2's CMake strips `-DNDEBUG`,
so the assert is live in a normal build.  Reaching it takes a packet number
within 2^31 of 2^62.  The corpus does not.  `FINDINGS.md` §1; the "release
builds are fine" sentence there is wrong for the reason just given.

### Reproduced, conformance not established

**A4 — §4.5, `STREAM_DATA_BLOCKED` past a final size.**  `bebcccddc00215a7`,
one exhaustive step: a `STREAM` with FIN (`id=0 off=0 data=656280`), then
`STREAM_DATA_BLOCKED id=0 v=30`.  ngtcp2 closes with `FINAL_SIZE_ERROR` (6);
both candidates accept the frame.  The sentences that name
`FINAL_SIZE_ERROR` attach it to a `RESET_STREAM` or `STREAM` frame and to
receipt of data (draft-34 lines 1517–1520).  §11 also allows an applicable
error code.  That is not enough to call the close non-conformant.  No patch.

**B2 — §4.1 / §4.6, a blocked-limit frame for a limit never granted.**
ngtcp2 closes with `FLOW_CONTROL_ERROR` (3) or `STREAM_LIMIT_ERROR` (4);
quiche accepts the same frames (section E).  `bebcc7ddc0020d28` (2 steps,
observed error 3, candidates permit error 4) and `bebcceddc002190d` (14
steps, observed error 4, candidates accept the packet).  Both printed
samples are after candidate loss.  Whether reporting a blocked offset by
itself is a violation is still open.

### Not a transport-rule divergence

The remaining signatures disagree with the model on observations the text
does not fix, or on state the candidate cap has already lost.  Buckets are
the first printed occurrence of each signature in the log above, read
against sections B and C.

| Class | What the step shows | Signatures | Steps |
|---|---|---:|---:|
| C4, callback shape | `recv_crypto_data` or `recv_stream_data` once per frame or per retransmission; the model reports one contiguous delivery | `4036bb62b857cb11` ×28, `3180074e24df84dd` ×8, `f565d890f7c3a6bc` ×2, `dd084b597791932d` ×1, `d4e745198464b820` ×1, `6c020a91973eb198` ×1 | 41 |
| C5, connection-ID timing | `dcid_status` or `remove_connection_id` from the timer, or bundled with another callback the model splits differently | `6a152ea1fb98615d` ×39, `f34ae1952a62e561` ×10, `688262718687b159` ×4, `8babe7e8640c3a7b` ×3, `5689cb8a0c85a7b2` ×1, `2b43bbe00e8b520e` ×1 | 58 |
| C3, implicit streams | `stream_open` where §2.1 already treats the stream as open, or the reverse | `91d69bb8e65b2f7a` ×3 | 3 |
| C6, mixed callbacks | Combinations of C3–C5 | `69315488f82ff058` ×3, `3d7a7a79f8a563ef` ×2, `36892f23d7bf997e` ×1, `22f03ea22aa57841` ×1 | 7 |
| B5, ACK the model refuses | An ACK whose packet number is absent from the candidates' received set.  The rule matches §13.1; the sets differ.  Every one is after candidate loss | `892de5bdb790c40d` ×7, `b75a6a4caf721c63` ×2, `d7a7c65f95fb7c6d` ×2, `f6e91f92cb3bcfcb` ×1, `b3c10263f238e80c` ×1 | 13 |
| B7, send on an unseen stream | `STREAM id=4` (`2f54b591a2287416`).  The refusal is `StreamTable.streamMaySend`'s `s.has id` conjunct, not a sentence of the text.  After candidate loss | 1 | 1 |
| ACK obligation | `bfd34bc6b6895906`.  Every candidate thinks an ACK is overdue at `now=3309000us`.  Model accounting, after candidate loss.  Not ngtcp2 being late (TRIAGE, the obligation note) | 1 | 3 |
| Unclassified | `405f42ebc91f5bc1`.  One exhaustive step: ngtcp2 returns success with no callbacks on `DATA_BLOCKED v=2`, `STOP_SENDING id=61`, `RESET_STREAM id=63`, and both candidates permit only `STREAM_LIMIT_ERROR` (4).  The same signature was A2's "observed OK" bucket on 2026-09-19; this input is not that frame.  `conn_recv_stop_sending` and `conn_recv_reset_stream` do contain the §4.6 limit check, and the return here was 0, so this step is not a confirmed bypass | 1 | 1 |

The 59 transport-parameter disagreements are the raw corpus bytes fed to
`quic_h_params_status` and to `ngtcp2_transport_params_decode`, compared only
on whether decoding succeeds.  They are not tied to a spec sentence.

## G. SHOULDs ngtcp2 does not follow, corpus replay of 2026-09-21

Same 2456 inputs, `out/endpoint_diff` after the receive-side recommendation
check.  10086 sends and 14340 receives were asked.  None of these is a
mismatch: every step was accepted.  A generic error code (§11) counts as
following the SHOULD.

Receive counts use the first candidate.  An ACK of a packet that candidate
has not recorded as sent is counted under §13.1 even when a later candidate
would have recorded the send.

| Count | What ngtcp2 did | Recommendation |
|---:|---|---|
| 340 | Accepted an ACK whose largest packet number is one this side has not sent | §13.1, line 5030: that SHOULD be `PROTOCOL_VIOLATION` when it can be detected (`recv:ackUnsent`) |
| 97 | Sent `RESET_STREAM` with an application error code other than the one from `STOP_SENDING` | §3.5, line 1263: the code SHOULD be copied; any application error code is still allowed (`stream:RESET_STREAM`) |
| 58 | Accepted a `STREAM` or `RESET_STREAM` that changes a known final size | §4.5, lines 1517 and 1520: that SHOULD be `FINAL_SIZE_ERROR` (`recv:finalSize`) |
| 45 | Sent `DATA_BLOCKED` while not at the connection data limit | §4.1, line 1375: send it when sent data has reached the peer's limit (`streamTable:DATA_BLOCKED`) |
| 30 | Sent `NEW_CONNECTION_ID` again after that frame had been acknowledged | §13.3, line 5461: SHOULD avoid retransmitting information once it is acknowledged (`retransmitAcked:NEW_CONNECTION_ID`) |
| 4 | Sent `STREAM` again after that frame had been acknowledged | the same sentence (`retransmitAcked:STREAM`) |
| 2 | Sent a packet with no ACK while at least two ack-eliciting packets were outstanding | §13.2.2, line 5163: SHOULD send an ACK after two ack-eliciting packets (`twoAckEliciting`) |

## What is not covered

Migration and second paths; loss recovery and congestion control; Retry and
version negotiation against a live peer; 0-RTT; key update; receive-side
coalescing under ngtcp2 (its stub AEAD cannot fail); any input found under
quiche's own coverage — `quiche_diff` has only replayed a corpus evolved under
ngtcp2.
