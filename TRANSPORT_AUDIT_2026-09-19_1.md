# Transport audit: recommendations after validating DIFFERENCES.md

Date: 2026-09-19. Baseline: Lean `4448547`, ngtcp2 `3c23148e`, and
quiche `d3e21813` (local patched checkout). Specification:
`spec/draft-ietf-quic-transport-34.txt`.

These recommendations follow the validation recorded in [DIFFERENCES.md](DIFFERENCES.md).
That pass included 16 focused runs against existing harness binaries, a Lean
evaluation of CRYPTO buffering, and source/spec review. The binaries were not
rebuilt, and historical corpus counts and digest-join totals were not replayed.
This document proposes changes; it does not record their implementation.

## 1. Restrict datagram dropping to justified conditions — highest priority

**Finding:** B3. `DatagramSize.Step.datagramDiscard` permits dropping every
received datagram, and endpoint composition preserves that alternative.
Section 14 permits dropping datagrams that fail size constraints, not arbitrary
otherwise-valid datagrams. The current over-approximation masks mandatory
processing and error requirements, including A2's repeated-sequence
NEW_CONNECTION_ID case.

**Recommended change:** Make the size-related discard alternative conditional
on a failed size constraint. If the event lacks the information needed to
decide this, enrich the event or move the decision to the layer that has it.
Preserve independently justified discard cases at their appropriate layers:
failed decryption, duplicates, packets below a retained packet-number window
(§12.3), and other explicit specification exceptions. Do not replace the
blanket alternative by forbidding all discretionary drops.

**Validation:** Show that an authenticated, otherwise-processable malformed
NEW_CONNECTION_ID cannot evade the required error through the size component.
Also verify that size-invalid datagrams and explicitly permitted packet drops
retain their allowed outcomes, and that skipping a coalesced packet preserves
processing of subsequent packets where §12.2 requires it.

## 2. Model CRYPTO resource policies beyond payload-byte count — high priority

**Finding:** B1. `Handshake.cryptoOutcomes` already permits
CRYPTO_BUFFER_EXCEEDED in specific cases. The remaining mismatch is its
resource accounting: `Handshake.bufferedBytes` counts only bytes held in
sparse ranges. A 16-byte frame at offset 196611 therefore costs 16 bytes in
the model and does not exceed its default 4096-byte limit. Both engines reject
the focused input with error 13; their checks include offset or reordering-span
limits.

**Recommended change:** Introduce an explicit resource-policy abstraction that
can represent buffering-span and storage constraints as well as payload-byte
limits. Constrain permitted policies by §7.5's minimum buffering support.
Determine the precise admissibility conditions from the text before treating
any particular implementation cutoff as conformant. Do not simply copy either
engine's absolute offset limit or permit arbitrary buffer errors.

Keep the phase-dependent outcomes: buffering failure during the handshake
requires expansion or the specified error; after the handshake, the model can
also discard the CRYPTO frame and future CRYPTO frames. That latter outcome
must still allow acknowledgment of the containing packet. It is not a
packet-level drop.

**Validation:** Exercise sparse high-offset input, contiguous delivery,
out-of-order buffering around the required minimum, and both handshake phases.
Check that permitted post-handshake CRYPTO discard leaves the containing
packet processed for acknowledgment purposes.

## 3. Represent implicit stream opening without enumerating every stream

**Finding:** B4. `StreamTable.openedEffects` uses `List.range'` to enumerate
implicitly opened streams. The function is total, but legal large stream IDs
make execution impractical. The harness skips those steps and stops tracking
the affected runs.

**Recommended change:** Use counters or ranges to represent implicit opening
and a compact semantic effect where necessary. Preserve the requirement that
using a stream ID opens lower-numbered streams of the same type. Avoid eager
per-stream API notifications: the protocol requirement does not require that
callback representation.

**Validation:** Check stream existence and limit enforcement for small and
large IDs, including IDs near the encoding bound. Verify that evaluating an
error outcome does not first enumerate all implicitly opened streams. Restore
harness coverage only once the relevant evaluation paths are tractable.

## 4. Map stream completion independently of callback names

**Finding:** B6. Both engines report a zero-length read carrying FIN for the
focused empty-STREAM example. The model emits completion without newly
available data. `Stream/Recv.lean` already distinguishes those semantic facts;
the harness maps completion to `stream_close` rather than a FIN-bearing read.
This is an API observation mismatch, not an established transport-spec defect.

**Recommended change:** Preserve separate semantic effects for newly available
bytes and reaching the final size. Adapt the observation layer so a FIN-bearing
empty read can correspond to completion without inventing newly delivered
bytes. Avoid requiring all implementations to expose the same callbacks.

**Validation:** Compare empty FIN, data plus FIN, and repeated FIN delivery;
ensure the mapping does not admit duplicate byte delivery or erase completion.

## 5. Changes to defer pending stronger evidence

| Finding | Recommendation |
|---|---|
| B2: DATA_BLOCKED / STREAMS_BLOCKED report limits never granted | Resolve whether the report itself constitutes a violation under §4.1 or §4.6 before adding error alternatives. Implementation disagreement does not establish that both behaviors conform. |
| A4: FINAL_SIZE_ERROR for STREAM_DATA_BLOCKED beyond final size | Keep the conformance question open. The cited final-size paragraph does not directly prescribe this case, but its silence alone does not prohibit the error. Do not add it solely to match ngtcp2. |
| B5: ACK frames refused by the retained candidates | Keep the received-packet requirement in `AckFrameSendable`. Investigate candidate loss, handshake bookkeeping, packet-number mapping, and other state drift before changing the rule. |
| B7: frames rejected for streams absent from model state | Keep the stream-existence check while verifying that opening events reach the model and valid candidates survive. A missing synthesized event is not evidence that the check is wrong. |
| B8: acknowledged-stream callbacks absent | Add ACK-to-stream delivery bookkeeping only if that API/recovery behavior is intended model scope. Its absence is not by itself a draft-34 transport violation. |

## 6. Harness work needed to interpret model results

Candidate truncation can remove a valid execution and create a false-positive
mismatch. Investigate cap exhaustion and candidate selection before weakening
rules to accommodate later send refusals. Make comparison results distinguish
exhaustive rejection from rejection after candidate loss.

Correct or explicitly account for handshake state, packet-number mapping,
synthesized stream-opening events, and connection-ID issuance differences.
Ensure that obligation checks give the implementation a send opportunity before
classifying an overdue ACK as a violation. These are harness changes and should
not be implemented as extra latitude in the transport model.

## Recommended order

1. Narrow unconditional datagram dropping (B3).
2. Define and implement admissible CRYPTO resource policies (B1).
3. Make implicit stream opening compact and executable (B4).
4. Improve completion observation mapping (B6).

For each change, validate both the behavior the specification permits and the
behavior the revised rule must reject. Address candidate tracking and state
synchronization alongside this work so subsequent mismatches remain useful
evidence. Leave B2 and A4 unresolved until their normative interpretations are
supported independently of implementation agreement.

## Implementation status (added 2026-09-19, after the fact)

Recommendations 1–4 and the §6 harness items were implemented the same day;
section 5 was left deferred as recommended.  Disposition: `PLAN.md` §4k.
Per-finding detail, the validation each change was given, and the corpus replay
before and after: `DIFFERENCES.md`.  The text above is unchanged.
