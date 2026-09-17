# Transport conformance review

Reviewed against the supplied draft-ietf-quic-transport-34.txt. The root and
spec/ copies are byte-identical. This is a source review with executable
counterexamples, not exhaustive certification against the final RFC 9000.

## Assessment

The repository has a substantial wire-format model and several individually
proved transport components. It is not yet a complete transport specification.
The conspicuous missing part is stream semantics (WP2), with stream-table and
connection flow control (WP9) also absent. Handshake (WP11), migration (WP10),
endpoint composition (WP12), and behavioral differential checking (WP13) remain
unimplemented. PLAN.md describes these as future work; the actual module tree
and QuicModel.lean imports confirm their absence.

## Confirmed behavioral defects

1. **High: ACK deadlines can move later (§13.2.1).**
   Ack.State.record updates largestTime whenever a larger packet number arrives
   (Ack.lean:400), including non-ack-eliciting packets. ackDeadline uses that
   timestamp (Ack.lean:813), rather than the oldest outstanding ack-eliciting
   packet's arrival time. Receive ack-eliciting PN 0 at 0 µs, then
   non-ack-eliciting PN 1 at 24,000 µs with max_ack_delay = 25,000 µs: the
   calculated deadline becomes 49,000 µs, although PN 0 must be acknowledged by
   25,000 µs. Track the oldest outstanding obligation separately from the
   timestamp used to encode ACK Delay.

2. **High: a partial ACK clears every pending ACK obligation (§13.2.1).**
   Event.sentAck has no ACK ranges (Ack.lean:435); afterAckSent unconditionally
   clears ackElicitingPending and the counters (Ack.lean:411). After receiving
   ack-eliciting packets 0 and 1, maySend permits an ACK containing only PN 1.
   Recording sentAck then makes ackDeadline return none, despite PN 0 never
   having been acknowledged. Carry the actual acknowledged ranges in the event
   and retain obligations for omitted packets. A deadline predicate evaluated
   only when an ACK is sent also does not by itself enforce eventual ACK sending;
   composition needs a timed trace requirement.

3. **Medium: packet-number exhaustion has an off-by-one (§12.3).**
   maySendPacketNumber (Ack.lean:659) accepts pn ≤ 2^62 − 1. The draft requires
   closing without CONNECTION_CLOSE or further packets when the sending number
   reaches 2^62 − 1. It must reject that number, and the endpoint must implement
   the corresponding terminal transition. The comment explicitly defers closing
   to Termination, but there is no composed endpoint to enforce it.

All three behaviors are demonstrated by checked examples in
out/TransportAudit.lean. They concern the current predicates and transitions;
there is no implemented endpoint in which to reproduce a complete network trace.

## Missing transport behavior

| Area | Present | Missing / consequence |
|---|---|---|
| Streams, §§2–3, 4.1–4.6, 19.4–19.6, 19.8–19.14 | Frame codecs, offset overflow checks, StreamId helpers, stream-count template | Send/receive states, reassembly and delivery, FIN/RESET final-size consistency, STOP_SENDING behavior, stream direction/state errors, implicit stream opening, per-stream and connection credit accounting. |
| Handshake, §§7.1–7.3, 7.5 | Parameter codec/value validation; externally supplied crypto/key facts | CRYPTO reassembly, key lifecycle, handshake progression, connection-ID authentication, enforcement of 0-RTT transitions. TLS internals can remain abstract, but these transport obligations cannot. |
| Migration, §9 | CID management and path challenge/response components | Migration policy, preferred-address processing, address changes and CID/path coordination, enforcement of disable_active_migration. |
| Endpoint integration | Component interface and local proofs | Datagram-to-component dispatch, combining packet/datagram send constraints, error-to-close transitions, cross-component state invariants. |
| Behavioral differential verification | C connection trace generator | Lean endpoint oracle and trace comparison. Dump.lean exports wire functions only; existing wire fuzz results do not validate transport state machines. |
| §13.3 retransmission and §13.4 ECN | ACK range processing and ECN frame fields | Retransmission obligations and ECN validation are excluded by the ACK assignment. The RFC 9002 recovery algorithms are separable, but transport requirements in these sections still need explicit coverage or assumptions. |

For example, Frame.check accepts two individually well-formed STREAM frames
that establish conflicting final sizes; it has no state to detect that the
second must cause FINAL_SIZE_ERROR (§4.5). Similarly, parsing MAX_DATA and
initial_max_data does not implement connection flow control.

## Strengths and assurance limits

Implemented areas include frame/packet parsing and encoding, round-trip proofs,
frame legality, ACK ranges and duplicate tracking, transport-parameter value
rules, connection IDs, anti-amplification, path validation, termination, version
negotiation, and datagram size constraints. The coverage tables and cited rules
make these components reviewable. This review does not certify every rule in
those modules.

outcomes_iff proves agreement between the executable function and the Lean Step
relation; step_sound does not prove that Step correctly translates the prose.
The counterexamples above pass alongside all existing proofs. Likewise,
Component.MaySend is frame-level: standalone packet/datagram/trace predicates
must be wired into the eventual endpoint before their presence enforces anything.

The repository also includes later extensions (DATAGRAM and QUIC v2), so its
wire language is intentionally broader than draft-34. Exact final-RFC conformance
would additionally require a draft-to-RFC text comparison and a defined extension
profile; neither is established by these results.

## Validation

- `timeout 120 lake build`: passed, 61 jobs.
- `timeout 120 lake env lean out/TransportAudit.lean`: passed, four examples.
- No `sorry` or `axiom` declarations found under QuicModel/.
- No implementation files changed. Existing fuzzing numbers in FINDINGS.md were
  read as historical evidence, not rerun or presented as new results.

Priority: correct ACK accounting, implement streams and flow control, then
compose the endpoint and connect the behavioral oracle. Track each deferred
coverage-table entry to an implemented owner before claiming full coverage.
