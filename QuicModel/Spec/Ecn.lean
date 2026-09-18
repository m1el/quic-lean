import QuicModel.Spec.Ecn.Theorems

/-
  WP14 (b): §13.4 Explicit Congestion Notification.

  Text: draft-ietf-quic-transport-34, lines 5475–5639 — §13.4.1 (reporting ECN
  counts), §13.4.2 (ECN validation), §13.4.2.1 (receiving ACK frames with ECN
  counts) and §13.4.2.2 (validation outcomes) — plus the definition of the three
  counts in §19.3.2, line 7407, which no other package owns
  (`Spec/Ack.lean` explicitly defers the ECN counts to this file).

  RFC 9002 stays abstract: whether a packet was newly acknowledged or deemed
  lost arrives as an event, together with the ECN marking the endpoint applied
  to it when it was sent.

  Exported for the composed endpoint (WP12):
  * `MayMarkEcn` / `mayMarkEcn` — §13.4.2.2's "It stops setting the ECT
    codepoint in IP packets that it sends" is a property of the *IP* header,
    and `Spec.OutDatagram` has no ECN field, so it cannot be a
    `MaySendDatagram` rule.  It is a free-standing predicate over the state and
    a `marked : Bool` (NOTE 6, and the `Core` request in the final report).
  * `feedbackOwed` / `FeedbackObligationMet` — §13.4.1 line 5504's MUST is an
    obligation to *send* feedback, which no single step can force.

  Split across:
  * `Ecn/Basic.lean`     part 1: `Codepoint`, `Mark`, `Phase`, `State`, events
  * `Ecn/Step.lean`      parts 2-5: `failsValidation`, `Step`, `outcomes`, `Inv`
  * `Ecn/Send.lean`      parts 6-7: `MaySendPacket`, `MayMarkEcn`, the component
  * `Ecn/Theorems.lean`  parts 8-9: named theorems and scenarios
-/

/-! ## 10. Coverage and notes

Assigned range: lines 5475–5639 (§13.4), plus §19.3.2, line 7407, which defines
the three counts and which `Spec/Ack.lean` explicitly leaves to this file.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §13.4 (5477) | "QUIC endpoints can use Explicit Congestion Notification (ECN) [RFC3168] to detect and respond to network congestion." | permission: `Mark.notEct` is always available (`Step.sentPacket` accepts any mark) and `MayMarkEcn s false` always holds |
| §13.4 (5481) | "Endpoints react to reported congestion by reducing their sending rate in response, as described in [QUIC-RECOVERY]." | out of scope: congestion response is RFC 9002 |
| §13.4 (5493) | "To enable ECN, a sending QUIC endpoint first determines whether a path supports ECN marking and whether the peer reports the ECN values in received IP headers" | `Phase`, `Event.beginValidation`, `Phase.marksPackets` |
| §13.4.1 (5500) | "If an endpoint does not implement ECN support or does not have access to received ECN fields, it does not report ECN counts for packets it receives." | `State.reportsEcn`, `State.recordRecv`, `Inv`, `recordRecv_ect0` |
| §13.4.1 (5504) | "Even if an endpoint does not set an ECT field on packets it sends, the endpoint MUST provide feedback about ECN markings it receives, if these are accessible." | `feedbackOwed` / `FeedbackObligationMet` (a run-level obligation, NOTE 2) and `Recommended.reportsWhenOwed` |
| §13.4.1 (5506) | "Failing to report the ECN counts will cause the sender to disable use of ECN for this connection." | informative: it is the consequence of `Step.ackFail` on the *peer's* instance (line 5583) |
| §13.4.1 (5509) | "On receiving an IP packet with an ECT(0), ECT(1) or CE codepoint, an ECN-enabled endpoint accesses the ECN field and increases the corresponding ECT(0), ECT(1), or CE count." | `Step.recvPacket` / `State.recordRecv`, `recordRecv_ect0`, `counts_mono` |
| §13.4.1 (5514) | "Each packet number space maintains separate acknowledgment state and separate ECN counts." | `State.space`, one instance per space (NOTE 1); `MaySendPacket` gates on `p.ptype.space` |
| §13.4.1 (5515) | "Coalesced QUIC packets (see Section 12.2) share the same IP header so the ECN counts are incremented once for each coalesced QUIC packet." | `Event.recvPacket` is per *QUIC packet*, not per datagram, so a coalesced datagram raises one event per packet, each with the datagram's codepoint |
| §13.4.1 (5519) | the Initial/Handshake/1-RTT coalescing example | example, no normative keyword: it is line 5515 worked through; three instances each see one `recvPacket` |
| §13.4.1 (5524) | "ECN counts are only incremented when QUIC packets from the received IP packet are processed.  As such, duplicate QUIC packets are not processed and do not increase ECN counts" | `Event.recvPacket`'s `processed` flag, `recordRecv_duplicate`; which packets are duplicates is `Spec/Ack.lean` (§12.3) |
| §13.4.2 (5532) | "To ensure connectivity in the presence of such devices, an endpoint validates the ECN counts for each network path and disables use of ECN on that path if errors are detected." | `Phase`, `Step.ackFail` / `Step.lostFail`, `MayMarkEcn`; per-path composition is WP12's (NOTE 1) |
| §13.4.2 (5539) | "The endpoint sets an ECT(0) codepoint in the IP header of early outgoing packets sent on a new path to the peer ([RFC8311])." | `Phase.marksPackets` (`testing` marks), `Event.sentPacket`, `State.restart` |
| §13.4.2 (5549) | "The endpoint monitors whether all packets sent with an ECT codepoint are eventually deemed lost (Section 6 of [QUIC-RECOVERY]), indicating that ECN validation has failed." | `allMarkedLost`, `Step.lostFail` (preferred) with `Step.lostOk` also permitted (NOTE 5) |
| §13.4.2 (5553) | "If an endpoint has cause to expect that IP packets with an ECT codepoint might be dropped …, the endpoint could set an ECT codepoint for only the first ten outgoing packets on a path, or for a period of three PTOs." | permission: `Event.testingEnded` may be raised at any point, so any testing-period length conforms |
| §13.4.2 (5557) | "If all packets marked with non-zero ECN codepoints are subsequently lost, it can disable marking on the assumption that the marking caused the loss." | permission: `Step.lostFail`; `Step.lostOk` is the alternative the "can" preserves |
| §13.4.2 (5561) | "An endpoint thus attempts to use ECN and validates this for each new connection, when switching to a server's preferred address, and on active connection migration to a new path." | `Event.beginValidation` with `Trigger`, `State.restart`, `beginValidation_restarts` |
| §13.4.2 (5566) | "Other methods of probing paths for ECN support are possible, as are different marking strategies." | permission: no `Step` constructor forces a particular probing schedule, and `Step.lostOk` keeps "do not fail" available where the text only *indicates* failure (NOTE 5) |
| §13.4.2 (5567) | "Implementations MAY use other methods defined in RFCs; see [RFC8311]." | permission: `Event.testingEnded` and `Event.beginValidation` are unconstrained in when they may be raised, and `Mark` admits ECT(1) as well as ECT(0) |
| §13.4.2 (5568) | "Implementations that use the ECT(1) codepoint need to perform ECN validation using the reported ECT(1) counts." | `Mark.ect1`, `State.sentEct1`, the ECT(1) half of `failsValidation` and `mayFailRemark` |
| §13.4.2.1 (5575) | "An endpoint that receives an ACK frame with ECN counts therefore validates the counts before using them.  It performs this validation by comparing newly received counts against those from the last successfully processed ACK frame." | `State.peerEct0/peerEct1/peerCe`, `State.recordCounts` (updated only on a *successful* validation), `failsValidation` |
| §13.4.2.1 (5583) | "If an ACK frame newly acknowledges a packet that the endpoint sent with either the ECT(0) or ECT(1) codepoint set, ECN validation fails if the corresponding ECN counts are not present in the ACK frame." | `failsValidation`, `none` branch; `Step.ackFail` |
| §13.4.2.1 (5589) | "ECN validation also fails if the sum of the increase in ECT(0) and ECN-CE counts is less than the number of newly acknowledged packets that were originally sent with an ECT(0) marking.  Similarly, … ECT(1) …" | `failsValidation`, `some` branch; `Step.ackFail` (NOTE 4) |
| §13.4.2.1 (5606) | "It is therefore possible for the total increase in ECT(0), ECT(1), and ECN-CE counts to be greater than the number of packets that are newly acknowledged by an ACK frame.  This is why ECN counts are permitted to be larger than the total number of packets that are acknowledged." | permission, and a negative requirement: `failsValidation` has no upper-bound check against `NewlyAcked.total`, so a larger increase never fails |
| §13.4.2.1 (5612) | "Validating ECN counts from reordered ACK frames can result in failure.  An endpoint MUST NOT fail ECN validation as a result of processing an ACK frame that does not increase the largest acknowledged packet number." | `increasesLargest`, `skipValidation`, `Step.ackNotValidated`, `no_fail_on_reordered_ack` |
| §13.4.2.1 (5617) | "ECN validation can fail if the received total count for either ECT(0) or ECT(1) exceeds the total number of packets sent with each corresponding ECT codepoint." | `mayFailRemark`, `Step.ackRemarkFail`; a MAY, so `Step.ackOk` stays available |
| §13.4.2.2 (5626) | "If validation fails, then the endpoint MUST disable ECN.  It stops setting the ECT codepoint in IP packets that it sends" | `State.fail`, `Effect.disableEcn`, `failure_disables`, `MayMarkEcn` / `mayMarkEcn` (NOTE 6) |
| §13.4.2.2 (5630) | "Even if validation fails, an endpoint MAY revalidate ECN for the same path at any later time in the connection.  An endpoint could continue to periodically attempt validation." | `Event.beginValidation .revalidation`, `failed_persists` (the MAY is the *only* exit from `failed`), `beginValidation_restarts` |
| §13.4.2.2 (5634) | "Upon successful validation, an endpoint MAY continue to set an ECT codepoint in subsequent packets it sends, with the expectation that the path is ECN-capable." | `Step.ackCapable` with `Step.ackOk` also permitted; `Phase.marksPackets .capable = true` |
| §13.4.2.2 (5636) | "Network routing and path elements can however change mid-connection; an endpoint MUST disable ECN if validation later fails." | `Step.ackFail` / `Step.ackRemarkFail` / `Step.lostFail` are not conditioned on the phase, so they apply from `capable` too (the last §13.4.2.1 example) |
| §19.3.2 (7407) | "ECT0 Count: A variable-length integer representing the total number of packets received with the ECT(0) codepoint in the packet number space of the ACK frame" (and ECT1, CE) | `ackEcnOk`, `MaySendPacket`, `ack_ecn_counts_exact` |
| §19.3.2 (7419) | "ECN counts are maintained separately for each packet number space." | `State.space`, as line 5514 |
| §13.2.1 (5112) | "packets marked with the ECN Congestion Experienced (CE) codepoint in the IP header SHOULD be acknowledged immediately" | out of range (it is §13.2.1, `Spec/Ack.lean`'s), where it is recorded as "advice, not checkable here: no event carries an IP ECN codepoint".  `Event.recvPacket` now does carry one, so WP12 can discharge it by pairing the two components (NOTE 7) |
| Appendix A.4 (10236) | the sample validation algorithm | informative and out of range; only its four state names (`Phase`) and the `unknown` → `capable` transition are used, both as permissions (NOTE 3) |

NOTES

1. **One instance per packet number space, but failure is per path.**  §13.4.1,
   line 5514 and §19.3.2, line 7419 make the counts, the peer's reported counts
   and the ACK frames that carry them per packet number space, and §13.4.2.1's
   whole comparison is between two ACK frames of the same space, so the
   component is per space (`State.space`, like `Spec/Ack.lean` NOTE 8).
   §13.4.2, line 5532, on the other hand, validates "for each network path" and
   line 5626 disables ECN for the path, not for one space.  Composition is
   therefore WP12's, and it must be a *conjunction*: a datagram may carry an ECT
   codepoint only if `MayMarkEcn` holds in **every** space's instance, and
   `Event.beginValidation` must be delivered to all three at once when the path
   changes.  Nothing here forces that; it is stated for the integrator.

2. **§13.4.1's MUST is an obligation to send.**  Line 5504 requires feedback to
   be *provided*, which no per-step relation can force, exactly as with
   §13.2.1's acknowledgment deadline.  `MaySendPacket` therefore does not reject
   an ACK frame without counts — that would be stricter than the text, since
   line 5500 permits an endpoint to report nothing at all and the text's own
   sanction (line 5506) is that the peer disables ECN, not that the frame is
   illegal.  The MUST is exported as `feedbackOwed` plus the run predicate
   `FeedbackObligationMet`, and restated per frame in `Recommended`.

3. **Appendix A.4 is informative.**  §13.4.2, line 5563 points at it as "one
   possible algorithm" and A.4 line 10255 says "Endpoints can implement
   different methods".  Its four state names are used because §13.4.2's own
   prose needs the distinction between "we are marking and have not yet learned
   anything" and "we have learned the path is capable", but every transition
   taken from A.4 rather than from §13.4 is a *permission*:
   `Event.testingEnded` may be raised at any point or never, and `ackCapable`
   always has `ackOk` beside it.  Only the failure transitions come from §13.4
   itself.

4. **"Counts decreasing" is not a separate rule in draft-34.**  §13.4.2.1 has no
   sentence saying that a decrease in a reported count is a failure; what it has
   is line 5589's comparison of the *increase* against the newly acknowledged
   marked packets.  Written over the integers that comparison is
   `(e.ect0 - peer.ect0) + (e.ce - peer.ce) < newly.ect0`, and `failsValidation`
   encodes it as the equivalent `Nat` inequality
   `e.ect0 + e.ce < peer.ect0 + peer.ce + newly.ect0`, which is *not* the
   truncated-subtraction reading.  Consequently a decrease does fail whenever the
   frame newly acknowledges at least one marked packet, and does not fail when it
   acknowledges none — which is what the text says, and which is why the stored
   peer counts are **not** monotone: the last examples of `Ecn/Theorems.lean`
   exhibit a state whose `peerEct0` drops from 5 to 0 through an ACK frame that
   neither check rejects, because a large CE count absorbs the difference while
   no ECT-marked packet is newly acknowledged.  Adding a monotonicity check
   would be stricter than draft-34 and is deliberately omitted; the *received*
   counts (theorem (a), `counts_mono`) are monotone, because §19.3.2, line 7407
   makes them totals.

5. **"All marked packets lost" is fail-preferred, not fail-only.**  Line 5549
   says the condition indicates failure and line 5626 then makes disabling
   mandatory, but line 5557 words the same rule as "it *can* disable marking",
   and line 5566 permits other probing methods entirely.  `Step.lostFail` is
   therefore listed first (so `component.step` disables ECN) while `Step.lostOk`
   remains permitted, per the BRIEF's rule that a permission is an additional
   outcome and never the only one.  `allMarkedLost` also requires at least one
   marked packet to have been sent, so a path on which nothing was ever marked
   never fails this way.

6. **`Core` has nowhere to put "this datagram is ECN-marked".**  §13.4.2.2,
   line 5626 is a rule about the IP header of an outgoing packet, and
   `Spec.OutDatagram` records size, destination and a PMTU-probe flag but no ECN
   codepoint.  `MayMarkEcn : State → Bool → Prop` is therefore a free-standing
   predicate rather than `MaySendDatagram`, and `Core` is left untouched as the
   BRIEF requires.  The change `Core` would need is recorded in the final
   report.

7. **The CE-acknowledgment SHOULD of §13.2.1.**  Line 5112 ("packets marked with
   the ECN Congestion Experienced (CE) codepoint … SHOULD be acknowledged
   immediately") is outside this package's range and `Spec/Ack.lean` recorded it
   as unmodellable because no event there carries an IP codepoint.
   `Event.recvPacket` here does, so WP12 can discharge it by raising
   `Ack.Event.recvPacket` and `Ecn.Event.recvPacket` from the same datagram and
   requiring `Ack.Recommended.immediate` whenever the codepoint was `.ce`.  No
   change is made to either component for it.

8. **A failing ACK frame does not update the baseline.**  §13.4.2.1, line 5577
   compares against "the last *successfully* processed ACK frame", so
   `Step.ackFail` and `Step.ackRemarkFail` leave `peerEct0/peerEct1/peerCe` and
   `largestAcked` alone and change only the phase.  Since the phase is then
   `failed`, and every later ACK takes `Step.ackNotValidated` until
   `Event.beginValidation`, the stale baseline is never read — but it is
   preserved rather than zeroed so that a revalidation starts from the counts
   the peer last reported, as Appendix A.4, line 10262 describes.

9. **`Event.recvAck` carries what RFC 9002 knows.**  "Newly acknowledged" and
   "the markings that were applied to those packets" (line 5578) are facts about
   the sender's record of packets in flight, which is RFC 9002's and out of
   scope; they are supplied on the event as `NewlyAcked`.  `NewlyAcked.total` is
   carried only so that line 5608's "permitted to be larger than the total
   number of packets that are acknowledged" can be seen to be respected — no
   rule reads it, which is the point.
-/
