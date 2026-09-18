import QuicModel.Spec.Retransmission.Theorems

/-
  WP14 (a): §13.3 Retransmission of Information — the *cross-cutting* rules.

  Text: draft-ietf-quic-transport-34, lines 5325–5474.

  Loss detection and congestion control are [QUIC-RECOVERY] (RFC 9002) and stay
  abstract: `Event.lost` says only that a packet was declared lost, and
  `Event.acked` that one was acknowledged.  What this component owns is what the
  transport text says happens *to the information* those packets carried.

  The per-frame send rules the individual frame types have are owned elsewhere
  and are not repeated here (components compose by conjunction):

  * `Spec/Stream/Send.lean`  — no STREAM data after RESET_STREAM (§3.1, §3.5).
  * `Spec/StreamTable.lean`  — §13.3 line 5403: a blocked frame carries the
    limit in force when it is transmitted.
  * `Spec/PathValidation.lean` — §8.2.2 line 3205: at most one PATH_RESPONSE per
    received PATH_CHALLENGE, which is §13.3 line 5418's "sent just once".
  * `Spec/ConnIds/*.lean`     — NEW_CONNECTION_ID / RETIRE_CONNECTION_ID repeats.
  * `Spec/Ack.lean`           — ACK frame contents (§13.2).
  * `Spec/Termination*.lean`  — CONNECTION_CLOSE, which §13.3 line 5367 hands to
    §10 wholesale.

  Exported for the composed endpoint (WP12):
  `Owes` / `owes` / `MustRetransmit` / `RepairObligationMet` — §13.3 line 5445's
  "MUST be retransmitted until it is acknowledged" is an obligation to *send*
  something, which no single step can force, exactly like `Ack.ackOverdue`.

  Split across:
  * `Retransmission/Basic.lean`     parts 0-2: helpers, `Info`, `State`, `Step`
  * `Retransmission/Step.lean`      parts 3-8: `outcomes`, `Inv`, send side,
    the `Component`, and `Owes` / `RepairObligationMet`
  * `Retransmission/Theorems.lean`  parts 9-10: named theorems and scenarios
-/

/-! ## 11. Coverage and notes

Assigned range: lines 5325–5474 (§13.3).  §13.4 is `Spec/Ecn.lean`.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §13.3 (5327) | "QUIC packets that are determined to be lost are not retransmitted whole.  The same applies to the frames that are contained within lost packets." | `Event.lost` produces `Effect.repair` per *information item*, never a packet; there is no "resend packet" event at all |
| §13.3 (5332) | "New frames and packets are used to carry information that is determined to have been lost.  In general, information is sent again when a packet containing that information is determined to be lost and sending ceases when a packet containing that information is acknowledged." | `Step.lost` / `State.afterLost` / `State.newlyOwed`; `Step.acked` / `State.afterAcked` |
| §13.3 (5338) | "Data sent in CRYPTO frames is retransmitted according to the rules in [QUIC-RECOVERY], until all data has been acknowledged." | `State.repairable` (`.crypto`), `MustRetransmit`; the *rules* are RFC 9002, out of scope |
| §13.3 (5339) | "Data in CRYPTO frames for Initial and Handshake packets is discarded when keys for the corresponding packet number space are discarded." | `Step.keysDiscarded` / `State.afterKeysDiscarded`; the key schedule itself is WP11 |
| §13.3 (5343) | "Application data sent in STREAM frames is retransmitted in new STREAM frames unless the endpoint has sent a RESET_STREAM for that stream.  Once an endpoint sends a RESET_STREAM frame, no further STREAM frames are needed." | `State.repairable` (`.streamData`), `supersededByReset`; the *prohibition* on STREAM after RESET_STREAM is §3.1/§3.5 and belongs to `Spec/Stream/Send.lean` |
| §13.3 (5348) | "ACK frames carry the most recent set of acknowledgments and the acknowledgment delay from the largest acknowledged packet" | `State.repairable .ack = false`; the contents of an ACK frame are `Spec/Ack.lean` |
| §13.3 (5350) | "Delaying the transmission of packets containing ACK frames or resending old ACK frames can cause the peer to generate an inflated RTT sample or unnecessarily disable ECN." | informative, no normative keyword: the consequence of the previous sentence; `State.repairable .ack = false` is the behaviour it argues for |
| §13.3 (5355) | "Cancellation of stream transmission, as carried in a RESET_STREAM frame, is sent until acknowledged or until all stream data is acknowledged by the peer" | `State.repairable` (`.resetStream`), `Step.sendDataAcked`, `MustRetransmit` |
| §13.3 (5359) | "The content of a RESET_STREAM frame MUST NOT change when it is sent again." | `MaySend` / `State.resetContent` / `recordResets`; also `Stream.Send.maySendReset` (WP2 owns the phase-based form) |
| §13.3 (5362) | "Similarly, a request to cancel stream transmission, as encoded in a STOP_SENDING frame, is sent until the receiving part of the stream enters either a "Data Recvd" or "Reset Recvd" state" | `State.repairable` (`.stopSending`), `Step.recvPhase`, `MustRetransmit` |
| §13.3 (5367) | "Connection close signals, including packets that contain CONNECTION_CLOSE frames, are not sent again when packet loss is detected, but as described in Section 10." | `State.repairable .connectionClose = false`, `never_owed`; the §10 rules that *do* apply are `Spec/Termination/Send.lean` (`MaySendPacket` in the closing state) |
| §13.3 (5381) | "The current connection maximum data is sent in MAX_DATA frames.  An updated value is sent in a MAX_DATA frame if the packet containing the most recently sent MAX_DATA frame is declared lost, or when the endpoint decides to update the limit." | `Info.maxData` (value dropped: NOTE 2), `State.repairable`, `State.newlyOwed`'s `lastSent` test ("most recently sent") |
| §13.3 (5384) | "Care is necessary to avoid sending this frame too often as the limit can increase frequently" | advice, not checkable here: "too often" is a rate over a run, and the model has no send schedule |
| §13.3 (5389) | "The current maximum stream data offset is sent in MAX_STREAM_DATA frames.  Like MAX_DATA, an updated value is sent when the packet containing the most recent MAX_STREAM_DATA frame for a stream is lost or when the limit is updated" | `Info.maxStreamData`, `State.repairable`, `lastSent` |
| §13.3 (5393) | "An endpoint SHOULD stop sending MAX_STREAM_DATA frames when the receiving part of the stream enters a "Size Known" or "Reset Recvd" state." | `Recommended.maxStreamDataStopped`; also `Stream.Recv.RecommendedSend` |
| §13.3 (5397) | "The limit on streams of a given type is sent in MAX_STREAMS frames.  Like MAX_DATA, an updated value is sent when a packet containing the most recent MAX_STREAMS for a stream type frame is declared lost" | `Info.maxStreams`, `State.repairable`, `lastSent` |
| §13.3 (5403) | "Blocked signals are carried in DATA_BLOCKED, STREAM_DATA_BLOCKED, and STREAMS_BLOCKED frames.  DATA_BLOCKED frames have connection scope, STREAM_DATA_BLOCKED frames have stream scope, and STREAMS_BLOCKED frames are scoped to a specific stream type." | `BlockedScope`, `Info.blockedScope` |
| §13.3 (5406) | "New frames are sent if packets containing the most recent frame for a scope is lost, but only while the endpoint is blocked on the corresponding limit." | `State.repairable` (blocked cases), `Step.blockedChanged`, `Recommended.blockedOnlyWhileBlocked` (NOTE 5) |
| §13.3 (5409) | "These frames always include the limit that is causing blocking at the time that they are transmitted." | `Spec/StreamTable.lean` `MaySend` (WP9 owns it); not repeated here |
| §13.3 (5412) | "A liveness or path validation check using PATH_CHALLENGE frames is sent periodically until a matching PATH_RESPONSE frame is received … PATH_CHALLENGE frames include a different payload each time they are sent." | `State.repairable .pathChallenge = false`, `never_owed`; the periodic retry is `Spec/PathValidation.lean` (§8.2.1) |
| §13.3 (5418) | "Responses to path validation using PATH_RESPONSE frames are sent just once." | `State.repairable .pathResponse = false`, `never_owed`; the MUST NOT form is §8.2.2 line 3205 in `Spec/PathValidation.lean` |
| §13.3 (5422) | "New connection IDs are sent in NEW_CONNECTION_ID frames and retransmitted if the packet containing them is lost.  Retransmissions of this frame carry the same sequence number value." | `Info.newConnectionId seq` (the sequence number *is* the identity), `State.repairable = true`; `Spec/ConnIds/Local.lean` owns that the sequence number determines the frame |
| §13.3 (5425) | "Likewise, retired connection IDs are sent in RETIRE_CONNECTION_ID frames and retransmitted if the packet containing them is lost." | `Info.retireConnectionId seq`, `State.repairable = true`; `Spec/ConnIds/Remote.lean` |
| §13.3 (5437) | "NEW_TOKEN frames are retransmitted if the packet containing them is lost.  No special support is made for detecting reordered and duplicated NEW_TOKEN frames other than a direct comparison of the frame contents." | `Info.newToken token`, `State.repairable = true` |
| §13.3 (5442) | "PING and PADDING frames contain no information, so lost PING or PADDING frames do not require repair." | `State.repairable .ping = .padding = false`, `never_owed` |
| §13.3 (5445) | "The HANDSHAKE_DONE frame MUST be retransmitted until it is acknowledged." | `State.repairable .handshakeDone = true`, `MustRetransmit`, `Owes` / `owes`, `RepairObligationMet` (NOTE 4) |
| §13.3 (5448) | "Endpoints SHOULD prioritize retransmission of data over sending new data, unless priorities specified by the application indicate otherwise" | advice, not checkable here: it orders two sends against each other, and this model has no send queue and no application priorities (§2.3 is out of scope) |
| §13.3 (5452) | "Even though a sender is encouraged to assemble frames containing up-to-date information every time it sends a packet, it is not forbidden to retransmit copies of frames from lost packets." | permission: `MaySend` never rejects a repeat (`maySend_resent`, `maySend_of_not_reset`) |
| §13.3 (5454) | "A sender that retransmits copies of frames needs to handle decreases in available payload size due to change in packet number length, connection ID length, and path MTU." | advice, no normative keyword: packet sizing is `Spec/DatagramSize.lean` (WP7) |
| §13.3 (5457) | "A receiver MUST accept packets containing an outdated frame, such as a MAX_DATA frame carrying a smaller maximum data than one found in an older packet." | send half: `maySend_outdated`.  Receive half is a MUST on *every other* component, discharged there: `Template.Step.maxStreamsStale`, `StreamTable` and `Stream.Recv` ignore stale limits rather than erroring, `ConnIds` accepts a repeated NEW_CONNECTION_ID (NOTE 6) |
| §13.3 (5461) | "A sender SHOULD avoid retransmitting information from packets once they are acknowledged.  This includes packets that are acknowledged after being declared lost" | `Recommended.notAlreadyAcked`, and `State.newlyOwed`'s `ackedInfo` test (NOTE 3) |
| §13.3 (5465) | "A sender can discard this information after a period of time elapses that adequately allows for reordering, such as a PTO …, or on other events, such as reaching a memory limit." | permission: `Event.discardHistory` / `Step.discardHistory`; *when* to do it is left free |
| §13.3 (5471) | "Upon detecting losses, a sender MUST take appropriate congestion control action.  The details of loss detection and congestion control are described in [QUIC-RECOVERY]." | `Effect.congestionControlAction`, emitted by `Step.lost` for every packet that was in flight; the action itself is RFC 9002, out of scope by assignment |

NOTES

1. **What "the packet was declared lost" means.**  Nothing in this component
   decides that a packet is lost; `Event.lost` is the report from RFC 9002's
   loss detection, and `Event.acked` the report from its acknowledgment
   processing.  `Step` is therefore total in the event: a `lost` or `acked` for a
   packet that is not in flight (already acknowledged, already declared lost, or
   never sent through this component) changes nothing and produces no effects.
   That is deliberate — line 5461 explicitly contemplates a packet being
   acknowledged *after* being declared lost, and this model must not treat the
   second report as an error.

2. **Value-carrying information drops its value.**  §13.3 distinguishes two
   kinds of bullet.  "Data sent in CRYPTO frames is retransmitted" (5338) and
   "Retransmissions of this frame carry the same sequence number value" (5424)
   are about a fixed piece of content.  "The current connection maximum data is
   sent in MAX_DATA frames.  An updated value is sent …" (5381) is about a scope
   whose current value is re-read at transmission time.  `Info` reflects exactly
   that: `Info.maxData`, `Info.maxStreamData id`, `Info.maxStreams dir` and the
   three blocked constructors carry no value, so re-sending MAX_DATA with a
   *different* value clears the same debt, which is what the text describes.
   The cost is that this component cannot see that a MAX_DATA with a new value
   is "new information" for the purposes of line 5333; see NOTE 3.

3. **"Once they are acknowledged" applies only to verbatim information.**  Read
   literally over `Info`, line 5461 would say that once *any* MAX_DATA has been
   acknowledged no MAX_DATA should ever be sent again, which is absurd — the
   next one carries a new limit.  `Info.isVerbatim` marks the constructors whose
   identity is their content, and both `State.newlyOwed` and
   `Recommended.notAlreadyAcked` are restricted to those.  The `lastSent` test
   does the corresponding work for the value-carrying constructors: only the
   most recent carrier of a scope creates a debt (lines 5381, 5389, 5397, 5406
   all say "the most recent"), so an older packet being declared lost after a
   newer one went out owes nothing.

4. **`owed` is bookkeeping; `MustRetransmit` is the obligation.**  Only four
   bullets of §13.3 say information is sent *until* something happens: CRYPTO
   (5338), RESET_STREAM (5355), STOP_SENDING (5362) and HANDSHAKE_DONE (5445,
   the section's only MUST about retransmission).  `RepairObligationMet` is
   stated for exactly those.  The other bullets say an updated value "is sent",
   which this model records so that `Effect.repair` is observable and so that
   `MaySend`-level components can see the debt, but which it does not turn into
   a liveness requirement — an endpoint that never re-sends a lost MAX_DATA
   loses throughput, not conformance.  Like `Ack.ackOverdue` this predicate
   binds nothing until WP12 supplies the run.

5. **"Only while blocked" is not a `MaySend` rule.**  Line 5406's clause
   restricts the *repair* of a blocked signal, not the sending of blocked frames
   in general: §19.12–§19.14 nowhere forbid a DATA_BLOCKED frame, and `MaySend`
   must never be stricter than the text (BRIEF).  It is therefore encoded twice
   in the places where it is exactly right — in `State.repairable`, which is
   about repair, and in `Recommended.blockedOnlyWhileBlocked`, which rejects
   nothing.  `Spec/StreamTable.lean` separately pins the *value* such a frame
   carries (line 5409).

6. **Line 5457 binds every other component, not this one.**  "A receiver MUST
   accept packets containing an outdated frame" is a prohibition on treating a
   stale frame as an error.  It is discharged wherever a stale frame is
   processed — `Template.Step.maxStreamsStale` ("MUST be ignored" as `.ok s []`,
   never `.error`), `StreamTable`, `Stream.Recv`, `ConnIds` — and this component
   only has to not make it false, which `maySend_outdated` records.  A reviewer
   checking line 5457 should read those `Step` relations, not this file.

7. **DATAGRAM frames are outside the assigned text.**  RFC 9221 postdates
   draft-34, so §13.3's list has no bullet for DATAGRAM.  `Info.datagramFrame`
   is classified as not repaired, following RFC 9221 §5 ("DATAGRAM frames …
   are not retransmitted upon loss detection"), and is flagged here rather than
   silently folded into one of §13.3's categories.

8. **One instance per connection, packets keyed by space.**  Unlike `Ack`, this
   component is not replicated per packet number space: §13.3's information is
   mostly connection-scoped (a stream's data, a connection ID, a token) and only
   CRYPTO data is per space.  Packets are therefore identified by a `PktId`
   carrying both the space and the number, and `Info.crypto` carries the space
   so that line 5339 can discard exactly the right data.

9. **`MaySendPacket` is the default.**  §13.3 has no rule about a packet as a
   whole: the one sentence that is about packets (line 5367, connection close)
   defers to §10, which `Spec/Termination/Send.lean` encodes as a
   `MaySendPacket`.  Adding a second, weaker copy here would only risk
   disagreeing with it.
-/
