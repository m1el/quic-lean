import QuicModel.Spec.StreamTable.Theorems

/-
  WP9 StreamTable, part 5 of 5: examples from the text (§9), the coverage table
  and the notes (§10).

  All the streams of one connection, as seen by one endpoint: stream creation
  and implicit opening (§2.1), the stream-count limits of §4.6, connection-level
  flow control (§4.1, §4.5, §19.9) and the routing of every stream-scoped frame
  to WP2's `Spec.Stream.component`.

  * `StreamTable/Defs.lean`    — §1 state, events, effects, routing vocabulary
  * `StreamTable/Step.lean`    — §2–§4 `Step`, `outcomes`, `outcomes_iff`
  * `StreamTable/Inv.lean`     — §5 `Inv`, `step_inv`
  * `StreamTable/Send.lean`    — §6 `MaySend`, §7 the `Component`
  * `StreamTable/Theorems.lean`— §8 named theorems
  * this file                  — §9 examples, §10 coverage and notes

  Supersedes `Spec/Template.lean`'s stream-count component (see NOTES).
-/
namespace Quic.Spec.StreamTable

/-! ## 9. Examples (scenarios from the text) -/

private def lim : Limits :=
  { maxData := 100, maxStreamDataBidiLocal := 100, maxStreamDataBidiRemote := 100,
    maxStreamDataUni := 100, maxStreamsBidi := 3, maxStreamsUni := 3 }

/-- A server that has advertised, and been told, the limits of `lim`. -/
private def srv : State := init .server lim lim

/-- Run a list of events through the reference implementation. -/
private def run (s : State) : List Event → State
  | [] => s
  | e :: es => run ((component.step s e).next s) es

-- §19.11, line 7813: "a server that receives a unidirectional stream limit of 3
-- is permitted to open stream 3, 7, and 11, but not stream 15."
example : component.step srv (.appOpenStream .uni) =
    .ok ((component.step srv (.appOpenStream .uni)).next srv) [.streamOpened ⟨3⟩] := by decide
example : (run srv [.appOpenStream .uni]).nextLocal .uni = ⟨7⟩ := by decide
example : (run srv [.appOpenStream .uni, .appOpenStream .uni]).nextLocal .uni = ⟨11⟩ := by decide
example : component.step (run srv [.appOpenStream .uni, .appOpenStream .uni, .appOpenStream .uni])
    (.appOpenStream .uni) = .drop := by decide

-- §2.1, line 718: a STREAM frame for client-initiated bidirectional stream 8
-- (index 2) opens streams 0 and 4 as well — one range effect, then the stream …
example : component.step srv (.stream ⟨8⟩ (.recv (.recvStream 0 5 false))) =
    .ok ((component.step srv (.stream ⟨8⟩ (.recv (.recvStream 0 5 false)))).next srv)
      [.streamsOpenedBelow ⟨0⟩ 2, .streamOpened ⟨8⟩,
       .stream ⟨8⟩ (.recv (.dataAvailable 5))] := by decide
-- The first frame for one of the implicitly opened streams says so
-- (`streamFirstUsed`: an API moment, not a second opening); the next does not.
example : component.step (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))])
      (.stream ⟨4⟩ (.recv (.recvStream 0 5 false))) =
    .ok (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false)),
                  .stream ⟨4⟩ (.recv (.recvStream 0 5 false))])
      [.streamFirstUsed ⟨4⟩, .stream ⟨4⟩ (.recv (.dataAvailable 5))] := by decide
example : component.step (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false)),
                                   .stream ⟨4⟩ (.recv (.recvStream 0 5 false))])
      (.stream ⟨4⟩ (.recv (.recvStream 5 5 false))) =
    .ok (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false)),
                  .stream ⟨4⟩ (.recv (.recvStream 0 5 false)),
                  .stream ⟨4⟩ (.recv (.recvStream 5 5 false))])
      [.stream ⟨4⟩ (.recv (.dataAvailable 10))] := by decide
-- Audit 2026-09-19, B4: the range is one effect however long it is, so a frame
-- naming a stream near the encoding bound (2^62 - 4 is client-initiated
-- bidirectional stream 2^60 - 1) is evaluated in constant time — both where it
-- breaks the limit we advertised (§4.6, line 1546) …
example : component.outcomes srv (.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false))) =
    [.error .streamLimitError] := by decide
-- … and where the limit allows it: every lower-numbered stream is opened.
private def srvWide : State := init .server { lim with maxStreamsBidi := 2 ^ 60 } lim
example : component.step srvWide (.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false))) =
    .ok ((component.step srvWide (.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false)))).next
          srvWide)
      [.streamsOpenedBelow ⟨0⟩ (2 ^ 60 - 1), .streamOpened ⟨2 ^ 62 - 4⟩,
       .stream ⟨2 ^ 62 - 4⟩ (.recv (.dataAvailable 5))] := by decide
example : (run srvWide [.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false))]).has ⟨4⟩ = true := by
  decide
example : (run srvWide [.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false))]).has
    ⟨2 ^ 62 - 8⟩ = true := by decide
-- The limit is still enforced one stream further on, and a stream opened that
-- way is not opened again.
example : (component.outcomes (run srvWide [.stream ⟨2 ^ 62 - 8⟩ (.recv (.recvStream 0 5 false))])
    (.stream ⟨2 ^ 62 - 4⟩ (.recv (.recvStream 0 5 false)))).all
      (fun o => match o with
        | .ok _ fx => fx.all (fun e => !e.opens ⟨4⟩)
        | _ => true) = true := by decide
-- … and they really exist afterwards, while stream 12 does not.
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨0⟩ = true := by decide
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨4⟩ = true := by decide
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨12⟩ = false := by decide

-- §4.6, line 1546: stream 12 is index 3, beyond the limit of 3 we advertised.
example : component.step srv (.stream ⟨12⟩ (.recv (.recvStream 0 5 false))) =
    .error .streamLimitError := by decide

-- §19.8, line 7637: stream 1 is server-initiated, so at a server a STREAM frame
-- for it before we created it is a STREAM_STATE_ERROR, and nothing else is
-- permitted …
example : component.outcomes srv (.stream ⟨1⟩ (.recv (.recvStream 0 5 false))) =
    [.error .streamStateError] := by decide
-- … and the same for STOP_SENDING (§19.5, line 7473) and MAX_STREAM_DATA
-- (§19.10, line 7734), the other two frames the text names for a
-- locally-initiated stream that has not yet been created.
example : component.outcomes srv (.stream ⟨1⟩ (.send (.recvStopSending 0))) =
    [.error .streamStateError] := by decide
example : component.outcomes srv (.stream ⟨1⟩ (.send (.recvMaxStreamData 5))) =
    [.error .streamStateError] := by decide
-- Stream 3 is server-initiated *unidirectional*, hence send-only at a server,
-- so §19.4, line 7431 and §19.13, line 7863 mandate the error for it too.
-- (The bidirectional case is P9-2 below: there the text mandates nothing.)
example : component.outcomes srv (.stream ⟨3⟩ (.recv (.recvResetStream 0 5))) =
    [.error .streamStateError] := by decide
example : component.outcomes srv (.stream ⟨3⟩ (.recv (.recvStreamDataBlocked 5))) =
    [.error .streamStateError] := by decide

-- §19.10, line 7734 through the routing: MAX_STREAM_DATA for a peer-initiated
-- *unidirectional* stream opens it and then fails, because it is receive-only.
example : component.step srv (.stream ⟨2⟩ (.send (.recvMaxStreamData 5))) =
    .error .streamStateError := by decide

-- §19.9, line 7712: 60 bytes on stream 0 and 60 on stream 4 exceed our MAX_DATA
-- of 100, although each is within its own stream limit of 100.
example : component.step (run srv [.stream ⟨0⟩ (.recv (.recvStream 0 60 false))])
    (.stream ⟨4⟩ (.recv (.recvStream 0 60 false))) = .error .flowControlError := by decide
-- §4.5, line 1495: a reset stream keeps consuming its final size, so the same
-- total is reached through RESET_STREAM.
example : component.step (run srv [.stream ⟨0⟩ (.recv (.recvResetStream 7 60))])
    (.stream ⟨4⟩ (.recv (.recvStream 0 60 false))) = .error .flowControlError := by decide

-- §2.1, line 687: a stream that has been reset is still "used"; its ID is never
-- available again.
example : (run srv [.stream ⟨0⟩ (.recv (.recvResetStream 7 5))]).has ⟨0⟩ = true := by decide

-- §19.11, line 7809: a MAX_STREAMS that does not increase the limit is ignored,
-- a larger one raises it.
example : component.step srv (.recvMaxStreams .uni 2) = .ok srv [] := by decide
example : component.step srv (.recvMaxStreams .uni 5) =
    .ok ((component.step srv (.recvMaxStreams .uni 5)).next srv)
      [.streamsAvailable .uni 5] := by decide
-- §19.14, line 7919: either error code is acceptable for an oversized value.
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1))
    (.error .streamLimitError) = true := by decide
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1))
    (.error .frameEncodingError) = true := by decide
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1)) (.ok srv []) = false := by
  decide

-- Following an implementation we cannot see inside (what the WP13 harness does).
example : component.track srv (.recvMaxData 500) (.ok [.dataCreditAvailable 500]) =
    some { srv with maxDataPeer := 500 } := by decide
-- An observation the spec does not permit empties the candidate set.
example : component.trackSet [srv] (.stream ⟨12⟩ (.recv (.recvStream 0 5 false)))
    (Obs.ok []).matchesLoosely = [] := by decide

-- Send side.  §4.1, line 1364: advertising a smaller limit is not an error …
example : component.maySend srv (.maxData 1) = true := by decide
example : component.maySend srv (.maxStreams .bidi 1) = true := by decide
-- … but 2^60 is the ceiling for MAX_STREAMS (§19.11, line 7802).
example : component.maySend srv (.maxStreams .bidi (2 ^ 60 + 1)) = false := by decide
-- §13.3, line 5409: a blocked frame carries the limit in force.
example : component.maySend srv (.dataBlocked 100) = true := by decide
example : component.maySend srv (.dataBlocked 99) = false := by decide
example : component.maySend srv (.streamsBlocked .uni 3) = true := by decide
-- Nothing may be sent for a stream that does not exist yet.  Review finding
-- S-5: this conjunct is the *model's*, not the text's — see NOTES 4 and the
-- obligation it places on WP13.
example : component.maySend srv (.stream 3 0 false ByteArray.empty) = false := by decide
-- After opening stream 3, a STREAM frame the application has written is allowed …
private def srvOpen : State :=
  run srv [.appOpenStream .uni, .stream ⟨3⟩ (.send (.appWrite 10))]
example : maySend srvOpen (.stream 3 0 false (ByteArray.mk #[1, 2, 3])) = true := by decide
-- … but not beyond the connection-level credit the peer gave us: with a peer
-- that allows 1000 bytes on the stream but only 100 on the connection, a frame
-- ending at offset 103 is within the stream limit and outside the connection's.
private def limBig : Limits := { lim with maxStreamDataUni := 1000 }
private def srvBig : State :=
  run (init .server lim limBig) [.appOpenStream .uni, .stream ⟨3⟩ (.send (.appWrite 200))]
example : maySend srvBig (.stream 3 0 false (ByteArray.mk #[1, 2, 3, 4, 5])) = true := by decide
example : maySend srvBig (.stream 3 98 false (ByteArray.mk #[1, 2, 3, 4, 5])) = false := by decide

/-! ### Regression examples for the Wave 2 review (`reviews/wave2.md`) -/

/-! **P9-1 (finding S-1).**  A client with `initial_max_data = 20` and a
generous per-stream limit.  Stream 3 (server-initiated unidirectional, so
receive-only at a client) receives 10 bytes with FIN: its final size is 10 and
`recvTotal` is 10.  A later frame claiming 200 bytes on that stream contradicts
the final size, so §4.5, line 1517 asks for a FINAL_SIZE_ERROR — but §4.5,
line 1522 says "Generating these errors is not mandatory", so ignoring the frame
is permitted as well, and §4.5, line 1495 says the stream goes on consuming
exactly its final size.  The table must therefore keep the ignore outcome and
must *not* charge 200 − 10 bytes of connection credit (which would raise a
spurious FLOW_CONTROL_ERROR: the defect S-1 reported). -/

private def cliLim : Limits :=
  { maxData := 20, maxStreamDataBidiLocal := 1000, maxStreamDataBidiRemote := 1000,
    maxStreamDataUni := 1000, maxStreamsBidi := 3, maxStreamsUni := 3 }
private def cli : State := init .client cliLim cliLim
/-- Stream 3's final size is known to be 10; `recvTotal = 10` of the 20 allowed. -/
private def cliFin : State := run cli [.stream ⟨3⟩ (.recv (.recvStream 0 10 true))]

example : cliFin.recvTotal = 10 := by decide
example : cliFin.maxDataLocal = 20 := by decide

-- WP2 offers both the FINAL_SIZE_ERROR and ignoring the frame …
example : Stream.outcomes (cliFin.get ⟨3⟩) (.recv (.recvStream 0 200 false))
    = [.error .finalSizeError, .ok (cliFin.get ⟨3⟩) []] := by decide
-- … and the table now keeps both, with the state (and `recvTotal`) unchanged.
example : component.outcomes cliFin (.stream ⟨3⟩ (.recv (.recvStream 0 200 false)))
    = [.error .finalSizeError, .ok cliFin []] := by decide
example : component.accepts cliFin (.stream ⟨3⟩ (.recv (.recvStream 0 200 false)))
    (.error .flowControlError) = false := by decide

-- The same through RESET_STREAM with a changed final size (§4.5, line 1517).
example : Stream.outcomes (cliFin.get ⟨3⟩) (.recv (.recvResetStream 0 200))
    = [.error .finalSizeError, .ok (cliFin.get ⟨3⟩) []] := by decide
example : component.outcomes cliFin (.stream ⟨3⟩ (.recv (.recvResetStream 0 200)))
    = [.error .finalSizeError, .ok cliFin []] := by decide
example : component.accepts cliFin (.stream ⟨3⟩ (.recv (.recvResetStream 0 200)))
    (.error .flowControlError) = false := by decide

-- §19.9, line 7712 still bites where the stream really does accept the bytes:
-- 10 more on stream 7 fits in the 20 we advertised, 11 does not.
example : (run cliFin [.stream ⟨7⟩ (.recv (.recvStream 0 10 false))]).recvTotal = 20 := by decide
example : component.outcomes cliFin (.stream ⟨7⟩ (.recv (.recvStream 0 11 false)))
    = [.error .flowControlError] := by decide

/-! **P9-2 (finding S-2).**  Stream 0 at a client is client-initiated
*bidirectional*; before `appOpenStream` it has not been created.  §19.4,
line 7431 and §19.13, line 7863 speak only of a *send-only* stream, so for
RESET_STREAM and STREAM_DATA_BLOCKED the text states no rule here and ignoring
the frame must stay permitted alongside the STREAM_STATE_ERROR. -/

example : (⟨0⟩ : StreamId).initiator = Role.client := by decide
example : (⟨0⟩ : StreamId).dir = StreamDir.bidi := by decide
example : cli.has ⟨0⟩ = false := by decide

example : component.outcomes cli (.stream ⟨0⟩ (.recv (.recvResetStream 0 5)))
    = [.error .streamStateError, .ok cli []] := by decide
example : component.outcomes cli (.stream ⟨0⟩ (.recv (.recvStreamDataBlocked 5)))
    = [.error .streamStateError, .ok cli []] := by decide
-- `.ok s []`, not `.drop`: the frame is processed to no effect and the packet
-- carrying it is still acknowledged (the convention of `Spec/Template.lean`).
example : component.accepts cli (.stream ⟨0⟩ (.recv (.recvResetStream 0 5))) .drop = false := by
  decide

-- The three frames the text does name stay mandatory, on the same stream …
example : component.outcomes cli (.stream ⟨0⟩ (.recv (.recvStream 0 5 false)))
    = [.error .streamStateError] := by decide
example : component.outcomes cli (.stream ⟨0⟩ (.send (.recvStopSending 3)))
    = [.error .streamStateError] := by decide
example : component.outcomes cli (.stream ⟨0⟩ (.send (.recvMaxStreamData 5)))
    = [.error .streamStateError] := by decide
-- … and stream 2 (client-initiated unidirectional, so send-only at a client) is
-- covered by §19.4, line 7431 and §19.13, line 7863 after all.
example : component.outcomes cli (.stream ⟨2⟩ (.recv (.recvResetStream 0 5)))
    = [.error .streamStateError] := by decide
example : component.outcomes cli (.stream ⟨2⟩ (.recv (.recvStreamDataBlocked 5)))
    = [.error .streamStateError] := by decide

/-! ## 10. Coverage and notes

Assigned text: §2.1 (677–732), §4–§4.3 (1293–1460), §4.6 (1527–1576), the
MAX_DATA / MAX_STREAMS / DATA_BLOCKED / STREAMS_BLOCKED frame sections
(7689–7717, 7773–7856, 7884–7922) and the "locally-initiated stream that has not
yet been created" half of §19.4/§19.5/§19.8/§19.10/§19.13.

Citation convention (every line number below was re-derived for this revision
and checked mechanically — see NOTES, "How the citations were checked"): a
citation names the line on which the quoted sentence's **first word** appears,
which may be in the middle of that line.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §2.1 (687) | a QUIC endpoint MUST NOT reuse a stream ID | `State.has` (high-water marks), `no_reuse`, `has_forever` |
| §2.1 (690, 695, 699) | the two low bits give initiator and directionality | `Spec.StreamId` (WP0), used throughout |
| §2.1 (718) | a stream ID used out of order opens all lower-numbered streams of that type | `State.openThrough`, `Step.openOk`, `openedEffects`, `has_lower`, `openOk_opens_lower` |
| §2.3 (774) | implementations SHOULD provide ways to indicate stream priority | advice, not checkable here: it is about an API and a scheduler, and §2.3, line 770 says QUIC "does not provide a mechanism for exchanging prioritization information", so no frame and no outcome depends on it |
| §4 (1297) | streams are flow controlled individually and across the connection | `State.recvTotal`/`maxDataLocal` here, `Stream.Recv.maxData` in WP2 |
| §4 (1304) | the cumulative number of streams a peer can initiate is limited | `State.maxStreamsLocal`/`maxStreamsPeer` |
| §4 (1308) | CRYPTO data is not flow controlled this way | out of scope: WP11 (CRYPTO stream) |
| §4 (1311) | implementations SHOULD provide an interface for the cryptographic protocol implementation to communicate its buffering limits | advice, not checkable here: the CRYPTO buffer limit is WP11's `Handshake.State.bufLimit` (and the CRYPTO_BUFFER_EXCEEDED of §7.5 that goes with it); this component holds no crypto state and sees no CRYPTO frame |
| §4.1 (1330) | senders MUST NOT send data in excess of either limit | `connSendBlocked`, `Step.existSendBlocked`, `MaySend`, `sentTotal_le_peer` |
| §4.1 (1332) | initial limits come from transport parameters | `Limits`, `init` |
| §4.1 (1349) | a receiver can advertise a larger stream limit with MAX_STREAM_DATA | WP2 (`Recv.Step.sendMaxStreamData`), routed here |
| §4.1 (1356) | a receiver can advertise a larger connection limit with MAX_DATA | `Step.sendMaxData`, `Step.maxDataRaise` |
| §4.1 (1358) | a receiver maintains a cumulative sum of bytes received on all streams | `State.recvTotal`, `afterStep`, `recvTotal_eq_sum` |
| §4.1 (1364) | advertising a smaller limit is not an error but has no effect | `Step.sendMaxData` (takes `max`), `MaySend` does *not* require an increase |
| §4.1 (1368) | FLOW_CONTROL_ERROR if the sender violates the advertised limits | `connRecvViolation`, `Step.existFlowControl`, `Step.openFlowControl`, `recvTotal_le_advertised` |
| §4.1 (1372) | a sender MUST ignore MAX_DATA frames that do not increase limits | `Step.maxDataStale` |
| §4.1 (1375, 1376, 1381) | a blocked sender SHOULD send DATA_BLOCKED, and SHOULD do so periodically | `Recommended`; `MaySend` permits it whenever the value is the limit in force |
| §4.2 (1388) | implementations decide when and how much credit to advertise | no normative keyword; `Step.sendMaxData`/`Step.sendMaxStreams` are events, so the model records what was advertised, not when |
| §4.2 (1392) | a receiver **MAY** send MAX_STREAM_DATA or MAX_DATA multiple times within a round trip, or early | satisfied: `Step.sendMaxData` and `Step.sendMaxStreams` accept any value at any time and any number of times (no monotonicity conjunct in `MaySend`, `max` in the state), so a repeat and an early send are both permitted outcomes |
| §4.2 (1405–1419) | overhead, increment size, autotuning | no normative keyword |
| §4.2 (1422) | a receiver MUST NOT wait for a STREAM_DATA_BLOCKED or DATA_BLOCKED frame before sending MAX_STREAM_DATA or MAX_DATA | advice/strategy, not checkable per step: it forbids a *scheduling* rule, and every single behaviour it rules out is permitted frame by frame — see NOTES 8, which also records that nothing in `Step`, `MaySend` or `Recommended` makes a MAX_DATA conditional on having received a DATA_BLOCKED |
| §4.2 (1429) | a sender that receives credit may cause short-term congestion | out of scope: RFC 9002 |
| §4.3 (1436–1448) | flow control performance | no normative keyword; no observable rule |
| §4.5 (1495) | the receiver MUST use the final size to account for all bytes in its connection-level flow controller | `recvHighest` (RESET_STREAM sets `highest` to the final size in WP2), `connRecvViolation`, `afterStep`; the §4.5 example above and P9-1 |
| §4.5 (1517, 1519, 1520, 1522) | the final size cannot change; SHOULD FINAL_SIZE_ERROR; generating these errors is **not mandatory** | WP2 (`Recv.finalSizeViolation`, `Recv.Recommended`), lifted here by `delegate`: both the error and the ignore outcome reach `outcomes`, and the ignore outcome costs no connection credit — P9-1, NOTES 7 |
| §4.6 (1530) | only streams with an index below the limit may be opened | `Step.openLimit`, `Step.openLocalBlocked` |
| §4.6 (1531) | initial limits are set in the transport parameters | `Limits`, `init` |
| §4.6 (1533) | subsequent limits are advertised using MAX_STREAMS frames | `Step.maxStreamsRaise`, `Step.sendMaxStreams` |
| §4.6 (1534) | separate limits for unidirectional and bidirectional streams | `Counts`, `Opened` |
| §4.6 (1537) | a max_streams value above 2^60: FRAME_ENCODING_ERROR (frame) / TRANSPORT_PARAMETER_ERROR (parameter) | `Step.maxStreamsTooLarge`; the transport-parameter half is WP1 |
| §4.6 (1546) | endpoints MUST NOT exceed the peer's limit; a frame beyond the limit we sent is a STREAM_LIMIT_ERROR | `Step.openLimit`, `State.withinPeerStreamLimit`, `openedLocal_le_peer`, `openedRemote_le_advertised`, `not_has_of_exceeding_limit` |
| §4.6 (1551) | advertising a smaller stream limit has no effect | `Step.sendMaxStreams` (takes `max`) |
| §4.6 (1552) | a MAX_STREAMS that does not increase the limit MUST be ignored | `Step.maxStreamsStale` |
| §4.6 (1555) | implementations decide when to advertise more streams | no normative keyword; `Step.sendMaxStreams` is an event: the model tracks what was advertised, not when |
| §4.6 (1561) | an endpoint unable to open a stream SHOULD send STREAMS_BLOCKED | `Recommended` (`.streamsBlocked`); `Step.openLocalBlocked` is the outcome it accompanies |
| §4.6 (1563) | an endpoint MUST NOT wait to receive STREAMS_BLOCKED before advertising additional credit | advice/strategy, not checkable per step: same shape as §4.2, line 1422 — `Step.sendMaxStreams` is never conditioned on a STREAMS_BLOCKED having arrived, which is the checkable half; see NOTES 8 |
| §19.9 (7710) | the sum of the final sizes on all streams MUST NOT exceed the advertised value | `Inv`, `recvTotal_le_advertised`, `recvTotal_eq_sum` |
| §19.9 (7712) | FLOW_CONTROL_ERROR if more data is received than the maximum data value sent | `connRecvViolation`, `Step.existFlowControl`, `Step.openFlowControl` |
| §19.10 (7734) | MAX_STREAM_DATA for a locally-initiated stream not yet created: STREAM_STATE_ERROR | `Step.localNotCreated`, `localNotCreatedMandatory`, `localNotCreated_iff` |
| §19.11 (7802) | a MAX_STREAMS value cannot exceed 2^60 | `maxStreamsLimit`, `Step.sendMaxStreamsForbidden`, `MaySend` |
| §19.11 (7803) | receipt of a frame permitting a larger stream: FRAME_ENCODING_ERROR | `Step.maxStreamsTooLarge` |
| §19.11 (7809) | MAX_STREAMS that do not increase the limit MUST be ignored | `Step.maxStreamsStale` |
| §19.11 (7812) | an endpoint MUST NOT open more streams than permitted | `Step.openLocal`, `Step.openLocalBlocked`, `openedLocal_le_peer` |
| §19.11 (7815) | STREAM_LIMIT_ERROR if a peer opens more streams than permitted | `Step.openLimit`, `openedRemote_le_advertised` |
| §19.11 (7820, 7822) | the limit counts closed streams too | high-water marks never decrease (`opened_step`, `has_forever`) |
| §19.12 (7827) | a sender SHOULD send DATA_BLOCKED when blocked | `Recommended`, `Step.dataBlocked` |
| §19.13 (7859) | a sender SHOULD send STREAM_DATA_BLOCKED when blocked by the stream limit | out of scope: WP2 (`Stream.Send.RecommendedSend`), a stream-level rule |
| §19.13 (7863) | STREAM_DATA_BLOCKED for a **send-only** stream MUST be STREAM_STATE_ERROR | WP2 (`Stream.Step.recvMissing`), reached through this file's routing; for an uncreated locally-initiated stream it applies only when that stream is unidirectional — `localNotCreatedMandatory` |
| §19.14 (7886) | a sender SHOULD send STREAMS_BLOCKED when unable to open a stream | `Recommended` |
| §19.14 (7901) | STREAMS_BLOCKED does not open the stream | `Step.streamsBlockedOk` (state unchanged) |
| §19.14 (7919) | STREAMS_BLOCKED above 2^60: STREAM_LIMIT_ERROR or FRAME_ENCODING_ERROR | `Step.streamsBlockedTooLarge₁/₂` |
| §19.8 (7637) | STREAM for a locally-initiated stream not yet created, **or for a send-only stream**: STREAM_STATE_ERROR | `Step.localNotCreated` / `localNotCreatedMandatory` for the first half; WP2 (`Stream.Step.recvMissing`) for the second |
| §19.5 (7473) | STOP_SENDING for a locally-initiated stream not yet created: STREAM_STATE_ERROR | `Step.localNotCreated`, `localNotCreatedMandatory` |
| §19.4 (7431), §19.5 (7475), §19.10 (7736) | the *send-only / receive-only* halves of those sentences | WP2 (`Stream.Step.sendMissing`/`recvMissing`), reached through this file's routing |
| §13.3 (5409) | blocked frames carry the limit in force when transmitted | `MaySend` for DATA_BLOCKED / STREAMS_BLOCKED |
| §13.3 (rest) | retransmission and loss | out of scope by assignment: WP14 |

Nothing in the assigned range mandates anything about a RESET_STREAM or a
STREAM_DATA_BLOCKED received for a locally-initiated **bidirectional** stream
that has not yet been created: see NOTES 3 and `Step.localNotCreatedIgnored`.

NOTES

1. **Existence is the high-water mark, not the table.**  §2.1 opens every
   lower-numbered stream of a type implicitly and forbids reusing an ID, so the
   set of streams of one type is always an initial segment: `State.opened` counts
   them and `State.has` decides existence.  The `Map StreamId Stream.State` holds
   the state of streams that have actually taken a step; `State.get` falls back
   to `State.freshStream`, so an implicitly opened stream that has seen no event
   costs nothing and is still fully specified.  The alternative — materialising
   every implicitly opened stream in the table — is observationally identical
   (all of them are at their initial state) but makes every theorem about
   implicit opening an induction over a range.  One consequence to keep in mind
   for WP12/WP13: two histories that differ only in events that left a stream at
   its initial state can produce table entries that differ syntactically while
   being equal as states, so `trackSet` may carry two candidates where one would
   do; it never loses the real state.
2. **Which error when several rules are violated.**  A frame can break the stream
   limit of §4.6, the connection-level limit of §19.9 and a stream-level rule of
   WP2 at once, and the text fixes no order between the checks.  `Step` therefore
   has one constructor per violated rule with no mutual exclusion, and `outcomes`
   lists STREAM_LIMIT_ERROR first, then every error the stream itself would
   raise, with the connection-level FLOW_CONTROL_ERROR standing where the
   accepting outcome it replaces stood.  The preferred outcome
   (`component.step`) is the first, but `accepts` takes any of them — being
   stricter here would fail implementations that check in a different order.
3. **A local action on a stream that does not exist is `.drop`; a *frame* is an
   error, except where the text does not say so.**  Same split as WP2: the
   application cannot write to a stream it never opened.  For a frame, §19.8,
   line 7637 (STREAM), §19.5, line 7473 (STOP_SENDING) and §19.10, line 7734
   (MAX_STREAM_DATA) mandate STREAM_STATE_ERROR for a locally-initiated stream
   that has not yet been created, and `Step.localNotCreated` is their only
   outcome.  §19.4, line 7431 (RESET_STREAM) and §19.13, line 7863
   (STREAM_DATA_BLOCKED) do **not**: they speak only of a *send-only* stream.
   A locally-initiated stream is send-only exactly when it is unidirectional, so
   for a locally-initiated **bidirectional** stream that has not been created
   those two frames are governed by no sentence of the text, and
   `Step.localNotCreatedIgnored` keeps ignoring them permitted alongside the
   error (review finding S-2; `localNotCreatedMandatory` is the split, and
   `localNotCreated_iff` / `localNotCreatedIgnored_iff` state both halves).
   The additional outcome is `.ok s []` and not `.drop`, following
   `Spec/Template.lean`: the frame is processed to no effect and the packet
   carrying it is still acknowledged — the text nowhere permits discarding it.
   The choice is invisible to WP13 in any case, because `Obs.matchesLoosely`
   identifies `ok []` with `drop`; it matters to WP12, where a `.drop` from one
   component can gate another's `.ok`.  The error stays first, so
   `component.step` is unchanged.
4. **`MaySend` for a stream that does not exist is `False`** (for all five
   stream-scoped frame types).  In this model a locally-initiated stream comes
   into existence through `appOpenStream`, which is where §4.6's "MUST NOT exceed
   the limit set by their peer" is enforced; with no state for the stream, none
   of §3.3, §4.1 or §4.5 can be checked, so nothing may be said about it.  This
   is a modelling decision, not a sentence of the text — §4.6, line 1546 and
   §19.11, line 7812 govern *opening*, and nothing in the range forbids sending
   a frame on a stream the sender has opened (review finding S-5).
   **Consequence for WP13, and it is an obligation, not a remark:** ngtcp2 opens
   streams internally and emits a STREAM frame on them with no observable "open"
   event, so every such frame would fail `maySend`.  The harness must synthesise
   `Event.appOpenStream dir` (and then `Stream.Send.Event.appWrite`, the same
   point wave1-a made about `Send.written`) for each locally-initiated stream
   *before* the first frame it sees on that stream, in increasing stream-ID
   order.  It is listed with the other events WP13 must synthesise in
   `reviews/wave2.md`, "Composition notes for WP12", item 6.
   For a *peer*-initiated stream the answer coincides with the text: the peer
   would treat MAX_STREAM_DATA or STOP_SENDING for a stream it has not created
   as a STREAM_STATE_ERROR (§19.10, line 7734; §19.5, line 7473).
5. **Advertising a smaller limit is permitted.**  `Spec/Template.lean` required
   `localMax ≤ v` in `MaySend` for MAX_STREAMS.  The text does not: §4.6,
   line 1551 says only that "advertising a smaller limit has no effect", and
   §4.1, line 1364 says explicitly that "it is not an error to advertise a
   smaller limit".  This file therefore drops that conjunct — "has no effect" is
   not "must not be sent" — and keeps the effect on the state (`max`), which is
   what `maxDataLocal_mono` / `maxStreamsLocal_mono` (theorem (f)) rest on.  This
   is the one place where this package deliberately differs from the template it
   supersedes.  The same freedom is what satisfies the MAY of §4.2, line 1392.
6. **Blocked frames must carry the current limit.**  §13.3, line 5409 is explicit
   that a retransmitted blocked frame carries the limit in force at transmission
   time, so requiring `v = s.maxDataPeer` (resp. the stream-type limit) does not
   clash with the project rule that an exact repeat of an accepted frame stays
   acceptable: after the limit moves, the frame that is re-sent is a different
   frame by the text's own account.
7. **Connection-level credit is accounted from the stream's reply, not from the
   frame.**  Earlier revisions charged `connRecvViolation` from the frame's end
   offset (`recvEnd`) *before* asking the stream, and kept only the error
   outcomes when it fired.  That was wrong twice over (review finding S-1,
   HIGH), and P9-1 is the regression test:
   * §4.5, line 1495 makes the stream consume exactly its final size, so a frame
     claiming data beyond a known final size adds *nothing* to the
     connection-level sum — charging `offset + len − highest` invented a
     FLOW_CONTROL_ERROR out of bytes the receiver never accepted;
   * §4.5, line 1522 ("Generating these errors is not mandatory") makes ignoring
     such a frame a permitted outcome, and deleting every non-error outcome
     removed it, so the model rejected conforming behaviour.

   `connRecvViolation s st st'` therefore compares the stream's own highest
   received offset before and after the outcome the stream chose — the very
   delta `afterStep` adds to `recvTotal` — and the test lives in `lift`, so it is
   made once per outcome.  An outcome in which the stream accepts nothing (an
   ignore, a `.drop`, an error, a `.send` event) can never violate the
   connection-level limit; an outcome in which it really accepts bytes past
   `maxDataLocal` becomes the FLOW_CONTROL_ERROR of §19.9, line 7712, and that
   error is then the only outcome of that branch, as the MUST requires.  A
   RESET_STREAM we *send* consumes no new credit because WP2's `maySendReset`
   forces its Final Size to equal `sent`, which is already counted.  The send
   side keeps charging from the frame (`connSendBlocked`, `sentEnd`), and that is
   right: §4.1, line 1330 is about the frame we are about to put on the wire, so
   the frame is what must be checked, before any state moves.
8. **The two "MUST NOT wait" sentences** — §4.2, line 1422 (do not wait for a
   STREAM_DATA_BLOCKED or DATA_BLOCKED before sending MAX_STREAM_DATA or
   MAX_DATA) and §4.6, line 1563 (the same for STREAMS_BLOCKED) — forbid a
   scheduling strategy, not an action: every individual behaviour they rule out
   is permitted frame by frame, and a violation is only visible over a whole run.
   Neither can be stated over a single step.  What *is* checkable, and holds, is
   that nothing in this component conditions a `sentMaxData` / `sentMaxStreams`
   event, or the `MaySend` of MAX_DATA / MAX_STREAMS, on a DATA_BLOCKED or
   STREAMS_BLOCKED having been received: `Step.dataBlocked` and
   `Step.streamsBlockedOk` change no state at all.
9. **The 2^62-1 bound on MAX_DATA** is not a sentence of §19.9; it follows from
   §16 (all frame fields are variable-length integers).  `MaySend` uses it as the
   only bound on MAX_DATA, and `Step.sendMaxDataForbidden` mirrors it.
10. **The initial state is a parameter.**  `init` takes both endpoints' `Limits`
    as plain numbers; `init_inv` needs only that the four `max_streams`
    parameters are within 2^60, which is exactly what WP1's transport-parameter
    validity guarantees.  WP12 will build the initial state from the negotiated
    parameters (including §7.4.1's remembered 0-RTT limits, which are WP1/WP11's
    business).
11. **How the citations were checked.**  Every `§x.y, line N` in this package
    was re-derived for this revision after review finding S-6, and then verified
    mechanically by `out/check_citations.py` in the fix run's worktree (scratch,
    like the review's own probes): the script pulls every citation out of the
    six Lean sources including this table, pairs each with the opening words of
    the sentence it names,
    normalises `spec/draft-ietf-quic-transport-34.txt` (rejoining words split by
    a hyphen at a hard line break), locates that first word in the normalised
    text and reports the line it falls on.  A citation passes only when that
    line is the cited one and the quotation occurs exactly once.  The convention
    is the line the sentence's first word sits on, which is often in the middle
    of the line (for instance §4.6, line 1546 begins after "…set by their peer."
    on the same line).  68 distinct citations (211 occurrences across the six
    files) pass; nothing in this package is unchecked.  One consequence worth
    flagging to the lead: the sentence "An endpoint that receives a STOP_SENDING
    frame for a receive-only stream MUST terminate the connection with error
    STREAM_STATE_ERROR" begins with "An" at the *end* of line 7475, so this
    package cites §19.5, line 7475, whereas WP2's `Spec/Stream.lean` cites 7476
    under its own convention ("except where its first word or two dangle at the
    end of the previous line — then it is the next line").  The two files
    therefore disagree by one line on that one sentence; the rule used here is
    the one the review asked for.
-/

end Quic.Spec.StreamTable
