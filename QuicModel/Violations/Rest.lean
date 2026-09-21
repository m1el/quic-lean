import QuicModel.Spec.TransportParams
import QuicModel.Spec.ConnIds.Local
import QuicModel.Spec.ConnIds.Remote
import QuicModel.Spec.FrameRules
import QuicModel.Spec.Ack
import QuicModel.Spec.Ecn.Basic
import QuicModel.Spec.Ecn.Step
import QuicModel.Spec.Ecn.Send
import QuicModel.Spec.Retransmission.Basic
import QuicModel.Spec.Retransmission.Step
import QuicModel.Spec.Template
import QuicModel.Violations.Trace

/-!
  Manufactured violations for the remaining components.
  `true` means the verifier rejects that trace.
  Names starting with `advice:` are SHOULDs or MAYs the checker does not reject.
-/
namespace Quic.Violations.Rest

open Quic Quic.Spec Quic.Spec.TransportParams

def ext (l : List (Nat × List UInt8)) : ByteArray :=
  TransportParams.encodeRaw (l.map fun e => (e.1, bytes e.2))

def tpCli : TransportParams.State := { role := .client, peer := none }
def tpSrv : TransportParams.State := { role := .server, peer := none }

def tok (b : UInt8) : ConnIds.ResetToken := List.replicate 16 b

def l0 : ConnIds.Local.State :=
  { nextSeq := 1, issued := [⟨0, [1], tok 0⟩], retired := [], peerLimit := 3,
    zeroLen := false, sentRetirePriorTo := 0 }

/-- One connection ID already issued and the peer's limit is 1. -/
def lLimit : ConnIds.Local.State := { l0 with peerLimit := 1 }

/-- Two IDs already out; Retire Prior To 1 still leaves the peer over a limit of 1. -/
def lKept : ConnIds.Local.State :=
  { nextSeq := 2, issued := [⟨0, [1], tok 0⟩, ⟨1, [2], tok 1⟩], retired := [],
    peerLimit := 1, zeroLen := false, sentRetirePriorTo := 0 }

def r0 : ConnIds.Remote.State :=
  { entries := [⟨0, [1], tok 0⟩, ⟨1, [2], tok 1⟩], retired := [], retirePriorTo := 0,
    limit := 4, peerZeroLen := false }

/-- Already over our own active_connection_id_limit. -/
def rOver : ConnIds.Remote.State := { r0 with limit := 1 }

/-- Exactly at the limit: one more connection ID without a retirement exceeds it. -/
def rFull : ConnIds.Remote.State :=
  { r0 with entries := r0.entries ++ [⟨2, [3], tok 3⟩, ⟨3, [4], tok 4⟩] }

def rRaised : ConnIds.Remote.State :=
  (ConnIds.Remote.component.step r0 (.recvNewCid 5 2 [3] (tok 3))).next r0

def rPrior : ConnIds.Remote.State :=
  (ConnIds.Remote.component.step r0 (.recvNewCid 5 4 [3] (tok 3))).next r0

def a0 : Ack.State :=
  { space := .appData, received := [], minPn := 0, largest := none, largestTime := 0,
    largestAckEliciting := none, outstanding := [], ackImmediately := false,
    largestSent := none, maxAckDelay := 25000 }

def aSent : Ack.State := { a0 with largestSent := some 5 }

def frCli : FrameRules.State := { role := .client }
def frSrv : FrameRules.State := { role := .server }

def e0 : Ecn.State := { space := .appData }

def eCounted : Ecn.State := e0.recordRecv .ect0 true

/-- Counts that would fail if this ACK were allowed to validate. -/
def eReordered : Ecn.State :=
  { space := .appData, sentEct0 := 4, largestAcked := some 10, peerEct0 := 4, phase := .capable }

def eUnknown : Ecn.State := { space := .appData, sentEct0 := 2, phase := .unknown }

def eFailed : Ecn.State := { space := .appData, phase := .failed }

def rt0 : Retransmission.State := {}
def rtp0 : Retransmission.PktId := ⟨.appData, 0⟩

def rtReset : Retransmission.State :=
  (rt0.afterSent rtp0 [.resetStream 4 3 10]).afterLost rtp0

def rtHsLost : Retransmission.State :=
  (rt0.afterSent rtp0 [.handshakeDone]).afterLost rtp0

def rtHsAcked : Retransmission.State :=
  (rt0.afterSent rtp0 [.handshakeDone]).afterAcked rtp0

def rtPastRecv : Retransmission.State := rt0.afterRecvPhase ⟨4⟩ .sizeKnown

def rtInFlight : Retransmission.State := rt0.afterSent rtp0 [.ping]

def t0 : Template.State :=
  { peerMaxBidi := 3, peerMaxUni := 3, localMaxBidi := 10, localMaxUni := 10 }

def paOk : PreferredAddress :=
  { ipv4 := bytes [0, 0, 0, 0], ipv4Port := 443,
    ipv6 := bytes (List.replicate 16 0), ipv6Port := 443,
    cid := bytes [9], token := bytes (List.replicate 16 1) }

def tpData20 : TransportParams := { defaults with initialMaxData := 20 }
def tpData100 : TransportParams := { defaults with initialMaxData := 100 }
def tpData50 : TransportParams := { defaults with initialMaxData := 50 }
def tpStreams8 : TransportParams := { defaults with initialMaxStreamsBidi := 8 }
def tpStreams4 : TransportParams := { defaults with initialMaxStreamsBidi := 4 }
def tpPayload1500 : TransportParams := { defaults with maxUdpPayloadSize := 1500 }
def tpPayload1300 : TransportParams := { defaults with maxUdpPayloadSize := 1300 }
def tpAcl4 : TransportParams := { defaults with activeConnectionIdLimit := 4 }
def tpAcl2 : TransportParams := { defaults with activeConnectionIdLimit := 2 }
def tpAde21 : TransportParams := { defaults with ackDelayExponent := 21 }
def tpMad5 : TransportParams := { defaults with maxAckDelay := 5 }
def tpRetry : TransportParams :=
  { defaults with retrySourceConnectionId := some (bytes [0x52]) }
def tpZeroSrc : TransportParams :=
  { defaults with preferredAddress := some paOk, initialSourceConnectionId := some ByteArray.empty }
def tpNoCid : TransportParams :=
  { defaults with preferredAddress := some { paOk with cid := ByteArray.empty }, initialSourceConnectionId := some (bytes [1]) }
def tpCarry : TransportParams :=
  { defaults with ackDelayExponent := 20, maxAckDelay := 100, initialSourceConnectionId := some (bytes [1]), originalDestinationConnectionId := some (bytes [2]), retrySourceConnectionId := some (bytes [3]), statelessResetToken := some (bytes (List.replicate 16 9)), initialMaxData := 50 }

def asBool (p : Prop) [Decidable p] : Bool := decide p

def checks : List Trace := [
  -- §7.4: an out-of-range max_streams value is not a parameter we may accept.
  must "TransportParams §7.4 (2535) invalid params accepted" (asBool (
    (TransportParams.validate .server
        [(0x08, bytes [0xd0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01])] = none) &&
    (TransportParams.component.accepts tpCli
        (.recvParams (ext [(0x08, [0xd0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01])]))
        (.ok tpCli []) = false))),
  -- §7.4: sending one parameter twice is visible to the checker.
  must "TransportParams §7.4 (2539) a duplicated parameter accepted" (asBool (
    TransportParams.duplicated [(0x04, bytes [0x0a]), (0x04, bytes [0x14])] = true)),
  -- §7.4 SHOULD: keeping a copy of a duplicate is still a permitted outcome.
  advice "TransportParams §7.4 (2540) advice if duplicate may be ignored; if MUST error, show .ok rejected" (asBool (
    TransportParams.component.accepts tpCli
        (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
        (.ok ⟨.client, some tpData20⟩ [.paramsApplied tpData20]) = false)),
  -- §7.4.1: the seven parameters that must not be remembered are put back.
  must "TransportParams §7.4.1 (2593) remembered set does not reset when it must — show a predicate violation if you can construct params that zeroRtt would wrongly allow; else accepts of a bad recvParams" (asBool (
    TransportParams.remembered tpCarry = tpData50)),
  -- §7.4.1: a limit the client must remember is not compatible once decreased.
  must "TransportParams §7.4.1 (2600) a decreased remembered limit treated as compatible" (asBool (
    ((TransportParams.remembered tpData100).initialMaxData = 100) &&
    (TransportParams.zeroRttCompatible (TransportParams.remembered tpData100) tpData50 = false))),
  -- §7.4.1: zero-rtt compatibility is false for a smaller stream limit.
  must "TransportParams §7.4.1 (2607) zero-rtt compatible returns true for a decreased limit" (asBool (
    TransportParams.zeroRttCompatible tpStreams8 tpStreams4 = false)),
  -- §7.4.1 SHOULD: all-zero 0-RTT limits are still valid parameters.
  advice "TransportParams §7.4.1 (2638) advice: recommended params not used, if the checker does not reject" (asBool (
    TransportParams.component.accepts tpCli (.recvParams (ext []))
        (.ok ⟨.client, some defaults⟩ [.paramsApplied defaults]) = false)),
  -- §7.4.1 MAY: the stricter test rejects a smaller max_udp_payload_size.
  must "TransportParams §7.4.1 (2645) strict compatibility true when a value required to be equal differs" (asBool (
    TransportParams.zeroRttCompatibleStrict tpPayload1500 tpPayload1300 = false)),
  -- §7.4.1: 0-RTT against a reduced active_connection_id_limit is incompatible.
  must "TransportParams §7.4.1 (2653) zero-rtt used when incompatible" (asBool (
    TransportParams.zeroRttCompatible tpAcl4 tpAcl2 = false)),
  -- §7.4.2: a reserved identifier is not a known parameter, and it is not an error.
  must "TransportParams §7.4.2 (2670) an unknown parameter treated as a known one that fails, or a reserved id accepted as known — knownEntries / ofCode?" (asBool (
    (TransportParams.ParamId.ofCode? 27 = none) &&
    (TransportParams.knownEntries [(27, bytes [0xde, 0xad])] = []) &&
    (TransportParams.component.accepts tpSrv
        (.recvParams (ext [(27, [0xde, 0xad])]))
        (.error .transportParameterError) = false))),
  -- §18.2: ack_delay_exponent above 20 is not accepted.
  must "TransportParams §18.2 (6951) a parameter value over its limit accepted (active_connection_id_limit 1, or max_ack_delay, or ack_delay_exponent)" (asBool (
    (TransportParams.validB .server tpAde21 = false) &&
    (TransportParams.component.accepts tpCli (.recvParams (ext [(0x0a, [21])]))
        (.ok tpCli []) = false))),
  -- §18.2 SHOULD: max_ack_delay without alarm slack is still accepted.
  advice "TransportParams §18.2 (7040) advice initial max values" (asBool (
    TransportParams.component.accepts tpCli (.recvParams (ext [(0x0b, [5])]))
        (.ok ⟨.client, some tpMad5⟩ [.paramsApplied tpMad5]) = false)),
  -- §18.2: a preferred address that does not parse, and one paired with a zero-length source CID.
  must "TransportParams §18.2 (7092) preferred address malformed accepted" (asBool (
    (TransportParams.component.accepts tpCli (.recvParams (ext [(0x0d, [0x00])]))
        (.ok tpCli []) = false) &&
    (TransportParams.validB .server tpZeroSrc = false))),
  -- §18.2: a preferred address whose connection ID is missing (length 0).
  must "TransportParams §18.2 (7094) missing required CID param accepted" (asBool (
    TransportParams.validB .server tpNoCid = false)),
  -- §18.2: a client sent stateless_reset_token.
  must "TransportParams §18.2 (7095) a server param from a client, or the invalid step's .ok" (asBool (
    TransportParams.component.accepts tpSrv
        (.recvParams (ext [(0x02, List.replicate 16 0)]))
        (.ok tpSrv []) = false)),
  -- §18.2: original_destination_connection_id from the client.
  must "TransportParams §18.2 (7124) original_destination_connection_id missing or from the client" (asBool (
    TransportParams.component.accepts tpSrv
        (.recvParams (ext [(0x00, [0xc1])]))
        (.ok tpSrv []) = false)),
  -- §18.2: active_connection_id_limit below 2 has no accepting outcome.
  must "TransportParams §18.2 (7125) the invalid outcome's complement (.ok when invalid)" (asBool (
    TransportParams.component.accepts tpCli (.recvParams (ext [(0x0e, [0x01])]))
        (.ok tpCli []) = false)),
  -- §18.2: retry_source_connection_id is server-only.
  must "TransportParams §18.2 (7149) retry_source_connection_id rules broken, accepted" (asBool (
    TransportParams.validB .client tpRetry = false)),
  -- §18.2: receiving that parameter from a client is not .ok.
  must "TransportParams §18.2 (7151) .ok when Step.invalid" (asBool (
    TransportParams.component.accepts tpSrv
        (.recvParams (ext [(0x10, [0x52])]))
        (.ok tpSrv []) = false)),

  -- §5.1: the same connection ID is not issued again.
  must "ConnIds §5.1 (1644) issuing a CID when canIssue is false" (asBool (
    (ConnIds.Local.canIssue l0 [1] (tok 7) 0 = false) &&
    (ConnIds.Local.component.accepts l0 (.issueCid [1] (tok 7) 0)
        (.ok (ConnIds.Local.applyIssue l0 [1] (tok 7) 0).1
          (ConnIds.Local.applyIssue l0 [1] (tok 7) 0).2) = false))),
  -- §5.1.1: more active connection IDs than the limit is not an accepting state.
  must "ConnIds §5.1.1 (1709) more active CIDs than the limit, if a predicate rejects the state or the issue" (asBool (
    ((rOver.activeCount ≤ rOver.limit) = false) &&
    (ConnIds.Remote.component.accepts rOver (.recvNewCid 2 0 [3] (tok 3))
        (.ok (ConnIds.Remote.applyNcid rOver 2 0 [3] (tok 3)).1
          (ConnIds.Remote.applyNcid rOver 2 0 [3] (tok 3)).2) = false))),
  -- §5.1.1: issuing past the peer's active_connection_id_limit is refused.
  must "ConnIds §5.1.1 (1721) issue that exceeds the peer's active_connection_id_limit" (asBool (
    (ConnIds.Local.canIssue lLimit [2] (tok 2) 0 = false) &&
    (ConnIds.Local.component.accepts lLimit (.issueCid [2] (tok 2) 0)
        (.ok (ConnIds.Local.applyIssue lLimit [2] (tok 2) 0).1
          (ConnIds.Local.applyIssue lLimit [2] (tok 2) 0).2) = false))),
  -- §5.1.1: a Retire Prior To that still leaves the peer over the limit is refused.
  must "ConnIds §5.1.1 (1722) peer kept more than the limit after retire" (asBool (
    ((lKept.peerActiveAfter 1 ≤ lKept.peerLimit) = false) &&
    (ConnIds.Local.canIssue lKept [3] (tok 3) 1 = false))),
  -- §5.1.1: a request that cannot be issued has only .drop.
  must "ConnIds §5.1.1 (1753) an issue the peer did not ask for is performed (.ok) when only .drop" (asBool (
    ConnIds.Local.component.accepts l0 (.issueCid [9] [1] 0)
        (.ok (ConnIds.Local.applyIssue l0 [9] [1] 0).1
          (ConnIds.Local.applyIssue l0 [9] [1] 0).2) = false)),
  -- §5.1.2: an increased Retire Prior To does not leave the old connection IDs in use.
  must "ConnIds §5.1.2 (1811) a NEW_CONNECTION_ID with retire_prior_to that does not retire the old one, if the only ok outcome retires — show an outcome that keeps using the retired id is rejected" (asBool (
    ConnIds.Remote.component.accepts r0 (.recvNewCid 2 2 [3] (tok 3)) (.ok r0 []) = false)),
  -- §19.15: no NEW_CONNECTION_ID while we require zero-length DCIDs, and none over 20 bytes.
  must "ConnIds §19.15 (7970) zero-length or over-length CID issued" (asBool (
    (ConnIds.Local.component.maySend { l0 with zeroLen := true }
        (.newConnectionId 1 0 (bytes [2]) (bytes (tok 2))) = false) &&
    (ConnIds.Local.component.maySend l0
        (.newConnectionId 1 0 (bytes (List.replicate 21 3)) (bytes (tok 2))) = false))),
  -- §19.15: Retire Prior To greater than the sequence number is not .ok.
  must "ConnIds §19.15 (7979) retire_prior_to greater than sequence accepted" (asBool (
    ConnIds.Remote.component.accepts r0 (.recvNewCid 2 3 [3] (tok 3)) (.ok r0 []) = false)),
  -- §19.15: one more active connection ID than we advertised is not .ok.
  must "ConnIds §19.15 (7985) a conflicting CID or one past the limit accepted" (asBool (
    ConnIds.Remote.component.accepts rFull (.recvNewCid 4 0 [5] (tok 5))
        (.ok (ConnIds.Remote.applyNcid rFull 4 0 [5] (tok 5)).1
          (ConnIds.Remote.applyNcid rFull 4 0 [5] (tok 5)).2) = false)),
  -- §19.15: a smaller Retire Prior To does not replace the largest one seen.
  must "ConnIds §19.15 (7998) retire_prior_to decreased" (asBool (
    ConnIds.Remote.component.accepts rRaised (.recvNewCid 6 1 [9] (tok 9))
        (.ok { rRaised with retirePriorTo := 1 } []) = false)),
  -- §19.15: a sequence number below a seen Retire Prior To is not left active.
  must "ConnIds §19.15 (8013) a retired CID still used (maySend / packet)" (asBool (
    (ConnIds.Remote.component.accepts rPrior (.recvNewCid 3 0 [9] (tok 9))
        (.ok { rPrior with entries := rPrior.entries ++ [⟨3, [9], tok 9⟩] } []) = false) &&
    ((ConnIds.Remote.component.step rPrior (.recvNewCid 3 0 [9] (tok 9))).next rPrior).isRetired 3
      = true)),
  -- §19.16: a sequence we were never issued is not retired, and retiring our own DCID is the error.
  must "ConnIds §19.16 (8050) retiring a sequence we never issued, accepted; or retiring our own CID" (asBool (
    (ConnIds.Remote.component.maySend r0 (.retireConnectionId 9) = false) &&
    (ConnIds.Local.component.accepts l0 (.recvRetireCid 1 none) (.ok l0 []) = false) &&
    (ConnIds.Local.component.step l0 (.recvRetireCid 0 (some 0)) = .error .protocolViolation))),

  -- §12.3: the next packet number does not increase.
  must "FrameRules §12.3 (4685) — this row names Ack.maySendPacketNumber. A non-increasing packet number. You may import Ack." (asBool (
    Ack.maySendPacketNumber aSent 5 = false)),
  -- §12.3: a packet number already used.
  must "FrameRules §12.3 (4692) packet number reuse" (asBool (
    Ack.maySendPacketNumber aSent 3 = false)),
  -- §12.3: 2^62-1 itself is not sent.
  must "FrameRules §12.3 (4693) packet number 2^62-1" (asBool (
    Ack.maySendPacketNumber a0 Ack.maxPn = false)),
  -- §12.4: a packet we send is not an empty frame list.
  must "FrameRules §12.4 (4740) an empty frame list sent as a packet that contains frames — maySendPacket false for []" (asBool (
    FrameRules.component.maySendPacket frSrv ⟨.oneRtt, []⟩ = false)),
  -- §12.4: an empty received packet is not .ok.
  must "FrameRules §12.4 (4742) an empty packet accepted as ok if the step only errors" (asBool (
    FrameRules.component.accepts frSrv (.recvPacketFrames .initial []) (.ok frSrv []) = false)),
  -- §12.4: STREAM is not a frame of an Initial packet.
  must "FrameRules §12.4 (4901) a frame forbidden in that packet type" (asBool (
    FrameRules.component.accepts frSrv
        (.recvFrame .initial (.stream 0 0 false ByteArray.empty))
        (.ok frSrv [.deliver (.stream 0 0 false ByteArray.empty)]) = false)),
  -- §12.5: a 0-RTT ACK does not acknowledge a packet this space never received.
  must "FrameRules §12.5 (4969)" (asBool (
    Ack.maySendPacket a0 { ptype := .zeroRtt, frames := [.ack 0 0 0 #[] none] } = false)),
  -- §12.5: ACK in 0-RTT is forbidden, not merely a MAY.
  must "FrameRules §12.5 (4978) a frame that is only MAY in 0-RTT sent as if required, or a forbidden 0-RTT frame; if both may and must-not exist, reject the must-not" (asBool (
    FrameRules.component.accepts frSrv
        (.recvFrame .zeroRtt (.ack 0 0 0 #[] none))
        (.ok frSrv [.deliver (.ack 0 0 0 #[] none)]) = false)),
  -- §19.7: a client does not send NEW_TOKEN.
  must "FrameRules §19.7 (7597) a client sending NEW_TOKEN" (asBool (
    FrameRules.component.maySendPacket frCli ⟨.oneRtt, [.newToken ByteArray.empty]⟩ = false)),
  -- §19.20: a client does not send HANDSHAKE_DONE.
  must "FrameRules §19.20 (8207) a client sending HANDSHAKE_DONE" (asBool (
    FrameRules.component.maySendPacket frCli ⟨.oneRtt, [.handshakeDone]⟩ = false)),

  -- §13.4.1: received ECN counts are feedback the endpoint still owes.
  must "Ecn §13.4.1 (5504) ECN counts changed and no feedback is owed when it should be, or a send without feedback when feedbackOwed — show the predicate flags the trace (feedbackOwed = true is the checker catching the violation)" (asBool (
    Ecn.feedbackOwed eCounted = true)),
  -- §13.4.2.1: a reordered ACK that does not advance the largest is not a failure.
  must "Ecn §13.4.2.1 (5612) failing validation on a reordered ACK that does not increase the largest" (asBool (
    Ecn.component.accepts eReordered
        (.recvAck 7 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩)
        (.ok eReordered.fail [.ecnValidationFailed, .disableEcn]) = false)),
  -- §13.4.2.2: after failure the endpoint does not mark ECT.
  must "Ecn §13.4.2.2 (5626) marking ECN after failure, mayMarkEcn false" (asBool (
    Ecn.mayMarkEcn eFailed true = false)),
  -- §13.4.2.2: a successful validation is not recorded as a failure.
  must "Ecn §13.4.2.2 (5634) an ACK that makes the path capable treated as failure" (asBool (
    Ecn.component.accepts eUnknown
        (.recvAck 1 (some ⟨0, 0, 1⟩) ⟨1, 1, 0⟩)
        (.ok eUnknown.fail [.ecnValidationFailed, .disableEcn]) = false)),
  -- §13.4.2.2: counts that fail validation are not a success, even from capable.
  must "Ecn §13.4.2.2 (5636) counts that must fail validation accepted as success" (asBool (
    Ecn.component.accepts eReordered
        (.recvAck 11 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩)
        (.ok (eReordered.recordCounts 11 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩) []) = false)),

  -- §13.3: a repeated RESET_STREAM keeps neither a new error code nor a new final size.
  must "Retransmission §13.3 (5359) resending RESET_STREAM with a different final size / error, maySend false" (asBool (
    (Retransmission.maySend rtReset (.resetStream 4 9 10) = false) &&
    (Retransmission.maySend rtReset (.resetStream 4 3 11) = false))),
  -- §13.3 SHOULD: MAX_STREAM_DATA after Size Known is not a MUST refusal.
  advice "Retransmission §13.3 (5393) advice MAX_STREAM_DATA after stop, prefix advice if only recommended" (asBool (
    Retransmission.maySend rtPastRecv (.maxStreamData 4 100) = false)),
  -- §13.3: a lost HANDSHAKE_DONE is still owed.
  must "Retransmission §13.3 (5445) HANDSHAKE_DONE was lost and the repair obligation is untrue when it should be owed — show owes is true (checker flags the missing retransmission)" (asBool (
    Retransmission.owes rtHsLost .handshakeDone = true)),
  -- §13.3 SHOULD: resending an acknowledged HANDSHAKE_DONE is not forbidden.
  advice "Retransmission §13.3 (5461) advice: retransmitting an already-acked frame is not a MUST rejection if only Recommended; if maySend forbids it, that Bool false is a rejection — use that if the code forbids it" (asBool (
    Retransmission.maySend rtHsAcked .handshakeDone = false)),
  -- §13.3: a loss of an in-flight packet with no congestion-control effect is not .ok.
  must "Retransmission §13.3 (5471) a loss that does not record a congestion-control action, if that effect is required and a no-effect outcome is rejected" (asBool (
    Retransmission.component.accepts rtInFlight (.lost rtp0)
        (.ok (rtInFlight.afterLost rtp0) []) = false)),

  -- §19.11: MAX_STREAMS above 2^60 is not accepted.
  must "Template §19.11 (7802) MAX_STREAMS above 2^60 accepted" (asBool (
    Template.component.accepts t0 (.recvMaxStreams .bidi (2 ^ 60 + 1)) (.ok t0 []) = false)),
  -- §19.11: a stale MAX_STREAMS does not raise the limit.
  must "Template §19.11 (7809) a stale MAX_STREAMS raises the limit" (asBool (
    Template.component.accepts t0 (.recvMaxStreams .uni 2)
        (.ok (t0.setPeerMax .uni 2) [.streamsAvailable .uni 2]) = false)),
]

end Quic.Violations.Rest
