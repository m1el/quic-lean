import QuicModel.Spec.Endpoint
import QuicModel.Spec.Template

/-!
  Exercises specification decision procedures on every differential-fuzzer
  input.  The corpus replay otherwise never reaches transport-parameter
  validation, version negotiation, Retry, migration, ECN validation, loss, or
  the closing period, because setup forces a single post-handshake path.

  Every call takes a value derived from the input bytes, so Lean cannot lift
  it to module initialisation (which the coverage measurement subtracts).
  The result is mixed into the returned word; the harness compares the
  transport-parameter half with ngtcp2's decoder.
-/
namespace Quic.Harness

open Quic Quic.Spec

def mix (h : UInt64) (n : Nat) : UInt64 :=
  (h * 33) ^^^ n.toUInt64

def mixB (h : UInt64) (b : Bool) : UInt64 :=
  mix h (if b then 1 else 0)

def nth (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (b[i]).toNat else 0

def nOut {σ ε} (l : List (Outcome σ ε)) : Nat := l.length

/-- A transport-parameter record that depends on the input, so neither the
    encoder nor the validity checks are closed terms. -/
def sampleParams (n : Nat) : TransportParams.TransportParams :=
  let cid := ByteArray.mk #[UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256)]
  { TransportParams.defaults with
    maxIdleTimeout := n
    initialMaxData := n + 1
    initialMaxStreamDataBidiRemote := n + 1
    initialMaxStreamsBidi := 1 + n % 4
    initialMaxStreamsUni := n % 3
    initialMaxStreamDataUni := n % 5
    maxAckDelay := 25 + n % 20
    activeConnectionIdLimit := if n % 7 = 0 then 0 else 2 + n % 3
    initialSourceConnectionId := some cid
    originalDestinationConnectionId := some cid }

def dupRaw (tp : TransportParams.TransportParams) : TransportParams.Raw :=
  -- Two separate spines: appending a list to itself cycles under the destructive append.
  TransportParams.toRaw tp ++ TransportParams.toRaw tp

/-- 0 = the bytes are not a parameter sequence, 1 = they are but fail a value
    rule, 2 = a sender of `senderServer` may send them. -/
@[export quic_h_params_status]
def paramsStatus (senderServer : UInt8) (b : ByteArray) : UInt8 :=
  let sender := if senderServer == 0 then Role.client else Role.server
  match TransportParams.decodeRaw b with
  | .error _ => 0
  | .ok raw =>
    match TransportParams.validate sender raw with
    | none => 1
    | some _ => 2

@[export quic_h_exercise]
def exercise (b : ByteArray) : UInt64 := Id.run do
  let n := nth b 0 + b.size
  let n1 := nth b 1
  let tp := sampleParams n
  let raw := TransportParams.toRaw tp
  let enc := TransportParams.encodeParams tp
  let sender := if n1 % 2 = 0 then Role.server else Role.client
  let mut h : UInt64 := 0
  -- §7.4 / §18.2, and the fuzz input's own bytes.
  h := mixB h (decide (TransportParams.Valid sender tp))
  h := mix h (nOut (TransportParams.outcomes ⟨sender.peer, none⟩ (.recvParams enc)))
  h := mix h (nOut (TransportParams.outcomes ⟨sender.peer, none⟩ (.recvParams b)))
  h := mixB h (TransportParams.duplicated (dupRaw tp))
  h := mixB h (TransportParams.recommendedParams (n % 2 = 0) (5 + n % 4) (1 + n % 3) tp)
  let remembered := TransportParams.remembered tp
  h := mixB h (TransportParams.zeroRttCompatible remembered tp)
  h := mixB h (TransportParams.zeroRttCompatibleStrict remembered tp)
  h := mix h (TransportParams.knownEntries raw).length
  -- §7.3 connection-ID match.
  let cid : List UInt8 := [UInt8.ofNat (n % 256)]
  let hs := Handshake.initClient cid cid
  h := mixB h (Handshake.cidMismatch hs tp)
  -- §12.5 frame-level ACK permission and §13.2.2's counter.
  let ack : Ack.State :=
    { space := .appData, received := [], minPn := 0, largest := none, largestTime := 0,
      largestAckEliciting := none, outstanding := [(n, 0), (n + 1, 1)],
      ackImmediately := false, largestSent := some (n + 3), maxAckDelay := 25000 }
  h := mix h ack.ackElicitingSinceAck
  h := mixB h (Ack.maySend ack .ping)
  -- §13.4 ECN validation, both the reordered-ACK exemption and a real check.
  let ecn : Ecn.State :=
    { space := .appData, ect0 := n % 5, sentEct0 := n % 5 + 1, largestAcked := some n }
  let counts : Quic.Ecn := { ect0 := n % 5 + 1, ect1 := 0, ce := 0 }
  let newly : Ecn.NewlyAcked := { total := 1, ect0 := 1, ect1 := 0 }
  h := mixB h (Ecn.increasesLargest ecn (n + 2))
  h := mixB h (Ecn.skipValidation ecn n)
  h := mixB h (Ecn.failsValidation ecn (some counts) newly)
  h := mixB h (Ecn.mayFailRemark ecn (some counts))
  h := mixB h (Ecn.canBecomeCapable ecn (some counts) newly)
  h := mix h (Ecn.State.recordCounts ecn (n + 2) (some counts) newly).ect0
  h := mix h (Ecn.State.recordAckedOnly ecn newly).markedAcked
  h := mixB h ((Ecn.State.fail ecn).phase == .failed)
  h := mixB h (Ecn.feedbackOwed { ecn with ect0 := n % 5 + 1 })
  h := mix h (nOut (Ecn.outcomes ecn (.recvAck (n + 2) (some counts) newly)))
  h := mix h (nOut (Ecn.outcomes ecn (.recvAck n none newly)))
  h := mix h (nOut (Ecn.outcomes ecn (.recvPacket .ect0 true)))
  h := mix h (nOut (Ecn.outcomes ecn (.lostMarked (n % 3))))
  -- §9 migration: a new peer address, a failed validation, a probe, a rebind.
  let p0 : Migration.Path := ⟨⟨0⟩, ⟨1⟩⟩
  let p1 : Migration.Path := ⟨⟨0⟩, ⟨2 + n % 3⟩⟩
  let mig := { (Migration.init .server p0 0) with handshakeConfirmed := true }
  h := mix h (nOut (Migration.outcomes mig (.recvPacket p1 (n + 1) false 0)))
  h := mix h (Migration.State.permit mig p1 (n + 1) false 0).largestPn
  h := mix h (Migration.State.permitFx mig p1).length
  h := mix h (nOut (Migration.outcomes mig (.requestProbe p1)))
  h := mix h (nOut (Migration.outcomes mig (.requestMigrate p1)))
  let failed := { mig with active := p1, lastValidated := some p0 }
  h := mix h (nOut (Migration.outcomes failed (.validationFailed p1)))
  h := mixB h (Migration.State.rebindKeepsCid mig p1 0)
  h := mixB h (Migration.State.otherValidating mig p0)
  let client := { (Migration.init .client p0 0) with
                  handshakeConfirmed := true, preferredPeer := some ⟨2⟩ }
  h := mix h (nOut (Migration.outcomes client (.validationSucceeded p1)))
  h := mix h (nOut (Migration.outcomes client (.learnPreferredAddress ⟨2 + n % 2⟩)))
  h := mix h (nOut (Migration.outcomes mig (.beginSendOn p1 0)))
  -- §8.2 path validation: a fresh challenge, then a repeat of its data.
  let data := ByteArray.mk #[UInt8.ofNat (n % 256), 1, 2, 3, 4, 5, 6, 7]
  let pv0 : PathValidation.State := PathValidation.init
  let started := PathValidation.outcomes pv0 (.startValidation ⟨n % 4⟩ data (1000 + n))
  h := mix h (nOut started)
  h := mixB h (pv0.hasData data)
  -- §13.3 loss of HANDSHAKE_DONE.
  let pkt : Retransmission.PktId := ⟨.appData, n⟩
  let sent := Retransmission.outcomes {} (.sentFrames pkt [.handshakeDone])
  h := mix h (nOut sent)
  h := mix h (nOut (Retransmission.outcomes {} (.lost pkt)))
  h := mixB h (Retransmission.owes {} .handshakeDone)
  h := mixB h (Retransmission.MustRetransmit .handshakeDone)
  h := mix h (Retransmission.State.newlyOwed {} n [.handshakeDone]).length
  -- §10 closing, stateless reset, and the Initial/Handshake close conversion.
  let term := Termination.init (30000000 + n) (30000000 + n % 5) (n % 2 = 0)
  h := mix h (nOut (Termination.outcomes term
        (.localError (n + 8) 100000 .protocolViolation (n % 9))))
  let closing : Termination.State :=
    { term with phase := .closing, closedWith := some (.transport .protocolViolation (n % 4)) }
  h := mix h (match closing.reason with | .transport _ ft => ft | .application c => c)
  h := mix h (nOut (Termination.outcomes closing (.recvPacket (n + 9) 100000 true)))
  h := mix h (nOut (Termination.outcomes term (.statelessReset (n + 9) 100000)))
  h := mixB h ((Termination.State.onStatelessReset term (n + 9) 100000).phase == .draining)
  let appClose := Frame.connectionClose (n % 16) none ByteArray.empty
  let conv := Termination.convertCloseForHandshake appClose
  h := mix h (match conv with | .connectionClose e _ _ => e | _ => 0)
  h := mixB h (Termination.maySendStatelessReset (n % 2 = 0) (40 + n % 50) (20 + n % 30))
  -- §17.2.5.1 Retry.
  let cidA := ByteArray.mk #[UInt8.ofNat (n % 256)]
  let cidB := ByteArray.mk #[UInt8.ofNat ((n + 1) % 256)]
  h := mixB h (AddressValidation.maySendRetry
        { clientDcid := cidA, clientScid := cidB, retryDcid := cidB, retryScid := cidA })
  h := mixB h (AddressValidation.atMostOneRetry
        [.sendRetry ⟨n % 4⟩, .sendRetry ⟨n % 4⟩])
  -- §6 version negotiation, both roles.
  let dcid := ByteArray.mk #[1, UInt8.ofNat (n % 256)]
  let scid := ByteArray.mk #[2, UInt8.ofNat ((n + 3) % 256)]
  h := mixB h (VersionNeg.isReservedVersion (0x0a0a0a0a + n % 2))
  let srv : VersionNeg.Server.State :=
    { supported := [1], advertised := [1, 0x0a0a0a0a], shortDcidLen := 8 }
  h := mix h (VersionNeg.Server.mkVersionNegotiation srv dcid scid).versions.length
  h := mix h (nOut (VersionNeg.Server.outcomes srv
        (.datagram (1200 + n % 20) (some (0x1a1a1a1a + n1)) dcid scid)))
  let cli : VersionNeg.Client.State :=
    { dcid, scid, chosen := 1, processedAny := false, abandoned := false }
  h := mix h (nOut (VersionNeg.Client.outcomes cli
        (.recvVersionNegotiation scid dcid [0x6b3343cf, 0x0a0a0a0a])))
  -- The template's MAX_STREAMS rules (the worked example of the framework).
  let tmpl : Template.State :=
    { peerMaxBidi := n % 8, peerMaxUni := 0, localMaxBidi := 4, localMaxUni := 2 }
  h := mix h (nOut (Template.outcomes tmpl (.recvMaxStreams .bidi (n % 8))))
  h := mix h (nOut (Template.outcomes tmpl (.recvMaxStreams .bidi (2 ^ 60 + 1))))
  h := mix h (tmpl.peerMax .bidi)
  return h

end Quic.Harness
