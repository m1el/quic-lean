import QuicModel.Spec.Termination
import QuicModel.Spec.DatagramSize
import QuicModel.Spec.VersionNegotiation
import QuicModel.Spec.Handshake
import QuicModel.Violations.Trace

/-!
  One manufactured violation per named Termination, DatagramSize,
  VersionNegotiation, and Handshake requirement.
  `true` means the verifier rejects that trace.
  Names starting with `advice:` are SHOULDs or MAYs the checker does not reject.
-/
open Quic Quic.Spec

namespace Quic.Violations.Termination

def active : Termination.State := Termination.init 100 100 false

def closing : Termination.State :=
  active.toClosing 0 10 (.transport .protocolViolation 0)

def draining : Termination.State :=
  active.toDraining 0 10 (some (.transport .protocolViolation 0))

def closed : Termination.State := active.toClosed

def dg (role : Role) (usable : Bool) (maxSz : Nat := 1200) : DatagramSize.State :=
  { role, peerMaxUdpPayload := none, maxDatagramSize := maxSz,
    pathUsable := usable, runsPmtuDiscovery := false }

def cliDg : DatagramSize.State := dg .client true
def srvDg : DatagramSize.State := dg .server true

def pkt (pt : PacketType) (fs : List Frame) : OutPacket := { ptype := pt, frames := fs }

def vnSrv : VersionNeg.Server.State :=
  { supported := [versionV1], advertised := [versionV1], shortDcidLen := 8 }

def vnCli : VersionNeg.Client.State :=
  { dcid := ⟨#[1, 2, 3, 4]⟩, scid := ⟨#[9, 9]⟩, chosen := versionV1,
    processedAny := false, abandoned := false }

def vnDc : ByteArray := ⟨#[1, 2, 3]⟩
def vnSc : ByteArray := ⟨#[9]⟩

def echoed (vs : List Nat) : VersionNeg.Client.Event :=
  .recvVersionNegotiation ⟨#[9, 9]⟩ ⟨#[1, 2, 3, 4]⟩ vs

def hsCli : Handshake.State :=
  Handshake.initClient [0xc1] (List.replicate 8 0x51)

def hsCli1 : Handshake.State := hsCli.adoptScid [0x53]

def hsSrv : Handshake.State := Handshake.initServer [0x53]

def dgram (pt : PacketType) (dcid scid : List UInt8) : OutDatagram :=
  { size := 1200, packets := [pkt pt [.ping]], dcid := some dcid, scid := some scid }

def badSource : Handshake.Params :=
  { TransportParams.defaults with
    originalDestinationConnectionId := some (bytes (List.replicate 8 0x51)),
    initialSourceConnectionId := some (bytes [0x99]) }

def badOdcid : Handshake.Params :=
  { TransportParams.defaults with
    originalDestinationConnectionId := some (bytes [0x11]),
    initialSourceConnectionId := some (bytes [0x53]) }

def checks : List Trace := [
  -- §10.1: effective idle is at least 3×PTO. Negotiated 100µs must not close the connection.
  must "Termination §10.1 (3848)" (let pto := 100
    let now := active.idleStart + active.negotiatedIdle + 1
    (decide (active.effectiveIdle pto < 3 * pto) == false) &&
      (Termination.component.accepts active (.tick now pto)
        (.ok active.toClosed [.discardState]) == false) &&
      (Termination.component.accepts active (.tick now pto)
        (.error .protocolViolation) == false)),
  -- §10.2 SHOULD: a close period shorter than 3×PTO is not rejected.
  advice "Termination §10.2 (3939)" (let s := { closing with closeDeadline := 1 }
    Termination.component.accepts s (.tick 1 10)
      (.ok s.toClosed [.discardState]) == false),
  -- §10.2: ending the period before the deadline when mayEndEarly is false.
  must "Termination §10.2 (3946)" (Termination.component.accepts closing (.tick 1 10)
      (.ok closing.toClosed [.discardState]) == false),
  -- §10.2: a packet in the closed state handled like an active packet.
  must "Termination §10.2 (3954)" (Termination.component.accepts closed (.recvPacket 1 10 true)
      (.ok (closed.restartIdle 1) []) == false),
  -- §10.2.1 SHOULD: answering while closing is also permitted, so not rejected.
  advice "Termination §10.2.1 (3969)" (Termination.component.accepts closing (.recvPacket 1 10 true)
      (.ok closing [.sendClose closing.reason]) == false),
  -- Same SHOULD, for a CONNECTION_CLOSE packet rather than an ordinary one.
  advice "Termination §10.2.1 (3981, 3983, 3985)" (Termination.component.accepts closing
      (.recvClose 1 10 (.transport .noError 0) true)
      (.ok closing [.sendClose closing.reason]) == false),
  -- §10.2.1: a closing packet that is only a PATH_CHALLENGE, not a close.
  must "Termination §10.2.1 (3992)" (Termination.maySendPacket closing
      (pkt .oneRtt [.pathChallenge ByteArray.empty]) == false),
  -- §10.2.1: respond and stay silent are both permitted; a third send is not.
  must "Termination §10.2.1 (3995)" (Termination.component.accepts closing (.recvPacket 1 10 true)
      (.ok closing [.sendFarewellClose]) == false),
  -- §10.2.1: an unvalidated packet while closing is processed as a normal one.
  must "Termination §10.2.1 (4008)" (Termination.component.accepts closing (.recvPacket 1 10 false)
      (.ok (closing.restartIdle 1) []) == false),
  -- §10.2.2: any frame in the draining state.
  must "Termination §10.2.2 (4023)" (Termination.maySend draining .ping == false),
  -- §10.2.2: the farewell close was the last packet; another one is sent.
  must "Termination §10.2.2 (4037)" (Termination.component.accepts draining
      (.recvClose 5 10 (.application 1) true)
      (.ok draining [.sendFarewellClose]) == false),
  -- §10.2.2: leaving closing for closed rather than draining.
  must "Termination §10.2.2 (4044)" (Termination.component.accepts closing
      (.recvClose 2 10 (.transport .noError 0) true)
      (.ok closing.toClosed []) == false),
  -- §10.2.3: after confirmation a closing packet that is not a close.
  must "Termination §10.2.3 (4056)" (let s := { closing with handshakeConfirmed := true }
    Termination.maySendPacket s (pkt .oneRtt [.ping]) == false),
  -- §10.2.3: an application CONNECTION_CLOSE in a Handshake packet before confirmation.
  must "Termination §10.2.3 (4058, 4067, 4078)" (Termination.maySendPacket { active with handshakeConfirmed := false }
      (pkt .handshake [.connectionClose 7 none ByteArray.empty]) == false),
  -- §10.2.3: the application close sent unchanged, without the handshake conversion.
  must "Termination §10.2.3 (4084, 4095)" (let f : Frame := .connectionClose 99 none (bytes [0x68])
    (decide (f ≠ Termination.convertCloseForHandshake f)) &&
      (Termination.maySendCloseIn false .initial f == false)),
  -- §10.3: a packet in closed becomes an error, not a reset or a discard.
  must "Termination §10.3 (4125)" (Termination.component.accepts closed (.recvPacket 1 10 true)
      (.error .protocolViolation) == false),
  -- §10.3: a stateless reset while the endpoint can still send.
  must "Termination §10.3 (4129)" (Termination.component.accepts active (.recvPacket 1 10 true)
      (.ok active [.sendStatelessReset]) == false),
  -- §10.3: a reset at least three times the trigger, even with anti-loop state.
  must "Termination §10.3 (4215)" (Termination.maySendStatelessReset true 40 120 == false),
  -- §10.3.1: a stateless reset that does not enter draining.
  must "Termination §10.3.1 (4323)" (Termination.component.accepts active (.statelessReset 1 10)
      (.ok active []) == false),
  -- §10.3.3: a reset that is not smaller than the packet that triggered it.
  must "Termination §10.3.3 (4393)" (Termination.maySendStatelessReset false 50 60 == false),
  -- §11: an error while active that does not signal a close.
  must "Termination §11 (4415)" (Termination.component.accepts active
      (.localError 1 10 .protocolViolation 0) (.error .protocolViolation) == false),
  -- §11: a specific code standing in for a different specific code.
  must "Termination §11 (4434)" (Quic.Spec.Obs.matchesSpec (ε := Termination.Effect)
      (.error .flowControlError) (.error .streamLimitError) == false),
  -- §11.1: a local error moves to closing without a CONNECTION_CLOSE.
  must "Termination §11.1 (4446)" (let s' := active.toClosing 1 10 (.transport .protocolViolation 0)
    Termination.component.accepts active
      (.localError 1 10 .protocolViolation 0) (.ok s' []) == false),
  -- §11.1: a later close carries a different error than the recorded reason.
  must "Termination §11.1 (4457)" (Termination.component.accepts closing (.recvPacket 2 10 true)
      (.ok closing [.sendClose (.transport .flowControlError 1)]) == false),
  -- §12.3: packet-number exhaustion sends a CONNECTION_CLOSE.
  must "Termination §12.3 (4693)" (Termination.component.accepts active (.pnExhausted 1 10)
      (.ok active.toClosed [.sendClose (.transport .noError 0)]) == false),
  -- §12.3: after closed, a fresh close rather than at most a stateless reset.
  must "Termination §12.3 (4696)" (Termination.component.accepts closed (.recvPacket 1 10 true)
      (.ok closed [.sendClose closed.reason]) == false),

  -- §14: on a path that cannot carry 1200 bytes, a non-probe is sent.
  must "DatagramSize §14 (5649)" (DatagramSize.maySendDatagram { cliDg with pathUsable := false }
      { size := 2000, packets := [pkt .oneRtt [.ping]] } == false),
  -- §14: closing because a datagram had the wrong size.
  must "DatagramSize §14 (5695)" (DatagramSize.component.accepts srvDg (.recvDatagram 20 1200)
      (.error .protocolViolation) == false),
  -- §14 MAY: delivering a datagram that fails its size constraint is permitted.
  advice "DatagramSize §14 (5697)" (DatagramSize.component.accepts srvDg (.recvDatagram 20 1200)
      (.ok srvDg [.deliver]) == false),
  -- §14.1: a client Initial datagram under 1200 bytes.
  must "DatagramSize §14.1 (5701)" (DatagramSize.maySendDatagram cliDg
      { size := 1199, packets := [pkt .initial [.crypto 0 ByteArray.empty]] } == false),
  -- §14.1: a server ack-eliciting Initial under 1200 bytes.
  must "DatagramSize §14.1 (5706)" (DatagramSize.maySendDatagram srvDg
      { size := 1199, packets := [pkt .initial [.ping]] } == false),
  -- §14.1: a client Initial that is only an ACK is still under the minimum.
  must "DatagramSize §14.1 (5723)" (DatagramSize.maySendDatagram cliDg
      { size := 1199, packets := [pkt .initial [.ack 0 0 0 #[] none]] } == false),
  -- §14.1: a too-small Initial is processed.
  must "DatagramSize §14.1 (5727)" (DatagramSize.component.accepts srvDg (.recvInitial 1199)
      (.ok srvDg [.deliver]) == false),
  -- §14.1 MAY: closing on a too-small Initial is permitted, so not rejected.
  advice "DatagramSize §14.1 (5729)" (DatagramSize.component.accepts srvDg (.recvInitial 1199)
      (.error .protocolViolation) == false),
  -- §14.2: an Initial on a path already declared lost.
  must "DatagramSize §14.2 (5758)" (DatagramSize.maySendDatagram { cliDg with pathUsable := false }
      { size := 1200, packets := [pkt .initial [.crypto 0 ByteArray.empty]] } == false),
  -- §14.2: the connection is closed while an alternative path exists.
  must "DatagramSize §14.2 (5762)" (DatagramSize.component.accepts cliDg (.pathBelowMinimum true)
      (.error .noViablePath) == false),
  -- §14.2: a PMTU probe that is not ack-eliciting.
  must "DatagramSize §14.2 (5778)" (DatagramSize.maySendDatagram cliDg
      { size := 1400, packets := [pkt .oneRtt [.padding 100]], isPmtuProbe := true } == false),
  -- §14.2.1: ICMP below the minimum changes the MTU.
  must "DatagramSize §14.2.1 (5793)" (let s := { cliDg with maxDatagramSize := 1452 }
    DatagramSize.component.accepts s (.icmpPtb 1199)
      (.ok { s with maxDatagramSize := 1199 } []) == false),
  -- §14.2.1: ICMP increases the MTU.
  must "DatagramSize §14.2.1 (5813)" (let s := { cliDg with maxDatagramSize := 1280 }
    DatagramSize.component.accepts s (.icmpPtb 1452)
      (.ok { s with maxDatagramSize := 1452 } []) == false),
  -- §14.2.1 MAY: reducing immediately is permitted alongside deferring.
  advice "DatagramSize §14.2.1 (5814)" (let s := { cliDg with maxDatagramSize := 1452 }
    DatagramSize.component.accepts s (.icmpPtb 1280)
      (.ok { s with maxDatagramSize := 1280 } []) == false),
  -- §5.2: a small Initial is kept, neither discarded nor closed.
  must "DatagramSize §5.2 (1878)" (DatagramSize.component.accepts srvDg (.recvInitial 1199) (.ok srvDg []) == false),
  -- §11.1: the same discard rule on a server whose maximum is larger.
  must "DatagramSize §11.1 (4485)" (let s := dg .server true 1500
    DatagramSize.component.accepts s (.recvInitial 800)
      (.ok s [.deliver]) == false),

  -- §5.2: a packet that must be dropped is processed.
  must "VersionNegotiation §5.2 (1878)" (VersionNeg.Client.component.accepts vnCli
      (.recvOther (some versionV2) false)
      (.ok { vnCli with processedAny := true } [.deliver]) == false),
  -- §5.2.1: a not-yet-decryptable packet is acted on.
  must "VersionNegotiation §5.2.1 (1893)" (VersionNeg.Client.component.accepts vnCli
      (.recvOther (some versionV1) false)
      (.ok { vnCli with processedAny := true } [.deliver]) == false),
  -- §5.2.1: a packet of the wrong version is accepted.
  must "VersionNegotiation §5.2.1 (1898)" (VersionNeg.Client.component.accepts vnCli
      (.recvOther (some versionV2) true)
      (.ok { vnCli with processedAny := true } [.deliver]) == false),
  -- §5.2.2: an unsupported version is delivered, neither answered nor dropped.
  must "VersionNegotiation §5.2.2 (1911)" (VersionNeg.Server.component.accepts vnSrv
      (.datagram 1200 (some 0xff00001d) vnDc vnSc)
      (.ok vnSrv [.deliver]) == false),
  -- §5.2.2: a too-small unsupported datagram is answered.
  must "VersionNegotiation §5.2.2 (1914)" (let vn := VersionNeg.Server.mkVersionNegotiation vnSrv vnDc vnSc
    VersionNeg.Server.component.accepts vnSrv
      (.datagram 1199 (some 0xff00001d) vnDc vnSc)
      (.ok vnSrv [.sendVersionNegotiation vn]) == false),
  -- §5.2.2: a too-small unsupported datagram is processed.
  must "VersionNegotiation §5.2.2 (1916)" (VersionNeg.Server.component.accepts vnSrv
      (.datagram 1199 (some 0xff00001d) vnDc vnSc)
      (.ok vnSrv [.deliver]) == false),
  -- §5.2.2: the server reacts to a Version Negotiation packet.
  must "VersionNegotiation §5.2.2 (1923)" (VersionNeg.Server.component.accepts vnSrv
      (.datagram 1200 (some VersionNeg.versionNegotiationVersion) vnDc vnSc)
      (.ok vnSrv [.deliver]) == false),
  -- §5.2.2: a datagram the server event does not recognize is not an event.
  must "VersionNegotiation §5.2.2 (1946)" ((VersionNeg.Server.eventOfDatagram vnSrv
      ⟨#[0xc0, 0xff, 0x00, 0x00, 0x1d, 2, 1, 2, 1, 9]⟩).isSome == false),
  -- §6: a Version Negotiation response to a datagram under 1200 bytes.
  must "VersionNegotiation §6 (2051)" (let vn := VersionNeg.Server.mkVersionNegotiation vnSrv vnDc vnSc
    VersionNeg.Server.maySendVn vnSrv
      (.datagram 1199 (some 0xff00001d) vnDc vnSc) vn == false),
  -- §6.1: a Version Negotiation packet sent in response to one.
  must "VersionNegotiation §6.1 (2066)" (let vn := VersionNeg.Server.mkVersionNegotiation vnSrv vnDc vnSc
    VersionNeg.Server.component.accepts vnSrv
      (.datagram 1200 (some VersionNeg.versionNegotiationVersion) vnDc vnSc)
      (.ok vnSrv [.sendVersionNegotiation vn]) == false),
  -- §6.1: an unsupported version that must be silent gets a Version Negotiation.
  must "VersionNegotiation §6.1 (2083)" (let vn := VersionNeg.Server.mkVersionNegotiation vnSrv vnDc vnSc
    VersionNeg.Server.maySendVn vnSrv
      (.datagram 1200 (some VersionNeg.versionNegotiationVersion) vnDc vnSc) vn == false),
  -- §6.2: abandon is always permitted; continuing after it is not.
  must "VersionNegotiation §6.2 (2098)" (let s := vnCli.afterVn
    VersionNeg.Client.component.accepts s
      (.recvOther (some versionV1) true)
      (.ok { s with processedAny := true } [.deliver]) == false),
  -- §6.2: acting on a second Version Negotiation packet.
  must "VersionNegotiation §6.2 (2100)" (let s := { vnCli with processedAny := true }
    VersionNeg.Client.component.accepts s (echoed [0xff00001d])
      (.ok s.afterVn [.abandon]) == false),
  -- §6.2: acting on a Version Negotiation packet that lists the chosen version.
  must "VersionNegotiation §6.2 (2103)" (VersionNeg.Client.component.accepts vnCli (echoed [versionV1])
      (.ok vnCli.afterVn [.abandon]) == false),
  -- §6.2.1: a Version Negotiation handled as an ordinary packet.
  must "VersionNegotiation §6.2.1 (2115)" (VersionNeg.Client.component.accepts vnCli (echoed [0xff00001d])
      (.ok { vnCli with processedAny := true } [.deliver]) == false),
  -- §6.2.1: a Version Negotiation whose connection IDs do not match, accepted.
  must "VersionNegotiation §6.2.1 (2120)" (VersionNeg.Client.component.accepts vnCli
      (.recvVersionNegotiation ⟨#[7, 7]⟩ ⟨#[1, 2, 3, 4]⟩ [0xff00001d])
      (.ok vnCli.afterVn [.attemptVersion 0xff00001d]) == false),
  -- §15: a reserved version used as a real version to retry.
  must "VersionNegotiation §15 (5947)" (let v := 0x1a2a3a4a
    (VersionNeg.isReservedVersion v) &&
      (VersionNeg.Client.component.accepts vnCli (echoed [v])
        (.ok vnCli.afterVn [.attemptVersion v]) == false)),
  -- §17.2.1: a Version Negotiation packet that does not echo the client's CIDs.
  must "VersionNegotiation §17.2.1 (6260)" (let bad : VersionNeg.Server.Vn :=
      { dcid := vnDc, scid := vnSc, versions := vnSrv.advertised }
    VersionNeg.Server.maySendVn vnSrv
      (.datagram 1200 (some 0xff00001d) vnDc vnSc) bad == false),

  -- §7.2: first flight whose Destination Connection ID is not the original.
  must "Handshake §7.2 (2340)" (Handshake.component.maySendDatagram hsCli
      (dgram .initial (List.replicate 8 0x99) [0xc1]) == false),
  -- §7.2: a later Destination Connection ID that was never adopted.
  must "Handshake §7.2 (2341)" (Handshake.maySendDatagramOn (some []) hsCli1
      (dgram .handshake (List.replicate 8 0x99) [0xc1]) == false),
  -- §7.3: transport parameters whose initial source CID does not match, accepted.
  must "Handshake §7.3 (2421)" (Handshake.component.accepts hsCli1
      (.tlsPeerParams (TransportParams.encodeParams badSource))
      (.ok { hsCli1 with peerParams := some badSource } [.peerParams badSource]) == false),
  -- §7.3: the original Destination Connection ID does not match, accepted.
  must "Handshake §7.3 (2418)" (Handshake.component.accepts hsCli1
      (.tlsPeerParams (TransportParams.encodeParams badOdcid))
      (.ok { hsCli1 with peerParams := some badOdcid } [.peerParams badOdcid]) == false),
  -- §17.2.3: 0-RTT after the client has started processing 1-RTT.
  must "Handshake §17.2.3 (6476)" (let s := { hsCli1 with
      write := { hsCli1.write with zeroRtt := .present }, processed1Rtt := true }
    Handshake.component.maySendPacket s (pkt .zeroRtt [.ping]) == false),
  -- §17.2.3 SHOULD: 0-RTT is still accepted when remembered limits are incompatible.
  advice "Handshake §17.2.3 (6483)" (let old := { TransportParams.defaults with initialMaxData := 100 }
    let new := { TransportParams.defaults with initialMaxData := 50 }
    ((TransportParams.zeroRttCompatible old new == false) &&
        Handshake.component.accepts hsSrv (.tlsZeroRtt true)
          (.ok { hsSrv with zeroRtt := .accepted } [])) == false),
  -- §19.20: a client sends HANDSHAKE_DONE.
  must "Handshake §19.20 (8207)" (Handshake.maySend { hsCli1 with complete := true } .handshakeDone == false),
  -- §19.20: a server treats HANDSHAKE_DONE as handshake completion.
  must "Handshake §19.20 (8208)" (Handshake.component.accepts hsSrv .recvHandshakeDone
      (.ok { hsSrv with complete := true, confirmed := true }
        [.handshakeComplete, .handshakeConfirmed]) == false),
]

end Quic.Violations.Termination
