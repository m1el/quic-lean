import QuicModel.Spec.Migration
import QuicModel.Spec.PathValidation
import QuicModel.Spec.AddressValidation
import QuicModel.Violations.Trace

/-!
  One manufactured violation per executable Migration, PathValidation, and
  AddressValidation requirement.  `true` means the verifier rejects that trace.
  Names starting with `advice:` are SHOULDs or MAYs the checker does not reject.
  Names starting with `nocode:` have no runtime predicate.
-/
namespace Quic.Violations.Migration

open Quic Quic.Spec

/-! ### Migration fixtures -/

def la0 : Migration.LocalAddr := ⟨0⟩
def la1 : Migration.LocalAddr := ⟨1⟩
def pa0 : Addr := ⟨0⟩
def pa1 : Addr := ⟨1⟩
def pa9 : Addr := ⟨9⟩
def p00 : Migration.Path := ⟨la0, pa0⟩
def p01 : Migration.Path := ⟨la0, pa1⟩
def p10 : Migration.Path := ⟨la1, pa0⟩
def p11 : Migration.Path := ⟨la1, pa1⟩

def c0 : CidBytes := [0, 0, 0, 0]
def c1 : CidBytes := [1, 1, 1, 1]

def ping : OutPacket := ⟨.oneRtt, [.ping]⟩
def probePkt : OutPacket := ⟨.oneRtt, [.pathChallenge ByteArray.empty]⟩

def dg (p : Migration.Path) (cid : Option CidBytes) (n : Nat) (pkts : List OutPacket) :
    OutDatagram :=
  { size := n, packets := pkts, src := ⟨p.loc.id⟩, dest := p.peer, dcid := cid }

def run (s : Migration.State) : List Migration.Event → Migration.State
  | [] => s
  | e :: es => run ((Migration.component.step s e).next s) es

/-- Handshake confirmed, peer connection IDs 0 and 1 known. -/
def srv : Migration.State :=
  run { (Migration.init .server p00 0) with handshakeConfirmed := true }
    [.learnPeerCid 0 c0, .learnPeerCid 1 c1]

def cli : Migration.State :=
  run { (Migration.init .client p00 0) with handshakeConfirmed := true }
    [.learnPeerCid 0 c0, .learnPeerCid 1 c1]

def unconfirmed : Migration.State := Migration.init .client p00 0

def cliNoMig : Migration.State := { cli with peerDisableMigration := true }

def srvNoMig : Migration.State := { srv with ourDisableMigration := true }

/-- No validated path left: failing `p01` may only wait or give up. -/
def noneLeft : Migration.State :=
  { (Migration.init .client p00 0) with
      handshakeConfirmed := true
      lastValidated := none
      paths := [(p00, { status := .failed }),
                (p01, { status := .unvalidated, validating := true })] }

def unk : Migration.Path := ⟨la0, pa9⟩

/-- Server has followed the peer to `p01`; the handshake path is the last validated one. -/
def srvAt5 : Migration.State :=
  (Migration.component.step srv (.recvPacket p01 5 false 0)).next srv

def srvNoLast : Migration.State := { srvAt5 with lastValidated := none }

def srvDiscarded : Migration.State :=
  (Migration.component.step srvNoLast (.validationFailed p01)).next srvNoLast

/-- Validation of the new peer address failed and the server reverted. -/
def srvBack : Migration.State :=
  (Migration.component.step srvAt5 (.validationFailed p01)).next srvAt5

def avTiny : AddressValidation.State :=
  (AddressValidation.init .server ByteArray.empty).addRecv pa1 10 false

def overProbe : OutDatagram :=
  { size := 301
    packets := [probePkt]
    src := ⟨la0.id⟩
    dest := pa1
    dcid := some c1 }

/-- Same connection ID, but the packets from the new source address use a different DCID of ours. -/
def rebindRefused : Migration.State :=
  run cli [.recvPacket p00 1 false 4, .recvPacket p01 2 false 5]

def cliPref : Migration.State :=
  (Migration.component.step cli (.learnPreferredAddress pa1)).next cli

def cliProbing : Migration.State :=
  (Migration.component.step cliPref (.requestMigrate p01)).next cliPref

def cliBad : Migration.State :=
  (Migration.component.step cliProbing (.validationFailed p01)).next cliProbing

def srvPref : Migration.State := { srv with preferredLocal := some la1 }

/-- A probe is already running on `p10` when the preferred path's validation succeeds. -/
def cliBoth : Migration.State :=
  run cli [.learnPreferredAddress pa1, .requestProbe p10]

/-- Preferred validation failed; reachability of the original server address from the new local address then succeeds. -/
def cliOrigOk : Migration.State :=
  run cli [.learnPreferredAddress pa1, .requestProbe p10, .requestMigrate p01,
           .validationFailed p01]

def moved : Migration.State :=
  (Migration.component.step cli (.beginSendOn p00 3)).next cli

/-! ### Path validation fixtures -/

def vp1 : PathValidation.Path := ⟨1⟩
def vp2 : PathValidation.Path := ⟨2⟩
def d8 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
def d8b : ByteArray := ⟨#[8, 7, 6, 5, 4, 3, 2, 1]⟩
def pv0 : PathValidation.State := PathValidation.init
def pv1 : PathValidation.State := pv0.addChallenge ⟨d8, vp1, 400⟩

def av600 : AddressValidation.State :=
  (AddressValidation.init .server ByteArray.empty).addRecv ⟨1⟩ 600 false
def av300 : AddressValidation.State :=
  (AddressValidation.init .server ByteArray.empty).addRecv ⟨1⟩ 300 false

def pdg (n : Nat) (fs : List Frame) : OutDatagram :=
  { size := n, packets := [⟨.oneRtt, fs⟩], dest := ⟨1⟩ }

def owed : PathValidation.State := { pv0 with pending := [(d8, vp1)] }
def sentOnce : PathValidation.State :=
  (PathValidation.component.step owed (.responseSent vp1 d8)).next owed

/-! ### Address validation fixtures -/

def a1 : Addr := ⟨1⟩
def a2 : Addr := ⟨2⟩
def cid0 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
def cid1 : ByteArray := ⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩
def tok : ByteArray := ⟨#[7, 7, 7, 7]⟩
def sv : AddressValidation.State :=
  (AddressValidation.init .server cid0).addRecv a1 1200 false
def cl : AddressValidation.State := AddressValidation.init .client cid0

def retryTok : AddressValidation.ClientToken := ⟨.retry, tok⟩
def emptyTok : AddressValidation.ClientToken := ⟨.retry, ByteArray.empty⟩

def clEcho : AddressValidation.State :=
  { cl with token := some retryTok, retriesAccepted := 1, sawServerPacket := true, dcid := cid0 }

def clEmpty : AddressValidation.State :=
  { cl with token := some emptyTok, retriesAccepted := 1, sawServerPacket := true, dcid := cid1 }

def checks : List Trace := [
  -- §9: a non-probing packet from a new local address before confirmation.
  must "Migration §9 (3280)" (Migration.component.maySendDatagram unconfirmed (dg p10 none 1200 [ping]) == false),
  -- §9: `disable_active_migration` also covers probing packets.
  must "Migration §9 (3284)" (Migration.component.maySendDatagram cliNoMig (dg p10 (some c1) 1200 [probePkt]) == false),
  -- §9: drop or a validating migration; a connection error is neither.
  must "Migration §9 (3289)" (Migration.component.accepts srvNoMig (.recvPacket p01 5 false 0)
      (.error .protocolViolation) == false),
  -- §9: a new peer address is taken in without starting path validation.
  must "Migration §9 (3312)" (Migration.component.accepts srv (.recvPacket p01 5 true 0)
      (.ok (srv.recordRecv p01 5 true 0) []) == false),
  -- §9: validation failed and nothing validated remains; keeping the new path is a third outcome.
  must "Migration §9 (3316)" (Migration.component.accepts noneLeft (.validationFailed p01)
      (.ok ((noneLeft.markFailed p01).switchTo p01) [.switchPath p01]) == false),
  -- §9: the other alternative's complement — an error, rather than waiting or discarding.
  must "Migration §9 (3317)" (Migration.component.accepts noneLeft (.validationFailed p01)
      (.error .noViablePath) == false),
  -- §9: a packet from an unknown server address becomes the active path.
  must "Migration §9 (3325)" (Migration.component.accepts cli (.recvPacket unk 5 false 0)
      (.ok (cli.switchTo unk) [.switchPath unk]) == false),
  -- §9.1: a probe that also switches the active path.
  must "Migration §9.1 (3331)" (Migration.component.accepts cli (.requestProbe p10)
      (.ok ((cli.startProbe p10).switchTo p10) [.startValidation p10, .switchPath p10]) == false),
  -- §9.2: before confirmation the migration is not applied, deferred or not.
  must "Migration §9.2 (3366)" (Migration.component.accepts unconfirmed (.requestMigrate p10)
      (.ok (unconfirmed.switchTo p10) [.switchPath p10]) == false),
  -- §9.3: neither permitting nor refusing; the packet is a connection error.
  must "Migration §9.3 (3382)" (Migration.component.accepts srv (.recvPacket p01 5 false 0)
      (.error .protocolViolation) == false),
  -- §9.3: a datagram to the peer address whose validation just failed, past the anti-amplification limit.
  must "Migration §9.3 (3392)" (decide (Migration.MaySendDatagramOn avTiny srvBack overProbe) == false),
  -- §9.3: non-probing send on a peer address that is still unvalidated.
  must "Migration §9.3 (3394)" (Migration.component.maySendDatagram srv (dg p01 (some c1) 1200 [ping]) == false),
  -- §9.3.2: validation of the active new path fails and the endpoint does not revert.
  must "Migration §9.3.2 (3452)" (Migration.component.accepts srvAt5 (.validationFailed p01)
      (.ok (srvAt5.markFailed p01) []) == false),
  -- §9.3.2: the connection has discarded its state and still sends.
  must "Migration §9.3.2 (3460)" (Migration.component.maySendPacket srvDiscarded ping == false),
  -- §9.3.3: the migration is taken but the previous path is not validated.
  must "Migration §9.3.3 (3498)" (Migration.component.accepts srv (.recvPacket p01 5 false 0)
      (.ok (srv.permit p01 5 false 0) [.startValidation p01, .switchPath p01]) == false),
  -- §9.5: `beginSendOn` with a connection ID already used on another path.
  must "Migration §9.5 (3600)" (Migration.component.accepts cli (.beginSendOn p10 0)
      (.ok (cli.useCid p10 0) []) == false),
  -- §9.5: connection ID 0 stays bound to its first local address.
  must "Migration §9.5 (3603)" (Migration.component.maySendDatagram moved (dg p10 (some c0) 1200 [ping]) == false),
  -- §9.5: the same connection ID to a second peer address, and this is not a rebind.
  must "Migration §9.5 (3608)" (Migration.component.maySendDatagram cli (dg p01 (some c0) 1200 [ping]) == false),
  -- §9.5: NAT rebind whose connection-ID check fails, so keeping the CID is refused.
  must "Migration §9.5 (3611)" ((!rebindRefused.rebindKeepsCid p01 0) &&
      (Migration.component.accepts rebindRefused (.beginSendOn p01 0)
        (.ok (rebindRefused.useCid p01 0) []) == false)),
  -- §9.6: drop and keep are both allowed; switching onto the unsolicited path is not.
  must "Migration §9.6 (3679)" (Migration.component.accepts cliPref (.recvPacket p01 5 false 0)
      (.ok (cliPref.permit p01 5 false 0) (cliPref.permitFx p01)) == false),
  -- §9.6.1: migrating to the preferred address before it is validated.
  must "Migration §9.6.1 (3701)" (Migration.component.accepts cliPref (.requestMigrate p01)
      (.ok (cliPref.switchTo p01) [.switchPath p01]) == false),
  -- §9.6.1 SHOULD: staying on the old address after success is still permitted.
  advice "Migration §9.6.1 (3707)" (Migration.component.accepts cliProbing (.validationSucceeded p01)
      (.ok (cliProbing.succStay p01) []) == false),
  -- §9.6.1: after the preferred address fails, a packet to it anyway.
  must "Migration §9.6.1 (3709)" (Migration.component.maySendDatagram cliBad (dg p01 (some c1) 1200 [ping]) == false),
  -- §9.6.2: the server switches to its preferred address before that path is validated.
  must "Migration §9.6.2 (3715)" (Migration.component.accepts srvPref (.requestMigrate p10)
      (.ok ((srvPref.startProbe p10).switchTo p10)
        [.startValidation p10, .switchPath p10]) == false),
  -- §9.6.2: a non-probing packet leaves from the preferred address before validation.
  must "Migration §9.6.2 (3721)" (Migration.component.maySendDatagram srvPref (dg p10 (some c1) 1200 [ping]) == false),
  -- §9.6.2: a packet at the preferred address is recorded and `mustValidate` is ignored.
  must "Migration §9.6.2 (3726)" (Migration.component.accepts srvPref (.recvPacket p10 5 true 0)
      (.ok (srvPref.recordRecv p10 5 true 0) []) == false),
  -- §9.6.3 SHOULD: a second concurrent probe is not forbidden.
  advice "Migration §9.6.3 (3746)" (Migration.component.accepts cliBoth (.requestProbe p01)
      (.ok (cliBoth.startProbe p01) [.startValidation p01]) == false),
  -- §9.6.3: preferred-address success while another validation runs, and the client does not switch.
  must "Migration §9.6.3 (3757)" (Migration.component.accepts cliBoth (.validationSucceeded p01)
      (.ok (cliBoth.succStay p01) []) == false),
  -- §9.6.3: success on the original server address does not permit switching; only staying does.
  must "Migration §9.6.3 (3759)" (Migration.component.accepts cliOrigOk (.validationSucceeded p10)
      (.ok (cliOrigOk.succSwitch p10) (cliOrigOk.succSwitchFx p10)) == false),
  -- §9.6.3: non-probing datagram toward the new client address at the preferred local address.
  must "Migration §9.6.3 (3766)" (Migration.component.maySendDatagram srvPref (dg p11 (some c1) 1200 [ping]) == false),
  -- §9.6.3: a different datagram under the same limit.
  must "Migration §9.6.3 (3772)" (Migration.component.maySendDatagram srvPref
      (dg p11 (some c1) 40 [⟨.initial, [.ping]⟩]) == false),

  -- §8.2: a PATH_RESPONSE for data we were never challenged with.
  must "PathValidation §8.2 (3108)" (PathValidation.component.maySend pv0 (.pathResponse d8) == false),
  -- §8.2.1: starting validation is `.ok` only; an error is not an outcome.
  must "PathValidation §8.2.1 (3141)" (PathValidation.component.accepts pv0 (.startValidation vp1 d8 400)
      (.error .protocolViolation) == false),
  -- §8.2.1 SHOULD NOT: two PATH_CHALLENGE frames in one packet are not rejected.
  advice "PathValidation §8.2.1 (3142)" (PathValidation.component.maySendPacket pv1
      ⟨.oneRtt, [.pathChallenge d8, .pathChallenge d8]⟩ == false),
  -- §8.2.1: no send queue and no clock, so the probe rate is not a predicate.
  unchecked "PathValidation §8.2.1 (3145)",
  -- §8.2.1: a PATH_CHALLENGE whose data is not an outstanding challenge.
  must "PathValidation §8.2.1 (3150)" (PathValidation.component.maySend pv0 (.pathChallenge d8) == false),
  -- §8.2.1: PATH_CHALLENGE datagram under 1200 while the anti-amplification limit would allow 1200.
  must "PathValidation §8.2.1 (3154)" (PathValidation.maySendDatagramOn av600 (pdg 900 [.pathChallenge d8]) == false),
  -- §8.2.2: the challenge is received and no PATH_RESPONSE is queued.
  must "PathValidation §8.2.2 (3177)" (PathValidation.component.accepts pv0 (.recvChallenge vp1 d8) (.ok pv0 []) == false),
  -- §8.2.2: the component has no notion of when a packet leaves.
  unchecked "PathValidation §8.2.2 (3179)",
  -- §8.2.2: PATH_RESPONSE owed on `vp2` and sent on `vp1`.
  must "PathValidation §8.2.2 (3183)" (PathValidation.maySendResponseOn { pv0 with pending := [(d8, vp2)] } d8 vp1 == false),
  -- §8.2.2: a response that matches nothing is treated as validation success.
  must "PathValidation §8.2.2 (3186)" (PathValidation.component.accepts pv1 (.recvResponse vp2 d8b)
      (.ok ((pv1.clearPath vp1).markValidated vp1) [.pathValidated vp1]) == false),
  -- §8.2.2: PATH_RESPONSE datagram under 1200 while expansion is required.
  must "PathValidation §8.2.2 (3197)" (PathValidation.maySendDatagramOn av600 (pdg 900 [.pathResponse d8]) == false),
  -- §8.2.2: expanding to 1200 when that datagram exceeds the anti-amplification limit.
  must "PathValidation §8.2.2 (3200)" (PathValidation.maySendDatagramOn av300 (pdg 1200 [.pathResponse d8]) == false),
  -- §8.2.2: the one owed PATH_RESPONSE has been sent; a second is refused.
  must "PathValidation §8.2.2 (3205)" (PathValidation.component.maySend sentOnce (.pathResponse d8) == false),
  -- §19.18: PATH_RESPONSE for data we never sent, accepted as a successful validation.
  must "PathValidation §19.18 (8110)" (PathValidation.component.accepts pv0 (.recvResponse vp1 d8)
      (.ok (pv0.markValidated vp1) [.pathValidated vp1]) == false),
  -- §19.17: a received PATH_CHALLENGE is dropped instead of answered.
  must "PathValidation §19.17 (8092)" (PathValidation.component.accepts pv0 (.recvChallenge vp1 d8) .drop == false),

  -- §8: more than three times the bytes received from an unvalidated address.
  must "AddressValidation §8 (2735)" (AddressValidation.component.maySendDatagram sv { size := 3601, packets := [], dest := a1 }
      == false),
  -- §8.1: both validating and not are permitted; dropping the event is not.
  must "AddressValidation §8.1 (2761)" (AddressValidation.component.accepts (AddressValidation.init .server cid0)
      (.peerUsedOurCid a1 true) .drop == false),
  -- §8.1: the budget is already spent; one more byte is refused.
  must "AddressValidation §8.1 (2773)" (AddressValidation.maySendTo (sv.addSent a1 3600) a1 1 == false),
  -- §8.1: a received datagram is discarded instead of counted.
  must "AddressValidation §8.1 (2776)" (AddressValidation.component.accepts sv (.datagramRecv a1 50 false) .drop == false),
  -- §8.1.2 SHOULD: proceeding on an invalid Retry token is still permitted.
  advice "AddressValidation §8.1.2 (2876)" (AddressValidation.component.accepts sv (.clientInitial a1 (.invalid .retry))
      (.ok sv [.handshakeProceeds a1]) == false),
  -- §8.1.3: the only outcome stores the token; an error does not.
  must "AddressValidation §8.1.3 (2899)" (AddressValidation.component.accepts cl (.recvNewToken tok) (.error .protocolViolation) == false),
  -- §8.1.3: a tokenless Initial is processed as a validated delivery.
  must "AddressValidation §8.1.3 (2919)" (AddressValidation.component.accepts sv (.clientInitial a1 .absent)
      (.ok (sv.validate a1) [.addressValidated a1, .handshakeProceeds a1]) == false),
  -- §8.1.3: an invalid token is treated as a valid one.
  must "AddressValidation §8.1.3 (2987)" (AddressValidation.component.accepts sv (.clientInitial a1 (.invalid .newToken))
      (.ok (sv.validate a1) [.addressValidated a1, .handshakeProceeds a1]) == false),
  -- §17.2.5.1: Retry Source Connection ID equals the client's Initial Destination Connection ID.
  must "AddressValidation §17.2.5.1 (6597)" (AddressValidation.maySendRetry
      { clientDcid := cid0, clientScid := cid1, retryDcid := cid1, retryScid := cid0 } == false),
  -- §17.2.5.1: that Retry is processed and installed as the new DCID.
  must "AddressValidation §17.2.5.1 (6598)" (AddressValidation.component.accepts cl (.recvRetry tok cid0 true)
      (.ok clEcho [.useToken tok, .useDcid cid0]) == false),
  -- §17.2.5.1: a well-formed Retry is dropped.
  must "AddressValidation §17.2.5.1 (6601)" (AddressValidation.component.accepts cl (.recvRetry tok cid1 true) .drop == false),
  -- §17.2.5.1: two Retry effects from one received datagram.
  must "AddressValidation §17.2.5.1 (6616)" (AddressValidation.atMostOneRetry [.sendRetry a1, .sendRetry a2] == false),
  -- §17.2.5.2: an empty Retry token is accepted.
  must "AddressValidation §17.2.5.2 (6630)" (AddressValidation.component.accepts cl (.recvRetry ByteArray.empty cid1 true)
      (.ok clEmpty [.useToken ByteArray.empty, .useDcid cid1]) == false),
]

end Quic.Violations.Migration
