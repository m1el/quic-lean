import QuicModel.Spec.PathValidation
import QuicModel.Spec.FrameRules

/-!
  WP10 "Migration", part 1: the vocabulary, the state, the events and the
  effects of §9 Connection Migration.

  Text: draft-ietf-quic-transport-34 lines 3272–3812 (§9 and its subsections).

  File order follows `Spec/Template.lean`; this file is parts 1–1c, `Step.lean`
  is parts 2–5, `Send.lean` parts 6–7, `Theorems.lean` parts 8–9, and the
  coverage table and NOTES (part 10) are in `Spec/Migration.lean`.
-/
namespace Quic.Spec.Migration

/-! ## 1. State, events, effects -/

/-- The peer's transport address, shared with `AddressValidation` so that WP12
    can look up the anti-amplification budget of a path's peer address without a
    translation table (§8.2, line 3075: "an address is the two-tuple of IP
    address and port"). -/
abbrev PeerAddr := AddressValidation.Addr

/-- One of our own transport addresses.  Opaque: the model never inspects it,
    and equality of handles means equality of the two-tuple.  §9.5, line 3603
    and §9.2, line 3345 are both about *which* local address a packet leaves
    from, never about its value. -/
structure LocalAddr where
  id : Nat
  deriving DecidableEq, Repr

/-- A network path, as §9 uses the word: the pair of a local address and a peer
    address.  `PathValidation.Path` is an opaque handle for the same thing; WP12
    maps one to the other (see NOTES 1 in `Spec/Migration.lean`). -/
structure Path where
  loc : LocalAddr
  peer : PeerAddr
  deriving DecidableEq, Repr

/-- Mirrored from `PathValidation`, so that the two components agree on the
    vocabulary of §8.2 without this one embedding the challenge bookkeeping. -/
abbrev PathStatus := PathValidation.PathStatus

/-- §5.1.1, line 1698: "If the preferred_address transport parameter is sent,
    the sequence number of the supplied connection ID is 1." -/
def preferredAddressCidSeq : Nat := 1

/-- What this component needs to remember about one path.  `status` and
    `validating` mirror `PathValidation`; everything else is §9's own. -/
structure PathInfo where
  /-- §8.2: has path validation succeeded / failed on this path? -/
  status : PathStatus := .unvalidated
  /-- Is a path validation underway on this path?  Mirrors a non-empty
      `PathValidation.State.outstanding` for the path. -/
  validating : Bool := false
  /-- The largest packet number received on this path (§9.6.2, line 3730). -/
  largestPn : Nat := 0
  /-- §9, line 3324 and §9.6.2, line 3722: has a non-probing packet arrived from
      the peer on this path? -/
  sawNonProbing : Bool := false
  deriving DecidableEq, Repr

/-- What the endpoint is currently composing outgoing packets for: the path they
    leave on, and the sequence number of the Destination Connection ID they
    carry.  §9's send-side rules are all about this pair, which is why they are
    `MaySendPacket` rules rather than `MaySend` rules: `Spec.OutPacket` carries
    neither the path nor the connection ID. -/
structure SendCtx where
  path : Path
  dcidSeq : Nat
  deriving DecidableEq, Repr

/-- One endpoint's view of which path the connection uses. -/
structure State where
  role : Role
  /-- §9, line 3281: "the handshake is confirmed, as defined in section 4.1.2 of
      [QUIC-TLS]".  Set by an event; WP11 owns the real signal. -/
  handshakeConfirmed : Bool
  /-- The peer sent `disable_active_migration` (§9, line 3284; §18.2). -/
  peerDisableMigration : Bool
  /-- We sent `disable_active_migration`, so the peer is under the MUST NOT of
      §9, line 3284 and we are the endpoint of line 3289. -/
  ourDisableMigration : Bool
  /-- The peer issued us zero-length connection IDs, so the Destination
      Connection IDs we send are zero-length and have no sequence number
      (§9.5, line 3630). -/
  peerZeroLen : Bool
  /-- We issued zero-length connection IDs, so incoming packets carry no
      Destination Connection ID sequence number (§9.5, line 3633). -/
  ourZeroLen : Bool
  /-- §9, line 3279: "endpoints retaining a stable address for the duration of
      the handshake" — the path the handshake ran on. -/
  handshakePath : Path
  /-- §9.3, line 3387: the path non-probing packets are sent on. -/
  active : Path
  /-- §9.3.2, line 3452: "the last validated peer address", to revert to. -/
  lastValidated : Option Path
  /-- Everything known about the other paths. -/
  paths : Map Path PathInfo
  /-- Outgoing direction: the connection ID (by sequence number) in use as
      Destination Connection ID on each path (§9.5, lines 3603 and 3608). -/
  dcidOn : Map Path Nat
  /-- Incoming direction: the connection ID of ours (by sequence number) the
      peer addresses packets to on each path.  Observed, never enforced;
      §9.5, line 3615: "These requirements … apply only to the sending of
      packets". -/
  scidOn : Map Path Nat
  /-- §9.3, line 3387: the number of the highest-numbered non-probing packet
      received on the connection. -/
  largestPn : Nat
  /-- Client: the server's preferred address (§9.6.1), once learned. -/
  preferredPeer : Option PeerAddr
  /-- Server: our own preferred address, from the parameter we sent. -/
  preferredLocal : Option LocalAddr
  /-- §9, line 3287 and §5.2.2, line 1979: the client has acted on the
      `preferred_address` transport parameter.  Both roles track it: the client
      sets it when it starts validating the preferred address, the server when a
      packet from the client reaches that address. -/
  preferredActedOn : Bool
  /-- §9.3.2, line 3461: all connection state has been discarded. -/
  discarded : Bool
  /-- The path and Destination Connection ID outgoing packets use. -/
  tx : SendCtx
  deriving DecidableEq, Repr

/-- A connection that has just finished its handshake on `p`, with no other
    path known. -/
def init (role : Role) (p : Path) (dcidSeq : Nat) : State where
  role := role
  handshakeConfirmed := false
  peerDisableMigration := false
  ourDisableMigration := false
  peerZeroLen := false
  ourZeroLen := false
  handshakePath := p
  active := p
  lastValidated := some p
  paths := [(p, { status := .validated, sawNonProbing := true })]
  dcidOn := [(p, dcidSeq)]
  scidOn := []
  largestPn := 0
  preferredPeer := none
  preferredLocal := none
  preferredActedOn := false
  discarded := false
  tx := ⟨p, dcidSeq⟩

/-! ## 1b. Events and effects -/

inductive Event where
  /-- A packet arrived on path `p` with packet number `pn`, carrying only
      probing frames (`FrameRules.packetProbing`) or not, addressed to the
      connection ID of ours with sequence number `dcidSeq`. -/
  | recvPacket (p : Path) (pn : Nat) (probingOnly : Bool) (dcidSeq : Nat)
  /-- WP5's `PathValidation.Effect.pathValidated` for `p`. -/
  | validationSucceeded (p : Path)
  /-- WP5's `PathValidation.Effect.pathFailed` for `p`. -/
  | validationFailed (p : Path)
  /-- §9.2, line 3345: the application (or the lead) asks to migrate to `p`. -/
  | requestMigrate (p : Path)
  /-- §9.1, line 3331: … or to probe `p` without migrating. -/
  | requestProbe (p : Path)
  /-- §9, line 3281: the handshake is confirmed (WP11 owns the real signal). -/
  | handshakeConfirmed
  /-- §9.6.1, line 3686: a `preferred_address` transport parameter arrived. -/
  | learnPreferredAddress (a : PeerAddr)
  /-- §9.5, line 3600: "At any time, endpoints MAY change the Destination
      Connection ID they transmit with to a value that has not been used on
      another path" — and start composing packets for `p` with it. -/
  | beginSendOn (p : Path) (dcidSeq : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- Ask `PathValidation` to start a validation of `p` (§8.2.1). -/
  | startValidation (p : Path)
  /-- §9.3, line 3382: send subsequent packets to this path. -/
  | switchPath (p : Path)
  /-- §9.3.3, line 3498: validate the path we have just left. -/
  | validatePrevious (p : Path)
  /-- §9.6.3, line 3757: abandon the validation of another path. -/
  | abandonValidation (p : Path)
  /-- §9.3.2, line 3461: "MUST close the connection silently by discarding all
      connection state". -/
  | discardState
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

namespace State

/-! ### Reading the path table -/

def infoOf (s : State) (p : Path) : PathInfo := (s.paths.get? p).getD {}

def statusOf (s : State) (p : Path) : PathStatus := (s.infoOf p).status

def isValidated (s : State) (p : Path) : Bool := decide (s.statusOf p = .validated)

def setInfo (s : State) (p : Path) (f : PathInfo → PathInfo) : State :=
  { s with paths := s.paths.set p (f (s.infoOf p)) }

/-- §8.2.3: validation of `p` succeeded. -/
def markValidated (s : State) (p : Path) : State :=
  s.setInfo p (fun i => { i with status := .validated, validating := false })

/-- §8.2.4: validation of `p` was abandoned.  As in `PathValidation`
    (NOTES 7 there), a path that is already validated stays validated. -/
def markFailed (s : State) (p : Path) : State :=
  if s.isValidated p then s.setInfo p (fun i => { i with validating := false })
  else s.setInfo p (fun i => { i with status := .failed, validating := false })

/-- A path validation has been started on `p`. -/
def markValidating (s : State) (p : Path) : State :=
  s.setInfo p (fun i => { i with validating := true })

/-- Is a validation underway on some path other than `p`?  §9.6.3, line 3757
    turns on this ("the client MUST abandon validation of the original
    address"). -/
def otherValidating (s : State) (p : Path) : Bool :=
  s.paths.any (fun e => decide (e.1 ≠ p) && e.2.validating)

/-- Is there a validated path at all?  §9, line 3316: "When an endpoint has no
    validated path on which to send packets, it MAY discard connection state." -/
def hasValidatedPath (s : State) : Bool :=
  s.paths.any (fun e => decide (e.2.status = .validated))

/-- §9, line 3324: "until they see a non-probing packet from that address" —
    from the address, not from the path. -/
def sawNonProbingFrom (s : State) (a : PeerAddr) : Bool :=
  s.paths.any (fun e => decide (e.1.peer = a) && e.2.sawNonProbing)

/-! ### Preferred address (§9.6) -/

/-- Is `p` a path to (client) or from (server) the server's preferred address? -/
def isPreferredPath (s : State) (p : Path) : Bool :=
  match s.role with
  | .client => match s.preferredPeer with
               | some a => decide (p.peer = a)
               | none => false
  | .server => match s.preferredLocal with
               | some a => decide (p.loc = a)
               | none => false

/-- §9, line 3326: "If a client receives packets from an unknown server
    address, the client MUST discard these packets."  The addresses a client
    knows are the one the handshake ran on and the preferred address. -/
def knownServerAddr (s : State) (a : PeerAddr) : Bool :=
  decide (a = s.handshakePath.peer) ||
    (match s.preferredPeer with | some b => decide (a = b) | none => false)

/-- §9.6, line 3680: "If a client receives packets from a new server address
    when the client has not initiated a migration to that address, the client
    SHOULD discard these packets."  Only reachable for the preferred address,
    since an entirely unknown one is already covered by `knownServerAddr`. -/
def unsolicitedServer (s : State) (p : Path) : Bool :=
  decide (s.role = .client) && decide (p.peer ≠ s.active.peer) &&
    decide (p.peer ≠ s.handshakePath.peer) && !s.preferredActedOn

/-! ### The two migration bans of §9, lines 3280 and 3284 -/

/-- Send side, §9, line 3284: "If the peer sent the disable_active_migration
    transport parameter, an endpoint also MUST NOT send packets (including
    probing packets; see Section 9.1) from a different local address to the
    address the peer used during the handshake, unless the endpoint has acted on
    a preferred_address transport parameter from the peer." -/
def sendBanned (s : State) (p : Path) : Bool :=
  s.peerDisableMigration && decide (p.loc ≠ s.handshakePath.loc) &&
    decide (p.peer = s.handshakePath.peer) && !s.preferredActedOn

/-- Receive side, the mirror of `sendBanned`: the peer is sending to us from a
    new address of its own while we sent `disable_active_migration` and it has
    not acted on our `preferred_address` — §9, line 3289: "If the peer violates
    this requirement …". -/
def peerViolatesDisableMigration (s : State) (p : Path) : Bool :=
  s.ourDisableMigration && decide (p.peer ≠ s.active.peer) &&
    decide (p.loc = s.handshakePath.loc) && !s.preferredActedOn

/-! ### §9.5: which connection ID may be used where -/

/-- §9.5, line 3603: "An endpoint MUST NOT reuse a connection ID when sending
    from more than one local address, for example when initiating connection
    migration as described in Section 9.2 or when probing a new network path as
    described in Section 9.1." -/
def reusedAcrossLocal (s : State) (p : Path) (seq : Nat) : Bool :=
  s.dcidOn.any (fun e => decide (e.2 = seq) && decide (e.1.loc ≠ p.loc))

/-- §9.5, line 3608: "Similarly, an endpoint MUST NOT reuse a connection ID when
    sending to more than one destination address." -/
def reusedAcrossPeer (s : State) (p : Path) (seq : Nat) : Bool :=
  s.dcidOn.any (fun e => decide (e.2 = seq) && decide (e.1.peer ≠ p.peer))

/-- §9.5, line 3609: "Due to network changes outside the control of its peer, an
    endpoint might receive packets from a new source address with the same
    destination connection ID, in which case it MAY continue to use the current
    connection ID with the new remote address while still sending from the same
    local address."

    Operationally: some path `q` already sends with `seq`, leaves from the same
    local address as `p`, differs only in the peer address, and the packets that
    arrived on `p` carried the same Destination Connection ID as those on `q` —
    which is what makes this a rebinding rather than a migration. -/
def rebindKeepsCid (s : State) (p : Path) (seq : Nat) : Bool :=
  s.dcidOn.any (fun e =>
    decide (e.2 = seq) && decide (e.1.loc = p.loc) && decide (e.1.peer ≠ p.peer) &&
      (match s.scidOn.get? e.1, s.scidOn.get? p with
       | some a, some b => decide (a = b)
       | _, _ => false))

/-! ### Packet arrival -/

/-- §9.3, line 3387: "An endpoint only changes the address to which it sends
    packets in response to the highest-numbered non-probing packet." -/
def isHighest (s : State) (pn : Nat) : Bool := decide (s.largestPn < pn)

def isNewPeer (s : State) (p : Path) : Bool := decide (p.peer ≠ s.active.peer)

/-- §9, line 3312: "An endpoint MUST perform path validation (Section 8.2) if it
    detects any change to a peer's address, unless it has previously validated
    that address", and §9.6.2, line 3726: "The server MUST probe on the path
    toward the client from its preferred address." -/
def mustValidate (s : State) (p : Path) : Bool :=
  !s.isValidated p && (s.isNewPeer p || decide (p.loc ≠ s.active.loc))

/-- Everything a received packet records, whatever the endpoint then does with
    it: which connection ID of ours it was addressed to, the largest packet
    number on the path and on the connection, and whether a non-probing packet
    has now been seen from that address. -/
def recordRecv (s : State) (p : Path) (pn : Nat) (probingOnly : Bool) (dcidSeq : Nat) : State :=
  { s with
    scidOn := if s.ourZeroLen then s.scidOn else s.scidOn.set p dcidSeq,
    paths := s.paths.set p
      { (s.infoOf p) with
        largestPn := Nat.max (s.infoOf p).largestPn pn,
        sawNonProbing := (s.infoOf p).sawNonProbing || !probingOnly },
    largestPn := if probingOnly then s.largestPn else Nat.max s.largestPn pn,
    preferredActedOn := s.preferredActedOn || s.isPreferredPath p }

/-- §9.3, line 3382: start sending to `p`, remembering the path we leave if it
    was validated (§9.3.2, line 3452). -/
def switchTo (s : State) (p : Path) : State :=
  { s with active := p,
           lastValidated := if s.isValidated s.active then some s.active else s.lastValidated }

/-- §9.3.2, line 3452: "an endpoint MUST revert to using the last validated peer
    address when validation of a new peer address fails". -/
def revertTo (s : State) (p : Path) : State := { s with active := p }

/-- The endpoint takes note of the packet but keeps sending where it was:
    §9.1, line 3340 (a probing packet), §9.3, line 3387 (a reordered one), or
    §9.3, line 3382's "if" not being taken. -/
def observe (s : State) (p : Path) (pn : Nat) (probingOnly : Bool) (dcidSeq : Nat) : State :=
  if s.mustValidate p then (s.recordRecv p pn probingOnly dcidSeq).markValidating p
  else s.recordRecv p pn probingOnly dcidSeq

def observeFx (s : State) (p : Path) : List Effect :=
  if s.mustValidate p then [.startValidation p] else []

/-- §9.3, lines 3382–3385: "If the recipient permits the migration, it MUST send
    subsequent packets to the new peer address and MUST initiate path validation
    (Section 8.2) to verify the peer's ownership of the address if validation is
    not already underway", together with §9.3.3, line 3498: "In response to an
    apparent migration, endpoints MUST validate the previously active path using
    a PATH_CHALLENGE frame." -/
def permit (s : State) (p : Path) (pn : Nat) (probingOnly : Bool) (dcidSeq : Nat) : State :=
  (((if s.isValidated p then s.recordRecv p pn probingOnly dcidSeq
      else (s.recordRecv p pn probingOnly dcidSeq).markValidating p)).markValidating
    s.active).switchTo p

def permitFx (s : State) (p : Path) : List Effect :=
  (if s.isValidated p then [] else [Effect.startValidation p]) ++
    [Effect.switchPath p, Effect.validatePrevious s.active]

end State


/-! ## 1c. The receive-side case analysis

Every guard §9 places on an arriving packet, as one total function, so that
`Step`, `outcomes` and the theorems all name the same branches and
`outcomes_iff` is a case split on the result. -/

inductive RecvCase where
  /-- §9.3.2, line 3461: the connection state is gone. -/
  | gone
  /-- §9, line 3326: an unknown server address (client only) — MUST discard. -/
  | unknownServer
  /-- §9.6, line 3680: a new server address the client did not ask for. -/
  | unsolicited
  /-- Nothing that §9 lets change the sending path. -/
  | quiet
  /-- §9, line 3289: the peer migrated although we sent
      `disable_active_migration`. -/
  | banned
  /-- §9.3, line 3379: an apparent migration. -/
  | migrate
  deriving DecidableEq, Repr

def recvCase (s : State) (p : Path) (pn : Nat) (probingOnly : Bool) : RecvCase :=
  if s.discarded then .gone
  else if decide (s.role = .client) && !s.knownServerAddr p.peer then .unknownServer
  else if s.unsolicitedServer p then .unsolicited
  else if probingOnly then .quiet
  else if !s.isNewPeer p then .quiet
  else if !s.isHighest pn then .quiet
  else if decide (p.loc ≠ s.active.loc) then .quiet
  else if s.peerViolatesDisableMigration p then .banned
  else .migrate

end Quic.Spec.Migration
