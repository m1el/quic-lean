import QuicModel.Spec.Endpoint.Lemmas
import QuicModel.Spec.Retransmission
import QuicModel.Spec.Ecn

/-!
  WP12 "Endpoint", part 1: the configuration, the composed state, the events and
  the effects, and the invariant.

  `Endpoint.State` is the product of every merged component's state, plus the
  handful of fields that belong to no component: the endpoint's role, the
  parameters of packet protection that the decoder needs (`shortDcidLen`,
  `tagLen`, `greaseQuicBit`), the current probe timeout (RFC 9002, out of scope,
  so it is carried and never computed), and the registry that gives every
  `Migration.Path` a `PathValidation.Path` handle.

  Packet protection itself (`Quic.Protection`) is *not* in the state: it is a
  record of functions and so has no `DecidableEq`.  It is a parameter of
  `Endpoint.component`, exactly as `Quic.decodePacket` takes it.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## 1a. Configuration -/

/-- Everything an endpoint needs to start a connection.  The transport
    parameters arrive as already-decoded numbers: decoding and validating them
    is WP1's `TransportParams`, and WP11's `Handshake` is what authenticates
    them, so `Config` is what is left once both have run. -/
structure Config where
  role : Role
  /-- §18.2, as `StreamTable.Limits`: the limits we advertised. -/
  ours : StreamTable.Limits
  /-- The limits the peer advertised. -/
  theirs : StreamTable.Limits
  /-- §7.2: the Source Connection ID we put in our own packets (sequence
      number 0 of the connection IDs we have issued). -/
  localCid : ConnIds.Cid
  /-- §19.15: the stateless reset token that goes with it. -/
  localToken : ConnIds.ResetToken
  /-- §7.2: the peer's Source Connection ID (= our Destination Connection ID),
      sequence number 0 of the connection IDs the peer has issued to us. -/
  peerCid : ConnIds.Cid
  peerToken : ConnIds.ResetToken
  /-- §7.3: the Destination Connection ID of the client's first Initial. -/
  origDcid : ConnIds.Cid
  /-- §18.2 `active_connection_id_limit` we advertised and the peer advertised. -/
  localCidLimit : Nat
  peerCidLimit : Nat
  /-- §18.2 `max_idle_timeout`, ours and the peer's, in µs. -/
  localMaxIdle : Nat
  peerMaxIdle : Nat
  /-- §18.2 `max_ack_delay`, in µs. -/
  maxAckDelay : Time
  /-- §10.2, line 3946: we can close the socket, so we may end the closing or
      draining state early. -/
  mayEndEarly : Bool := false
  /-- §5.2.2 / §6.1: the versions we accept and the list we advertise. -/
  supported : List Nat := [versionV1]
  advertised : List Nat := [versionV1]
  /-- §5.2.1: the version a client selected. -/
  chosen : Nat := versionV1
  /-- The length of the connection IDs we issue, so that a short header can be
      parsed (RFC 8999). -/
  shortDcidLen : Nat
  /-- AEAD tag length; 16 for every AEAD of RFC 9001 and for `Protection.stub`. -/
  tagLen : Nat := 16
  /-- RFC 9287: the peer sent `grease_quic_bit`, so a clear fixed bit is legal. -/
  greaseQuicBit : Bool := false
  /-- §14.2: the endpoint's maximum datagram size at the start. -/
  maxDatagramSize : Nat := DatagramSize.smallestMaxDatagramSize
  /-- RFC 9002's probe timeout, in µs.  Out of scope, so it is carried. -/
  pto : Nat
  /-- §8.2: the path the handshake runs on. -/
  localAddr : Migration.LocalAddr
  peerAddr : Addr
  /-- §7.5: how much out-of-order CRYPTO data we buffer (at least 4096). -/
  bufLimit : Nat := 4096
  /-- Packet protection.  Abstract in general; `Protection.stub tagLen` is what
      the differential harness uses. -/
  prot : Protection

/-! ## 1b. The composed state -/

/-- One endpoint's whole connection state: the product of the merged
    components', plus what belongs to no component. -/
structure State where
  /-- §5.2: which end of the connection this is.  Every component carries its
      own copy; `Inv` says they agree. -/
  role : Role
  /-- RFC 8999: the length of the Destination Connection ID of a short-header
      packet addressed to us — i.e. the length of the connection IDs we issue. -/
  shortDcidLen : Nat
  tagLen : Nat
  greaseQuicBit : Bool
  /-- RFC 9002's probe timeout.  Supplied, never computed (out of scope). -/
  pto : Nat
  /-- WP11 §7, §17.2.2–§17.2.4, §19.6, §19.20. -/
  hs : Handshake.State
  /-- WP9 §2.1, §4.1, §4.5, §4.6 (and WP2 inside it). -/
  st : StreamTable.State
  /-- WP3a §12.4, §12.5. -/
  fr : FrameRules.State
  /-- WP3b §12.3, §13.1, §13.2 — one instance per packet number space. -/
  ackInitial : Ack.State
  ackHandshake : Ack.State
  ackAppData : Ack.State
  /-- WP4 §5.1.1 (the connection IDs we issued). -/
  cidLocal : ConnIds.Local.State
  /-- WP4 §5.1.2 (the connection IDs the peer issued to us). -/
  cidRemote : ConnIds.Remote.State
  /-- WP5a §8, §8.1. -/
  av : AddressValidation.State
  /-- WP5b §8.2. -/
  pv : PathValidation.State
  /-- WP10 §9. -/
  mig : Migration.State
  /-- WP6 §10, §11. -/
  term : Termination.State
  /-- WP7b §5.2.2, §6.1. -/
  vnServer : VersionNeg.Server.State
  /-- WP7b §5.2.1, §6.2. -/
  vnClient : VersionNeg.Client.State
  /-- WP7a §14. -/
  dsz : DatagramSize.State
  /-- WP14a §13.3 — one instance per connection. -/
  rtx : Retransmission.State
  /-- WP14b §13.4 — one instance per packet number space (`Ecn` NOTES 1). -/
  ecnInitial : Ecn.State
  ecnHandshake : Ecn.State
  ecnAppData : Ecn.State
  /-- The bijection `Migration.Path ↔ PathValidation.Path` that `Migration`
      NOTES 1 leaves to WP12: a path gets a fresh handle the first time it is
      seen, so distinct paths never share one. -/
  pathIds : Map Migration.Path Nat
  nextPathId : Nat
  deriving DecidableEq

namespace State

/-- The `Ack` instance of a packet number space (§12.3, line 4662). -/
def ack (s : State) : PnSpace → Ack.State
  | .initial => s.ackInitial
  | .handshake => s.ackHandshake
  | .appData => s.ackAppData

def setAck (s : State) : PnSpace → Ack.State → State
  | .initial, a => { s with ackInitial := a }
  | .handshake, a => { s with ackHandshake := a }
  | .appData, a => { s with ackAppData := a }

@[simp] theorem ack_setAck_self (s : State) (sp : PnSpace) (a : Ack.State) :
    (s.setAck sp a).ack sp = a := by cases sp <;> rfl

/-- The `Ecn` instance of a packet number space (§13.4.1, line 5514). -/
def ecn (s : State) : PnSpace → Ecn.State
  | .initial => s.ecnInitial
  | .handshake => s.ecnHandshake
  | .appData => s.ecnAppData

def setEcn (s : State) : PnSpace → Ecn.State → State
  | .initial, a => { s with ecnInitial := a }
  | .handshake, a => { s with ecnHandshake := a }
  | .appData, a => { s with ecnAppData := a }

@[simp] theorem ecn_setEcn_self (s : State) (sp : PnSpace) (a : Ecn.State) :
    (s.setEcn sp a).ecn sp = a := by cases sp <;> rfl

/-- The `PathValidation` handle of a `Migration` path, if it has one. -/
def pathId? (s : State) (p : Migration.Path) : Option Nat := s.pathIds.get? p

/-- The handle a path has, or the one it is about to be given. -/
def pathOf (s : State) (p : Migration.Path) : PathValidation.Path :=
  ⟨(s.pathIds.get? p).getD s.nextPathId⟩

/-- The reverse lookup: which `Migration.Path` a handle belongs to. -/
def pathOfId (s : State) (i : Nat) : Option Migration.Path :=
  (s.pathIds.find? (fun e => decide (e.2 = i))).map (·.1)

/-- Give `p` a handle if it does not have one.  Fresh handles come from a
    counter, so two paths never share one. -/
def register (s : State) (p : Migration.Path) : State :=
  match s.pathIds.get? p with
  | some _ => s
  | none => { s with pathIds := s.pathIds.set p s.nextPathId, nextPathId := s.nextPathId + 1 }

end State

/-! ## 1c. Initial state -/

/-- §7.2: a client's own first Destination Connection ID, or a server's view of
    the client's, as a `Handshake.State`. -/
def initHandshake (cfg : Config) : Handshake.State :=
  match cfg.role with
  | .client =>
    { Handshake.initClient cfg.localCid cfg.peerCid cfg.bufLimit with
      originalDcid := some cfg.origDcid }
  | .server =>
    { Handshake.initServer cfg.localCid cfg.bufLimit with
      dcidSent := some cfg.peerCid, peerScid := some cfg.peerCid,
      originalDcid := some cfg.origDcid, sawPeerInitial := true, dcidChanges := 1 }

/-- One `Ack` instance, in the space it tracks. -/
def initAck (cfg : Config) (sp : PnSpace) : Ack.State :=
  { space := sp, received := [], minPn := 0, largest := none, largestTime := 0,
    largestAckEliciting := none, outstanding := [], ackImmediately := false,
    largestSent := none, maxAckDelay := cfg.maxAckDelay }

/-- One `Ecn` instance, in the space it counts for. -/
def initEcn (sp : PnSpace) : Ecn.State := { space := sp }

def initPath (cfg : Config) : Migration.Path := ⟨cfg.localAddr, cfg.peerAddr⟩

/-- The connection as it stands once the handshake has produced the parameters
    in `cfg`.  §5.1.1: sequence number 0 is the connection ID each side sent in
    the Source Connection ID field of its first packets. -/
def init (cfg : Config) : State where
  role := cfg.role
  shortDcidLen := cfg.shortDcidLen
  tagLen := cfg.tagLen
  greaseQuicBit := cfg.greaseQuicBit
  pto := cfg.pto
  hs := initHandshake cfg
  st := StreamTable.init cfg.role cfg.ours cfg.theirs
  fr := { role := cfg.role }
  ackInitial := initAck cfg .initial
  ackHandshake := initAck cfg .handshake
  ackAppData := initAck cfg .appData
  cidLocal :=
    { nextSeq := 1, issued := [⟨0, cfg.localCid, cfg.localToken⟩], retired := [],
      peerLimit := cfg.peerCidLimit, zeroLen := cfg.localCid.isEmpty,
      sentRetirePriorTo := 0 }
  cidRemote :=
    { entries := [⟨0, cfg.peerCid, cfg.peerToken⟩], retired := [], retirePriorTo := 0,
      limit := cfg.localCidLimit, peerZeroLen := cfg.peerCid.isEmpty }
  av := AddressValidation.init cfg.role (bytes cfg.peerCid)
  pv := PathValidation.init
  mig := Migration.init cfg.role (initPath cfg) 0
  term := Termination.init cfg.localMaxIdle cfg.peerMaxIdle cfg.mayEndEarly
  vnServer :=
    { supported := cfg.supported, advertised := cfg.advertised,
      shortDcidLen := cfg.shortDcidLen }
  vnClient :=
    { dcid := bytes cfg.peerCid, scid := bytes cfg.localCid, chosen := cfg.chosen,
      processedAny := false, abandoned := false }
  dsz :=
    { role := cfg.role, peerMaxUdpPayload := none, maxDatagramSize := cfg.maxDatagramSize,
      pathUsable := true, runsPmtuDiscovery := false }
  rtx := {}
  ecnInitial := initEcn .initial
  ecnHandshake := initEcn .handshake
  ecnAppData := initEcn .appData
  pathIds := [(initPath cfg, 0)]
  nextPathId := 1

/-! ## 1d. Events -/

/-- What the application asks the connection to do.  Every constructor is one
    of the merged components' own application events (WP2 `Stream`, WP9
    `StreamTable`, WP6 `Termination`); nothing new is invented here. -/
inductive AppAction where
  /-- §2.1: open a new locally-initiated stream of this type. -/
  | openStream (dir : StreamDir)
  /-- §2.4, line 801: write `len` further bytes on a stream. -/
  | write (id : StreamId) (len : Nat)
  /-- §2.4, line 805: end the stream cleanly. -/
  | fin (id : StreamId)
  /-- §2.4, line 808: reset the stream. -/
  | reset (id : StreamId) (code : Nat)
  /-- §2.4, line 816: abort reading, which asks for a STOP_SENDING frame. -/
  | stopSending (id : StreamId) (code : Nat)
  /-- §2.4, line 814: the application consumed `len` bytes. -/
  | read (id : StreamId) (len : Nat)
  /-- §4.1: raise the stream-level limit and send MAX_STREAM_DATA. -/
  | extendMaxStreamData (id : StreamId) (v : Nat)
  /-- §4.1: raise the connection-level limit and send MAX_DATA. -/
  | extendMaxData (v : Nat)
  /-- §4.6: raise the stream limit and send MAX_STREAMS. -/
  | extendMaxStreams (dir : StreamDir) (v : Nat)
  /-- §10.2, line 3932: the application closes the connection. -/
  | close (code : Nat)
  deriving DecidableEq

/-- The decisions an endpoint takes by itself: everything that is neither a
    datagram, nor the application, nor TLS, nor the clock. -/
inductive LocalAction where
  /-- §5.1.1, line 1702: issue a new connection ID. -/
  | issueCid (cid : ConnIds.Cid) (token : ConnIds.ResetToken) (rpt : Nat)
  /-- §5.1.2, line 1779: stop using one of the peer's connection IDs. -/
  | retireCid (seq : Nat)
  /-- §5.1.2, line 1823: this many RETIRE_CONNECTION_ID frames are unacked. -/
  | retirementBacklog (pending : Nat)
  /-- §8.2.1, line 3131: start validating a path. -/
  | startPathValidation (p : Migration.Path) (data : ByteArray) (deadline : Time)
  /-- §8.2.4, line 3234: the abandon timer for a path fired. -/
  | pathTimeout (p : Migration.Path)
  /-- §9.2, line 3345: migrate to a path. -/
  | migrate (p : Migration.Path)
  /-- §9.1, line 3331: probe a path without migrating. -/
  | probe (p : Migration.Path)
  /-- §9.5, line 3600: start transmitting on `p` with this connection ID. -/
  | beginSendOn (p : Migration.Path) (dcidSeq : Nat)
  /-- §9.6.1, line 3686: the peer's `preferred_address`. -/
  | learnPreferredAddress (a : Addr)
  /-- §13.1: we sent a packet of this type with this number. -/
  | sentPacket (ptype : PacketType) (pn : Nat) (ackEliciting : Bool)
  /-- §19.3: we sent an ACK frame for this space. -/
  | sentAck (sp : PnSpace) (largest first : Nat) (ranges : List AckRange)
  /-- A frame we put on the wire, in a packet of type `ptype` on path `p`; the
      bookkeeping the components need (`Stream.Send.sentStream`,
      `PathValidation.responseSent`, `Ack.sentAck`, `Handshake.sentCrypto`).
      The packet type is carried because the level a CRYPTO frame belongs to and
      the space an ACK frame acknowledges are properties of the packet, not of
      the frame (`Ack` NOTES 15, `FrameRules` NOTES 8). -/
  | sentFrameIn (ptype : PacketType) (p : Migration.Path) (f : Frame)
  /-- §8.1, line 2776: a datagram of `n` payload bytes left for `a`. -/
  | sentDatagram (a : Addr) (n : Nat)
  /-- §10.3.1, line 4323: the trailing 16 bytes matched a stateless reset token. -/
  | statelessReset
  /-- §12.3, line 4693: a packet number space is spent. -/
  | pnExhausted
  /-- §11.1: a component outside this model detected a connection error. -/
  | localError (err : TransportError) (frameType : Nat)
  /-- §14.2.1: a validated ICMP Packet Too Big. -/
  | icmpPtb (pmtu : Nat)
  /-- §14.2, line 5758: the path cannot carry 1200 bytes. -/
  | pathBelowMinimum (alternativeExists : Bool)
  /-- §13.3, line 5332: a packet of `sp` numbered `pn` carried `fs`, so the
      information in it is now in flight.  Fired alongside `sentPacket`; kept
      separate because `Retransmission` needs the frame list and `Ack` does
      not. -/
  | sentPacketFrames (sp : PnSpace) (pn : Nat) (fs : List Frame)
  /-- §13.3, line 5333: anything else RFC 9002 reports — an acknowledgment, a
      loss, a stream phase change, a blocked-limit change, history discard. -/
  | rtxEvent (e : Retransmission.Event)
  /-- §13.4: anything the IP layer reports.  The ECN codepoint of a received
      packet is a field of the IP header, not of the QUIC datagram, so it cannot
      be carried on `Event.datagram`; the harness supplies it here, one event per
      QUIC packet (§13.4.1, line 5515). -/
  | ecnEvent (sp : PnSpace) (e : Ecn.Event)
  deriving DecidableEq

/-- TLS as an event source, exactly as WP11 defines it. -/
abbrev TlsEvent := Handshake.Event

inductive Event where
  /-- A UDP datagram arrived from `src` at our local address `dest`. -/
  | datagram (src dest : Addr) (bytes : ByteArray) (now : Time)
  /-- The application asked for something. -/
  | app (a : AppAction) (now : Time)
  /-- TLS said something (§7; RFC 9001). -/
  | tls (e : TlsEvent)
  /-- Time passed: the only event that can fire a timeout. -/
  | timer (now : Time)
  /-- The endpoint decided something by itself. -/
  | local (a : LocalAction) (now : Time)
  deriving DecidableEq

/-! ## 1e. Effects

The union of the components' effects, tagged by component, plus `sendPending`:
the marker a component's rule leaves when it asks for a frame to be *queued*
rather than for something to happen now. -/

inductive Effect where
  | hs (e : Handshake.Effect)
  | st (e : StreamTable.Effect)
  | fr (e : FrameRules.Effect)
  | ack (sp : PnSpace) (e : Ack.Effect)
  | cidLocal (e : ConnIds.Local.Effect)
  | cidRemote (e : ConnIds.Remote.Effect)
  | av (e : AddressValidation.Effect)
  | pv (e : PathValidation.Effect)
  | mig (e : Migration.Effect)
  | term (e : Termination.Effect)
  | vnServer (e : VersionNeg.Server.Effect)
  | vnClient (e : VersionNeg.Client.Effect)
  | dsz (e : DatagramSize.Effect)
  | rtx (e : Retransmission.Effect)
  | ecn (sp : PnSpace) (e : Ecn.Effect)
  /-- A frame the endpoint now owes its peer.  It is *not* a packet going out:
      §13.2 and §13.3 decide when it actually travels, which is out of scope. -/
  | sendPending (f : Frame)
  /-- A packet of the received datagram was skipped: §12.2, line 4622, "if the
      packet cannot be processed, an endpoint MUST discard the remainder of the
      datagram". -/
  | skippedRest
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ## 1f. The invariant -/

/-- Handshake confirmation is mirrored in three places — WP11 holds it, WP6
    needs it for §10.2.3 line 4056, WP10 for §9 line 3280 — so the composition
    keeps the three copies equal.  `Endpoint.syncConfirmed` is what maintains
    it; `Endpoint.Lemmas.handshake_confirmed_mono` is why re-imposing WP11's bit
    on the other two is a faithful reading of `Termination.Step.handshakeConfirmed`
    and `Migration.Step.confirmed`, which only ever set it. -/
def InvConfirmed (s : State) : Prop :=
  s.term.handshakeConfirmed = s.hs.confirmed ∧ s.mig.handshakeConfirmed = s.hs.confirmed

/-- Every component agrees about which end of the connection this is. -/
def InvRole (s : State) : Prop :=
  s.hs.role = s.role ∧ s.st.role = s.role ∧ s.fr.role = s.role ∧
  s.av.role = s.role ∧ s.mig.role = s.role ∧ s.dsz.role = s.role

/-- §12.3, line 4662 and §13.4.1, line 5514: each per-space instance tracks the
    space it was built for. -/
def InvSpaces (s : State) : Prop :=
  s.ackInitial.space = .initial ∧ s.ackHandshake.space = .handshake ∧
  s.ackAppData.space = .appData ∧
  s.ecnInitial.space = .initial ∧ s.ecnHandshake.space = .handshake ∧
  s.ecnAppData.space = .appData

/-- The path registry is an injection: fresh handles come from a counter that
    only goes up, so no two paths share one. -/
def InvPaths (s : State) : Prop :=
  (∀ p i, s.pathIds.get? p = some i → i < s.nextPathId) ∧
  (∀ p q i, s.pathIds.get? p = some i → s.pathIds.get? q = some i → p = q)

/-- The conjunction of every component's invariant with the four
    cross-component ones.  A structure rather than nested `∧` so that the
    setter lemmas of `Endpoint/Merge.lean` can name their fields. -/
structure Inv (s : State) : Prop where
  hs : Handshake.Inv s.hs
  st : StreamTable.Inv s.st
  fr : FrameRules.Inv s.fr
  ackI : Ack.Inv s.ackInitial
  ackH : Ack.Inv s.ackHandshake
  ackA : Ack.Inv s.ackAppData
  cidL : ConnIds.Local.Inv s.cidLocal
  cidR : ConnIds.Remote.Inv s.cidRemote
  av : AddressValidation.Inv s.av
  pv : PathValidation.Inv s.pv
  mig : Migration.Inv s.mig
  term : Termination.Inv s.term
  vnS : VersionNeg.Server.Inv s.vnServer
  vnC : VersionNeg.Client.Inv s.vnClient
  dsz : DatagramSize.Inv s.dsz
  rtx : Retransmission.Inv s.rtx
  ecnI : Ecn.Inv s.ecnInitial
  ecnH : Ecn.Inv s.ecnHandshake
  ecnA : Ecn.Inv s.ecnAppData
  confirmed : InvConfirmed s
  role : InvRole s
  spaces : InvSpaces s
  paths : InvPaths s

/-- The `Ack` invariant of any of the three instances. -/
theorem Inv.ackOf {s : State} (hi : Inv s) : ∀ sp, Ack.Inv (s.ack sp)
  | .initial => hi.ackI
  | .handshake => hi.ackH
  | .appData => hi.ackA

theorem Inv.spaceOf {s : State} (hi : Inv s) : ∀ sp, (s.ack sp).space = sp
  | .initial => hi.spaces.1
  | .handshake => hi.spaces.2.1
  | .appData => hi.spaces.2.2.1

theorem Inv.ecnOf {s : State} (hi : Inv s) : ∀ sp, Ecn.Inv (s.ecn sp)
  | .initial => hi.ecnI
  | .handshake => hi.ecnH
  | .appData => hi.ecnA

theorem Inv.ecnSpaceOf {s : State} (hi : Inv s) : ∀ sp, (s.ecn sp).space = sp
  | .initial => hi.spaces.2.2.2.1
  | .handshake => hi.spaces.2.2.2.2.1
  | .appData => hi.spaces.2.2.2.2.2

/-- `Migration` NOTES 1's second obligation: the path status `Migration` mirrors
    agrees with `PathValidation`'s, for every path the registry knows.

    It is *not* part of `Inv`, and deliberately: `Migration.Step.succGone` and
    `failGone` drop a validation result once `Migration.State.discarded` is set,
    so the two components part company exactly there — which is harmless (a
    discarded connection sends nothing) but false as an unconditional
    invariant.  `Endpoint.pathMirror_preserved` proves it for the dispatcher
    that keeps the two in step. -/
def PathMirror (s : State) : Prop :=
  s.mig.discarded = false →
    ∀ p i, s.pathIds.get? p = some i → s.mig.statusOf p = s.pv.statusOf ⟨i⟩

end Quic.Spec.Endpoint
