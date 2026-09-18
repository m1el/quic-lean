import QuicModel.Spec.Migration.Inv

/-!
  WP10 "Migration", parts 6–7: the send side and the `Component` value.
-/
namespace Quic.Spec.Migration

/-! ## 6. Send side

§9 places no condition on an individual *frame*: every one of its send-side
rules is about the path a packet leaves on and the connection ID it carries.
`Spec.OutDatagram` carries both — `src`/`dest` are the path (§8.2, line 3074)
and `dcid` the Destination Connection ID of every packet in it (§12.2 forbids
coalescing packets with different connection IDs) — so those rules are
`MaySendDatagram` rules over the datagram's own fields, and not `MaySend` rules.
`MaySendPacket` keeps only the one prohibition that is about the connection
rather than about a path. -/

/-- No frame is governed by this component on its own. -/
def MaySend (_ : State) : Frame → Prop := fun _ => True

def maySend (_ : State) : Frame → Bool := fun _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend]

/-- The path a datagram leaves on: §8.2, line 3074, "an endpoint … an address
    is … the two-tuple of IP address and port", and §9's paths are the pair of
    a local and a peer address. -/
def pathOf (d : OutDatagram) : Path := ⟨⟨d.src.id⟩, d.dest⟩

/-- §9.3.2, line 3460: "MUST close the connection silently by discarding all
    connection state" — a discarded connection sends nothing.  This is the only
    §9 send-side rule that does not look at the path, so it is the only one
    left at packet level; the rest are in `MaySendDatagram`. -/
def MaySendPacket (s : State) (_pkt : OutPacket) : Prop :=
  s.discarded = false

instance instDecMaySendPacket (s : State) (pkt : OutPacket) : Decidable (MaySendPacket s pkt) :=
  inferInstanceAs (Decidable (_ = _))

def maySendPacket (s : State) (pkt : OutPacket) : Bool := decide (MaySendPacket s pkt)

theorem maySendPacket_iff (s : State) (pkt : OutPacket) :
    maySendPacket s pkt = true ↔ MaySendPacket s pkt := by simp [maySendPacket]

/-- What §9 forbids an endpoint to put on the wire on path `p`, packet by
    packet.  The four clauses, in order:

    1. §9, line 3280: "An endpoint MUST NOT initiate connection migration before
       the handshake is confirmed", read with §9.2, line 3345: "An endpoint can
       migrate a connection to a new local address by sending packets containing
       non-probing frames from that address."  So before confirmation a
       non-probing packet must leave from the handshake's local address.
    2. §9, line 3284: "If the peer sent the disable_active_migration transport
       parameter, an endpoint also MUST NOT send packets (including probing
       packets; see Section 9.1) from a different local address to the address
       the peer used during the handshake, unless the endpoint has acted on a
       preferred_address transport parameter from the peer."  Note that this one
       is *not* limited to non-probing packets.
    3. §9, line 3323: "Servers do not send non-probing packets (see Section 9.1)
       toward a client address until they see a non-probing packet from that
       address", together with §9.6.2, line 3721: "The server MUST send
       non-probing packets from its original address until it receives a
       non-probing packet from the client at its preferred address and until the
       server has validated the new path."
    4. §9.6.1, line 3710: "If path validation fails, the client MUST continue
       sending all future packets to the server's original IP address." -/
def MaySendOn (s : State) (p : Path) (pkt : OutPacket) : Prop :=
  (s.handshakeConfirmed = true ∨ FrameRules.packetProbing pkt.frames = true ∨
    p.loc = s.handshakePath.loc) ∧
  s.sendBanned p = false ∧
  (s.role = .client ∨ FrameRules.packetProbing pkt.frames = true ∨
    (s.sawNonProbingFrom p.peer = true ∧
      (s.isPreferredPath p = false ∨
        ((s.infoOf p).sawNonProbing = true ∧ s.isValidated p = true)))) ∧
  (s.role = .server ∨ s.isPreferredPath p = false ∨ s.statusOf p ≠ .failed)

instance instDecMaySendOn (s : State) (p : Path) (pkt : OutPacket) :
    Decidable (MaySendOn s p pkt) := inferInstanceAs (Decidable (_ ∧ _))

/-- §9.5, line 3603: "An endpoint MUST NOT reuse a connection ID when sending
    from more than one local address"; line 3608: "Similarly, an endpoint MUST
    NOT reuse a connection ID when sending to more than one destination
    address"; line 3611: "… in which case it MAY continue to use the current
    connection ID with the new remote address while still sending from the same
    local address."  Both prohibitions are about the grow-only history
    (`State.dcidFrom`, `State.dcidTo`), not about what is in use now. -/
def MaySendCidOn (s : State) (p : Path) (n : Nat) : Prop :=
  s.reusedAcrossLocal p n = false ∧
    (s.reusedAcrossPeer p n = false ∨ s.rebindKeepsCid p n = true)

instance instDecMaySendCidOn (s : State) (p : Path) (n : Nat) :
    Decidable (MaySendCidOn s p n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The sequence number of the connection ID a datagram carries, if this
    component has been told it (`Event.learnPeerCid`).  §9.5 is written about
    sequence numbers; `Spec.OutDatagram.dcid` carries bytes. -/
def dcidSeqOf (s : State) (d : OutDatagram) : Option Nat := d.dcid.bind s.seqOfCid

/-- §9.5 applied to the connection ID a datagram actually carries.  With
    zero-length connection IDs there is no sequence number and the two MUST NOTs
    have no content — §9.5, line 3630 answers that case with a SHOULD NOT, which
    is `RecommendedMigration`.  `none` (no `dcid` on the datagram, or bytes this
    component has not been told about) means the rule cannot be evaluated and
    therefore does not forbid the send; see NOTES 16 for what WP12 owes. -/
def MaySendCid (s : State) (p : Path) (n? : Option Nat) : Prop :=
  s.peerZeroLen = true ∨
    (match n? with
     | none => True
     | some n => MaySendCidOn s p n)

instance instDecMaySendCid (s : State) (p : Path) (n? : Option Nat) :
    Decidable (MaySendCid s p n?) := by
  unfold MaySendCid
  cases n? <;> dsimp only <;> infer_instance

/-- A datagram leaves on one path with one Destination Connection ID, so every
    packet coalesced in it is bound by the same path rules (§12.2: "a sender can
    coalesce multiple QUIC packets … into one UDP datagram"), judged on the
    datagram's own `src`, `dest` and `dcid`.  The anti-amplification limit that
    §9.3, line 3392 and §9.3.1, line 3431 refer to is WP5's and is added by
    `MaySendDatagramOn`. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  s.discarded = false ∧
  (∀ pkt ∈ d.packets, MaySendOn s (pathOf d) pkt) ∧
  MaySendCid s (pathOf d) (dcidSeqOf s d)

instance instDecMaySendDatagram (s : State) (d : OutDatagram) : Decidable (MaySendDatagram s d) :=
  inferInstanceAs (Decidable (_ ∧ _))

def maySendDatagram (s : State) (d : OutDatagram) : Bool := decide (MaySendDatagram s d)

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by simp [maySendDatagram]

/-- Every packet in a permitted datagram is a permitted packet. -/
theorem maySendPacket_of_maySendDatagram {s : State} {d : OutDatagram} {pkt : OutPacket}
    (h : MaySendDatagram s d) (_ : pkt ∈ d.packets) : MaySendPacket s pkt := h.1

/-- §9.3, line 3392: "An endpoint MAY send data to an unvalidated peer address,
    but it MUST protect against potential attacks as described in Section 9.3.1
    and Section 9.3.2"; §9.3.1, line 3431: "Until a peer's address is deemed
    valid, an endpoint limits the amount of data it sends to that address; see
    Section 8."  The limit itself is `AddressValidation.MaySendTo` (the
    per-address form behind WP5's `MaySendDatagram` field), not duplicated here:
    `av` is WP5's state and `d.dest` the address the datagram is going to.
    §9.3.1, line 3436 ("If an endpoint skips validation of
    a peer address as described above, it does not need to limit its sending
    rate") is already in WP5's predicate, which is satisfied outright once the
    address is marked validated. -/
def MaySendDatagramOn (av : AddressValidation.State) (s : State) (d : OutDatagram) : Prop :=
  MaySendDatagram s d ∧ AddressValidation.MaySendTo av d.dest d.size

instance (av : AddressValidation.State) (s : State) (d : OutDatagram) :
    Decidable (MaySendDatagramOn av s d) := inferInstanceAs (Decidable (_ ∧ _))

/-! ### Advice

SHOULDs that recommend rather than permit: a conforming implementation is never
rejected for ignoring them. -/

/-- The recommended outcome where §9 expresses a preference between permitted
    ones: §9.6, line 3680 ("the client SHOULD discard these packets") and
    §9.6.1, line 3707 / §9.6.2, line 3730 (begin sending to the preferred
    address as soon as validation succeeds).  The either/or of §9, line 3289 and
    the MAYs of §9.1 and §9.5 carry no preference and are left unconstrained. -/
def Recommended : State → Event → Out → Prop
  | s, .recvPacket p pn pr _, o => recvCase s p pn pr = .unsolicited → o = .drop
  | s, .validationSucceeded p, o =>
      succCase s p = .maySwitch → o = .ok (s.succSwitch p) (s.succSwitchFx p)
  | _, _, _ => True

/-- §9.5, line 3630: "An endpoint SHOULD NOT initiate migration with a peer that
    has requested a zero-length connection ID, because traffic over the new path
    might be trivially linkable to traffic over the old one."  This is the only
    thing the text says about migrating with zero-length connection IDs, and it
    is advice, so `Step` and `MaySendPacket` allow it. -/
def RecommendedMigration (s : State) (_p : Path) : Prop := s.peerZeroLen = false

/-- §9.3.3, line 3505: "An endpoint that receives a PATH_CHALLENGE on an active
    path SHOULD send a non-probing packet in response."  The PATH_CHALLENGE
    itself is WP5's event; what §9 recommends is the shape of the reply. -/
def RecommendedRespondToChallenge (s : State) (p : Path) (pkt : OutPacket) : Prop :=
  p = s.active → FrameRules.packetProbing pkt.frames = false

/-- §9.3, line 3407: "After verifying a new client address, the server SHOULD
    send new address validation tokens (Section 8) to the client."  The token is
    WP5's (`AddressValidation`), so this records only when the advice applies. -/
def RecommendedNewTokens (s : State) (p : Path) : Prop :=
  s.role = .server ∧ s.isValidated p = true ∧ p ≠ s.handshakePath

/-! ## 7. The component -/

@[reducible] def component : Component where
  State := State
  Event := Event
  Effect := Effect
  Step := Step
  outcomes := outcomes
  outcomes_iff := outcomes_iff
  outcomes_ne := outcomes_ne
  Inv := Inv
  step_inv := step_inv
  MaySend := MaySend
  maySend := maySend
  maySend_iff := maySend_iff
  MaySendPacket := MaySendPacket
  maySendPacket := maySendPacket
  maySendPacket_iff := maySendPacket_iff
  MaySendDatagram := MaySendDatagram
  maySendDatagram := maySendDatagram
  maySendDatagram_iff := maySendDatagram_iff

end Quic.Spec.Migration
