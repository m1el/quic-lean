import QuicModel.Spec.Migration.Inv

/-!
  WP10 "Migration", parts 6–7: the send side and the `Component` value.
-/
namespace Quic.Spec.Migration

/-! ## 6. Send side

§9 places no condition on an individual *frame*: every one of its send-side
rules is about the path a packet leaves on and the connection ID it carries, so
they live in `MaySendPacket` (over `State.tx`) and not in `MaySend`. -/

/-- No frame is governed by this component on its own. -/
def MaySend (_ : State) : Frame → Prop := fun _ => True

def maySend (_ : State) : Frame → Bool := fun _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend]

/-- Everything §9 forbids an endpoint to put on the wire, as a condition on the
    packet and on the path and Destination Connection ID it goes out with
    (`s.tx`).

    The six clauses, in order:

    1. §9.3.2, line 3461: "MUST close the connection silently by discarding all
       connection state" — a discarded connection sends nothing.
    2. §9, line 3280: "An endpoint MUST NOT initiate connection migration before
       the handshake is confirmed", read with §9.2, line 3345: "An endpoint can
       migrate a connection to a new local address by sending packets containing
       non-probing frames from that address."  So before confirmation a
       non-probing packet must leave from the handshake's local address.
    3. §9, line 3284: "If the peer sent the disable_active_migration transport
       parameter, an endpoint also MUST NOT send packets (including probing
       packets; see Section 9.1) from a different local address to the address
       the peer used during the handshake, unless the endpoint has acted on a
       preferred_address transport parameter from the peer."  Note that this one
       is *not* limited to non-probing packets.
    4. §9, line 3323: "Servers do not send non-probing packets (see Section 9.1)
       toward a client address until they see a non-probing packet from that
       address", together with §9.6.2, line 3721: "The server MUST send
       non-probing packets from its original address until it receives a
       non-probing packet from the client at its preferred address and until the
       server has validated the new path."
    5. §9.6.1, line 3710: "If path validation fails, the client MUST continue
       sending all future packets to the server's original IP address."
    6. §9.5, line 3603: "An endpoint MUST NOT reuse a connection ID when sending
       from more than one local address"; line 3608: "Similarly, an endpoint
       MUST NOT reuse a connection ID when sending to more than one destination
       address"; line 3611: "… in which case it MAY continue to use the current
       connection ID with the new remote address while still sending from the
       same local address."  With zero-length connection IDs there is no
       sequence number and the two MUST NOTs have no content — §9.5, line 3630
       answers that case with a SHOULD NOT, which is `RecommendedMigration`. -/
def MaySendPacket (s : State) (pkt : OutPacket) : Prop :=
  s.discarded = false ∧
  (s.handshakeConfirmed = true ∨ FrameRules.packetProbing pkt.frames = true ∨
    s.tx.path.loc = s.handshakePath.loc) ∧
  s.sendBanned s.tx.path = false ∧
  (s.role = .client ∨ FrameRules.packetProbing pkt.frames = true ∨
    (s.sawNonProbingFrom s.tx.path.peer = true ∧
      (s.isPreferredPath s.tx.path = false ∨
        ((s.infoOf s.tx.path).sawNonProbing = true ∧ s.isValidated s.tx.path = true)))) ∧
  (s.role = .server ∨ s.isPreferredPath s.tx.path = false ∨
    s.statusOf s.tx.path ≠ .failed) ∧
  (s.peerZeroLen = true ∨
    (s.reusedAcrossLocal s.tx.path s.tx.dcidSeq = false ∧
      (s.reusedAcrossPeer s.tx.path s.tx.dcidSeq = false ∨
        s.rebindKeepsCid s.tx.path s.tx.dcidSeq = true)))

instance instDecMaySendPacket (s : State) (pkt : OutPacket) : Decidable (MaySendPacket s pkt) :=
  inferInstanceAs (Decidable (_ ∧ _))

def maySendPacket (s : State) (pkt : OutPacket) : Bool := decide (MaySendPacket s pkt)

theorem maySendPacket_iff (s : State) (pkt : OutPacket) :
    maySendPacket s pkt = true ↔ MaySendPacket s pkt := by simp [maySendPacket]

/-- A datagram leaves on one path with one Destination Connection ID, so every
    packet coalesced in it is bound by the same rules (§12.2: "a sender can
    coalesce multiple QUIC packets … into one UDP datagram").  The
    anti-amplification limit that §9.3, line 3392 and §9.3.1, line 3431 refer to
    is WP5's and is added by `MaySendDatagramOn`. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  ∀ pkt ∈ d.packets, MaySendPacket s pkt

instance instDecMaySendDatagram (s : State) (d : OutDatagram) : Decidable (MaySendDatagram s d) :=
  inferInstanceAs (Decidable (∀ pkt ∈ d.packets, MaySendPacket s pkt))

def maySendDatagram (s : State) (d : OutDatagram) : Bool := decide (MaySendDatagram s d)

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by simp [maySendDatagram]

/-- §9.3, line 3392: "An endpoint MAY send data to an unvalidated peer address,
    but it MUST protect against potential attacks as described in Section 9.3.1
    and Section 9.3.2"; §9.3.1, line 3431: "Until a peer's address is deemed
    valid, an endpoint limits the amount of data it sends to that address; see
    Section 8."  The limit itself is `AddressValidation.MaySendTo` (the
    per-address form behind WP5's `MaySendDatagram` field), not duplicated here:
    `av` is WP5's state and `s.tx.path.peer` the address of the path the
    datagram leaves on.  §9.3.1, line 3436 ("If an endpoint skips validation of
    a peer address as described above, it does not need to limit its sending
    rate") is already in WP5's predicate, which is satisfied outright once the
    address is marked validated. -/
def MaySendDatagramOn (av : AddressValidation.State) (s : State) (d : OutDatagram) : Prop :=
  MaySendDatagram s d ∧ AddressValidation.MaySendTo av s.tx.path.peer d.size

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
