import QuicModel.Spec.Endpoint.Events

/-!
  WP12 "Endpoint", part 6: **the send side**.

  Three predicates, each the conjunction of the merged components' own:

  * `MaySend s f` — the frame-level rules (`Component.MaySend`);
  * `MaySendPacket s p` — every component's `MaySendPacket`, plus `FrameRules`'
    packet-type table, plus `MaySend` applied to every frame in the packet;
  * `MaySendDatagram s d` — every component's `MaySendDatagram`, plus
    `MaySendPacket` for every packet coalesced in it, plus the three rules the
    packages could not state from one state alone and left here:
    `PathValidation.maySendDatagramOn av` (§8.2.1 line 3154, §8.2.2 lines 3197
    and 3200), `Migration.MaySendDatagramOn av` (§9.3.1, line 3431) and
    §8.2.2 line 3183's "a PATH_RESPONSE frame MUST be sent on the network path
    where the PATH_CHALLENGE was received", which needs `OutDatagram.src` as
    well as `dest` (`PathValidation` NOTES 11).

  Three more rules are about things that are not datagrams of QUIC packets at
  all, so they stay free functions with their own arguments, exactly as WP5,
  WP6 and WP7 exported them: the Retry header (`maySendRetryHeader`), the
  Version Negotiation packet (`maySendVn`), and the Stateless Reset
  (`maySendStatelessReset`).
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## 6.1 Frame level -/

/-- Six of the thirteen components govern a frame on its own; the other seven
    have `MaySend = True` by design, and their rules are packet- or
    datagram-level (`FrameRules` NOTES 8, `Ack` NOTES 15, `Migration` part 6). -/
def MaySend (s : State) (f : Frame) : Prop :=
  Handshake.MaySend s.hs f ∧ StreamTable.MaySend s.st f ∧
  ConnIds.Local.MaySend s.cidLocal f ∧ ConnIds.Remote.MaySend s.cidRemote f ∧
  PathValidation.MaySend s.pv f ∧ Termination.MaySend s.term f

def maySend (s : State) (f : Frame) : Bool :=
  Handshake.maySend s.hs f && StreamTable.maySend s.st f &&
  ConnIds.Local.maySend s.cidLocal f && ConnIds.Remote.maySend s.cidRemote f &&
  PathValidation.maySend s.pv f && Termination.maySend s.term f

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp only [maySend, MaySend, Bool.and_eq_true, Handshake.maySend_iff, StreamTable.maySend_iff,
    ConnIds.Local.maySend_iff, ConnIds.Remote.maySend_iff, PathValidation.maySend_iff,
    Termination.maySend_iff, and_assoc]

instance instDecidableMaySend (s : State) (f : Frame) : Decidable (MaySend s f) :=
  decidable_of_iff _ (maySend_iff s f)

/-! ## 6.2 Packet level -/

/-- `Ack` has one instance per packet number space, and each instance's rule is
    conditioned on the packet belonging to *its* space, so all three apply. -/
def AckPacketOk (s : State) (p : OutPacket) : Prop :=
  Ack.MaySendPacket s.ackInitial p ∧ Ack.MaySendPacket s.ackHandshake p ∧
  Ack.MaySendPacket s.ackAppData p

def ackPacketOk (s : State) (p : OutPacket) : Bool :=
  Ack.maySendPacket s.ackInitial p && Ack.maySendPacket s.ackHandshake p &&
  Ack.maySendPacket s.ackAppData p

theorem ackPacketOk_iff (s : State) (p : OutPacket) :
    ackPacketOk s p = true ↔ AckPacketOk s p := by
  simp only [ackPacketOk, AckPacketOk, Bool.and_eq_true, Ack.maySendPacket_iff, and_assoc]

def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  FrameRules.MaySendPacket s.fr p ∧ Handshake.MaySendPacket s.hs p ∧
  Termination.MaySendPacket s.term p ∧ Migration.MaySendPacket s.mig p ∧
  AckPacketOk s p ∧ ∀ f ∈ p.frames, MaySend s f

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  FrameRules.maySendPacket s.fr p && Handshake.maySendPacket s.hs p &&
  Termination.maySendPacket s.term p && Migration.maySendPacket s.mig p &&
  ackPacketOk s p && p.frames.all (maySend s)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  simp only [maySendPacket, MaySendPacket, Bool.and_eq_true, FrameRules.maySendPacket_iff,
    Handshake.maySendPacket_iff, Termination.maySendPacket_iff, Migration.maySendPacket_iff,
    ackPacketOk_iff, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun f hf => (maySend_iff s f).mp (h6 f hf)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun f hf => (maySend_iff s f).mpr (h6 f hf)⟩

instance instDecidableMaySendPacket (s : State) (p : OutPacket) : Decidable (MaySendPacket s p) :=
  decidable_of_iff _ (maySendPacket_iff s p)

/-! ## 6.3 Datagram level -/

/-- The path a datagram leaves on: §8.2, line 3075's two-tuple, built from
    `OutDatagram.src` and `OutDatagram.dest`. -/
def datagramPath (d : OutDatagram) : Migration.Path := ⟨⟨d.src.id⟩, d.dest⟩

/-- §8.2.2, line 3183: "A PATH_RESPONSE frame MUST be sent on the network path
    where the PATH_CHALLENGE was received."  `PathValidation.MaySendResponseOn`
    is the rule; this is it applied to one frame of a datagram
    (`PathValidation` NOTES 11). -/
def frameResponseOk (s : State) (pa : PathValidation.Path) : Frame → Prop
  | .pathResponse bs => PathValidation.MaySendResponseOn s.pv bs pa
  | _ => True

def frameResponseOkB (s : State) (pa : PathValidation.Path) : Frame → Bool
  | .pathResponse bs => PathValidation.maySendResponseOn s.pv bs pa
  | _ => true

theorem frameResponseOk_iff (s : State) (pa : PathValidation.Path) (f : Frame) :
    frameResponseOkB s pa f = true ↔ frameResponseOk s pa f := by
  cases f <;>
    simp [frameResponseOkB, frameResponseOk, PathValidation.maySendResponseOn_iff]

def PathResponsesOnPath (s : State) (d : OutDatagram) : Prop :=
  ∀ p ∈ d.packets, ∀ f ∈ p.frames, frameResponseOk s (s.pathOf (datagramPath d)) f

def pathResponsesOnPath (s : State) (d : OutDatagram) : Bool :=
  d.packets.all (fun p => p.frames.all (frameResponseOkB s (s.pathOf (datagramPath d))))

theorem pathResponsesOnPath_iff (s : State) (d : OutDatagram) :
    pathResponsesOnPath s d = true ↔ PathResponsesOnPath s d := by
  simp only [pathResponsesOnPath, PathResponsesOnPath, List.all_eq_true]
  constructor
  · intro h p hp f hf
    exact (frameResponseOk_iff _ _ f).mp (h p hp f hf)
  · intro h p hp f hf
    exact (frameResponseOk_iff _ _ f).mpr (h p hp f hf)

/-- Everything the model knows about a datagram this endpoint may send. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §8, line 2735 / §8.1, line 2773: the anti-amplification budget
  AddressValidation.MaySendTo s.av d.dest d.size ∧
  -- §14.1, §14.2, §14.4
  DatagramSize.MaySendDatagram s.dsz d ∧
  -- §9: the path and connection-ID rules, for every packet in it
  Migration.MaySendDatagram s.mig d ∧
  -- §8.2.1 line 3154 and §8.2.2 lines 3197/3200: expansion to 1200 bytes,
  -- unless the anti-amplification limit forbids it
  PathValidation.MaySendDatagramOn s.av d ∧
  -- §9.3.1, line 3431: the limit on the path the datagram leaves on
  Migration.MaySendDatagramOn s.av s.mig d ∧
  -- §8.2.2, line 3183
  PathResponsesOnPath s d ∧
  -- every packet coalesced in it
  ∀ p ∈ d.packets, MaySendPacket s p

def maySendDatagram (s : State) (d : OutDatagram) : Bool :=
  AddressValidation.maySendTo s.av d.dest d.size &&
  DatagramSize.maySendDatagram s.dsz d &&
  Migration.maySendDatagram s.mig d &&
  PathValidation.maySendDatagramOn s.av d &&
  decide (Migration.MaySendDatagramOn s.av s.mig d) &&
  pathResponsesOnPath s d &&
  d.packets.all (maySendPacket s)

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by
  simp only [maySendDatagram, MaySendDatagram, Bool.and_eq_true, AddressValidation.maySendTo_iff,
    DatagramSize.maySendDatagram_iff, Migration.maySendDatagram_iff,
    PathValidation.maySendDatagramOn_iff, pathResponsesOnPath_iff, decide_eq_true_eq,
    List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, fun p hp => (maySendPacket_iff s p).mp (h7 p hp)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6, fun p hp => (maySendPacket_iff s p).mpr (h7 p hp)⟩

instance instDecidableMaySendDatagram (s : State) (d : OutDatagram) :
    Decidable (MaySendDatagram s d) := decidable_of_iff _ (maySendDatagram_iff s d)

/-! ## 6.4 The three things that are not datagrams of QUIC packets

Each is exported by its package as a free function with arguments
`Spec.OutDatagram` cannot carry; they are collected here so that WP13 has one
place to look. -/

/-- §17.2.5.1, lines 6592 and 6597: the connection IDs of a Retry packet a
    server sends in answer to a client Initial. -/
def maySendRetryHeader (h : AddressValidation.RetryHeader) : Bool :=
  AddressValidation.maySendRetry h

/-- §17.2.5.1, line 6616: "A server MUST NOT send more than one Retry packet in
    response to a single UDP datagram" — a property of the effects one received
    datagram produced, so it is checked over the whole outcome. -/
def atMostOneRetry (fx : List Effect) : Prop :=
  (fx.filter (fun e => match e with | .av (.sendRetry _) => true | _ => false)).length ≤ 1

def atMostOneRetryB (fx : List Effect) : Bool :=
  decide ((fx.filter (fun e => match e with | .av (.sendRetry _) => true | _ => false)).length ≤ 1)

theorem atMostOneRetryB_iff (fx : List Effect) : atMostOneRetryB fx = true ↔ atMostOneRetry fx := by
  simp [atMostOneRetryB, atMostOneRetry]

/-- §5.2.2, §6.1 and §17.2.1: the Version Negotiation packet a server may send
    in answer to a particular datagram.  `VersionNeg` NOTES: WP12 must call it
    with the triggering event, not with `maySendPacket`. -/
def maySendVn (s : State) (e : VersionNeg.Server.Event) (vn : VersionNeg.Server.Vn) : Bool :=
  VersionNeg.Server.maySendVn s.vnServer e vn

/-- §10.3, line 4215 and §10.3.3, line 4393: a Stateless Reset uses a whole UDP
    datagram and its size is bounded by the size of the datagram that triggered
    it, which `Spec.OutDatagram` does not carry (`Termination` part 6.3). -/
def maySendStatelessReset (preventsLooping : Bool) (triggerSize resetSize : Nat) : Bool :=
  Termination.maySendStatelessReset preventsLooping triggerSize resetSize

/-! ## 6.5 Named send-side facts -/

/-- §10.2.2, line 4023 and §10.2, line 3953: a draining or closed endpoint may
    send no frame at all, whatever the other components think. -/
theorem maySend_false_of_draining_or_closed {s : State} (f : Frame)
    (hp : s.term.phase = .draining ∨ s.term.phase = .closed) : ¬ MaySend s f := by
  rintro ⟨-, -, -, -, -, h⟩
  exact Termination.maySend_false_of_draining_or_closed _ f hp h

/-- §12.3, line 4693: once a packet number space is spent, no packet of that
    space may be sent.  Lifted from `Ack.not_maySendPacket_of_exhausted`. -/
theorem not_maySendPacket_of_pnExhausted {s : State} {p : OutPacket} {sp : PnSpace}
    (hsp : p.ptype.space = some sp) (hspace : (s.ack sp).space = sp)
    (hx : Ack.pnExhausted (s.ack sp) = true) : ¬ MaySendPacket s p := by
  rintro ⟨-, -, -, -, ⟨hi, hh, ha⟩, -⟩
  have : Ack.MaySendPacket (s.ack sp) p := by cases sp <;> assumption
  exact Ack.not_maySendPacket_of_exhausted hx (by rw [hsp, hspace]) this

/-- §12.4, line 4740: a packet this endpoint sends always carries a frame. -/
theorem maySendPacket_frames_ne_nil {s : State} {p : OutPacket} (h : MaySendPacket s p) :
    p.frames ≠ [] := h.1.1

end Quic.Spec.Endpoint
