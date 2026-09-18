import QuicModel.Spec.Ecn.Step

/-
  WP14 (b), parts 6-7: the send side (`MaySendPacket` for ECN counts in ACK
  frames, `MayMarkEcn`, the feedback obligation) and the `Component` value.
-/
namespace Quic.Spec.Ecn

/-! ## 6. Send side

One instance of this component exists per packet number space, so a frame-only
predicate would have to hold in all three at once and would reject every ACK
frame that reports a non-zero count.  The rule therefore lives in
`MaySendPacket`, which sees the packet's type and so its space — the same
reasoning as `Spec/Ack.lean`, NOTE 15. -/

/-- §19.3.2, line 7407: "ECT0 Count: A variable-length integer representing the
    total number of packets received with the ECT(0) codepoint in the packet
    number space of the ACK frame", and likewise for ECT(1) and CE. -/
def ackEcnOk (s : State) : Frame → Bool
  | .ack _ _ _ _ (some e) =>
    decide (e.ect0 = s.ect0) && decide (e.ect1 = s.ect1) && decide (e.ce = s.ce)
  | _ => true

/-- §13.4.1, line 5500 permits an endpoint not to report counts at all, so an
    ACK frame of type 0x02 (no counts) is always sendable; only the counts that
    *are* reported are pinned. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  p.ptype.space = some s.space → ∀ f ∈ p.frames, ackEcnOk s f = true

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  !decide (p.ptype.space = some s.space) || p.frames.all (ackEcnOk s)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  simp only [maySendPacket, MaySendPacket, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.all_eq_true]
  constructor
  · rintro (h | h) hsp
    · exact absurd hsp h
    · intro f hf; exact h f hf
  · intro h
    by_cases hsp : p.ptype.space = some s.space
    · exact Or.inr fun f hf => h hsp f hf
    · exact Or.inl hsp

/-- Nothing about an individual frame is governed here (see above). -/
def MaySend (_ : State) (_ : Frame) : Prop := True
def maySend (_ : State) (_ : Frame) : Bool := true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-- §13.4.2.2, line 5626: "If validation fails, then the endpoint MUST disable
    ECN.  It stops setting the ECT codepoint in IP packets that it sends".
    `Spec.OutDatagram` has no ECN field, so this cannot be a `MaySendDatagram`
    rule; `marked` is the flag an endpoint would set on the IP header
    (NOTE 6). -/
def MayMarkEcn (s : State) (marked : Bool) : Prop := marked = true → s.phase ≠ .failed

def mayMarkEcn (s : State) (marked : Bool) : Bool :=
  !marked || !decide (s.phase = .failed)

theorem mayMarkEcn_iff (s : State) (marked : Bool) :
    mayMarkEcn s marked = true ↔ MayMarkEcn s marked := by
  cases marked <;> simp [mayMarkEcn, MayMarkEcn]

/-- §13.4.1, line 5504: "Even if an endpoint does not set an ECT field on packets
    it sends, the endpoint MUST provide feedback about ECN markings it receives,
    if these are accessible."  Like §13.2.1's acknowledgment MUST this is an
    obligation to *send* something, so it is a property of a run, not of a step
    (NOTE 2). -/
def feedbackOwed (s : State) : Bool :=
  s.reportsEcn && decide (0 < s.ect0 + s.ect1 + s.ce)

def carriesEcnCounts : Frame → Bool
  | .ack _ _ _ _ (some _) => true
  | _ => false

/-- `run` pairs each ACK frame this space sent with the state it was sent in.
    WP12 must require this of a completed run. -/
def FeedbackObligationMet (run : List (State × Frame)) : Prop :=
  ∀ p ∈ run, feedbackOwed p.1 = true → ∃ q ∈ run, carriesEcnCounts q.2 = true

/-- The SHOULDs and recommendations of §13.4 that constrain a frame. -/
structure Recommended (s : State) (f : Frame) : Prop where
  /-- §13.4.1, line 5504, per frame: while counts are owed, an ACK frame reports
      them.  A recommendation here, because the MUST is about providing feedback
      at all, not about any single frame (NOTE 2). -/
  reportsWhenOwed : feedbackOwed s = true → ∀ l d fr rs, f ≠ .ack l d fr rs none

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

end Quic.Spec.Ecn
