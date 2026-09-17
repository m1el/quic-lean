import QuicModel.Spec.Stream.Send
import QuicModel.Spec.Stream.Recv

/-
  WP2 Stream, part 3 of 3: one whole stream, as seen by one endpoint.

  §3, line 866: "Unidirectional streams use either the sending or receiving
  state machine depending on the stream type and endpoint role.  Bidirectional
  streams use both state machines at both endpoints."  So a stream is the two
  halves of `Spec/Stream/Send.lean` and `Spec/Stream/Recv.lean`, present or not
  according to `StreamId.dir`, `StreamId.initiator` and our own role.

  This file adds what only the whole stream knows: the direction, hence the
  STREAM_STATE_ERRORs of §19.4/§19.5/§19.8/§19.10/§19.13 for frames that arrive
  for a half that does not exist; §3.3's permitted frame types; and §3.4's
  composite bidirectional states.

  Creating streams, stream counts, connection-level flow control and implicit
  opening of lower-numbered streams are WP9.
-/
namespace Quic.Spec.Stream

/-! ## 1. State, events, effects -/

/-- §3, line 866 and §2.1, Table 1: the endpoint has a sending part for a
    bidirectional stream, or for a unidirectional stream it initiated itself. -/
def hasSend (id : StreamId) (role : Role) : Bool :=
  match id.dir with
  | .bidi => true
  | .uni => decide (id.initiator = role)

/-- The mirror image: a receiving part for a bidirectional stream, or for a
    unidirectional stream the peer initiated. -/
def hasRecv (id : StreamId) (role : Role) : Bool :=
  match id.dir with
  | .bidi => true
  | .uni => decide (id.initiator ≠ role)

theorem hasSend_or_hasRecv (id : StreamId) (role : Role) :
    hasSend id role = true ∨ hasRecv id role = true := by
  unfold hasSend hasRecv
  cases id.dir
  · exact Or.inl rfl
  · by_cases h : id.initiator = role
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])

structure State where
  id : StreamId
  role : Role
  /-- §3.1, present iff `hasSend id role`. -/
  send : Option Send.State
  /-- §3.2, present iff `hasRecv id role`. -/
  recv : Option Recv.State
  deriving DecidableEq, Repr

/-- `sendMax` is the peer's `initial_max_stream_data_*` for this stream (what we
    may send), `recvMax` ours (what we let the peer send). -/
def init (id : StreamId) (role : Role) (sendMax recvMax : Nat) : State :=
  { id, role,
    send := if hasSend id role then some (Send.init id role sendMax) else none,
    recv := if hasRecv id role then some (Recv.init id role recvMax) else none }

inductive Event where
  | send (e : Send.Event)
  | recv (e : Recv.Event)
  deriving DecidableEq, Repr

inductive Effect where
  | send (e : Send.Effect)
  | recv (e : Recv.Effect)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-- Which half an event belongs to is fixed by the event: MAX_STREAM_DATA and
    STOP_SENDING concern the sending part (they are frames *about* what we
    send), STREAM, RESET_STREAM and STREAM_DATA_BLOCKED the receiving part. -/
def liftSend (s : State) : Outcome Send.State Send.Effect → Out
  | .ok ss fx => .ok { s with send := some ss } (fx.map .send)
  | .error c => .error c
  | .drop => .drop

def liftRecv (s : State) : Outcome Recv.State Recv.Effect → Out
  | .ok rs fx => .ok { s with recv := some rs } (fx.map .recv)
  | .error c => .error c
  | .drop => .drop

/-! ## 2. The specification

Each constructor is split by the shape of the half's outcome, so that a
composite outcome is never a `match`: that keeps `cases` on
`Step s e (.ok s' fx)` usable in the theorems below. -/

inductive Step : State → Event → Out → Prop
  /-- The stream has a sending part and §3.1 accepts the event. -/
  | sendOk {s ss e ss' fx} (h : s.send = some ss) (hs : Send.Step ss e (.ok ss' fx)) :
      Step s (.send e) (.ok { s with send := some ss' } (fx.map .send))
  /-- §3.1 turns the event into a connection error. -/
  | sendError {s ss e c} (h : s.send = some ss) (hs : Send.Step ss e (.error c)) :
      Step s (.send e) (.error c)
  /-- §3.1 ignores the event entirely. -/
  | sendDrop {s ss e} (h : s.send = some ss) (hs : Send.Step ss e .drop) :
      Step s (.send e) .drop
  /-- §19.10, line 7736: "An endpoint that receives a MAX_STREAM_DATA frame for
      a receive-only stream MUST terminate the connection with error
      STREAM_STATE_ERROR"; §19.5, line 7476: the same for STOP_SENDING. -/
  | sendMissing {s e} (h : s.send = none) (hp : e.isPeerFrame = true) :
      Step s (.send e) (.error .streamStateError)
  /-- A local action on a sending part that does not exist cannot happen. -/
  | sendAbsent {s e} (h : s.send = none) (hp : e.isPeerFrame = false) :
      Step s (.send e) .drop
  /-- The stream has a receiving part and §3.2 accepts the event. -/
  | recvOk {s rs e rs' fx} (h : s.recv = some rs) (hs : Recv.Step rs e (.ok rs' fx)) :
      Step s (.recv e) (.ok { s with recv := some rs' } (fx.map .recv))
  | recvError {s rs e c} (h : s.recv = some rs) (hs : Recv.Step rs e (.error c)) :
      Step s (.recv e) (.error c)
  | recvDrop {s rs e} (h : s.recv = some rs) (hs : Recv.Step rs e .drop) :
      Step s (.recv e) .drop
  /-- §19.8, line 7638: "An endpoint MUST terminate the connection with error
      STREAM_STATE_ERROR if it receives a STREAM frame for a locally-initiated
      stream that has not yet been created, or for a send-only stream";
      §19.4, line 7431 for RESET_STREAM and §19.13, line 7864 for
      STREAM_DATA_BLOCKED. -/
  | recvMissing {s e} (h : s.recv = none) (hp : e.isPeerFrame = true) :
      Step s (.recv e) (.error .streamStateError)
  | recvAbsent {s e} (h : s.recv = none) (hp : e.isPeerFrame = false) :
      Step s (.recv e) .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .send e =>
      match s.send with
      | some ss => (Send.outcomes ss e).map (liftSend s)
      | none => if e.isPeerFrame then [.error .streamStateError] else [.drop]
  | .recv e =>
      match s.recv with
      | some rs => (Recv.outcomes rs e).map (liftRecv s)
      | none => if e.isPeerFrame then [.error .streamStateError] else [.drop]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | send e =>
      simp only [outcomes] at h
      split at h
      · rename_i ss heq
        simp only [List.mem_map] at h
        obtain ⟨o', ho', rfl⟩ := h
        have hstep := (Send.outcomes_iff ss e o').mp ho'
        cases o' with
        | ok ss' fx => exact .sendOk heq hstep
        | error c => exact .sendError heq hstep
        | drop => exact .sendDrop heq hstep
      · rename_i heq
        split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .sendMissing heq ‹_›
        · simp only [List.mem_singleton] at h; subst h
          exact .sendAbsent heq (Bool.eq_false_iff.mpr ‹_›)
    | recv e =>
      simp only [outcomes] at h
      split at h
      · rename_i rs heq
        simp only [List.mem_map] at h
        obtain ⟨o', ho', rfl⟩ := h
        have hstep := (Recv.outcomes_iff rs e o').mp ho'
        cases o' with
        | ok rs' fx => exact .recvOk heq hstep
        | error c => exact .recvError heq hstep
        | drop => exact .recvDrop heq hstep
      · rename_i heq
        split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .recvMissing heq ‹_›
        · simp only [List.mem_singleton] at h; subst h
          exact .recvAbsent heq (Bool.eq_false_iff.mpr ‹_›)
  · intro h
    cases h with
    | @sendOk ss e ss' fx hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Send.outcomes_iff ss e _).mpr hs, rfl⟩
    | @sendError ss e c hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Send.outcomes_iff ss e _).mpr hs, rfl⟩
    | @sendDrop ss e hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Send.outcomes_iff ss e _).mpr hs, rfl⟩
    | @recvOk rs e rs' fx hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Recv.outcomes_iff rs e _).mpr hs, rfl⟩
    | @recvError rs e c hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Recv.outcomes_iff rs e _).mpr hs, rfl⟩
    | @recvDrop rs e hh hs =>
      simp only [outcomes, hh]
      exact List.mem_map.mpr ⟨_, (Recv.outcomes_iff rs e _).mpr hs, rfl⟩
    | sendMissing hh hp => simp [outcomes, hh, hp]
    | sendAbsent hh hp => simp [outcomes, hh, hp]
    | recvMissing hh hp => simp [outcomes, hh, hp]
    | recvAbsent hh hp => simp [outcomes, hh, hp]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e with
  | send e =>
    simp only [outcomes]
    split
    · rename_i ss _
      cases hh : Send.outcomes ss e with
      | nil => exact absurd hh (Send.outcomes_ne ss e)
      | cons a l => simp
    · split <;> simp
  | recv e =>
    simp only [outcomes]
    split
    · rename_i rs _
      cases hh : Recv.outcomes rs e with
      | nil => exact absurd hh (Recv.outcomes_ne rs e)
      | cons a l => simp
    · split <;> simp

/-! ## 5. Invariant -/

/-- The two halves exist exactly where §3 says they do, they agree with the
    stream about its identity, and each satisfies its own invariant. -/
def Inv (s : State) : Prop :=
  s.send.isSome = hasSend s.id s.role ∧ s.recv.isSome = hasRecv s.id s.role ∧
  (∀ ss, s.send = some ss → ss.id = s.id ∧ ss.role = s.role ∧ Send.Inv ss) ∧
  (∀ rs, s.recv = some rs → rs.id = s.id ∧ rs.role = s.role ∧ Recv.Inv rs)

theorem init_inv (id : StreamId) (role : Role) (m n : Nat) : Inv (init id role m n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [init]; split <;> simp_all
  · simp only [init]; split <;> simp_all
  · intro ss h
    simp only [init] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, Send.init_inv id role m⟩
    · exact absurd h (by simp)
  · intro rs h
    simp only [init] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, Recv.init_inv id role n⟩
    · exact absurd h (by simp)

/-- Neither half ever changes the stream it belongs to. -/
theorem send_step_id {ss ss' : Send.State} {e : Send.Event} {fx : List Send.Effect}
    (h : Send.Step ss e (.ok ss' fx)) : ss'.id = ss.id ∧ ss'.role = ss.role := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem recv_step_id {rs rs' : Recv.State} {e : Recv.Event} {fx : List Recv.Effect}
    (h : Recv.Step rs e (.ok rs' fx)) : rs'.id = rs.id ∧ rs'.role = rs.role := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨i1, i2, i3, i4⟩ := hi
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    obtain ⟨hid, hrole, hinv⟩ := i3 ss hh
    obtain ⟨hid', hrole'⟩ := send_step_id hs
    refine ⟨?_, i2, ?_, i4⟩
    · simp only [Option.isSome_some]
      rw [hh] at i1
      simpa using i1
    · intro a ha
      simp only [Option.some.injEq] at ha
      subst ha
      exact ⟨by rw [hid', hid], by rw [hrole', hrole], Send.step_inv ss e2 _ gx hinv hs⟩
  | @recvOk rs e2 rs2 gx hh hs =>
    obtain ⟨hid, hrole, hinv⟩ := i4 rs hh
    obtain ⟨hid', hrole'⟩ := recv_step_id hs
    refine ⟨i1, ?_, i3, ?_⟩
    · simp only [Option.isSome_some]
      rw [hh] at i2
      simpa using i2
    · intro a ha
      simp only [Option.some.injEq] at ha
      subst ha
      exact ⟨by rw [hid', hid], by rw [hrole', hrole], Recv.step_inv rs e2 _ gx hinv hs⟩

/-! ## 6. Send side: §3.3 permitted frame types

§3.3, line 1105: "The sender of a stream sends just three frame types that
affect the state of a stream at either sender or receiver: STREAM,
STREAM_DATA_BLOCKED and RESET_STREAM"; line 1120: "The receiver of a stream
sends MAX_STREAM_DATA and STOP_SENDING frames."  A half that does not exist may
not be spoken for at all. -/

/-- Frames that belong to the sending part of stream `id`. -/
def governedBySend (id : StreamId) : Frame → Bool
  | .stream fid _ _ _ | .streamDataBlocked fid _ | .resetStream fid _ _ => decide (fid = id.val)
  | _ => false

/-- Frames that belong to the receiving part of stream `id`. -/
def governedByRecv (id : StreamId) : Frame → Bool
  | .maxStreamData fid _ | .stopSending fid _ => decide (fid = id.val)
  | _ => false

def MaySend (s : State) (f : Frame) : Prop :=
  (match s.send with
   | some ss => Send.MaySend ss f
   | none => governedBySend s.id f = false) ∧
  (match s.recv with
   | some rs => Recv.MaySend rs f
   | none => governedByRecv s.id f = false)

def maySend (s : State) (f : Frame) : Bool :=
  (match s.send with
   | some ss => Send.maySend ss f
   | none => !governedBySend s.id f) &&
  (match s.recv with
   | some rs => Recv.maySend rs f
   | none => !governedByRecv s.id f)

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp only [maySend, MaySend, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · revert h1; cases s.send <;> simp [Send.maySend_iff]
    · revert h2; cases s.recv <;> simp [Recv.maySend_iff]
  · rintro ⟨h1, h2⟩
    constructor
    · revert h1; cases s.send <;> simp [Send.maySend_iff]
    · revert h2; cases s.recv <;> simp [Recv.maySend_iff]

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

/-! ## 8. Named theorems -/

/-- **(a) The final size is immutable**, on both halves (§4.5, line 1516). -/
theorem finalSize_immutable {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) :
    (∀ ss ss' f, s.send = some ss → s'.send = some ss' → ss.finalSize = some f →
      ss'.finalSize = some f) ∧
    (∀ rs rs' f, s.recv = some rs → s'.recv = some rs' → rs.finalSize = some f →
      rs'.finalSize = some f) := by
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b f ha hb hf
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Send.finalSize_immutable hs hf
    · intro a b f ha hb hf
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb; exact hf
  | @recvOk rs e2 rs2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b f ha hb hf
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb; exact hf
    · intro a b f ha hb hf
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Recv.finalSize_immutable hs hf

/-- **(b) Data received never exceeds the credit advertised** (§4.1, line 1359). -/
theorem highest_le_maxData {s₀ s : State} {rs : Recv.State}
    (h0 : Inv s₀) (h : component.Reachable s₀ s) (hr : s.recv = some rs) :
    rs.highest ≤ rs.maxData :=
  ((component.inv_of_reachable h0 h).2.2.2 rs hr).2.2.1

/-- **(c) Terminal states absorb**, on both halves (§3.1, §3.2). -/
theorem terminal_absorbing {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) :
    (∀ ss ss', s.send = some ss → s'.send = some ss' → ss.phase.terminal = true → ss' = ss) ∧
    (∀ rs rs', s.recv = some rs → s'.recv = some rs' → rs.phase.terminal = true →
      rs'.phase = rs.phase) := by
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b ha hb ht
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Send.terminal_absorbing ht hs
    · intro a b ha hb _
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb; rfl
  | @recvOk rs e2 rs2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b ha hb _
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb; rfl
    · intro a b ha hb ht
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Recv.terminal_absorbing ht hs

/-- **(d, second half) No step leaves the diagrams of §3.1 and §3.2.** -/
theorem step_follows_diagram {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) :
    (∀ ss ss', s.send = some ss → s'.send = some ss' →
      Send.Reaches ss.phase ss'.phase = true) ∧
    (∀ rs rs', s.recv = some rs → s'.recv = some rs' →
      Recv.Reaches rs.phase rs'.phase = true) := by
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b ha hb
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Send.step_follows_diagram hs
    · intro a b ha hb
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      cases a.phase <;> rfl
  | @recvOk rs e2 rs2 gx hh hs =>
    refine ⟨?_, ?_⟩
    · intro a b ha hb
      simp only at hb
      rw [ha] at hb
      simp only [Option.some.injEq] at hb
      subst hb
      cases a.phase <;> rfl
    · intro a b ha hb
      rw [hh] at ha
      simp only [Option.some.injEq] at ha hb
      subst ha; subst hb
      exact Recv.step_follows_diagram hs

/-! ### §3.3 Permitted frame types, as theorems -/

/-- §3.3, line 1112: "A sender MUST NOT send any of these frames from a terminal
    state ('Data Recvd' or 'Reset Recvd')." -/
theorem no_send_from_terminal {s : State} {ss : Send.State} {f : Frame}
    (hh : s.send = some ss) (hid : ss.id = s.id) (ht : ss.phase.terminal = true)
    (hf : governedBySend s.id f = true) : maySend s f = false := by
  have ht' : ss.phase.mayCarryData = false := by
    cases hp : ss.phase <;> simp_all [Send.Phase.terminal, Send.Phase.mayCarryData]
  simp only [maySend, hh, Bool.and_eq_false_iff]
  refine Or.inl ?_
  cases f <;>
    simp_all [governedBySend, Send.maySend, Send.maySendStream, Send.maySendBlocked,
      Send.maySendReset]

/-- §3.3, line 1114: "A sender MUST NOT send a STREAM or STREAM_DATA_BLOCKED
    frame for a stream in the 'Reset Sent' state or any terminal state." -/
theorem no_data_after_reset {s : State} {ss : Send.State} {offset : Nat} {fin : Bool}
    {data : ByteArray} (hh : s.send = some ss) (hid : ss.id = s.id)
    (ht : ss.phase.mayCarryData = false) :
    maySend s (.stream s.id.val offset fin data) = false ∧
    ∀ v, maySend s (.streamDataBlocked s.id.val v) = false := by
  constructor
  · simp [maySend, hh, hid, Send.maySend, Send.maySendStream, ht]
  · intro v; simp [maySend, hh, hid, Send.maySend, Send.maySendBlocked, ht]

/-- §3.3, line 1121: "The receiver only sends MAX_STREAM_DATA in the 'Recv'
    state." -/
theorem maxStreamData_only_in_recv {s : State} {rs : Recv.State} {v : Nat}
    (hh : s.recv = some rs) (hid : rs.id = s.id)
    (h : maySend s (.maxStreamData s.id.val v) = true) : rs.phase = .recv := by
  simp only [maySend, hh, Bool.and_eq_true] at h
  have h2 := h.2
  simp only [Recv.maySend, hid, reduceIte, Recv.maySendMaxStreamData] at h2
  cases hp : rs.phase <;> simp_all [Recv.Phase.isRecv]

/-- §3.3, line 1123: "A receiver MAY send STOP_SENDING in any state where it has
    not received a RESET_STREAM frame; that is states other than 'Reset Recvd'
    or 'Reset Read'." -/
theorem stopSending_not_after_reset {s : State} {rs : Recv.State} {code : Nat}
    (hh : s.recv = some rs) (hid : rs.id = s.id) (ht : rs.phase.mayStopSending = false) :
    maySend s (.stopSending s.id.val code) = false := by
  simp [maySend, hh, hid, Recv.maySend, Recv.maySendStopSending, ht]

/-- A stream with no sending part (a receive-only unidirectional stream) may not
    have STREAM, STREAM_DATA_BLOCKED or RESET_STREAM sent for it at all; the
    mirror of §19.8, line 7638 and §19.4, line 7431 on the receiving endpoint. -/
theorem nothing_sent_on_recv_only {s : State} {f : Frame}
    (hh : s.send = none) (hf : governedBySend s.id f = true) : maySend s f = false := by
  simp [maySend, hh, hf]

/-- The mirror: no MAX_STREAM_DATA or STOP_SENDING for a send-only stream
    (§19.10, line 7736; §19.5, line 7476). -/
theorem nothing_sent_on_send_only {s : State} {f : Frame}
    (hh : s.recv = none) (hf : governedByRecv s.id f = true) : maySend s f = false := by
  simp [maySend, hh, hf]

/-! ### §3.4 Bidirectional stream states -/

/-- §3.4, Table 2: a composite state for a bidirectional stream.  `openStream`
    is Table 2's "open" (`open` is a Lean keyword). -/
inductive Composite where
  | idle | openStream | halfClosedRemote | halfClosedLocal | closed
  deriving DecidableEq, Repr

/-- §3.4, Table 2, rows 2–9.  The sending part contributes only whether it is
    still able to carry data ("Ready"/"Send"/"Data Sent") and the receiving part
    only whether it is still waiting for data ("Recv"/"Size Known"). -/
def Composite.of (a : Send.Phase) (b : Recv.Phase) : Composite :=
  match a.mayCarryData, b.beforeAllData with
  | true, true => .openStream
  | true, false => .halfClosedRemote
  | false, true => .halfClosedLocal
  | false, false => .closed

/-- §3.4, Note (*1): "A stream is considered 'idle' if it has not yet been
    created, or if the receiving part of the stream is in the 'Recv' state
    without yet having received any frames." -/
def Recv.untouched (rs : Recv.State) : Bool :=
  rs.ranges.isEmpty && decide (rs.highest = 0) && rs.finalSize.isNone && rs.stopSending.isNone

/-- The composite state of a bidirectional stream; `none` for a unidirectional
    one, which has only one half (§3.4, line 1133). -/
def State.composite (s : State) : Option Composite :=
  match s.send, s.recv with
  | some ss, some rs =>
      some (if ss.phase = .ready && Recv.untouched rs && rs.phase = .recv then .idle
            else Composite.of ss.phase rs.phase)
  | _, _ => none

/-- §3.4, line 1140: "The simplest model presents the stream as 'open' when
    either sending or receiving parts are in a non-terminal state and 'closed'
    when both sending and receiving streams are in terminal states."  This one
    also covers unidirectional streams. -/
def State.simpleClosed (s : State) : Bool :=
  (match s.send with | some ss => ss.phase.terminal | none => true) &&
  (match s.recv with | some rs => rs.phase.terminal | none => true)

/-- Table 2 read as a statement about the halves: each composite state is
    exactly one combination of "the sending part can still carry data" and "the
    receiving part is still waiting for data". -/
theorem composite_of_iff (a : Send.Phase) (b : Recv.Phase) :
    (Composite.of a b = .openStream ↔ a.mayCarryData = true ∧ b.beforeAllData = true) ∧
    (Composite.of a b = .halfClosedRemote ↔ a.mayCarryData = true ∧ b.beforeAllData = false) ∧
    (Composite.of a b = .halfClosedLocal ↔ a.mayCarryData = false ∧ b.beforeAllData = true) ∧
    (Composite.of a b = .closed ↔ a.mayCarryData = false ∧ b.beforeAllData = false) := by
  cases a <;> cases b <;> decide

/-- Both halves terminal ⇒ Table 2 says "closed". -/
theorem composite_closed_of_terminal {a : Send.Phase} {b : Recv.Phase}
    (ha : a.terminal = true) (hb : b.terminal = true) : Composite.of a b = .closed := by
  cases a <;> cases b <;> simp_all [Send.Phase.terminal, Recv.Phase.terminal] <;> decide

/-- The state-level form: when the simple model of §3.4 calls a bidirectional
    stream closed, Table 2 does too. -/
theorem simpleClosed_composite {s : State} {a : Send.State} {b : Recv.State}
    (h : s.simpleClosed = true) (hs : s.send = some a) (hr : s.recv = some b) :
    s.composite = some .closed := by
  simp only [State.simpleClosed, hs, hr, Bool.and_eq_true] at h
  have hidle : (decide (a.phase = .ready) && Recv.untouched b && decide (b.phase = .recv)) = false := by
    cases hp : a.phase <;> simp_all [Send.Phase.terminal]
  simp only [State.composite, hs, hr, hidle, Bool.false_eq_true, ite_false, Option.some.injEq]
  exact composite_closed_of_terminal h.1 h.2

/-! ## 9. Examples -/

-- §2.1, Table 1: stream 2 is client-initiated and unidirectional, so a client
-- has only a sending part and a server only a receiving part.
private def uniC : State := init (StreamId.make .client .uni 0) .client 100 100
private def uniS : State := init (StreamId.make .client .uni 0) .server 100 100
-- Stream 0 is client-initiated and bidirectional: both halves at both ends.
private def biC : State := init (StreamId.make .client .bidi 0) .client 100 100

example : uniC.recv = none := by decide
example : uniS.send = none := by decide
example : biC.send.isSome ∧ biC.recv.isSome := by decide

-- §19.8, line 7638: a STREAM frame for a send-only stream is a
-- STREAM_STATE_ERROR …
example : component.step uniC (.recv (.recvStream 0 5 false)) = .error .streamStateError := by
  decide
-- … as is a RESET_STREAM (§19.4, line 7431) …
example : component.step uniC (.recv (.recvResetStream 1 0)) = .error .streamStateError := by
  decide
-- … and a STREAM_DATA_BLOCKED (§19.13, line 7864).
example : component.step uniC (.recv (.recvStreamDataBlocked 0)) = .error .streamStateError := by
  decide
-- §19.10, line 7736 / §19.5, line 7476: MAX_STREAM_DATA and STOP_SENDING for a
-- receive-only stream are STREAM_STATE_ERRORs.
example : component.step uniS (.send (.recvMaxStreamData 200)) = .error .streamStateError := by
  decide
example : component.step uniS (.send (.recvStopSending 3)) = .error .streamStateError := by
  decide

-- §3.4, line 1133: a unidirectional stream has no composite state …
example : uniC.composite = none := by decide
-- … while a fresh bidirectional stream is "idle" (Table 2, Note *1) …
example : biC.composite = some .idle := by decide
-- … and becomes "open" as soon as anything has been sent or received.
example :
    ((component.step biC (.recv (.recvStream 0 5 false))).next biC).composite =
      some .openStream := by
  decide

-- §4.4, line 1466: "For a bidirectional stream, RESET_STREAM has no effect on
-- data flow in the opposite direction."  Resetting our sending part leaves the
-- receiving part exactly where it was.
example :
    ((component.step biC (.send (.sentResetStream 1 0))).next biC).recv = biC.recv := by decide

-- §3.3: a frame for another stream is never this stream's business.
example : component.maySend uniC (.maxStreamData 4 100) = true := by decide
-- but MAX_STREAM_DATA for *this* send-only stream may not be sent.
example : component.maySend uniC (.maxStreamData 2 100) = false := by decide

-- Following an implementation from the outside, through both halves.
private def biCrecvd : Recv.State :=
  { Recv.init (StreamId.make .client .bidi 0) .client 100 with
      phase := .dataRecvd, highest := 5, ranges := [(0, 5)], finalSize := some 5 }

example :
    component.track biC (.recv (.recvStream 0 5 true))
        (.ok [.recv (.dataAvailable 5), .recv (.allDataReceived 5)]) =
      some { biC with recv := some biCrecvd } := by
  rfl

/-! ## 10. Coverage and notes

Assigned text for this file: §2 (overview), §3 (intro), §3.3, §3.4, and the
direction rules of §19.4/§19.5/§19.8/§19.10/§19.13.  §3.1, §3.2, §3.5, §4.1,
§4.4 and §4.5 are covered in `Spec/Stream/Send.lean` and `Spec/Stream/Recv.lean`,
each of which carries its own coverage table.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §2 (641–736) | streams are an ordered byte-stream abstraction, created by either endpoint | descriptive; the model is one stream seen by one endpoint |
| §2.1 (680) | a stream ID MUST NOT be reused | out of scope: WP9 |
| §2.1 (697) | the two low bits give initiator and directionality | `Spec.StreamId` (WP0), used by `hasSend`/`hasRecv` |
| §2.1 (712) | a stream ID used out of order opens all lower-numbered streams | out of scope: WP9 |
| §2.3 (777) | implementations SHOULD offer stream prioritization | out of scope: not observable behaviour |
| §3 (866) | unidirectional streams use one state machine, bidirectional both | `hasSend`, `hasRecv`, `State` |
| §3 (879) | the state machines are informative; other state machines are allowed | `Step` is what constrains; the phases are a presentation |
| §3 (892) | one event can cause a transition through several states | `Send.Reaches` / `Recv.Reaches` are the reflexive-transitive closures |
| §3.3 (1105) | the sender sends STREAM, STREAM_DATA_BLOCKED, RESET_STREAM | `governedBySend` |
| §3.3 (1112) | MUST NOT send any of them from a terminal state | `no_send_from_terminal` |
| §3.3 (1114) | MUST NOT send STREAM / STREAM_DATA_BLOCKED after RESET_STREAM | `no_data_after_reset` |
| §3.3 (1116) | a receiver could receive any of the three in any state | `Recv.Step` has an outcome for every phase |
| §3.3 (1120) | the receiver sends MAX_STREAM_DATA and STOP_SENDING | `governedByRecv` |
| §3.3 (1121) | MAX_STREAM_DATA only in "Recv" | `maxStreamData_only_in_recv` |
| §3.3 (1123) | STOP_SENDING in any state other than "Reset Recvd"/"Reset Read" | `stopSending_not_after_reset` |
| §3.3 (1127) | a sender could receive either of those two in any state | `Send.Step.maxStreamDataIgnored`, `Send.Step.stopSendingLate` |
| §3.4 (1130) | a bidirectional stream is composed of sending and receiving parts | `State` |
| §3.4 (1140) | the simplest model: open unless both parts are terminal | `State.simpleClosed` |
| §3.4 (Table 2) | the HTTP/2-like composite mapping | `Composite.of`, `State.composite`, `composite_of_iff` |
| §3.4 (Note *1) | idle = nothing received yet | `Recv.untouched` |
| §19.4 (7431) | RESET_STREAM for a send-only stream MUST be STREAM_STATE_ERROR | `Step.recvMissing` |
| §19.5 (7476) | STOP_SENDING for a receive-only stream MUST be STREAM_STATE_ERROR | `Step.sendMissing` |
| §19.5 (7474) | STOP_SENDING for a locally-initiated stream not yet created | out of scope: WP9 (stream creation) |
| §19.8 (7638) | STREAM for a send-only stream MUST be STREAM_STATE_ERROR | `Step.recvMissing` |
| §19.10 (7736) | MAX_STREAM_DATA for a receive-only stream MUST be STREAM_STATE_ERROR | `Step.sendMissing` |
| §19.13 (7864) | STREAM_DATA_BLOCKED for a send-only stream MUST be STREAM_STATE_ERROR | `Step.recvMissing` |

NOTES

* **Two components, joined by a third.**  The sending and receiving parts are
  separate `Component`s because §3.1 and §3.2 are separate state machines whose
  only interaction is through frames on the wire, and because a unidirectional
  stream has only one of them.  This file's `component` is their product: every
  event belongs to exactly one half, so the composite's `outcomes` is one
  `List.map` and all of its theorems lift from the halves.  Each half carries
  the `StreamId` and `Role` so that its own `MaySend` can tell a frame for this
  stream from a frame for another; `Inv` keeps the three copies in agreement.
* **Which half an event belongs to** is decided by which part of the stream the
  frame concerns, not by who sent it: MAX_STREAM_DATA and STOP_SENDING arrive
  from the peer but concern *our sending* part, and are therefore `Event.send`.
  That is also what makes the STREAM_STATE_ERROR rules fall out: a frame for a
  half that does not exist is exactly the "send-only"/"receive-only" case of
  §19.4/§19.5/§19.8/§19.10/§19.13.
* **`Step` for a missing half distinguishes frames from local actions.**  A
  frame for a half that does not exist is a connection error; an application
  call on a half that does not exist (the application asking to write to a
  receive-only stream) simply cannot happen and is `.drop`.
* **Table 2 is not "both halves terminal".**  §3.4's mapping calls
  (Reset Sent, Data Recvd) "closed" although "Reset Sent" is not a terminal
  state of §3.1, so `Composite.of a b = .closed` is strictly weaker than
  `State.simpleClosed`; `composite_closed_of_terminal` is the implication that
  does hold, and the text itself says the mapping "is just one possibility".
* **"Idle" cannot be read off the phases alone** (Note *1 says "without yet
  having received any frames"), so `State.composite` also looks at whether the
  receiving part has any record of a frame.  A STREAM_DATA_BLOCKED, or an empty
  STREAM frame at offset 0, leaves no trace in the receiving state, so a stream
  that has received only those still counts as idle here.
* **Stream creation is WP9.**  This file assumes the stream exists; the other
  half of §19.5/§19.8/§19.10's STREAM_STATE_ERROR sentences — "for a
  locally-initiated stream that has not yet been created" — needs the stream
  table and is left to WP9, as is §2.1's implicit opening of lower-numbered
  streams and both connection-level limits.
-/

end Quic.Spec.Stream
