import QuicModel.Spec.AddressValidation

/-
  WP5b: §8.2 path validation — PATH_CHALLENGE and PATH_RESPONSE.

  Text: draft-ietf-quic-transport-34 lines 3070–3271 (§8.2 and its four
  subsections).  The anti-amplification limit the datagram-expansion rules refer
  to lives in `Spec/AddressValidation.lean`; migration policy (§9) is WP10's.

  File order as in `Spec/Template.lean`.
-/
namespace Quic.Spec.PathValidation

/-- §19.17: the PATH_CHALLENGE Data field is 8 bytes. -/
def challengeSize : Nat := 8

/-- §14, §8.2.1 line 3154: "the smallest allowed maximum datagram size of 1200
    bytes". -/
def minDatagramSize : Nat := 1200

/-! ## 1. State, events, effects -/

/-- A network path: a local address and a peer address (§8.2, line 3074).  An
    opaque handle; the model never inspects it. -/
structure Path where
  id : Nat
  deriving DecidableEq, Repr

/-- A PATH_CHALLENGE we have sent and not yet had answered. -/
structure Challenge where
  /-- §8.2.1, line 3150: "unpredictable data in every PATH_CHALLENGE frame". -/
  data : ByteArray
  /-- The path the challenge was sent on; §8.2.3, line 3214: a response "received
      on any network path validates the path on which the PATH_CHALLENGE was
      sent". -/
  path : Path
  /-- §8.2.4, line 3234: "Endpoints SHOULD abandon path validation based on a
      timer."  The instant at which this attempt is abandoned. -/
  deadline : Time
  deriving DecidableEq

inductive PathStatus where
  | unvalidated
  | validated
  | failed
  deriving DecidableEq, Repr

structure State where
  /-- Challenges we have sent, newest first. -/
  outstanding : List Challenge
  /-- §8.2.2, line 3177: PATH_RESPONSEs we owe, each with the path the
      PATH_CHALLENGE arrived on.  A multiset: one entry per PATH_CHALLENGE
      received, so that line 3205's "MUST NOT send more than one PATH_RESPONSE
      frame in response to one PATH_CHALLENGE frame" is a counting property. -/
  pending : List (ByteArray × Path)
  status : Map Path PathStatus
  deriving DecidableEq

def init : State := { outstanding := [], pending := [], status := [] }

def State.statusOf (s : State) (p : Path) : PathStatus := (s.status.get? p).getD .unvalidated

def State.isValidated (s : State) (p : Path) : Bool := decide (s.statusOf p = .validated)

def State.setStatus (s : State) (p : Path) (st : PathStatus) : State :=
  { s with status := s.status.set p st }

def State.markValidated (s : State) (p : Path) : State := s.setStatus p .validated

/-- §8.2.4: abandoning validation makes the path unusable.  A path that is
    already validated stays validated — §8.2.3, line 3221 has an endpoint start a
    *second* validation on a validated path to check the MTU, and failing that
    one does not undo the first. -/
def State.markFailed (s : State) (p : Path) : State :=
  if s.statusOf p = .validated then s else s.setStatus p .failed

/-- Drop every outstanding challenge for a path (it has been validated, or
    abandoned). -/
def State.clearPath (s : State) (p : Path) : State :=
  { s with outstanding := s.outstanding.filter (fun c => decide (c.path ≠ p)) }

/-- Do we already have an outstanding challenge carrying this data? -/
def State.hasData (s : State) (d : ByteArray) : Bool :=
  s.outstanding.any (fun c => decide (c.data = d))

/-- The outstanding challenge a PATH_RESPONSE carrying `d` answers, if any. -/
def State.matching (s : State) (d : ByteArray) : Option Challenge :=
  s.outstanding.find? (fun c => decide (c.data = d))

/-- §8.2.4, line 3234: some challenge on `p` has reached the instant at which
    this validation is abandoned. -/
def State.expired (s : State) (p : Path) (now : Time) : Bool :=
  s.outstanding.any (fun c => decide (c.path = p ∧ c.deadline ≤ now))

inductive Event where
  /-- §8.2.1, line 3131: "To initiate path validation, an endpoint sends a
      PATH_CHALLENGE frame containing an unpredictable payload on the path to be
      validated."  The unpredictable payload is supplied on the event: entropy is
      abstract here, only freshness is checked. -/
  | startValidation (p : Path) (data : ByteArray) (deadline : Time)
  /-- §8.2.2, line 3177: a PATH_CHALLENGE arrived on path `p`. -/
  | recvChallenge (p : Path) (data : ByteArray)
  /-- §8.2.3, line 3212: a PATH_RESPONSE arrived on path `p`. -/
  | recvResponse (p : Path) (data : ByteArray)
  /-- The PATH_RESPONSE echoing `data` was sent on path `p`. -/
  | responseSent (p : Path) (data : ByteArray)
  /-- §8.2.4, line 3234: the abandon timer for `p` fired at `now`. -/
  | timeout (p : Path) (now : Time)
  deriving DecidableEq

inductive Effect where
  /-- §8.2.1: send a PATH_CHALLENGE carrying `data` on `p`. -/
  | sendChallenge (p : Path) (data : ByteArray)
  /-- §8.2.2, line 3183: "A PATH_RESPONSE frame MUST be sent on the network path
      where the PATH_CHALLENGE was received" — the path is part of the effect. -/
  | queueResponse (p : Path) (data : ByteArray)
  /-- §8.2.3: path validation succeeded. -/
  | pathValidated (p : Path)
  /-- §8.2.4: path validation was abandoned; the path is unusable. -/
  | pathFailed (p : Path)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-- Remove one occurrence of `q`: `pending` is a multiset (see NOTES 9), and
    sending one PATH_RESPONSE discharges one received PATH_CHALLENGE. -/
def removeFirst (l : List (ByteArray × Path)) (q : ByteArray × Path) : List (ByteArray × Path) :=
  match l with
  | [] => []
  | x :: xs => if x = q then xs else x :: removeFirst xs q

/-- How many times `q` occurs in `l`. -/
def occurs (l : List (ByteArray × Path)) (q : ByteArray × Path) : Nat :=
  match l with
  | [] => 0
  | x :: xs => (if x = q then 1 else 0) + occurs xs q

theorem mem_of_mem_removeFirst : ∀ (l : List (ByteArray × Path)) (q x : ByteArray × Path),
    x ∈ removeFirst l q → x ∈ l := by
  intro l
  induction l with
  | nil => intro q x h; simp [removeFirst] at h
  | cons y ys ih =>
    intro q x h
    rw [removeFirst] at h
    split at h
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih q x h')

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §8.2.1, lines 3131 and 3150: a validation starts with a fresh,
      unpredictable 8-byte payload sent on the path to be validated. -/
  | start {s p d dl} (h : d.size = challengeSize ∧ s.hasData d = false) :
      Step s (.startValidation p d dl)
        (.ok { s with outstanding := ⟨d, p, dl⟩ :: s.outstanding } [.sendChallenge p d])
  /-- §8.2.1, line 3150: "The endpoint MUST use unpredictable data in every
      PATH_CHALLENGE frame so that it can associate the peer's response with the
      corresponding PATH_CHALLENGE."  Reusing data that is already outstanding
      would break that association, so no validation starts. -/
  | startStale {s p d dl} (h : ¬ (d.size = challengeSize ∧ s.hasData d = false)) :
      Step s (.startValidation p d dl) .drop
  /-- §8.2.2, line 3177: "On receiving a PATH_CHALLENGE frame, an endpoint MUST
      respond by echoing the data contained in the PATH_CHALLENGE frame in a
      PATH_RESPONSE frame", line 3183 "on the network path where the
      PATH_CHALLENGE was received". -/
  | challenge {s p d} :
      Step s (.recvChallenge p d)
        (.ok { s with pending := s.pending ++ [(d, p)] } [.queueResponse p d])
  /-- §8.2.3, line 3212: "Path validation succeeds when a PATH_RESPONSE frame is
      received that contains the data that was sent in a previous PATH_CHALLENGE
      frame.  A PATH_RESPONSE frame received on any network path validates the
      path on which the PATH_CHALLENGE was sent." -/
  | responseMatch {s p d c} (hf : s.matching d = some c) :
      Step s (.recvResponse p d)
        (.ok ((s.clearPath c.path).markValidated c.path) [.pathValidated c.path])
  /-- §19.18: a PATH_RESPONSE that matches nothing may simply be ignored. -/
  | responseIgnore {s p d} (hf : s.matching d = none) :
      Step s (.recvResponse p d) (.ok s [])
  /-- §19.18: "If the content of a PATH_RESPONSE frame does not match the content
      of a PATH_CHALLENGE frame previously sent by the endpoint, the endpoint MAY
      generate a connection error of type PROTOCOL_VIOLATION." -/
  | responseViolation {s p d} (hf : s.matching d = none) :
      Step s (.recvResponse p d) (.error .protocolViolation)
  /-- §8.2.2, line 3205: "An endpoint MUST NOT send more than one PATH_RESPONSE
      frame in response to one PATH_CHALLENGE frame" — sending one consumes the
      queued obligation. -/
  | responseSent {s p d} :
      Step s (.responseSent p d) (.ok { s with pending := removeFirst s.pending (d, p) } [])
  /-- §8.2.4, lines 3231–3234: "Path validation only fails when the endpoint
      attempting to validate the path abandons its attempt to validate the path.
      Endpoints SHOULD abandon path validation based on a timer." -/
  | timeoutFail {s p now} (h : s.expired p now = true) :
      Step s (.timeout p now) (.ok ((s.clearPath p).markFailed p) [.pathFailed p])
  /-- No challenge on `p` has reached its deadline: nothing is abandoned. -/
  | timeoutEarly {s p now} (h : s.expired p now = false) :
      Step s (.timeout p now) .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .startValidation p d dl =>
      if d.size = challengeSize ∧ s.hasData d = false then
        [.ok { s with outstanding := ⟨d, p, dl⟩ :: s.outstanding } [.sendChallenge p d]]
      else [.drop]
  | .recvChallenge p d =>
      [.ok { s with pending := s.pending ++ [(d, p)] } [.queueResponse p d]]
  | .recvResponse _ d =>
      match s.matching d with
      | some c => [.ok ((s.clearPath c.path).markValidated c.path) [.pathValidated c.path]]
      | none => [.ok s [], .error .protocolViolation]
  | .responseSent p d => [.ok { s with pending := removeFirst s.pending (d, p) } []]
  | .timeout p now =>
      if s.expired p now = true then [.ok ((s.clearPath p).markFailed p) [.pathFailed p]]
      else [.drop]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | startValidation p d dl =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .start ‹_›
        · simp only [List.mem_singleton] at h; subst h; exact .startStale ‹_›
    | recvChallenge p d => simp only [outcomes, List.mem_singleton] at h; subst h; exact .challenge
    | recvResponse p d =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .responseMatch ‹_›
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact .responseIgnore ‹_›
          · exact .responseViolation ‹_›
    | responseSent p d => simp only [outcomes, List.mem_singleton] at h; subst h; exact .responseSent
    | timeout p now =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .timeoutFail ‹_›
        · simp only [List.mem_singleton] at h; subst h
          exact .timeoutEarly (by simpa using ‹¬ (s.expired p now = true)›)
  · intro h
    cases h with
    | start h => simp [outcomes, h]
    | startStale h => simp [outcomes, h]
    | challenge => simp [outcomes]
    | responseMatch hf => simp [outcomes, hf]
    | responseIgnore hf => simp [outcomes, hf]
    | responseViolation hf => simp [outcomes, hf]
    | responseSent => simp [outcomes]
    | timeoutFail h => simp [outcomes, h]
    | timeoutEarly h => simp [outcomes, h]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- §19.17: every challenge we are waiting on carries 8 bytes of data. -/
def Inv (s : State) : Prop := ∀ c ∈ s.outstanding, c.data.size = challengeSize

@[simp] theorem outstanding_setStatus (s : State) (p : Path) (st : PathStatus) :
    (s.setStatus p st).outstanding = s.outstanding := rfl

@[simp] theorem outstanding_markValidated (s : State) (p : Path) :
    (s.markValidated p).outstanding = s.outstanding := rfl

@[simp] theorem outstanding_markFailed (s : State) (p : Path) :
    (s.markFailed p).outstanding = s.outstanding := by
  unfold State.markFailed; split <;> rfl

@[simp] theorem outstanding_clearPath (s : State) (p : Path) :
    (s.clearPath p).outstanding = s.outstanding.filter (fun c => decide (c.path ≠ p)) := rfl

@[simp] theorem pending_setStatus (s : State) (p : Path) (st : PathStatus) :
    (s.setStatus p st).pending = s.pending := rfl

@[simp] theorem pending_markValidated (s : State) (p : Path) :
    (s.markValidated p).pending = s.pending := rfl

@[simp] theorem pending_markFailed (s : State) (p : Path) :
    (s.markFailed p).pending = s.pending := by
  unfold State.markFailed; split <;> rfl

@[simp] theorem pending_clearPath (s : State) (p : Path) :
    (s.clearPath p).pending = s.pending := rfl

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | start h =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact hi c hc
  | challenge => exact hi
  | responseMatch =>
    intro c hc
    simp only [outstanding_markValidated, outstanding_clearPath, List.mem_filter] at hc
    exact hi c hc.1
  | responseIgnore => exact hi
  | responseSent => exact hi
  | timeoutFail =>
    intro c hc
    simp only [outstanding_markFailed, outstanding_clearPath, List.mem_filter] at hc
    exact hi c hc.1

/-! ## 6. Send side -/

/-- §8.2.2, line 3177: a PATH_RESPONSE echoes a PATH_CHALLENGE we received, and
    §8.2.2, line 3205: at most one per PATH_CHALLENGE — so the data must still be
    queued.  §8.2.1, line 3150: a PATH_CHALLENGE carries data we can associate
    with a response, i.e. one of our outstanding challenges. -/
def MaySend (s : State) : Frame → Prop
  | .pathChallenge d => ∃ c ∈ s.outstanding, c.data = d
  | .pathResponse d => ∃ q ∈ s.pending, q.1 = d
  | _ => True

def maySend (s : State) : Frame → Bool
  | .pathChallenge d => s.outstanding.any (fun c => decide (c.data = d))
  | .pathResponse d => s.pending.any (fun q => decide (q.1 = d))
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend]

/-- The path-aware form of the PATH_RESPONSE rule (§8.2.2, line 3183: the
    response goes back on the path the challenge arrived on). -/
def MaySendResponseOn (s : State) (d : ByteArray) (p : Path) : Prop := (d, p) ∈ s.pending

/-- A datagram carries a PATH_CHALLENGE or PATH_RESPONSE and so must be
    expanded. -/
def isProbeFrame : Frame → Bool
  | .pathChallenge _ => true
  | .pathResponse _ => true
  | _ => false

def expandRequired (fs : List Frame) : Bool := fs.any isProbeFrame

/-- §8.2.1, line 3154: "An endpoint MUST expand datagrams that contain a
    PATH_CHALLENGE frame to at least the smallest allowed maximum datagram size
    of 1200 bytes, unless the anti-amplification limit for the path does not
    permit sending a datagram of this size", and §8.2.2, line 3197, the same for
    PATH_RESPONSE: "an endpoint MUST NOT expand the datagram containing the
    PATH_RESPONSE if the resulting data exceeds the anti-amplification limit."

    `av`/`a` are the anti-amplification state of `Spec/AddressValidation.lean`
    for the peer address of this path. -/
def MaySendDatagram (av : AddressValidation.State) (a : AddressValidation.Addr)
    (fs : List Frame) (nBytes : Nat) : Prop :=
  AddressValidation.MaySendDatagram av a nBytes ∧
    (expandRequired fs = false ∨
      ¬ AddressValidation.MaySendDatagram av a minDatagramSize ∨
      minDatagramSize ≤ nBytes)

instance instDecMaySendDatagram (av : AddressValidation.State) (a : AddressValidation.Addr)
    (fs : List Frame) (n : Nat) : Decidable (MaySendDatagram av a fs n) :=
  inferInstanceAs (Decidable (_ ∧ _))

def maySendDatagram (av : AddressValidation.State) (a : AddressValidation.Addr)
    (fs : List Frame) (nBytes : Nat) : Bool := decide (MaySendDatagram av a fs nBytes)

theorem maySendDatagram_iff (av : AddressValidation.State) (a : AddressValidation.Addr)
    (fs : List Frame) (n : Nat) : maySendDatagram av a fs n = true ↔ MaySendDatagram av a fs n := by
  simp [maySendDatagram]

/-- §8.2.1, line 3142: "an endpoint SHOULD NOT send multiple PATH_CHALLENGE
    frames in a single packet."  Advice, so it is not part of `MaySend`: an
    implementation that ignores it is still conforming. -/
def RecommendedPacket (fs : List Frame) : Prop :=
  (fs.filter (fun f => match f with | .pathChallenge _ => true | _ => false)).length ≤ 1

/-! ## 7. The component -/

def component : Component where
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

theorem statusOf_setStatus_self (s : State) (p : Path) (st : PathStatus) :
    (s.setStatus p st).statusOf p = st := by
  simp [State.statusOf, State.setStatus]

theorem statusOf_setStatus_ne (s : State) {p q : Path} (st : PathStatus) (h : q ≠ p) :
    (s.setStatus p st).statusOf q = s.statusOf q := by
  simp [State.statusOf, State.setStatus, Map.get?_set_of_ne _ _ h]

@[simp] theorem statusOf_clearPath (s : State) (p q : Path) :
    (s.clearPath p).statusOf q = s.statusOf q := rfl

@[simp] theorem isValidated_clearPath (s : State) (p q : Path) :
    (s.clearPath p).isValidated q = s.isValidated q := rfl

theorem isValidated_setStatus_ne (s : State) {p q : Path} (st : PathStatus) (h : q ≠ p) :
    (s.setStatus p st).isValidated q = s.isValidated q := by
  simp [State.isValidated, statusOf_setStatus_ne _ _ h]

/-- **(c)** A path becomes validated only by a PATH_RESPONSE that carries the
    data of one of our outstanding challenges for that path.
    §8.2.3, lines 3212–3215; §8.2.4, line 3253: "a PATH_RESPONSE frame with
    appropriate data is required for path validation to succeed." -/
theorem validated_only_by_response {s s' : State} {e : Event} {fx : List Effect} {p : Path}
    (h : Step s e (.ok s' fx)) (h0 : s.isValidated p = false) (h1 : s'.isValidated p = true) :
    ∃ (q : Path) (d : ByteArray) (c : Challenge),
      e = .recvResponse q d ∧ c ∈ s.outstanding ∧ c.data = d ∧ c.path = p := by
  cases h with
  | start => exact absurd h1 (by simp [State.isValidated, State.statusOf] at h0 ⊢; exact h0)
  | challenge => exact absurd h1 (by simp [State.isValidated, State.statusOf] at h0 ⊢; exact h0)
  | responseIgnore => exact absurd h1 (by simp [h0])
  | responseSent => exact absurd h1 (by simp [State.isValidated, State.statusOf] at h0 ⊢; exact h0)
  | @responseMatch p' d c hf =>
    by_cases hEq : p = c.path
    · refine ⟨p', d, c, rfl, List.mem_of_find?_eq_some hf, ?_, hEq.symm⟩
      simpa using List.find?_some hf
    · rw [State.markValidated, isValidated_setStatus_ne _ _ hEq, isValidated_clearPath] at h1
      exact absurd h1 (by simp [h0])
  | @timeoutFail p' now _ =>
    exfalso
    unfold State.markFailed at h1
    split at h1
    · rw [isValidated_clearPath] at h1; simp [h0] at h1
    · by_cases hEq : p = p'
      · subst hEq
        simp [State.isValidated, statusOf_setStatus_self] at h1
      · rw [isValidated_setStatus_ne _ _ hEq, isValidated_clearPath] at h1
        simp [h0] at h1

/-- A validated path stays validated: §8.2.3's success is permanent, and the
    abandon of §8.2.4 only applies to a path that is not yet validated. -/
theorem validated_persists {s s' : State} {e : Event} {fx : List Effect} {p : Path}
    (h : Step s e (.ok s' fx)) (hv : s.isValidated p = true) : s'.isValidated p = true := by
  cases h with
  | start => exact hv
  | challenge => exact hv
  | responseIgnore => exact hv
  | responseSent => exact hv
  | @responseMatch p' d c hf =>
    by_cases hEq : p = c.path
    · subst hEq; simp [State.markValidated, State.isValidated, statusOf_setStatus_self]
    · rw [State.markValidated, isValidated_setStatus_ne _ _ hEq, isValidated_clearPath]; exact hv
  | @timeoutFail p' now _ =>
    unfold State.markFailed
    split
    · rw [isValidated_clearPath]; exact hv
    · rename_i hne
      by_cases hEq : p = p'
      · subst hEq
        exact absurd (by simpa [State.isValidated] using hv) hne
      · rw [isValidated_setStatus_ne _ _ hEq, isValidated_clearPath]; exact hv

/-- Nothing is ever queued for a PATH_RESPONSE except by receiving the
    PATH_CHALLENGE it echoes, on the path it arrived on (§8.2.2, lines
    3177–3185). -/
theorem pending_only_from_challenge {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (q : ByteArray × Path) (hq : q ∈ s'.pending) :
    q ∈ s.pending ∨ e = .recvChallenge q.2 q.1 := by
  cases h with
  | start => exact Or.inl hq
  | @challenge p d =>
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl hq
    · simp only [List.mem_singleton] at hq; subst hq; exact Or.inr rfl
  | responseIgnore => exact Or.inl hq
  | responseSent => exact Or.inl (mem_of_mem_removeFirst _ _ _ hq)
  | responseMatch => exact Or.inl (by simpa using hq)
  | timeoutFail => exact Or.inl (by simpa using hq)

theorem occurs_removeFirst : ∀ (l : List (ByteArray × Path)) (q : ByteArray × Path),
    0 < occurs l q → occurs (removeFirst l q) q + 1 = occurs l q := by
  intro l
  induction l with
  | nil => intro q h; simp [occurs] at h
  | cons x xs ih =>
    intro q h
    by_cases hx : x = q
    · subst hx
      simp only [removeFirst, occurs, reduceIte]
      omega
    · simp only [occurs, hx, reduceIte] at h ⊢
      simp only [removeFirst, hx, reduceIte, occurs]
      have := ih q (by omega)
      omega

theorem not_mem_of_occurs_zero : ∀ (l : List (ByteArray × Path)) (q : ByteArray × Path),
    occurs l q = 0 → q ∉ l := by
  intro l
  induction l with
  | nil => intro q _; simp
  | cons x xs ih =>
    intro q h
    simp only [occurs] at h
    by_cases hx : x = q
    · simp [hx] at h
    · intro hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hx rfl
      · simp only [hx, reduceIte] at h
        exact ih q (by omega) hmem

/-- §8.2.2, line 3205: "An endpoint MUST NOT send more than one PATH_RESPONSE
    frame in response to one PATH_CHALLENGE frame."  Sending the response
    consumes the queued obligation, so it may not be sent again unless the peer
    sends another PATH_CHALLENGE with the same data. -/
theorem response_once {s s' : State} {p : Path} {d : ByteArray} {fx : List Effect}
    (h : Step s (.responseSent p d) (.ok s' fx)) (h1 : occurs s.pending (d, p) = 1) :
    ¬ MaySendResponseOn s' d p := by
  cases h with
  | responseSent =>
    have h2 := occurs_removeFirst s.pending (d, p) (by omega)
    exact not_mem_of_occurs_zero (removeFirst s.pending (d, p)) (d, p) (by omega)

/-- §8.2.1, line 3171: "endpoints MUST NOT discard datagrams that appear to be
    too small when they contain PATH_CHALLENGE or PATH_RESPONSE."  Neither
    receive event has `drop` among its permitted outcomes, for any state — so
    no size test can make the model discard one. -/
theorem challenge_never_dropped (s : State) (p : Path) (d : ByteArray) :
    (Outcome.drop : Out) ∉ outcomes s (.recvChallenge p d) := by
  simp [outcomes]

theorem response_never_dropped (s : State) (p : Path) (d : ByteArray) :
    (Outcome.drop : Out) ∉ outcomes s (.recvResponse p d) := by
  simp only [outcomes]
  split <;> simp

/-- A received PATH_CHALLENGE is always answered, on the path it arrived on. -/
theorem challenge_answered (s : State) (p : Path) (d : ByteArray) :
    component.step s (.recvChallenge p d) =
      .ok { s with pending := s.pending ++ [(d, p)] } [.queueResponse p d] := rfl

/-! ## 9. Examples (scenarios from the text) -/

private def p1 : Path := ⟨1⟩
private def p2 : Path := ⟨2⟩
private def d1 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
private def d2 : ByteArray := ⟨#[8, 7, 6, 5, 4, 3, 2, 1]⟩
private def s0 : State := init
/-- After starting a validation of `p1` with `d1`, abandoning at t = 400. -/
private def s1 : State := { s0 with outstanding := [⟨d1, p1, 400⟩] }

-- §8.2.1, line 3131: starting validation sends a PATH_CHALLENGE on the path.
example : component.step s0 (.startValidation p1 d1 400) = .ok s1 [.sendChallenge p1 d1] := by decide
-- §8.2.1, line 3150: data already outstanding is not reused.
example : component.step s1 (.startValidation p2 d1 800) = .drop := by decide
-- … but fresh data on another path is fine (simultaneous probes, line 3123).
example : component.accepts s1 (.startValidation p2 d2 800)
    (.ok { s1 with outstanding := [⟨d2, p2, 800⟩, ⟨d1, p1, 400⟩] } [.sendChallenge p2 d2])
    = true := by decide

-- §8.2.2, line 3177: a PATH_CHALLENGE is echoed on the path it arrived on.
example : component.step s0 (.recvChallenge p2 d2) =
    .ok { s0 with pending := [(d2, p2)] } [.queueResponse p2 d2] := by decide
-- and only then may we send the PATH_RESPONSE …
example : component.maySend s0 (.pathResponse d2) = false := by decide
example : component.maySend { s0 with pending := [(d2, p2)] } (.pathResponse d2) = true := by decide
-- … once (line 3205).
example : component.maySend
    ((component.step { s0 with pending := [(d2, p2)] } (.responseSent p2 d2)).next s0)
    (.pathResponse d2) = false := by decide

-- §8.2.3, line 3214: a matching PATH_RESPONSE arriving on *another* path still
-- validates the path the PATH_CHALLENGE was sent on.
example : component.step s1 (.recvResponse p2 d1) =
    .ok { outstanding := [], pending := [], status := [(p1, .validated)] } [.pathValidated p1] := by
  decide
-- §19.18: an unmatched PATH_RESPONSE is ignored, or is a PROTOCOL_VIOLATION …
example : component.step s1 (.recvResponse p1 d2) = .ok s1 [] := by decide
example : component.accepts s1 (.recvResponse p1 d2) (.error .protocolViolation) = true := by decide
-- … and §8.2.1 line 3171: never discarded.
example : component.accepts s1 (.recvResponse p1 d2) .drop = false := by decide

-- §8.2.4, line 3234: the abandon timer fires and the path fails …
example : component.step s1 (.timeout p1 400) =
    .ok { outstanding := [], pending := [], status := [(p1, .failed)] } [.pathFailed p1] := by decide
-- … but not before the deadline.
example : component.step s1 (.timeout p1 399) = .drop := by decide

-- §8.2.1, line 3154 / §8.2.2, line 3197: expansion to 1200 bytes, unless the
-- anti-amplification limit forbids it.  A server that has received 300 bytes
-- from an unvalidated address may send 900 …
private def av300 : AddressValidation.State :=
  (AddressValidation.init .server ByteArray.empty).addRecv ⟨1⟩ 300
example : maySendDatagram av300 ⟨1⟩ [.pathChallenge d1] 900 = true := by decide
-- … and 900 is permitted unexpanded precisely because 1200 is over the limit …
example : AddressValidation.maySendDatagram av300 ⟨1⟩ 1200 = false := by decide
-- … while 1300 is over the anti-amplification limit outright.
example : maySendDatagram av300 ⟨1⟩ [.pathChallenge d1] 1300 = false := by decide
-- With budget to spare, a short PATH_CHALLENGE datagram is not allowed …
private def av600 : AddressValidation.State :=
  (AddressValidation.init .server ByteArray.empty).addRecv ⟨1⟩ 600
example : maySendDatagram av600 ⟨1⟩ [.pathChallenge d1] 900 = false := by decide
example : maySendDatagram av600 ⟨1⟩ [.pathResponse d1] 1200 = true := by decide
-- … though a datagram with neither frame is unconstrained by the expansion rule.
example : maySendDatagram av600 ⟨1⟩ [.ping] 900 = true := by decide

/-! ## 10. Coverage and notes

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §8.2 (3090) | path validation does not validate the return direction | `State.status` is per path and set only by our own challenges; NOTES 1 |
| §8.2 (3097) | path validation can be used at any time by either endpoint | `Step.start` has no precondition beyond freshness |
| §8.2 (3108) | an endpoint MAY include other frames with PATH_CHALLENGE/PATH_RESPONSE | `MaySend` is `True` for every other frame |
| §8.2 (3115) | an endpoint uses a new connection ID for probes from a new local address | out of scope: WP4 ConnIds / WP10 Migration (§9.5) |
| §8.2.1 (3131) | initiate validation by sending PATH_CHALLENGE with an unpredictable payload | `Step.start`, `Effect.sendChallenge` |
| §8.2.1 (3141) | an endpoint MAY send multiple PATH_CHALLENGE frames | several `Step.start`s on one path are permitted |
| §8.2.1 (3142) | SHOULD NOT send multiple PATH_CHALLENGE frames in a single packet | `RecommendedPacket` (advice, not `MaySend`) |
| §8.2.1 (3145) | SHOULD NOT probe more often than it would send an Initial | out of scope: pacing, RFC 9002; NOTES 5 |
| §8.2.1 (3150) | MUST use unpredictable data in every PATH_CHALLENGE | `Step.start`'s freshness guard + `MaySend (.pathChallenge …)`; NOTES 2 |
| §8.2.1 (3154) | MUST expand PATH_CHALLENGE datagrams to ≥ 1200 bytes unless the anti-amplification limit forbids it | `MaySendDatagram` |
| §8.2.1 (3161) | MUST perform a second, expanded path validation when the first could not be expanded | not encoded; NOTES 3 |
| §8.2.1 (3171) | MUST NOT discard datagrams that look too small when they carry PATH_CHALLENGE/PATH_RESPONSE | `challenge_never_dropped`, `response_never_dropped` |
| §8.2.2 (3177) | MUST respond by echoing the PATH_CHALLENGE data in a PATH_RESPONSE | `Step.challenge`, `Effect.queueResponse`, `MaySend` |
| §8.2.2 (3179) | MUST NOT delay a packet containing PATH_RESPONSE except for congestion control | out of scope: no scheduling in this model; NOTES 5 |
| §8.2.2 (3183) | PATH_RESPONSE MUST be sent on the path the PATH_CHALLENGE was received on | the path in `Effect.queueResponse` / `State.pending`; `MaySendResponseOn` |
| §8.2.2 (3186) | this requirement MUST NOT be enforced by the initiator of path validation | `Step.responseMatch` ignores the path a response arrives on |
| §8.2.2 (3197) | MUST expand PATH_RESPONSE datagrams to ≥ 1200 bytes, MUST NOT past the anti-amplification limit | `MaySendDatagram` |
| §8.2.2 (3205) | MUST NOT send more than one PATH_RESPONSE per PATH_CHALLENGE | `Step.responseSent`, `response_once` |
| §8.2.3 (3212) | validation succeeds on a PATH_RESPONSE carrying the data of a previous PATH_CHALLENGE | `Step.responseMatch`, `validated_only_by_response` |
| §8.2.3 (3214) | a PATH_RESPONSE on any path validates the path the challenge was sent on | `Challenge.path`, not the event's path |
| §8.2.3 (3219) | after validation the endpoint can send more than 3× the data received | `AddressValidation.Step.pathValidates`, driven by `Effect.pathValidated` |
| §8.2.3 (3221) | MUST initiate another validation with an expanded datagram | not encoded; NOTES 3 |
| §8.2.3 (3225) | an acknowledgment of a PATH_CHALLENGE is not adequate validation | only `Step.responseMatch` validates; `validated_only_by_response` |
| §8.2.4 (3231) | validation fails only when the endpoint abandons the attempt | `Step.timeoutFail` is the only failing step |
| §8.2.4 (3234) | endpoints SHOULD abandon path validation based on a timer, 3×PTO RECOMMENDED | `Challenge.deadline`, supplied on `startValidation`; NOTES 4 |
| §8.2.4 (3253) | a PATH_RESPONSE with appropriate data is required for validation to succeed | `validated_only_by_response` |
| §8.2.4 (3257) | an abandoned path is unusable; the connection need not fail | `PathStatus.failed`, `Effect.pathFailed` |
| §8.2.4 (3262) | an endpoint with no valid path MAY signal NO_VIABLE_PATH | out of scope: connection-level, WP6 Termination; NOTES 6 |
| §8.2.4 (3267) | validation may be abandoned because a migration started | out of scope: WP10 Migration |
| §19.18 | an unmatched PATH_RESPONSE MAY be a PROTOCOL_VIOLATION | `Step.responseIgnore` / `Step.responseViolation` |

NOTES

1. **One direction only.**  §8.2 line 3090 is a statement about what path
   validation means, not a rule an implementation can violate; it shows up here
   as the shape of the state: `status` records only paths *we* challenged, and
   answering someone else's PATH_CHALLENGE never sets it.

2. **"Unpredictable data" is not checkable, freshness is.**  Entropy is
   abstract: the caller supplies the payload on `startValidation`.  What the
   model does enforce is the purpose the sentence gives for the requirement —
   "so that it can associate the peer's response with the corresponding
   PATH_CHALLENGE" — by refusing to start a validation with data that is already
   outstanding (`Step.startStale`), and by permitting a PATH_CHALLENGE frame to
   be sent only for data we have registered (`MaySend`).  An implementation that
   picks its 8 bytes from a counter is accepted; one that reuses live data is
   not.

3. **The second, expanded validation (lines 3161 and 3221) is not encoded.**
   Both sentences are obligations to start *another* path validation at some
   unspecified later time ("after a PATH_RESPONSE is successfully received or
   when enough bytes have been received on the path").  A liveness obligation
   with no deadline cannot be stated as a `Step` constraint, and inventing one
   would reject conforming implementations.  It needs the size of the datagram a
   challenge was sent in to be carried in `Challenge`, plus a temporal operator;
   both are deferred.  WP10 Migration is the natural owner, since it is where
   MTU on a new path matters.

4. **The abandon timer is a parameter, not a computation.**  §8.2.4 RECOMMENDS
   three times the larger of the current PTO and the new path's PTO; PTO belongs
   to RFC 9002, which is out of scope throughout.  The deadline is therefore
   supplied on the `startValidation` event and only compared against the `now`
   of the `timeout` event.  `Step.timeoutFail` requires that some challenge on
   the path has actually reached its deadline, so a spurious timeout is not a
   permitted way to fail a path.

5. **Scheduling MUSTs are out of scope.**  Line 3179 ("MUST NOT delay
   transmission of a packet containing a PATH_RESPONSE") and line 3145 (probe no
   more often than an Initial) constrain *when* a packet leaves, which this
   model does not represent: `Component` relates an event to a next state, with
   no notion of a send queue or of elapsed time between events.  They are listed
   here so a reviewer can see they were read and deliberately dropped.

6. **NO_VIABLE_PATH is deliberately absent from `Step`.**  §8.2.4 line 3262
   makes it a MAY, and hedges it further ("only possible if the network path
   exists but does not support the required MTU").  Admitting it as an outcome
   of `timeout` would let the model accept a connection error after any failed
   probe, which is looser than the text.  Since the decision needs a view of
   every path and of the MTU, it belongs to WP6/WP10.

7. **Ambiguity: does a failed validation un-validate a path?**  §8.2.4 line 3231
   defines failure as abandoning "its attempt to validate the path", and §8.2.3
   line 3221 has an endpoint validate an already-validated path a second time
   for the MTU.  The reading encoded here: `State.markFailed` leaves a validated
   path validated, so a failed MTU probe marks nothing.  `validated_persists`
   depends on this reading.

8. **Ambiguity: which outstanding challenges does a success clear?**  Line 3212
   says validation succeeds; it does not say what happens to the other
   PATH_CHALLENGEs sent on the same path to guard against loss (line 3141).  The
   reading encoded here: `Step.responseMatch` clears *all* outstanding challenges
   for that path, so a late second PATH_RESPONSE for the same path is then an
   unmatched one (ignored, or PROTOCOL_VIOLATION).  The alternative — keep them
   and let each be answered — would make the same later response validate an
   already validated path, which is harmless but leaves the timer of §8.2.4
   armed on a validated path.

9. **`pending` is a multiset.**  Receiving the same PATH_CHALLENGE data twice
   entitles the peer to two PATH_RESPONSEs — line 3207: "The peer is expected to
   send more PATH_CHALLENGE frames as necessary to evoke additional
   PATH_RESPONSE frames."  One entry per received challenge, one removed per
   response sent, is what makes line 3205 a counting property rather than a
   set-membership one.

10. **Composition.**  `MaySendDatagram` takes the `AddressValidation` state
    explicitly rather than duplicating the budget here, so WP12 can pass the
    anti-amplification state of the peer address of the path.  The two
    components are joined at two points: `Effect.pathValidated` should fire
    `AddressValidation.Event.pathValidated` for that address (§8.2.3, line
    3219), and the byte counters are updated by `AddressValidation`'s own
    datagram events.
-/

end Quic.Spec.PathValidation
