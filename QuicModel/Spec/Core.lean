import QuicModel.Frame

/-
  Shared vocabulary for the behavioural part of the spec, and the one shape
  every component takes (`Component`).  Read `Spec/Template.lean` next: it is a
  complete small component written to this shape.
-/
namespace Quic.Spec

/-! ### Vocabulary -/

/-- §20.1 transport error codes. -/
inductive TransportError where
  | noError | internalError | connectionRefused | flowControlError
  | streamLimitError | streamStateError | finalSizeError | frameEncodingError
  | transportParameterError | connectionIdLimitError | protocolViolation
  | invalidToken | applicationError | cryptoBufferExceeded | keyUpdateError
  | aeadLimitReached | noViablePath
  | cryptoError (alert : UInt8)          -- 0x0100 + TLS alert
  deriving DecidableEq, Repr

def TransportError.code : TransportError → Nat
  | .noError => 0x0 | .internalError => 0x1 | .connectionRefused => 0x2
  | .flowControlError => 0x3 | .streamLimitError => 0x4 | .streamStateError => 0x5
  | .finalSizeError => 0x6 | .frameEncodingError => 0x7
  | .transportParameterError => 0x8 | .connectionIdLimitError => 0x9
  | .protocolViolation => 0xa | .invalidToken => 0xb | .applicationError => 0xc
  | .cryptoBufferExceeded => 0xd | .keyUpdateError => 0xe | .aeadLimitReached => 0xf
  | .noViablePath => 0x10 | .cryptoError alert => 0x100 + alert.toNat

inductive Role where | client | server
  deriving DecidableEq, Repr

def Role.peer : Role → Role
  | .client => .server
  | .server => .client

/-- Time in microseconds.  Always supplied on events; the model never reads a clock. -/
abbrev Time := Nat

/-- §2.1: a stream ID is a 62-bit integer; its two low bits give the type.
    Frames carry stream IDs as bare `Nat`s; wrap them with `⟨id⟩`. -/
structure StreamId where
  val : Nat
  deriving DecidableEq, Repr

namespace StreamId
def initiator (id : StreamId) : Role := if id.val % 2 = 0 then .client else .server
def dir (id : StreamId) : StreamDir := if id.val / 2 % 2 = 0 then .bidi else .uni
/-- Ordinal of the stream among streams of its type (0, 1, 2, …). -/
def index (id : StreamId) : Nat := id.val / 4
def make (initiator : Role) (dir : StreamDir) (index : Nat) : StreamId :=
  ⟨4 * index + (match dir with | .bidi => 0 | .uni => 2) +
    (match initiator with | .client => 0 | .server => 1)⟩

theorem initiator_make (r : Role) (d : StreamDir) (n : Nat) : (make r d n).initiator = r := by
  unfold make initiator
  cases r <;> cases d
  · exact ite_eq_left (by dsimp only; omega)
  · exact ite_eq_left (by dsimp only; omega)
  · exact ite_eq_right (by dsimp only; omega)
  · exact ite_eq_right (by dsimp only; omega)

theorem dir_make (r : Role) (d : StreamDir) (n : Nat) : (make r d n).dir = d := by
  unfold make dir
  cases r <;> cases d
  · exact ite_eq_left (by dsimp only; omega)
  · exact ite_eq_right (by dsimp only; omega)
  · exact ite_eq_left (by dsimp only; omega)
  · exact ite_eq_right (by dsimp only; omega)

theorem index_make (r : Role) (d : StreamDir) (n : Nat) : (make r d n).index = n := by
  unfold make index
  cases r <;> cases d <;> dsimp only <;> omega
end StreamId

/-- §12.3 packet number spaces. -/
inductive PnSpace where | initial | handshake | appData
  deriving DecidableEq, Repr

inductive PacketType where
  | initial | zeroRtt | handshake | oneRtt | retry | versionNegotiation
  deriving DecidableEq, Repr

/-- The space a packet's number lives in; Retry and VN have no packet number. -/
def PacketType.space : PacketType → Option PnSpace
  | .initial => some .initial
  | .handshake => some .handshake
  | .zeroRtt | .oneRtt => some .appData
  | .retry | .versionNegotiation => none

/-! ### Finite maps

Association lists: executable, `DecidableEq`, and easy to reason about.
`set` keeps one entry per key, so states built only through `set`/`erase`
compare equal when they should. -/

abbrev Map (κ ν : Type) := List (κ × ν)

namespace Map
variable {κ ν : Type} [DecidableEq κ]

def get? (m : Map κ ν) (k : κ) : Option ν :=
  match m with
  | [] => none
  | (k', v) :: m => if k' = k then some v else get? m k

def set (m : Map κ ν) (k : κ) (v : ν) : Map κ ν :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: m => if k' = k then (k, v) :: m else (k', v') :: set m k v

def erase (m : Map κ ν) (k : κ) : Map κ ν := m.filter (·.1 ≠ k)

def keys (m : Map κ ν) : List κ := m.map (·.1)

@[simp] theorem get?_set_self (m : Map κ ν) (k : κ) (v : ν) : (m.set k v).get? k = some v := by
  induction m with
  | nil => simp [set, get?]
  | cons p m ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k' = k <;> simp [set, get?, h, ih]

theorem get?_set_of_ne (m : Map κ ν) {k k' : κ} (v : ν) (h : k' ≠ k) :
    (m.set k v).get? k' = m.get? k' := by
  induction m with
  | nil => simp [set, get?, Ne.symm h]
  | cons p m ih =>
    obtain ⟨k₀, v₀⟩ := p
    by_cases h0 : k₀ = k
    · subst h0; simp [set, get?, Ne.symm h]
    · by_cases h1 : k₀ = k'
      · subst h1; simp [set, get?, h0]
      · simp [set, get?, h0, h1, ih]
end Map

/-! ### Outcomes -/

/-- What handling one event results in. -/
inductive Outcome (σ ε : Type) where
  /-- New state and the effects produced, in order. -/
  | ok (s : σ) (effects : List ε)
  /-- Connection error (§11.1): the connection closes with this code. -/
  | error (code : TransportError)
  /-- The input is discarded or ignored and nothing changes. -/
  | drop
  deriving DecidableEq, Repr

/-- The part of an outcome visible from outside an implementation. -/
inductive Obs (ε : Type) where
  | ok (effects : List ε)
  | error (code : TransportError)
  | drop
  deriving DecidableEq, Repr

def Outcome.obs : Outcome σ ε → Obs ε
  | .ok _ fx => .ok fx
  | .error c => .error c
  | .drop => .drop

/-- State after the outcome; errors and drops leave the component where it was
    (what a connection error does to the *connection* is `Termination`'s job). -/
def Outcome.next (s : σ) : Outcome σ ε → σ
  | .ok s' _ => s'
  | _ => s

/-! ### The shape of a component -/

/-- One part of the transport, specified twice and proved to agree.

* `Step` is the specification: a relation containing every outcome the text
  permits, one constructor per rule, each citing its sentence.
* `outcomes` is the executable form: all permitted outcomes as a list, the
  preferred one first.  Receive-side looseness in QUIC is always a finite
  choice (which of two error codes, ignore or not), so a list suffices.
* `MaySend` constrains what may be sent; it must be `True` for frames the
  component does not govern, so that components compose by conjunction. -/
structure Component where
  State : Type
  Event : Type
  Effect : Type
  [decState : DecidableEq State]
  [decEffect : DecidableEq Effect]
  Step : State → Event → Outcome State Effect → Prop
  outcomes : State → Event → List (Outcome State Effect)
  outcomes_iff : ∀ s e o, o ∈ outcomes s e ↔ Step s e o
  /-- The spec always permits something. -/
  outcomes_ne : ∀ s e, outcomes s e ≠ []
  Inv : State → Prop
  step_inv : ∀ s e s' fx, Inv s → Step s e (.ok s' fx) → Inv s'
  MaySend : State → Frame → Prop
  maySend : State → Frame → Bool
  maySend_iff : ∀ s f, maySend s f = true ↔ MaySend s f

namespace Component
variable (C : Component)

instance : DecidableEq C.State := C.decState
instance : DecidableEq C.Effect := C.decEffect

/-- The reference implementation: the preferred permitted outcome. -/
def step (s : C.State) (e : C.Event) : Outcome C.State C.Effect :=
  (C.outcomes s e).head (C.outcomes_ne s e)

/-- Is this outcome permitted? -/
def accepts (s : C.State) (e : C.Event) (o : Outcome C.State C.Effect) : Bool :=
  decide (o ∈ C.outcomes s e)

/-- Follow an implementation whose state we cannot see: given what it visibly
    did, the state the spec says it is now in, or `none` if nothing the spec
    permits looks like that. -/
def track (s : C.State) (e : C.Event) (ob : Obs C.Effect) : Option C.State :=
  ((C.outcomes s e).find? (·.obs = ob)).map (·.next s)

theorem step_sound (s : C.State) (e : C.Event) : C.Step s e (C.step s e) :=
  (C.outcomes_iff s e _).mp (List.head_mem _)

theorem accepts_iff (s : C.State) (e : C.Event) (o : Outcome C.State C.Effect) :
    C.accepts s e o = true ↔ C.Step s e o := by
  simp [accepts, C.outcomes_iff]

theorem track_sound {s : C.State} {e : C.Event} {ob : Obs C.Effect} {s' : C.State}
    (h : C.track s e ob = some s') : ∃ o, C.Step s e o ∧ o.obs = ob ∧ o.next s = s' := by
  simp only [track, Option.map_eq_some_iff] at h
  obtain ⟨o, ho, rfl⟩ := h
  refine ⟨o, (C.outcomes_iff s e o).mp (List.mem_of_find?_eq_some ho), ?_, rfl⟩
  simpa using List.find?_some ho

/-- If the spec permits something that looks like `ob`, tracking succeeds. -/
theorem track_complete {s : C.State} {e : C.Event} {o : Outcome C.State C.Effect}
    (h : C.Step s e o) : (C.track s e o.obs).isSome := by
  have hm := (C.outcomes_iff s e o).mpr h
  simp only [track, Option.isSome_map]
  rw [List.find?_isSome]
  exact ⟨o, hm, by simp⟩

/-- States reachable from `s₀` by permitted steps. -/
inductive Reachable (s₀ : C.State) : C.State → Prop
  | refl : Reachable s₀ s₀
  | step {s s' e fx} : Reachable s₀ s → C.Step s e (.ok s' fx) → Reachable s₀ s'

/-- Induction over reachable states, stated with a plain `motive` so that it
    applies from a concrete component, where `induction` on `Reachable` trips
    over `component.State` vs. the concrete state type. -/
theorem reachable_induction {s₀ : C.State} {motive : C.State → Prop} (base : motive s₀)
    (ind : ∀ {s s' e fx}, C.Reachable s₀ s → C.Step s e (.ok s' fx) → motive s → motive s')
    {s : C.State} (h : C.Reachable s₀ s) : motive s := by
  induction h with
  | refl => exact base
  | step hr hs ih => exact ind hr hs ih

theorem inv_of_reachable {s₀ s : C.State} (h0 : C.Inv s₀) (h : C.Reachable s₀ s) : C.Inv s := by
  induction h with
  | refl => exact h0
  | step _ hs ih => exact C.step_inv _ _ _ _ ih hs

end Component

end Quic.Spec
