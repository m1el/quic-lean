import QuicModel.Spec.Core

/-
  TEMPLATE: a complete component, small enough to read in one sitting.
  Copy this file's structure for every work package.

  Subject: the stream-count limits of §4.6 as seen by one endpoint — receiving
  MAX_STREAMS (§19.11) and STREAMS_BLOCKED (§19.14), and what it may send.
  (WP9 StreamTable supersedes this; it is here to fix the conventions.)

  Order of a component file:
    1. State / Event / Effect          plain data, `deriving DecidableEq`
    2. Step                            the spec, one constructor per sentence
    3. outcomes                        executable: every permitted outcome
    4. outcomes_iff, outcomes_ne       the two agree; something is always permitted
    5. Inv, step_inv                   invariant
    6. MaySend / maySend / maySend_iff send side
    7. the `Component` value           bundles 1–6; gives step/accepts/track for free
    8. named theorems                  the safety properties of this component
    9. examples                        scenarios from the text
   10. coverage table and notes        as a comment at the end
-/
namespace Quic.Spec.Template

/-- §4.6: "this value cannot exceed 2^60". -/
def maxStreamsLimit : Nat := 2 ^ 60

/-! ## 1. State, events, effects -/

structure State where
  /-- Cumulative number of streams the peer lets us open, per direction. -/
  peerMaxBidi : Nat
  peerMaxUni : Nat
  /-- Cumulative number of streams we let the peer open. -/
  localMaxBidi : Nat
  localMaxUni : Nat
  deriving DecidableEq, Repr

def State.peerMax (s : State) : StreamDir → Nat
  | .bidi => s.peerMaxBidi
  | .uni => s.peerMaxUni

def State.setPeerMax (s : State) : StreamDir → Nat → State
  | .bidi, v => { s with peerMaxBidi := v }
  | .uni, v => { s with peerMaxUni := v }

inductive Event where
  | recvMaxStreams (dir : StreamDir) (v : Nat)
  | recvStreamsBlocked (dir : StreamDir) (v : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- Tell the application it may open more streams. -/
  | streamsAvailable (dir : StreamDir) (max : Nat)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ## 2. The specification

One constructor per normative sentence.  Where the text allows alternatives,
there is one constructor per alternative. -/

inductive Step : State → Event → Out → Prop
  /-- §19.11, line 7802: "This value cannot exceed 2^60 ... Receipt of a frame
      that permits opening of a stream larger than this limit MUST be treated
      as a FRAME_ENCODING_ERROR." -/
  | maxStreamsTooLarge {s dir v} (h : v > maxStreamsLimit) :
      Step s (.recvMaxStreams dir v) (.error .frameEncodingError)
  /-- §19.11, line 7809: "MAX_STREAMS frames that do not increase the stream
      limit MUST be ignored." -/
  | maxStreamsStale {s dir v} (h : v ≤ maxStreamsLimit) (hle : v ≤ s.peerMax dir) :
      Step s (.recvMaxStreams dir v) (.ok s [])
  /-- §4.6: a larger limit takes effect. -/
  | maxStreamsRaise {s dir v} (h : v ≤ maxStreamsLimit) (hgt : s.peerMax dir < v) :
      Step s (.recvMaxStreams dir v) (.ok (s.setPeerMax dir v) [.streamsAvailable dir v])
  /-- §19.14, line 7919: "Receipt of a frame that encodes a larger stream ID
      MUST be treated as a STREAM_LIMIT_ERROR or a FRAME_ENCODING_ERROR."
      First alternative. -/
  | blockedTooLarge₁ {s dir v} (h : v > maxStreamsLimit) :
      Step s (.recvStreamsBlocked dir v) (.error .streamLimitError)
  /-- Same sentence, second alternative. -/
  | blockedTooLarge₂ {s dir v} (h : v > maxStreamsLimit) :
      Step s (.recvStreamsBlocked dir v) (.error .frameEncodingError)
  /-- §19.14: otherwise STREAMS_BLOCKED is informational. -/
  | blockedOk {s dir v} (h : v ≤ maxStreamsLimit) :
      Step s (.recvStreamsBlocked dir v) (.ok s [])

/-! ## 3. Executable form

Same case analysis, as a function returning every permitted outcome,
preferred first.  Keep it a flat `match`/`if`: `outcomes_iff` is then a
case split followed by `simp`. -/

def outcomes (s : State) : Event → List Out
  | .recvMaxStreams dir v =>
    if v > maxStreamsLimit then [.error .frameEncodingError]
    else if v ≤ s.peerMax dir then [.ok s []]
    else [.ok (s.setPeerMax dir v) [.streamsAvailable dir v]]
  | .recvStreamsBlocked _ v =>
    if v > maxStreamsLimit then [.error .streamLimitError, .error .frameEncodingError]
    else [.ok s []]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvMaxStreams dir v =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .maxStreamsTooLarge ‹_›
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .maxStreamsStale (by omega) ‹_›
        · simp only [List.mem_singleton] at h; subst h
          exact .maxStreamsRaise (by omega) (by omega)
    | recvStreamsBlocked dir v =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .blockedTooLarge₁ ‹_›
        · exact .blockedTooLarge₂ ‹_›
      · simp only [List.mem_singleton] at h; subst h; exact .blockedOk (by omega)
  · intro h
    cases h with
    | maxStreamsTooLarge h => simp [outcomes, h]
    | maxStreamsStale h hle =>
      have : ¬ _ > maxStreamsLimit := Nat.not_lt.mpr h
      simp [outcomes, this, hle]
    | maxStreamsRaise h hgt =>
      have h1 : ¬ _ > maxStreamsLimit := Nat.not_lt.mpr h
      have h2 : ¬ _ ≤ s.peerMax _ := Nat.not_le.mpr hgt
      simp [outcomes, h1, h2]
    | blockedTooLarge₁ h => simp [outcomes, h]
    | blockedTooLarge₂ h => simp [outcomes, h]
    | blockedOk h =>
      have : ¬ _ > maxStreamsLimit := Nat.not_lt.mpr h
      simp [outcomes, this]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- Limits never exceed 2^60. -/
def Inv (s : State) : Prop :=
  s.peerMaxBidi ≤ maxStreamsLimit ∧ s.peerMaxUni ≤ maxStreamsLimit ∧
  s.localMaxBidi ≤ maxStreamsLimit ∧ s.localMaxUni ≤ maxStreamsLimit

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | maxStreamsStale => exact hi
  | blockedOk => exact hi
  | @maxStreamsRaise dir v h _ =>
    obtain ⟨h1, h2, h3, h4⟩ := hi
    cases dir
    · exact ⟨h, h2, h3, h4⟩
    · exact ⟨h1, h, h3, h4⟩

/-! ## 6. Send side

`True` for every frame this component does not govern. -/

def MaySend (s : State) : Frame → Prop
  -- §4.6 / §19.11: never advertise more than 2^60, and never reduce the
  -- limit already advertised.
  | .maxStreams dir v =>
    v ≤ maxStreamsLimit ∧ (match dir with | .bidi => s.localMaxBidi | .uni => s.localMaxUni) ≤ v
  -- §19.14: the frame reports the limit we are actually blocked at.
  | .streamsBlocked dir v => v = s.peerMax dir
  | _ => True

def maySend (s : State) : Frame → Bool
  | .maxStreams dir v =>
    decide (v ≤ maxStreamsLimit) &&
      decide ((match dir with | .bidi => s.localMaxBidi | .uni => s.localMaxUni) ≤ v)
  | .streamsBlocked dir v => decide (v = s.peerMax dir)
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend]

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

/-- The peer's limit, as we track it, never goes down. -/
theorem peerMax_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (dir : StreamDir) : s.peerMax dir ≤ s'.peerMax dir := by
  cases h with
  | maxStreamsStale => exact Nat.le_refl _
  | blockedOk => exact Nat.le_refl _
  | @maxStreamsRaise d v _ hgt =>
    cases d <;> cases dir <;> simp only [State.peerMax, State.setPeerMax] at hgt ⊢ <;> omega

/-- The application is told about new streams exactly when the limit rises. -/
theorem effect_iff_raise {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : fx ≠ [] ↔ s' ≠ s := by
  cases h with
  | maxStreamsStale => simp
  | blockedOk => simp
  | @maxStreamsRaise d v _ hgt =>
    refine ⟨fun _ heq => ?_, fun _ => by simp⟩
    cases d
    · have := congrArg State.peerMaxBidi heq
      simp only [State.peerMax, State.setPeerMax] at hgt this
      omega
    · have := congrArg State.peerMaxUni heq
      simp only [State.peerMax, State.setPeerMax] at hgt this
      omega

/-! ## 9. Examples (scenarios from the text) -/

private def s0 : State := { peerMaxBidi := 3, peerMaxUni := 3, localMaxBidi := 10, localMaxUni := 10 }

-- §19.11: "a server that receives a unidirectional stream limit of 3 ..." then a raise to 5
example : component.step s0 (.recvMaxStreams .uni 5) =
    .ok { s0 with peerMaxUni := 5 } [.streamsAvailable .uni 5] := by decide
-- a reordered, older MAX_STREAMS is ignored
example : component.step s0 (.recvMaxStreams .uni 2) = .ok s0 [] := by decide
-- either error code is acceptable for an oversized STREAMS_BLOCKED …
example : component.accepts s0 (.recvStreamsBlocked .bidi (2 ^ 60 + 1)) (.error .streamLimitError) = true := by decide
example : component.accepts s0 (.recvStreamsBlocked .bidi (2 ^ 60 + 1)) (.error .frameEncodingError) = true := by decide
-- … but nothing else is
example : component.accepts s0 (.recvStreamsBlocked .bidi (2 ^ 60 + 1)) (.ok s0 []) = false := by decide
-- following an implementation we cannot see inside
example : component.track s0 (.recvMaxStreams .bidi 7) (.ok [.streamsAvailable .bidi 7]) =
    some { s0 with peerMaxBidi := 7 } := by decide
example : component.maySend s0 (.maxStreams .bidi 9) = false := by decide  -- would lower our limit

/-! ## 10. Coverage and notes

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §19.11 (7802) | MAX_STREAMS > 2^60 MUST be FRAME_ENCODING_ERROR | `Step.maxStreamsTooLarge` |
| §19.11 (7809) | non-increasing MAX_STREAMS MUST be ignored | `Step.maxStreamsStale` |
| §19.14 (7919) | STREAMS_BLOCKED > 2^60: STREAM_LIMIT_ERROR or FRAME_ENCODING_ERROR | `Step.blockedTooLarge₁/₂` |
| §4.6 (1527–) | MUST NOT open more streams than the peer's limit | out of scope here: needs the stream table (WP9) |

NOTES
- "MUST be ignored" is encoded as `.ok s []`, not `.drop`: the frame is
  processed and has no effect, the packet is still acknowledged.  `.drop` is
  reserved for discarding a whole packet or datagram.
- §4.6 says an endpoint "MUST NOT" lower a limit it advertised only implicitly
  (limits are cumulative); `MaySend` makes that explicit.
-/

end Quic.Spec.Template
