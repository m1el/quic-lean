import QuicModel.Spec.ConnIds.Common

/-!
  §5.1.2 "Consuming and Retiring Connection IDs", the receive side of §19.15
  NEW_CONNECTION_ID and the send side of §19.16 RETIRE_CONNECTION_ID:
  one endpoint's view of the connection IDs *its peer issued to it*, which it
  uses as Destination Connection IDs.

  File order is `Spec/Template.lean`'s ten parts.
-/
namespace Quic.Spec.ConnIds.Remote

/-! ## 1. State, events, effects -/

/-- The connection IDs the peer has given us.

`entries` holds every connection ID the peer ever told us about, including the
initial one (sequence number 0) and the `preferred_address` one (sequence
number 1); those two are supplied in the initial state, since learning them is
part of the handshake (WP11).  Nothing is ever removed from `entries`:
retirement is recorded in `retired`, which keeps §19.15's "unless it has
already done so for that sequence number" decidable and makes "a retired
sequence number never becomes active again" a property of the state rather than
of the history. -/
structure State where
  /-- Everything the peer has issued to us, at most one entry per sequence number. -/
  entries : List Entry
  /-- Sequence numbers we have retired (a RETIRE_CONNECTION_ID has been queued). -/
  retired : List Nat
  /-- §19.15, line 8000: "the largest received Retire Prior To value". -/
  retirePriorTo : Nat
  /-- Our own `active_connection_id_limit`, i.e. the value we told the peer. -/
  limit : Nat
  /-- True when the peer issued us a zero-length connection ID, i.e. we send
      packets with a zero-length Destination Connection ID (§5.1). -/
  peerZeroLen : Bool
  deriving DecidableEq, Repr

namespace State

/-- §5.1.1, line 1712: "Connection IDs that are issued and not retired are
    considered active". -/
def active (s : State) : List Entry :=
  s.entries.filter (fun e => decide (e.seq ∉ s.retired))

def activeCount (s : State) : Nat := s.active.length

/-- Have we already retired this sequence number? -/
def isRetired (s : State) (n : Nat) : Bool := decide (n ∈ s.retired)

end State

inductive Event where
  /-- A NEW_CONNECTION_ID frame arrived (§19.15). -/
  | recvNewCid (seq rpt : Nat) (cid : Cid) (token : ResetToken)
  /-- We decide to stop using a connection ID (§5.1.2, line 1779: "When the
      endpoint wishes to remove a connection ID from use"); driven by the
      application or by migration (WP10). -/
  | retireCid (seq : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- §19.15, line 8011: "the peer MUST stop using the corresponding connection
      IDs" — this one must no longer be used as a Destination Connection ID. -/
  | stopUsing (seq : Nat) (cid : Cid)
  /-- Queue a RETIRE_CONNECTION_ID frame for this sequence number (§19.16). -/
  | queueRetire (seq : Nat)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ## 1b. Processing a NEW_CONNECTION_ID

Everything a well-formed NEW_CONNECTION_ID does to the state, as one total
function, so that `Step`, `outcomes` and the theorems all refer to the same
term. -/

/-- The entry list after adding the received connection ID.  A sequence number
    we have already seen is *not* re-added: §19.15, line 7979, "Receipt of the
    same frame multiple times MUST NOT be treated as a connection error". -/
def entriesAfter (s : State) (seq : Nat) (cid : Cid) (token : ResetToken) : List Entry :=
  if (entryOf? s.entries seq).isSome then s.entries else s.entries ++ [⟨seq, cid, token⟩]

/-- The entries this frame retires: those below the new Retire Prior To that we
    have not retired already.  Computed over the *post*-insertion entry list, so
    a connection ID whose own sequence number is below Retire Prior To is
    retired at once (§19.15, line 8013). -/
def staleOf (s : State) (entries : List Entry) (newRpt : Nat) : List Entry :=
  entries.filter (fun e => decide (e.seq < newRpt ∧ e.seq ∉ s.retired))

/-- The state and effects after processing a NEW_CONNECTION_ID. -/
def applyNcid (s : State) (seq rpt : Nat) (cid : Cid) (token : ResetToken) :
    State × List Effect :=
  ({ s with entries := entriesAfter s seq cid token,
            retired := s.retired ++
              seqs (staleOf s (entriesAfter s seq cid token) (Nat.max s.retirePriorTo rpt)),
            retirePriorTo := Nat.max s.retirePriorTo rpt },
   (staleOf s (entriesAfter s seq cid token) (Nat.max s.retirePriorTo rpt)).flatMap
     (fun e => [Effect.stopUsing e.seq e.cid, Effect.queueRetire e.seq]))

/-- §19.15, line 7985: "a NEW_CONNECTION_ID frame that repeats a previously
    issued connection ID with a different Stateless Reset Token or a different
    sequence number, or if a sequence number is used for different connection
    IDs". -/
def conflicts (s : State) (seq : Nat) (cid : Cid) (token : ResetToken) : Bool :=
  (match entryOf? s.entries seq with
   | some e => decide (e.cid ≠ cid ∨ e.token ≠ token)
   | none => false)
  || s.entries.any (fun e => decide (e.cid = cid ∧ (e.seq ≠ seq ∨ e.token ≠ token)))

/-- The outcome of a NEW_CONNECTION_ID that is going to be processed: either it
    fits under our `active_connection_id_limit` or the connection dies.
    §5.1.1, line 1743: "After processing a NEW_CONNECTION_ID frame and adding
    and retiring active connection IDs, if the number of active connection IDs
    exceeds the value advertised in its active_connection_id_limit transport
    parameter, an endpoint MUST close the connection with an error of type
    CONNECTION_ID_LIMIT_ERROR." -/
def ncidResult (s : State) (seq rpt : Nat) (cid : Cid) (token : ResetToken) : List Out :=
  if (applyNcid s seq rpt cid token).1.activeCount > s.limit then
    [.error .connectionIdLimitError]
  else
    [.ok (applyNcid s seq rpt cid token).1 (applyNcid s seq rpt cid token).2]

/-- Our own decision to retire a connection ID we hold. -/
def applyRetire (s : State) (e : Entry) : State × List Effect :=
  ({ s with retired := s.retired ++ [e.seq] }, [.stopUsing e.seq e.cid, .queueRetire e.seq])

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §19.15, line 7974: "An endpoint that is sending packets with a zero-length
      Destination Connection ID MUST treat receipt of a NEW_CONNECTION_ID frame
      as a connection error of type PROTOCOL_VIOLATION." -/
  | ncidZeroLen {s seq rpt cid token} (hz : s.peerZeroLen = true) :
      Step s (.recvNewCid seq rpt cid token) (.error .protocolViolation)
  /-- §19.15, line 7959: "Values less than 1 and greater than 20 are invalid and
      MUST be treated as a connection error of type FRAME_ENCODING_ERROR." -/
  | ncidBadLen {s seq rpt cid token} (hz : s.peerZeroLen = false)
      (h : cidLenOk cid = false) :
      Step s (.recvNewCid seq rpt cid token) (.error .frameEncodingError)
  /-- §19.15, line 7993: "The Retire Prior To field MUST be less than or equal
      to the Sequence Number field.  Receiving a value greater than the Sequence
      Number MUST be treated as a connection error of type
      FRAME_ENCODING_ERROR." -/
  | ncidRptTooLarge {s seq rpt cid token} (hz : s.peerZeroLen = false)
      (hl : cidLenOk cid = true) (h : rpt > seq) :
      Step s (.recvNewCid seq rpt cid token) (.error .frameEncodingError)
  /-- §19.15, line 7985: "the endpoint MAY treat that receipt as a connection
      error of type PROTOCOL_VIOLATION".  First alternative of the MAY. -/
  | ncidConflict {s seq rpt cid token} (hz : s.peerZeroLen = false)
      (hl : cidLenOk cid = true) (hr : ¬ rpt > seq)
      (h : conflicts s seq cid token = true) :
      Step s (.recvNewCid seq rpt cid token) (.error .protocolViolation)
  /-- §5.1.1, line 1743: too many active connection IDs after processing.
      Reached whether or not the frame conflicts — taking the second alternative
      of the MAY above means processing the frame as usual. -/
  | ncidLimit {s seq rpt cid token} (hz : s.peerZeroLen = false)
      (hl : cidLenOk cid = true) (hr : ¬ rpt > seq)
      (h : (applyNcid s seq rpt cid token).1.activeCount > s.limit) :
      Step s (.recvNewCid seq rpt cid token) (.error .connectionIdLimitError)
  /-- The ordinary case: §19.15, line 7998 ("A receiver MUST ignore any Retire
      Prior To fields that do not increase the largest received Retire Prior To
      value" — hence `Nat.max`), line 8011 ("the peer MUST stop using the
      corresponding connection IDs and retire them with RETIRE_CONNECTION_ID
      frames before adding the newly provided connection ID"), line 8013 (a
      sequence number below a previously received Retire Prior To "MUST send a
      corresponding RETIRE_CONNECTION_ID frame ... unless it has already done so
      for that sequence number") and line 7979 (a repeat is not an error). -/
  | ncidOk {s seq rpt cid token} (hz : s.peerZeroLen = false)
      (hl : cidLenOk cid = true) (hr : ¬ rpt > seq)
      (h : ¬ (applyNcid s seq rpt cid token).1.activeCount > s.limit) :
      Step s (.recvNewCid seq rpt cid token)
        (.ok (applyNcid s seq rpt cid token).1 (applyNcid s seq rpt cid token).2)
  /-- §5.1.2, line 1779: "When the endpoint wishes to remove a connection ID
      from use, it sends a RETIRE_CONNECTION_ID frame to its peer." -/
  | retireOk {s n e} (he : entryOf? s.entries n = some e) (hr : s.isRetired n = false) :
      Step s (.retireCid n) (.ok (applyRetire s e).1 (applyRetire s e).2)
  /-- Retiring something we do not hold, or hold already retired, does nothing:
      this is a local request, not a received frame. -/
  | retireNop {s n} (h : entryOf? s.entries n = none ∨ s.isRetired n = true) :
      Step s (.retireCid n) .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvNewCid seq rpt cid token =>
    if s.peerZeroLen then [.error .protocolViolation]
    else if cidLenOk cid = false then [.error .frameEncodingError]
    else if rpt > seq then [.error .frameEncodingError]
    else if conflicts s seq cid token then
      .error .protocolViolation :: ncidResult s seq rpt cid token
    else ncidResult s seq rpt cid token
  | .retireCid n =>
    match entryOf? s.entries n with
    | some e => if s.isRetired n then [.drop] else [.ok (applyRetire s e).1 (applyRetire s e).2]
    | none => [.drop]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvNewCid seq rpt cid token =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h
        exact .ncidZeroLen (by simp_all)
      · have hz : s.peerZeroLen = false := by simp_all
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .ncidBadLen hz ‹_›
        · have hl : cidLenOk cid = true := by simp_all
          split at h
          · simp only [List.mem_singleton] at h; subst h; exact .ncidRptTooLarge hz hl ‹_›
          · have hr : ¬ rpt > seq := ‹_›
            have key : ∀ o', o' ∈ ncidResult s seq rpt cid token →
                Step s (.recvNewCid seq rpt cid token) o' := by
              intro o' ho'
              simp only [ncidResult] at ho'
              split at ho'
              · simp only [List.mem_singleton] at ho'; subst ho'
                exact .ncidLimit hz hl hr ‹_›
              · simp only [List.mem_singleton] at ho'; subst ho'
                exact .ncidOk hz hl hr ‹_›
            split at h
            · simp only [List.mem_cons] at h
              rcases h with h | h
              · subst h; exact .ncidConflict hz hl hr (by simp_all)
              · exact key _ h
            · exact key _ h
    | retireCid n =>
      simp only [outcomes] at h
      split at h
      · rename_i e he
        split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .retireNop (.inr (by simp_all))
        · simp only [List.mem_singleton] at h; subst h
          exact .retireOk he (by simp_all)
      · rename_i he
        simp only [List.mem_singleton] at h; subst h
        exact .retireNop (.inl he)
  · intro h
    cases h with
    | ncidZeroLen hz => simp [outcomes, hz]
    | ncidBadLen hz hb => simp [outcomes, hz, hb]
    | ncidRptTooLarge hz hl hg => simp [outcomes, hz, hl, hg]
    | @ncidConflict seq rpt cid token hz hl hr hc => simp [outcomes, hz, hl, hr, hc]
    | @ncidLimit seq rpt cid token hz hl hr hg =>
      by_cases hc : conflicts s seq cid token = true <;>
        simp [outcomes, hz, hl, hr, hc, ncidResult, hg]
    | @ncidOk seq rpt cid token hz hl hr hg =>
      by_cases hc : conflicts s seq cid token = true <;>
        simp [outcomes, hz, hl, hr, hc, ncidResult, hg]
    | @retireOk n e he hr => simp [outcomes, he, hr]
    | @retireNop n hn =>
      rcases hn with he | hr
      · simp [outcomes, he]
      · cases he : entryOf? s.entries n with
        | none => simp [outcomes, he]
        | some e => simp [outcomes, he, hr]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e with
  | recvNewCid seq rpt cid token =>
    simp only [outcomes, ncidResult]; repeat' split
    all_goals simp
  | retireCid n =>
    simp only [outcomes]; repeat' split
    all_goals simp

/-! ## 5. Invariant -/

/-- Sequence numbers are unique, and we never hold more active connection IDs
    than we told the peer we would (§5.1.1, line 1743). -/
def Inv (s : State) : Prop := (seqs s.entries).Nodup ∧ s.activeCount ≤ s.limit

theorem entriesAfter_nodup {s : State} (hn : (seqs s.entries).Nodup)
    (seq : Nat) (cid : Cid) (token : ResetToken) :
    (seqs (entriesAfter s seq cid token)).Nodup := by
  unfold entriesAfter
  split
  · exact hn
  · rename_i hno
    have hmem : seq ∉ seqs s.entries := fun hm => hno (entryOf?_isSome.mpr hm)
    simp only [seqs_append, seqs_singleton]
    exact nodup_append_singleton hn hmem

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hn, hc⟩ := hi
  cases h with
  | @ncidOk seq rpt cid token _ _ _ hlim =>
    refine ⟨entriesAfter_nodup hn seq cid token, ?_⟩
    have : (applyNcid s seq rpt cid token).1.limit = s.limit := rfl
    omega
  | @retireOk n en he hr =>
    refine ⟨hn, ?_⟩
    have hlim : (applyRetire s en).1.limit = s.limit := rfl
    rw [hlim]
    refine Nat.le_trans ?_ hc
    simp only [State.activeCount, State.active, applyRetire]
    refine length_filter_mono _ _ _ ?_
    intro x _ hx
    simp only [decide_eq_true_eq, List.mem_append, List.mem_singleton, not_or] at hx ⊢
    exact hx.1

/-! ## 6. Send side

This component owns RETIRE_CONNECTION_ID (§19.16); NEW_CONNECTION_ID belongs to
the other half, so it is unconstrained here. -/

/-- §19.16, line 8046: the sequence number must be one the peer sent us
    ("greater than any previously sent to the peer" as seen from the receiver);
    §5.1.2, line 1781: sending the frame "indicates that the connection ID will
    not be used again", so we do not retire the same one twice;
    §19.16, line 8055: "An endpoint cannot send this frame if it was provided
    with a zero-length connection ID by its peer." -/
def MaySend (s : State) : Frame → Prop
  | .retireConnectionId n =>
    s.peerZeroLen = false ∧ n ∈ seqs s.entries ∧ n ∉ s.retired
  | _ => True

def maySend (s : State) : Frame → Bool
  | .retireConnectionId n =>
    decide (s.peerZeroLen = false) && decide (n ∈ seqs s.entries) && decide (n ∉ s.retired)
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend, and_assoc]

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

/-- (a) Active connection IDs never exceed our `active_connection_id_limit`. -/
theorem active_le_limit {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    s.activeCount ≤ s.limit :=
  (component.inv_of_reachable h0 h).2

/-- The limit is fixed by the transport parameters: no step changes it, so
    `active_le_limit` really is about the number we advertised. -/
theorem limit_const {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s'.limit = s.limit := by
  cases h <;> rfl

/-- (b) A sequence number identifies at most one connection ID. -/
theorem seq_unique {s : State} (hi : Inv s) {e₁ e₂ : Entry}
    (h1 : e₁ ∈ s.entries) (h2 : e₂ ∈ s.entries) (hs : e₁.seq = e₂.seq) : e₁ = e₂ :=
  entry_eq_of_seq_eq hi.1 h1 h2 hs

theorem inv_nodup_reachable {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    (seqs s.entries).Nodup :=
  (component.inv_of_reachable h0 h).1

/-- (c) Retirement is permanent: `retired` only ever grows. -/
theorem retired_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : ∀ n ∈ s.retired, n ∈ s'.retired := by
  cases h with
  | ncidOk => intro n hn; exact List.mem_append_left _ hn
  | retireOk => intro n hn; exact List.mem_append_left _ hn

theorem retired_mono_reachable {s₀ s : State} (h : component.Reachable s₀ s) :
    ∀ n ∈ s₀.retired, n ∈ s.retired :=
  Component.Reachable.rec (motive := fun (t : State) _ => ∀ n ∈ s₀.retired, n ∈ t.retired)
    (fun _ hn => hn) (fun _ hs ih n hn => retired_mono hs n (ih n hn)) h

theorem not_active_of_retired {s : State} {n : Nat} (h : n ∈ s.retired) :
    ∀ e ∈ s.active, e.seq ≠ n := by
  intro e he heq
  simp only [State.active, List.mem_filter, decide_eq_true_eq] at he
  exact he.2 (heq ▸ h)

/-- (c), as a statement about runs: once retired, never active again. -/
theorem retired_never_active {s₀ s : State} (h : component.Reachable s₀ s)
    {n : Nat} (hn : n ∈ s₀.retired) : ∀ e ∈ s.active, e.seq ≠ n :=
  not_active_of_retired (retired_mono_reachable h n hn)

/-- (d) The largest Retire Prior To we have seen never decreases. -/
theorem rpt_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.retirePriorTo ≤ s'.retirePriorTo := by
  cases h with
  | ncidOk => exact Nat.le_max_left _ _
  | retireOk => exact Nat.le_refl _

theorem rpt_mono_reachable {s₀ s : State} (h : component.Reachable s₀ s) :
    s₀.retirePriorTo ≤ s.retirePriorTo :=
  Component.Reachable.rec (motive := fun (t : State) _ => s₀.retirePriorTo ≤ t.retirePriorTo)
    (Nat.le_refl _) (fun _ hs ih => Nat.le_trans ih (rpt_mono hs)) h

/-! ## 9. Examples (scenarios from the text) -/

section Examples

/-- A 128-bit stateless reset token, all bytes equal. -/
private def tok (b : UInt8) : ResetToken := List.replicate 16 b

/-- After the handshake: the peer's initial connection ID (sequence number 0)
    and the one from its `preferred_address` (sequence number 1); we advertised
    an `active_connection_id_limit` of 4. -/
private def s0 : State :=
  { entries := [⟨0, [1], tok 0⟩, ⟨1, [2], tok 1⟩], retired := [], retirePriorTo := 0,
    limit := 4, peerZeroLen := false }

-- An ordinary NEW_CONNECTION_ID with Retire Prior To 0: the ID is added and
-- nothing is retired.
example : component.step s0 (.recvNewCid 2 0 [3] (tok 3)) =
    .ok { s0 with entries := s0.entries ++ [⟨2, [3], tok 3⟩] } [] := by decide

-- §5.1.2, line 1811: "Upon receipt of an increased Retire Prior To field, the
-- peer MUST stop using the corresponding connection IDs and retire them with
-- RETIRE_CONNECTION_ID frames before adding the newly provided connection ID".
example : (component.step s0 (.recvNewCid 2 2 [3] (tok 3))).obs =
    .ok [.stopUsing 0 [1], .queueRetire 0, .stopUsing 1 [2], .queueRetire 1] := by decide
example : ((component.step s0 (.recvNewCid 2 2 [3] (tok 3))).next s0).retired = [0, 1] := by decide
example : ((component.step s0 (.recvNewCid 2 2 [3] (tok 3))).next s0).retirePriorTo = 2 := by decide
example : ((component.step s0 (.recvNewCid 2 2 [3] (tok 3))).next s0).activeCount = 1 := by decide

-- §19.15, line 7979: "Receipt of the same frame multiple times MUST NOT be
-- treated as a connection error" — the second copy changes nothing.
example :
    component.step ((component.step s0 (.recvNewCid 2 2 [3] (tok 3))).next s0)
      (.recvNewCid 2 2 [3] (tok 3)) =
    .ok ((component.step s0 (.recvNewCid 2 2 [3] (tok 3))).next s0) [] := by decide

-- §19.15, line 8013: "An endpoint that receives a NEW_CONNECTION_ID frame with
-- a sequence number smaller than the Retire Prior To field of a previously
-- received NEW_CONNECTION_ID frame MUST send a corresponding
-- RETIRE_CONNECTION_ID frame that retires the newly received connection ID,
-- unless it has already done so for that sequence number."
private def s2 : State := (component.step s0 (.recvNewCid 5 4 [3] (tok 3))).next s0
example : s2.retirePriorTo = 4 ∧ s2.retired = [0, 1] := by decide
example : (component.step s2 (.recvNewCid 3 0 [9] (tok 9))).obs =
    .ok [.stopUsing 3 [9], .queueRetire 3] := by decide
-- … "unless it has already done so": sequence number 1 was retired above.
example : (component.step s2 (.recvNewCid 1 0 [2] (tok 1))).obs = .ok [] := by decide

-- §19.15, line 7998: "A receiver MUST ignore any Retire Prior To fields that do
-- not increase the largest received Retire Prior To value."
example :
    ((component.step ((component.step s0 (.recvNewCid 5 2 [3] (tok 3))).next s0)
      (.recvNewCid 6 1 [9] (tok 9))).next s0).retirePriorTo = 2 := by decide

-- §19.15, line 7993: Retire Prior To greater than the sequence number.
example : component.step s0 (.recvNewCid 2 3 [3] (tok 3)) =
    .error .frameEncodingError := by decide

-- §19.15, line 7959: connection ID length outside 1..20.
example : component.step s0 (.recvNewCid 2 0 [] (tok 3)) =
    .error .frameEncodingError := by decide

-- §5.1.1, line 1743: a fifth active connection ID under a limit of 4.
private def s1 : State := { s0 with entries := s0.entries ++ [⟨2, [3], tok 3⟩, ⟨3, [4], tok 4⟩] }
example : s1.activeCount = 4 := by decide
example : component.step s1 (.recvNewCid 4 0 [5] (tok 5)) =
    .error .connectionIdLimitError := by decide
-- …but the same frame with a large enough Retire Prior To is fine (§5.1.1,
-- line 1722: "An endpoint MAY send connection IDs that temporarily exceed a
-- peer's limit if the NEW_CONNECTION_ID frame also requires the retirement of
-- any excess").
example : ((component.step s1 (.recvNewCid 4 4 [5] (tok 5))).next s1).activeCount = 1 := by decide

-- §19.15, line 7985: a sequence number reused for a different connection ID.
-- Both alternatives of the MAY are permitted …
private def reuse : Event := .recvNewCid 1 0 [7] (tok 1)
example : component.accepts s0 reuse (.error .protocolViolation) = true := by decide
example : component.accepts s0 reuse (.ok s0 []) = true := by decide
-- … and nothing else is.
example : component.accepts s0 reuse (.error .frameEncodingError) = false := by decide

-- §19.15, line 7974: we send packets with a zero-length Destination Connection
-- ID, so NEW_CONNECTION_ID is a PROTOCOL_VIOLATION.
example : component.step { s0 with entries := [], peerZeroLen := true }
    (.recvNewCid 1 0 [7] (tok 1)) = .error .protocolViolation := by decide

-- §19.16 send side.
example : component.maySend s0 (.retireConnectionId 1) = true := by decide
example : component.maySend s0 (.retireConnectionId 9) = false := by decide       -- never issued
example : component.maySend { s0 with retired := [1] } (.retireConnectionId 1) = false := by decide
example : component.maySend { s0 with peerZeroLen := true } (.retireConnectionId 1) = false := by
  decide

-- Following an implementation whose state we cannot see.
example : component.track s0 (.recvNewCid 2 0 [3] (tok 3)) (.ok []) =
    some { s0 with entries := s0.entries ++ [⟨2, [3], tok 3⟩] } := by decide

end Examples

/-! ## 10. Coverage and notes

Assigned text: lines 1608–1834 (§5.1, §5.1.1, §5.1.2) and 7923–8058 (§19.15,
§19.16).  This file covers the half of it that concerns connection IDs the peer
issued to us.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §5.1 (1641) | connection IDs MUST NOT be correlatable by an observer | out of scope: a property of the issuer's generation function, not of any state machine |
| §5.1 (1644) | the same connection ID MUST NOT be issued more than once | `Local.canIssue` (send side) |
| §5.1 (1670) | MUST NOT reuse an address/port pair for concurrent zero-length-CID connections | out of scope: about several connections, not one endpoint's CID set |
| §5.1.1 (1709) | an issuer MUST accept packets carrying an issued CID until retired | `Local.State.active` |
| §5.1.1 (1712) | issued and not retired = active | `State.active` |
| §5.1.1 (1718) | SHOULD keep the peer supplied with CIDs | `Local.Recommended` (advice, not `Step`) |
| §5.1.1 (1721) | MUST NOT provide more CIDs than the peer's limit | `Local.canIssue`, `Local.issue_respects_peer_limit` |
| §5.1.1 (1722) | MAY exceed temporarily with a large enough Retire Prior To | `Local.State.peerActiveAfter` |
| §5.1.1 (1743) | more active CIDs than advertised → CONNECTION_ID_LIMIT_ERROR | `Step.ncidLimit`, `Inv`, `active_le_limit` |
| §5.1.1 (1749) | SHOULD supply a new CID when the peer retires one | `Local.Effect.cidRetiredByPeer` (advice) |
| §5.1.1 (1753) | MAY limit the total number of CIDs issued | permitted: `Step.issueRefused` allows refusing |
| §5.1.1 (1766) | a zero-length-CID endpoint cannot issue a new CID | `Local.canIssue` |
| §5.1.2 (1779) | send RETIRE_CONNECTION_ID to remove a CID from use | `Step.retireOk`, `MaySend` |
| §5.1.2 (1799) | SHOULD retire CIDs no longer used on a path | out of scope: paths are WP10 |
| §5.1.2 (1806) | the issuer SHOULD keep accepting until retired; MAY close otherwise | advice; closing is WP6 |
| §5.1.2 (1811) | MUST stop using, and retire, CIDs below an increased Retire Prior To, before adding the new one | `staleOf`, `applyNcid`, `Effect.stopUsing`/`queueRetire` |
| §5.1.2 (1823) | SHOULD limit unacknowledged retirements; MUST NOT forget a CID without retiring it; MAY treat an excess as CONNECTION_ID_LIMIT_ERROR | partly: `entries` is never pruned, so nothing is forgotten; the retirement backlog needs the loss recovery state (RFC 9002), out of scope |
| §5.1.2 (1831) | SHOULD NOT raise Retire Prior To before the previous one is honoured | `Local.Recommended` |
| §19.15 (7959) | CID length <1 or >20 → FRAME_ENCODING_ERROR | `Step.ncidBadLen` |
| §19.15 (7970) | MUST NOT send NEW_CONNECTION_ID while requiring zero-length DCIDs from the peer | `Local.canIssue` |
| §19.15 (7974) | receiving it while sending zero-length DCIDs → PROTOCOL_VIOLATION | `Step.ncidZeroLen` |
| §19.15 (7979) | a repeated frame MUST NOT be a connection error | `entriesAfter`, `Step.ncidOk` |
| §19.15 (7985) | reused CID/sequence number MAY be PROTOCOL_VIOLATION | `Step.ncidConflict` vs `Step.ncidLimit`/`ncidOk` |
| §19.15 (7993) | Retire Prior To > Sequence Number → FRAME_ENCODING_ERROR | `Step.ncidRptTooLarge` |
| §19.15 (7998) | MUST ignore a Retire Prior To that does not increase the largest seen | `Nat.max` in `applyNcid`, `rpt_mono` |
| §19.15 (8013) | a sequence number below a seen Retire Prior To MUST be retired, unless already done | `staleOf` over `entriesAfter` |
| §19.16 (8046) | sequence number greater than any sent → PROTOCOL_VIOLATION | `Local.Step.retireUnknown` |
| §19.16 (8050) | MUST NOT retire the packet's own DCID; peer MAY treat as PROTOCOL_VIOLATION | `Local.Step.retireSelf`; the send-side MUST NOT needs the packet being assembled, which is WP12 |
| §19.16 (8055) | cannot send when the peer's CID is zero-length; receiving one when we issue zero-length CIDs → PROTOCOL_VIOLATION | `MaySend` here, `Local.Step.retireZeroLen` there |

NOTES on this half are collected in `QuicModel/Spec/ConnIds.lean`.
-/

end Quic.Spec.ConnIds.Remote
