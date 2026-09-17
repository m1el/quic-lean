import QuicModel.Spec.TransportParams.Wire

/-
  Order independence of the interpretation of transport parameters (§18).
-/
namespace Quic.Spec.TransportParams

/-! ## Order independence

`setParam` splits into a check on the value bytes, which does not look at the
record, and an update, which touches only its own parameter's field.  Two
different parameters therefore commute, and interpreting a list whose
identifiers are distinct does not depend on the order. -/

/-- Is this value well formed for this parameter? -/
def parseOk : ParamId → ByteArray → Bool
  | .originalDestinationConnectionId, _ => true
  | .maxIdleTimeout, v => (varintValue? v).isSome
  | .statelessResetToken, v => decide (v.size = 16)
  | .maxUdpPayloadSize, v => (varintValue? v).isSome
  | .initialMaxData, v => (varintValue? v).isSome
  | .initialMaxStreamDataBidiLocal, v => (varintValue? v).isSome
  | .initialMaxStreamDataBidiRemote, v => (varintValue? v).isSome
  | .initialMaxStreamDataUni, v => (varintValue? v).isSome
  | .initialMaxStreamsBidi, v => (varintValue? v).isSome
  | .initialMaxStreamsUni, v => (varintValue? v).isSome
  | .ackDelayExponent, v => (varintValue? v).isSome
  | .maxAckDelay, v => (varintValue? v).isSome
  | .disableActiveMigration, v => decide (v.size = 0)
  | .preferredAddress, v => (decodePreferredAddress v).isSome
  | .activeConnectionIdLimit, v => (varintValue? v).isSome
  | .initialSourceConnectionId, _ => true
  | .retrySourceConnectionId, _ => true

/-- The field this parameter sets; total, and meaningful only when `parseOk`. -/
def update (tp : TransportParams) : ParamId → ByteArray → TransportParams
  | .originalDestinationConnectionId, v => { tp with originalDestinationConnectionId := some v }
  | .maxIdleTimeout, v => { tp with maxIdleTimeout := (varintValue? v).getD 0 }
  | .statelessResetToken, v => { tp with statelessResetToken := some v }
  | .maxUdpPayloadSize, v => { tp with maxUdpPayloadSize := (varintValue? v).getD 0 }
  | .initialMaxData, v => { tp with initialMaxData := (varintValue? v).getD 0 }
  | .initialMaxStreamDataBidiLocal, v =>
      { tp with initialMaxStreamDataBidiLocal := (varintValue? v).getD 0 }
  | .initialMaxStreamDataBidiRemote, v =>
      { tp with initialMaxStreamDataBidiRemote := (varintValue? v).getD 0 }
  | .initialMaxStreamDataUni, v => { tp with initialMaxStreamDataUni := (varintValue? v).getD 0 }
  | .initialMaxStreamsBidi, v => { tp with initialMaxStreamsBidi := (varintValue? v).getD 0 }
  | .initialMaxStreamsUni, v => { tp with initialMaxStreamsUni := (varintValue? v).getD 0 }
  | .ackDelayExponent, v => { tp with ackDelayExponent := (varintValue? v).getD 0 }
  | .maxAckDelay, v => { tp with maxAckDelay := (varintValue? v).getD 0 }
  | .disableActiveMigration, _ => { tp with disableActiveMigration := true }
  | .preferredAddress, v => { tp with preferredAddress := decodePreferredAddress v }
  | .activeConnectionIdLimit, v => { tp with activeConnectionIdLimit := (varintValue? v).getD 0 }
  | .initialSourceConnectionId, v => { tp with initialSourceConnectionId := some v }
  | .retrySourceConnectionId, v => { tp with retrySourceConnectionId := some v }

/-- A value-parse followed by a field update, rewritten as a test and an
    update that no longer mentions each other. -/
theorem opt_map_eq_cond {α β : Type} (o : Option α) (f : α → β) (y : β)
    (h : ∀ a, o = some a → f a = y) :
    o.map f = cond o.isSome (some y) none := by
  cases o with
  | none => simp
  | some a => simp [h a rfl]

theorem setParam_eq (tp : TransportParams) (p : ParamId) (v : ByteArray) :
    setParam tp p v = cond (parseOk p v) (some (update tp p v)) none := by
  cases p <;> simp only [setParam, parseOk, update] <;>
    first
      | rfl
      | (refine opt_map_eq_cond _ _ _ ?_; intro a ha; simp [ha])
      | (split <;> simp_all)

theorem update_comm {p q : ParamId} (hne : p ≠ q) (tp : TransportParams) (v w : ByteArray) :
    update (update tp p v) q w = update (update tp q w) p v := by
  cases p <;> cases q <;> first | exact absurd rfl hne | rfl

theorem setParam_comm {p q : ParamId} (hne : p ≠ q) (tp : TransportParams) (v w : ByteArray) :
    (setParam tp p v).bind (fun s => setParam s q w)
      = (setParam tp q w).bind (fun s => setParam s p v) := by
  simp only [setParam_eq]
  cases hp : parseOk p v <;> cases hq : parseOk q w <;> simp [update_comm hne]

theorem applyEntries_perm {l₁ l₂ : List (ParamId × ByteArray)} (h : l₁.Perm l₂) :
    ∀ tp : TransportParams, (l₁.map Prod.fst).Nodup → applyEntries l₁ tp = applyEntries l₂ tp := by
  induction h with
  | nil => intro _ _; rfl
  | cons a _hp ih =>
    intro tp hnd
    obtain ⟨p, v⟩ := a
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [applyEntries]
    cases hs : setParam tp p v with
    | none => rfl
    | some s => simpa using ih s hnd.2
  | swap a b l =>
    intro tp hnd
    obtain ⟨p, v⟩ := a
    obtain ⟨q, w⟩ := b
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
    have hne : q ≠ p := fun h => hnd.1 (Or.inl h)
    simp only [applyEntries]
    rw [← Option.bind_assoc, ← Option.bind_assoc, setParam_comm hne tp w v]
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    intro tp hnd
    have hnd₂ : (l₂.map Prod.fst).Nodup := ((h₁.map Prod.fst).nodup_iff).mp hnd
    rw [ih₁ tp hnd, ih₂ tp hnd₂]

theorem knownEntries_eq_filterMap (raw : Raw) :
    knownEntries raw = raw.filterMap (fun e => (ParamId.ofCode? e.1).map fun p => (p, e.2)) := by
  induction raw with
  | nil => rfl
  | cons a l ih => obtain ⟨id, v⟩ := a; cases h : ParamId.ofCode? id <;> simp [knownEntries, h, ih]

theorem knownEntries_perm {l₁ l₂ : Raw} (h : l₁.Perm l₂) :
    (knownEntries l₁).Perm (knownEntries l₂) := by
  rw [knownEntries_eq_filterMap, knownEntries_eq_filterMap]
  exact h.filterMap _

/-- **Order independence (c).**  As long as no known parameter appears twice,
    the interpretation does not depend on the order the parameters arrive in. -/
theorem interpret_perm {l₁ l₂ : Raw} (h : l₁.Perm l₂) (hnd : (knownIds l₁).Nodup) :
    interpret l₁ = interpret l₂ :=
  applyEntries_perm (knownEntries_perm h) defaults hnd

end Quic.Spec.TransportParams
