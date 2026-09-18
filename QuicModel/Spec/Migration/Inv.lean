import QuicModel.Spec.Migration.Step

/-!
  WP10 "Migration", part 5: the invariant, and the projection lemmas that make
  it provable.
-/
namespace Quic.Spec.Migration

/-! ## 5. Invariant

Two facts a reachable state never loses:

* the "last validated peer address" of §9.3.2, line 3451 really is validated,
  which is what makes reverting to it meaningful (theorem `revert_or_close`);
* §9.5, line 3603: every connection ID in use as a Destination Connection ID is
  in use from the one local address the *history* (`dcidFrom`) records for it.
  Since `dcidFrom` is never rewritten, this is the reuse prohibition and not
  merely a statement about the current `dcidOn`.  Line 3608's companion rule is
  *not* part of the invariant: the MAY of line 3611 breaks it, see the
  counterexample section of `Migration/Theorems.lean`. -/

def InvLastValidated (s : State) : Prop :=
  ∀ q, s.lastValidated = some q → s.statusOf q = .validated

/-- §9.5, line 3603, over the grow-only record: the connection ID in use on a
    path has only ever been sent from that path's local address. -/
def InvOneLocalAddrPerCid (s : State) : Prop :=
  ∀ e ∈ s.dcidOn, s.dcidFrom.get? e.2 = some e.1.loc

def Inv (s : State) : Prop := InvLastValidated s ∧ InvOneLocalAddrPerCid s


/-! ### Projection lemmas

Every state update in this component either leaves `paths` alone or rewrites one
entry without touching its `status`, and only `beginSendOn` touches `dcidOn` or
`dcidFrom`. -/

namespace State

theorem statusOf_of_set (s t : State) (p q : Path) (f : PathInfo → PathInfo)
    (hp : t.paths = s.paths.set p (f (s.infoOf p)))
    (hf : (f (s.infoOf p)).status = (s.infoOf p).status) :
    t.statusOf q = s.statusOf q := by
  show ((t.paths.get? q).getD {}).status = ((s.paths.get? q).getD {}).status
  rw [hp]
  by_cases h : q = p
  · subst h; rw [Map.get?_set_self]; exact hf
  · rw [Map.get?_set_of_ne _ _ h]

theorem statusOf_setInfo_ne (s : State) (p q : Path) (f : PathInfo → PathInfo) (h : q ≠ p) :
    (s.setInfo p f).statusOf q = s.statusOf q := by
  show (((s.paths.set p (f (s.infoOf p))).get? q).getD {}).status = _
  rw [Map.get?_set_of_ne _ _ h]
  rfl

theorem statusOf_setInfo_self (s : State) (p : Path) (f : PathInfo → PathInfo) :
    (s.setInfo p f).statusOf p = (f (s.infoOf p)).status := by
  show (((s.paths.set p (f (s.infoOf p))).get? p).getD {}).status = _
  rw [Map.get?_set_self]
  rfl

theorem statusOf_setInfo (s : State) (p q : Path) (f : PathInfo → PathInfo)
    (hf : (f (s.infoOf p)).status = (s.infoOf p).status) :
    (s.setInfo p f).statusOf q = s.statusOf q := by
  by_cases h : q = p
  · subst h; rw [statusOf_setInfo_self]; exact hf
  · exact statusOf_setInfo_ne s p q f h

@[simp] theorem statusOf_markValidating (s : State) (p q : Path) :
    (s.markValidating p).statusOf q = s.statusOf q :=
  statusOf_setInfo s p q (fun i => { i with validating := true }) rfl

@[simp] theorem statusOf_recordRecv (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).statusOf q = s.statusOf q :=
  statusOf_of_set s _ p q
    (fun i => { i with largestPn := Nat.max i.largestPn pn,
                       sawNonProbing := i.sawNonProbing || !pr }) rfl rfl

@[simp] theorem statusOf_markValidated_self (s : State) (p : Path) :
    (s.markValidated p).statusOf p = .validated := by
  rw [markValidated, statusOf_setInfo_self]

theorem statusOf_markValidated_ne (s : State) {p q : Path} (h : q ≠ p) :
    (s.markValidated p).statusOf q = s.statusOf q :=
  statusOf_setInfo_ne s p q _ h

theorem statusOf_markFailed_of_validated (s : State) (p : Path) {q : Path}
    (hq : s.statusOf q = .validated) : (s.markFailed p).statusOf q = .validated := by
  unfold markFailed
  split
  · rw [statusOf_setInfo s p q (fun i => { i with validating := false }) rfl]; exact hq
  · rename_i hv
    by_cases h : q = p
    · subst h
      have : s.isValidated q = true := by simp [isValidated, hq]
      exact absurd this hv
    · rw [statusOf_setInfo_ne s p q _ h]; exact hq

@[simp] theorem statusOf_switchTo (s : State) (p q : Path) :
    (s.switchTo p).statusOf q = s.statusOf q := rfl

@[simp] theorem statusOf_revertTo (s : State) (p q : Path) :
    (s.revertTo p).statusOf q = s.statusOf q := rfl

@[simp] theorem statusOf_startProbe (s : State) (p q : Path) :
    (s.startProbe p).statusOf q = s.statusOf q :=
  statusOf_of_set s _ p q (fun i => { i with validating := true }) rfl rfl

@[simp] theorem statusOf_observe (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).statusOf q = s.statusOf q := by
  unfold observe; split <;> simp

@[simp] theorem statusOf_permit (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).statusOf q = s.statusOf q := by
  unfold permit; split <;> simp

theorem statusOf_succStay_ne (s : State) {p q : Path} (h : q ≠ p) :
    (s.succStay p).statusOf q = s.statusOf q := statusOf_markValidated_ne (s := s) h

theorem statusOf_succStay_self (s : State) (p : Path) :
    (s.succStay p).statusOf p = .validated := statusOf_markValidated_self s p

@[simp] theorem lastValidated_markValidating (s : State) (p : Path) :
    (s.markValidating p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_markValidated (s : State) (p : Path) :
    (s.markValidated p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_markFailed (s : State) (p : Path) :
    (s.markFailed p).lastValidated = s.lastValidated := by unfold markFailed; split <;> rfl

@[simp] theorem lastValidated_startProbe (s : State) (p : Path) :
    (s.startProbe p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).lastValidated = s.lastValidated := by unfold observe; split <;> rfl

@[simp] theorem lastValidated_revertTo (s : State) (p : Path) :
    (s.revertTo p).lastValidated = s.lastValidated := rfl

@[simp] theorem dcidOn_setInfo (s : State) (p : Path) (f : PathInfo → PathInfo) :
    (s.setInfo p f).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markValidating (s : State) (p : Path) :
    (s.markValidating p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markValidated (s : State) (p : Path) :
    (s.markValidated p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markFailed (s : State) (p : Path) :
    (s.markFailed p).dcidOn = s.dcidOn := by unfold markFailed; split <;> rfl

@[simp] theorem dcidOn_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_switchTo (s : State) (p : Path) : (s.switchTo p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_revertTo (s : State) (p : Path) : (s.revertTo p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).dcidOn = s.dcidOn := by unfold observe; split <;> rfl

@[simp] theorem dcidOn_permit (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).dcidOn = s.dcidOn := by unfold permit; split <;> rfl

@[simp] theorem dcidOn_startProbe (s : State) (p : Path) : (s.startProbe p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_succStay (s : State) (p : Path) : (s.succStay p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_succSwitch (s : State) (p : Path) :
    (s.succSwitch p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidFrom_setInfo (s : State) (p : Path) (f : PathInfo → PathInfo) :
    (s.setInfo p f).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_markValidating (s : State) (p : Path) :
    (s.markValidating p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_markValidated (s : State) (p : Path) :
    (s.markValidated p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_markFailed (s : State) (p : Path) :
    (s.markFailed p).dcidFrom = s.dcidFrom := by unfold markFailed; split <;> rfl

@[simp] theorem dcidFrom_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_switchTo (s : State) (p : Path) :
    (s.switchTo p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_revertTo (s : State) (p : Path) :
    (s.revertTo p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).dcidFrom = s.dcidFrom := by unfold observe; split <;> rfl

@[simp] theorem dcidFrom_permit (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).dcidFrom = s.dcidFrom := by unfold permit; split <;> rfl

@[simp] theorem dcidFrom_startProbe (s : State) (p : Path) :
    (s.startProbe p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_succStay (s : State) (p : Path) :
    (s.succStay p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidFrom_succSwitch (s : State) (p : Path) :
    (s.succSwitch p).dcidFrom = s.dcidFrom := rfl

@[simp] theorem dcidOn_recordPeerCid (s : State) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).dcidOn = s.dcidOn := by unfold recordPeerCid; split <;> rfl

@[simp] theorem dcidFrom_recordPeerCid (s : State) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).dcidFrom = s.dcidFrom := by unfold recordPeerCid; split <;> rfl

@[simp] theorem lastValidated_recordPeerCid (s : State) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).lastValidated = s.lastValidated := by
  unfold recordPeerCid; split <;> rfl

@[simp] theorem statusOf_recordPeerCid (s : State) (q : Path) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).statusOf q = s.statusOf q := by
  unfold recordPeerCid; split <;> rfl

/-- The history is grow-only: `recordCidUse` never rewrites an entry. -/
theorem dcidFrom_recordCidUse_of_some (s : State) (p : Path) (n : Nat) {l : LocalAddr}
    (h : s.dcidFrom.get? n = some l) : (s.recordCidUse p n).dcidFrom = s.dcidFrom := by
  show (match s.dcidFrom.get? n with
        | some _ => s.dcidFrom
        | none => s.dcidFrom.set n p.loc) = s.dcidFrom
  rw [h]

theorem dcidFrom_recordCidUse_of_none (s : State) (p : Path) (n : Nat)
    (h : s.dcidFrom.get? n = none) :
    (s.recordCidUse p n).dcidFrom = s.dcidFrom.set n p.loc := by
  show (match s.dcidFrom.get? n with
        | some _ => s.dcidFrom
        | none => s.dcidFrom.set n p.loc) = s.dcidFrom.set n p.loc
  rw [h]

@[simp] theorem dcidOn_recordCidUse (s : State) (p : Path) (n : Nat) :
    (s.recordCidUse p n).dcidOn = s.dcidOn := rfl

end State

/-! ### Preservation -/

theorem invOneLocal_congr {s t : State} (hi : InvOneLocalAddrPerCid s) (h : t.dcidOn = s.dcidOn)
    (hf : t.dcidFrom = s.dcidFrom) : InvOneLocalAddrPerCid t := by
  intro e he
  rw [h] at he
  rw [hf]
  exact hi e he

theorem invLast_congr {s t : State} (hi : InvLastValidated s)
    (hl : t.lastValidated = s.lastValidated) (hs : ∀ q, t.statusOf q = s.statusOf q) :
    InvLastValidated t := by
  intro q hq
  rw [hs q]
  exact hi q (hl ▸ hq)

/-- Switching the sending path keeps the invariant: the path we leave is
    recorded as "last validated" only when it is in fact validated. -/
theorem invLast_switchTo (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.switchTo p) := by
  intro q hq
  rw [State.statusOf_switchTo]
  simp only [State.switchTo] at hq
  split at hq
  · rename_i hv
    rcases Option.some.inj hq with rfl
    simpa [State.isValidated] using hv
  · exact ht q hq

theorem invLast_revertTo (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.revertTo p) := fun q hq => ht q hq

theorem invLast_discard (t : State) (ht : InvLastValidated t) :
    InvLastValidated { t with discarded := true } := fun q hq => ht q hq

theorem invLast_markFailed (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.markFailed p) := by
  intro q hq
  exact State.statusOf_markFailed_of_validated _ _ (ht q (by simpa using hq))

theorem invLast_succStay (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.succStay p) := by
  intro q hq
  simp only [State.succStay] at hq
  by_cases hqp : q = p
  · subst hqp; exact State.statusOf_succStay_self t q
  · rw [State.statusOf_succStay_ne _ hqp]
    split at hq
    · exact absurd (Option.some.inj hq).symm hqp
    · exact ht q hq

/-- `Map.set` never invents an entry: what comes out was already there, or is
    the one just written. -/
theorem mem_set_weak {κ ν : Type} [DecidableEq κ] (m : Map κ ν) (k : κ) (v : ν) (e : κ × ν)
    (h : e ∈ m.set k v) : e = (k, v) ∨ e ∈ m := by
  induction m with
  | nil => simp only [Map.set, List.mem_singleton] at h; exact Or.inl h
  | cons x xs ih =>
    rw [Map.set] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The history records `n` as sent from `p.loc` once `p` has used it, provided
    §9.5 line 3603 permitted the use in the first place. -/
theorem get?_dcidFrom_recordCidUse_self {s : State} {p : Path} {n : Nat}
    (hr : s.reusedAcrossLocal p n = false) :
    (s.recordCidUse p n).dcidFrom.get? n = some p.loc := by
  cases h : s.dcidFrom.get? n with
  | none => rw [State.dcidFrom_recordCidUse_of_none s p n h, Map.get?_set_self]
  | some l =>
    rw [State.dcidFrom_recordCidUse_of_some s p n h, h]
    have : (decide (l ≠ p.loc)) = false := by
      simpa only [State.reusedAcrossLocal, h] using hr
    simp only [decide_eq_false_iff_not, Decidable.not_not] at this
    rw [this]

/-- Entries for other connection IDs are untouched. -/
theorem get?_dcidFrom_recordCidUse_ne {s : State} {p : Path} {n k : Nat} (h : k ≠ n) :
    (s.recordCidUse p n).dcidFrom.get? k = s.dcidFrom.get? k := by
  cases hn : s.dcidFrom.get? n with
  | none => rw [State.dcidFrom_recordCidUse_of_none s p n hn, Map.get?_set_of_ne _ _ h]
  | some l => rw [State.dcidFrom_recordCidUse_of_some s p n hn]

/-- §9.5, line 3603 is exactly what keeps `InvOneLocalAddrPerCid` true. -/
theorem invOneLocal_useCid {s : State} {p : Path} {n : Nat}
    (hi : InvOneLocalAddrPerCid s) (hr : s.reusedAcrossLocal p n = false) :
    InvOneLocalAddrPerCid (s.useCid p n) := by
  intro e he
  simp only [State.useCid] at he ⊢
  rcases mem_set_weak _ _ _ _ he with rfl | he
  · exact get?_dcidFrom_recordCidUse_self hr
  · have hold := hi e he
    by_cases hk : e.2 = n
    · subst hk
      rw [State.dcidFrom_recordCidUse_of_some s p e.2 hold]
      exact hold
    · rw [get?_dcidFrom_recordCidUse_ne hk]
      exact hold

theorem reusedAcrossLocal_false_of_cidCase {s : State} {p : Path} {n : Nat}
    (h : cidCase s p n = .rebind ∨ cidCase s p n = .fresh) :
    s.reusedAcrossLocal p n = false := by
  unfold cidCase at h
  split at h
  · rcases h with h | h <;> simp at h
  · split at h
    · rcases h with h | h <;> simp at h
    · split at h
      · rcases h with h | h <;> simp at h
      · rename_i hx
        cases hb : s.reusedAcrossLocal p n
        · rfl
        · exact absurd hb hx

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hA, hB⟩ := hi
  cases h with
  | recvUnsolicitedKeep hc | recvQuiet hc | recvRefuse hc =>
    exact ⟨invLast_congr hA (by simp) (by simp), invOneLocal_congr hB (by simp) (by simp)⟩
  | recvBannedMigrate hc | recvMigrate hc =>
    refine ⟨?_, invOneLocal_congr hB (by simp) (by simp)⟩
    unfold State.permit
    refine invLast_switchTo _ _ (invLast_congr hA ?_ ?_)
    · split <;> rfl
    · intro q; split <;> simp
  | succStay hc | succKeep hc => exact ⟨invLast_succStay _ _ hA, invOneLocal_congr hB (by simp) (by simp)⟩
  | succMustSwitch hc | succSwitch hc =>
    exact ⟨invLast_switchTo _ _ (invLast_succStay _ _ hA), invOneLocal_congr hB (by simp) (by simp)⟩
  | failRevert hc =>
    exact ⟨invLast_revertTo _ _ (invLast_markFailed _ _ hA), invOneLocal_congr hB (by simp) (by simp)⟩
  | failNoPath hc | failOtherGiveUp hc =>
    exact ⟨invLast_discard _ (invLast_markFailed _ _ hA), invOneLocal_congr hB (by simp) (by simp)⟩
  | failOther hc | failOtherWait hc =>
    exact ⟨invLast_markFailed _ _ hA, invOneLocal_congr hB (by simp) (by simp)⟩
  | migValidateFirst hc | probeStart hc =>
    exact ⟨invLast_congr hA (by simp) (by simp), invOneLocal_congr hB (by simp) (by simp)⟩
  | migAlready hc | migDefer hc =>
    exact ⟨invLast_switchTo _ _ hA, invOneLocal_congr hB (by simp) (by simp)⟩
  | migFresh hc =>
    exact ⟨invLast_switchTo _ _ (invLast_congr hA (by simp) (by simp)),
           invOneLocal_congr hB (by simp) (by simp)⟩
  | confirmed => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl rfl⟩
  | preferredLearn h => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl rfl⟩
  | cidZeroLen hc => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl rfl⟩
  | cidRebindKeep hc =>
    exact ⟨invLast_congr hA rfl (fun _ => rfl),
           invOneLocal_useCid hB (reusedAcrossLocal_false_of_cidCase (Or.inl hc))⟩
  | cidFresh hc =>
    exact ⟨invLast_congr hA rfl (fun _ => rfl),
           invOneLocal_useCid hB (reusedAcrossLocal_false_of_cidCase (Or.inr hc))⟩
  | peerCidLearn =>
    exact ⟨invLast_congr hA (by simp) (by simp), invOneLocal_congr hB (by simp) (by simp)⟩

end Quic.Spec.Migration
