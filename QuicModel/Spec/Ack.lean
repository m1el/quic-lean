import QuicModel.Spec.FrameRules

/-
  WP3 (b): per packet-number-space receive tracking (§12.3 duplicate
  suppression), the acknowledgment rules of §13.1 and the generation rules of
  §13.2.

  Text: draft-ietf-quic-transport-34, lines 4694–4700 (§12.3), 5018–5324
  (§13.1, §13.2.1–§13.2.7), with the ACK frame arithmetic of §19.3.1.

  Table 3 and the packet-type legality of frames are in
  `QuicModel/Spec/FrameRules.lean`.
-/
namespace Quic.Spec.Ack

/-! ## 0. The set of received packet numbers

§13.2.3, line 5185: "When an ACK frame is sent, one or more ranges of
acknowledged packets are included."  The receiver's record of what it has
processed in one packet number space is kept in exactly that shape: a list of
closed ranges `[lo, hi]`, in increasing order, non-empty, and separated by a
gap of at least one packet number so that the representation is canonical. -/

/-- A closed range of packet numbers, `lo ≤ hi`. -/
structure Rng where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

namespace Ranges

/-- Is `n` in one of the ranges? -/
def mem : List Rng → Nat → Bool
  | [], _ => false
  | r :: rs, n => (decide (r.lo ≤ n) && decide (n ≤ r.hi)) || mem rs n

@[simp] theorem mem_nil (n : Nat) : mem [] n = false := rfl

@[simp] theorem mem_cons_iff (r : Rng) (rs : List Rng) (n : Nat) :
    mem (r :: rs) n = true ↔ ((r.lo ≤ n ∧ n ≤ r.hi) ∨ mem rs n = true) := by
  simp [mem]

theorem mem_of_mem_list {l : List Rng} {r : Rng} (hr : r ∈ l) {n : Nat}
    (h1 : r.lo ≤ n) (h2 : n ≤ r.hi) : mem l n = true := by
  induction l with
  | nil => cases hr
  | cons a as ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst h; simp [mem_cons_iff]; omega
    · simp [mem_cons_iff]; exact Or.inr (ih h)

theorem exists_of_mem {l : List Rng} {n : Nat} (h : mem l n = true) :
    ∃ r ∈ l, r.lo ≤ n ∧ n ≤ r.hi := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    rw [mem_cons_iff] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨r, hr, h1, h2⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, h1, h2⟩

/-- `wfFrom lo l`: the ranges of `l` are non-empty, increasing, and separated
    by a gap of at least one packet number, and the first of them starts at
    `lo` or later. -/
def wfFrom : Nat → List Rng → Bool
  | _, [] => true
  | lo, r :: rs => decide (lo ≤ r.lo) && decide (r.lo ≤ r.hi) && wfFrom (r.hi + 2) rs

/-- The invariant of a received-packet-number set. -/
def wf (l : List Rng) : Bool := wfFrom 0 l

@[simp] theorem wfFrom_nil (lo : Nat) : wfFrom lo [] = true := rfl

@[simp] theorem wfFrom_cons_iff (lo : Nat) (r : Rng) (rs : List Rng) :
    wfFrom lo (r :: rs) = true ↔ (lo ≤ r.lo ∧ r.lo ≤ r.hi ∧ wfFrom (r.hi + 2) rs = true) := by
  simp [wfFrom, and_assoc]

theorem wfFrom_mono {lo lo' : Nat} {l : List Rng} (h : lo' ≤ lo) (hw : wfFrom lo l = true) :
    wfFrom lo' l = true := by
  cases l with
  | nil => rfl
  | cons r rs => rw [wfFrom_cons_iff] at hw ⊢; exact ⟨Nat.le_trans h hw.1, hw.2⟩

/-- Everything recorded is at or above the lower bound. -/
theorem le_of_mem_wfFrom {lo : Nat} {l : List Rng} (hw : wfFrom lo l = true) {n : Nat}
    (h : mem l n = true) : lo ≤ n := by
  induction l generalizing lo with
  | nil => simp at h
  | cons r rs ih =>
    rw [wfFrom_cons_iff] at hw
    rw [mem_cons_iff] at h
    rcases h with h | h
    · omega
    · have := ih hw.2.2 h; omega

/-- Add one packet number.  Total, and canonical: adjacent ranges merge.

    Every branch condition is an inequality rather than an equation: under
    `wfFrom` the inequalities pin down the same cases, and keeping them
    inequalities is what lets the proofs below discharge each branch with
    `omega`. -/
def insert : List Rng → Nat → List Rng
  | [], n => [⟨n, n⟩]
  | r :: rs, n =>
    if n + 1 < r.lo then ⟨n, n⟩ :: r :: rs                -- strictly below, no touch
    else if n + 1 ≤ r.lo then ⟨n, r.hi⟩ :: rs             -- n + 1 = r.lo: extend down
    else if n ≤ r.hi then r :: rs                         -- already recorded
    else if n ≤ r.hi + 1 then                             -- n = r.hi + 1: extend up
      match rs with
      | [] => [⟨r.lo, n⟩]
      | r' :: rs' =>
        if r'.lo ≤ n + 1 then ⟨r.lo, r'.hi⟩ :: rs'        -- closes the gap: merge
        else ⟨r.lo, n⟩ :: r' :: rs'
    else r :: insert rs n

/-- The invariant is preserved. -/
theorem wfFrom_insert {lo n : Nat} {l : List Rng} (hn : lo ≤ n) (hw : wfFrom lo l = true) :
    wfFrom lo (insert l n) = true := by
  induction l generalizing lo with
  | nil =>
    have e : insert ([] : List Rng) n = [⟨n, n⟩] := rfl
    rw [e, wfFrom_cons_iff]
    exact ⟨hn, Nat.le_refl _, rfl⟩
  | cons r rs ih =>
    rw [wfFrom_cons_iff] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    by_cases cA : n + 1 < r.lo
    · have e : insert (r :: rs) n = ⟨n, n⟩ :: r :: rs := by simp [insert, cA]
      rw [e]; simp only [wfFrom_cons_iff]
      exact ⟨hn, Nat.le_refl _, by omega, h2, h3⟩
    · by_cases cB : n + 1 ≤ r.lo
      · have e : insert (r :: rs) n = ⟨n, r.hi⟩ :: rs := by simp [insert, cA, cB]
        rw [e]; simp only [wfFrom_cons_iff]
        exact ⟨hn, by omega, wfFrom_mono (by omega) h3⟩
      · by_cases cC : n ≤ r.hi
        · have e : insert (r :: rs) n = r :: rs := by simp [insert, cA, cB, cC]
          rw [e]; simp only [wfFrom_cons_iff]; exact ⟨h1, h2, h3⟩
        · by_cases cD : n ≤ r.hi + 1
          · cases rs with
            | nil =>
              have e : insert [r] n = [⟨r.lo, n⟩] := by simp [insert, cA, cB, cC, cD]
              rw [e]; simp only [wfFrom_cons_iff]; exact ⟨h1, by omega, rfl⟩
            | cons r' rs' =>
              rw [wfFrom_cons_iff] at h3
              obtain ⟨h4, h5, h6⟩ := h3
              by_cases cE : r'.lo ≤ n + 1
              · have e : insert (r :: r' :: rs') n = ⟨r.lo, r'.hi⟩ :: rs' := by
                  simp [insert, cA, cB, cC, cD, cE]
                rw [e]; simp only [wfFrom_cons_iff]
                exact ⟨h1, by omega, wfFrom_mono (by omega) h6⟩
              · have e : insert (r :: r' :: rs') n = ⟨r.lo, n⟩ :: r' :: rs' := by
                  simp [insert, cA, cB, cC, cD, cE]
                rw [e]; simp only [wfFrom_cons_iff]
                exact ⟨h1, by omega, by omega, h5, h6⟩
          · have e : insert (r :: rs) n = r :: insert rs n := by
              simp [insert, cA, cB, cC, cD]
            rw [e]; simp only [wfFrom_cons_iff]
            exact ⟨h1, h2, ih (by omega) h3⟩

theorem wf_insert {l : List Rng} (hw : wf l = true) (n : Nat) : wf (insert l n) = true :=
  wfFrom_insert (Nat.zero_le n) hw

/-- Soundness of the representation: after inserting `n`, the recorded set is
    exactly what it was, plus `n`. -/
theorem mem_insert {lo : Nat} {l : List Rng} (hw : wfFrom lo l = true) (n m : Nat) :
    mem (insert l n) m = true ↔ (mem l m = true ∨ m = n) := by
  induction l generalizing lo with
  | nil =>
    have e : insert ([] : List Rng) n = [⟨n, n⟩] := rfl
    rw [e, mem_cons_iff]
    simp only [mem_nil, Bool.false_eq_true, or_false, false_or]
    omega
  | cons r rs ih =>
    rw [wfFrom_cons_iff] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    by_cases cA : n + 1 < r.lo
    · have e : insert (r :: rs) n = ⟨n, n⟩ :: r :: rs := by simp [insert, cA]
      rw [e]; simp only [mem_cons_iff]
      constructor
      · rintro (h | h)
        · exact Or.inr (by omega)
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (by omega)
    · by_cases cB : n + 1 ≤ r.lo
      · have e : insert (r :: rs) n = ⟨n, r.hi⟩ :: rs := by simp [insert, cA, cB]
        rw [e]; simp only [mem_cons_iff]
        constructor
        · rintro (h | h)
          · by_cases hm : m = n
            · exact Or.inr hm
            · exact Or.inl (Or.inl ⟨by omega, h.2⟩)
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | h)
          · exact Or.inl (by omega)
          · exact Or.inr h
          · exact Or.inl (by omega)
      · by_cases cC : n ≤ r.hi
        · have e : insert (r :: rs) n = r :: rs := by simp [insert, cA, cB, cC]
          rw [e]
          constructor
          · intro h; exact Or.inl h
          · rintro (h | h)
            · exact h
            · rw [mem_cons_iff]; exact Or.inl (by omega)
        · by_cases cD : n ≤ r.hi + 1
          · cases rs with
            | nil =>
              have e : insert [r] n = [⟨r.lo, n⟩] := by simp [insert, cA, cB, cC, cD]
              rw [e]; simp only [mem_cons_iff, mem_nil, Bool.false_eq_true, or_false]
              omega
            | cons r' rs' =>
              rw [wfFrom_cons_iff] at h3
              obtain ⟨h4, h5, h6⟩ := h3
              by_cases cE : r'.lo ≤ n + 1
              · have e : insert (r :: r' :: rs') n = ⟨r.lo, r'.hi⟩ :: rs' := by
                  simp [insert, cA, cB, cC, cD, cE]
                rw [e]; simp only [mem_cons_iff]
                constructor
                · rintro (h | h)
                  · by_cases hm : m ≤ r.hi
                    · exact Or.inl (Or.inl ⟨h.1, hm⟩)
                    · by_cases hm2 : m = n
                      · exact Or.inr hm2
                      · exact Or.inl (Or.inr (Or.inl ⟨by omega, h.2⟩))
                  · exact Or.inl (Or.inr (Or.inr h))
                · rintro ((h | h | h) | h)
                  · exact Or.inl ⟨h.1, by omega⟩
                  · exact Or.inl ⟨by omega, h.2⟩
                  · exact Or.inr h
                  · exact Or.inl (by omega)
              · have e : insert (r :: r' :: rs') n = ⟨r.lo, n⟩ :: r' :: rs' := by
                  simp [insert, cA, cB, cC, cD, cE]
                rw [e]; simp only [mem_cons_iff]
                constructor
                · rintro (h | h)
                  · by_cases hm : m ≤ r.hi
                    · exact Or.inl (Or.inl ⟨h.1, hm⟩)
                    · exact Or.inr (by omega)
                  · exact Or.inl (Or.inr h)
                · rintro ((h | h) | h)
                  · exact Or.inl ⟨h.1, by omega⟩
                  · exact Or.inr h
                  · exact Or.inl (by omega)
          · have e : insert (r :: rs) n = r :: insert rs n := by
              simp [insert, cA, cB, cC, cD]
            rw [e]; simp only [mem_cons_iff, ih h3]
            constructor
            · rintro (h | h | h)
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr h)
              · exact Or.inr h
            · rintro ((h | h) | h)
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)

theorem mem_insert_self {lo : Nat} {l : List Rng} (hw : wfFrom lo l = true) (n : Nat) :
    mem (insert l n) n = true := (mem_insert hw n n).mpr (Or.inr rfl)

theorem mem_insert_mono {lo : Nat} {l : List Rng} (hw : wfFrom lo l = true) (n : Nat) {m : Nat}
    (h : mem l m = true) : mem (insert l n) m = true := (mem_insert hw n m).mpr (Or.inl h)

/-- Is the whole range `r` already recorded?  Because the recorded ranges are
    disjoint and non-adjacent, a contiguous range is covered exactly when one
    recorded range covers it. -/
def subsetOf (r : Rng) (l : List Rng) : Bool :=
  l.any (fun r' => decide (r'.lo ≤ r.lo) && decide (r.hi ≤ r'.hi))

theorem mem_of_subsetOf {r : Rng} {l : List Rng} (h : subsetOf r l = true) {n : Nat}
    (h1 : r.lo ≤ n) (h2 : n ≤ r.hi) : mem l n = true := by
  simp only [subsetOf, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨r', hr', hl, hh⟩ := h
  exact mem_of_mem_list hr' (by omega) (by omega)

end Ranges

end Quic.Spec.Ack
