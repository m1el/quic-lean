import QuicModel.Spec.FrameRules

/-
  WP3 (b): per packet-number-space receive tracking (§12.3 duplicate
  suppression), the acknowledgment rules of §13.1 and the generation rules of
  §13.2.

  Text: draft-ietf-quic-transport-34, lines 4709–4713 (§12.3), 5018–5324
  (§13.1, §13.2.1–§13.2.7), with the ACK frame arithmetic of §19.3.1.

  Table 3 and the packet-type legality of frames are in
  `QuicModel/Spec/FrameRules.lean`.

  Exported for the composed endpoint (WP12) and for Termination (WP6):
  `ackOverdue` / `AckObligationMet` / `EventuallyAcknowledged` — §13.2.1's MUST
  and SHOULD are about *sending* an acknowledgment, which no single step can
  force — and `pnExhausted`, §12.3's silent close once a packet number space is
  spent.
-/
namespace Quic.Spec.Ack

/-! ## 0. The set of received packet numbers

§13.2.3, line 5176: "When an ACK frame is sent, one or more ranges of
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

theorem wfFrom_zero_of_wf {l : List Rng} (h : wf l = true) : wfFrom 0 l = true := h

theorem mem_of_subsetOf {r : Rng} {l : List Rng} (h : subsetOf r l = true) {n : Nat}
    (h1 : r.lo ≤ n) (h2 : n ≤ r.hi) : mem l n = true := by
  simp only [subsetOf, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨r', hr', hl, hh⟩ := h
  exact mem_of_mem_list hr' (by omega) (by omega)

end Ranges

/-! ## 0c. What an ACK frame acknowledges (§19.3.1) -/

/-- §12.3, line 4636: "The packet number is an integer in the range 0 to
    2^62-1." -/
def maxPn : Nat := 2 ^ 62 - 1

/-- §19.3.1, lines 7358 and 7373: "smallest = largest - ack_range" and
    "largest = previous_smallest - gap - 2".  `none` when a computed packet
    number would be negative — line 7375: "If any computed packet number is
    negative, an endpoint MUST generate a connection error of type
    FRAME_ENCODING_ERROR." -/
def ackedAux (smallest : Nat) : List AckRange → Option (List Rng)
  | [] => some []
  | r :: rs =>
    if smallest < r.gap + 2 then none
    else if smallest - r.gap - 2 < r.len then none
    else (ackedAux (smallest - r.gap - 2 - r.len) rs).map
      (fun l => ⟨smallest - r.gap - 2 - r.len, smallest - r.gap - 2⟩ :: l)

/-- The packet numbers an ACK frame acknowledges, largest range first.
    §19.3, line 7299: "That is, the smallest packet acknowledged in the range is
    determined by subtracting the First ACK Range value from the Largest
    Acknowledged." -/
def acked (largest first : Nat) (rs : List AckRange) : Option (List Rng) :=
  if largest < first then none
  else (ackedAux (largest - first) rs).map (fun l => ⟨largest - first, largest⟩ :: l)

/-- This ACK frame acknowledges packet number `n`. -/
def Acks (largest first : Nat) (rs : List AckRange) (n : Nat) : Prop :=
  ∃ l, acked largest first rs = some l ∧ Ranges.mem l n = true

private theorem isSome_map {α β : Type} (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by cases o <;> rfl

/-- The arithmetic agrees with `Frame.check`'s, which is what the wire decoder
    and the C implementation use. -/
theorem ackedAux_isSome_iff (smallest : Nat) (rs : List AckRange) :
    (ackedAux smallest rs).isSome = true ↔ checkAckRanges smallest rs = none := by
  induction rs generalizing smallest with
  | nil => simp [ackedAux, checkAckRanges]
  | cons r rs ih =>
    simp only [ackedAux, checkAckRanges]
    by_cases c1 : smallest < r.gap + 2
    · simp [c1]
    · by_cases c2 : smallest - r.gap - 2 < r.len
      · simp [c1, c2]
      · simp only [c1, c2, ite_false, isSome_map, ih]

theorem acked_isSome_iff_check (largest delay first : Nat) (ranges : Array AckRange)
    (ecn : Option Ecn) :
    (acked largest first ranges.toList).isSome = true ↔
      Frame.check (.ack largest delay first ranges ecn) = none := by
  by_cases c : largest < first
  · simp [acked, Frame.check, c]
  · simp only [acked, Frame.check, c, ite_false, isSome_map, ackedAux_isSome_iff]

/-! ## 1. State, events, effects

One instance per packet number space (§12.3, line 4662: "Packet numbers are
divided into 3 spaces in QUIC"). -/

/-- The largest packet number seen once `pn` is added. -/
def maxOpt : Option Nat → Nat → Nat
  | none, pn => pn
  | some m, pn => max m pn

theorem le_maxOpt (o : Option Nat) (pn : Nat) : pn ≤ maxOpt o pn := by
  cases o <;> simp only [maxOpt] <;> omega

theorem le_maxOpt_of_eq {o : Option Nat} {m : Nat} (h : o = some m) (pn : Nat) :
    m ≤ maxOpt o pn := by subst h; simp only [maxOpt]; omega

structure State where
  /-- Which packet number space this instance tracks (§12.3, line 4662). -/
  space : PnSpace
  /-- §12.3, line 4709: the packet numbers already processed in this space. -/
  received : List Rng
  /-- §12.3, line 4717: "The data required for detecting duplicates can be
      limited by maintaining a minimum packet number below which all packets are
      immediately dropped."  `0` means no minimum is maintained.  Raised by
      `Event.raiseMinimum`; `received` is *not* pruned with it, so the model
      keeps at least as much information as the implementation it follows. -/
  minPn : Nat
  /-- §13.2.3, line 5218: "they MUST retain the largest packet number that has
      been successfully processed". -/
  largest : Option Nat
  /-- §13.2.5, line 5271: when the packet with the largest packet number was
      received; the basis of the ACK Delay field. -/
  largestTime : Time
  /-- The largest ack-eliciting packet number received (§13.2.1, line 5101). -/
  largestAckEliciting : Option Nat
  /-- §13.2.1, line 5075: the ack-eliciting packets received in this space and
      not yet acknowledged, each with the time it arrived.  This is the
      *obligation*: every entry must be acknowledged by its own deadline, so the
      deadline of the state is the earliest of them.  It is deliberately not a
      single flag and not `largestTime`: a later packet must never be able to
      postpone an earlier packet's deadline, and a partial ACK must discharge
      only what it covers. -/
  outstanding : List (Nat × Time)
  /-- §13.2.1, line 5101: reordering or a gap was seen, so an ACK should go out
      without delay. -/
  ackImmediately : Bool
  /-- §13.1, line 5030: the largest packet number we have sent in this space. -/
  largestSent : Option Nat
  /-- §18.2: the max_ack_delay we advertised, in microseconds. -/
  maxAckDelay : Time
  /-- §17.1, line 6023: the largest of *our* packet numbers the peer has
      acknowledged in this space; `none` "prior to receiving an
      acknowledgment".  Only the size of a packet number encoding depends on
      it (`maySendPacketNumberSize`). -/
  largestAcked : Option Nat := none
  deriving DecidableEq, Repr

/-- §13.2, line 5048: "only ack-eliciting packets cause an ACK frame to be sent
    within the maximum ack delay".  Derived from `outstanding` rather than
    stored, so that it cannot disagree with it. -/
def State.ackElicitingPending (s : State) : Bool := !s.outstanding.isEmpty

/-- §13.2.2, line 5163: "A receiver SHOULD send an ACK frame after receiving at
    least two ack-eliciting packets."  Counted as the ack-eliciting packets
    still awaiting acknowledgement; see NOTE 9. -/
def State.ackElicitingSinceAck (s : State) : Nat := s.outstanding.length

/-- The earliest arrival time among a set of outstanding packets. -/
def minArrival : List (Nat × Time) → Option Time
  | [] => none
  | (_, t) :: ps => some (match minArrival ps with | none => t | some t' => min t t')

@[simp] theorem minArrival_nil : minArrival [] = none := rfl

theorem minArrival_eq_none_iff {l : List (Nat × Time)} : minArrival l = none ↔ l = [] := by
  cases l <;> simp [minArrival]

theorem minArrival_mem {l : List (Nat × Time)} {m : Time} (h : minArrival l = some m) :
    ∃ pn, (pn, m) ∈ l := by
  induction l with
  | nil => simp [minArrival] at h
  | cons p ps ih =>
    obtain ⟨pn0, t0⟩ := p
    cases hps : minArrival ps with
    | none =>
      simp only [minArrival, hps] at h
      exact ⟨pn0, by rw [← Option.some.inj h]; exact List.mem_cons_self ..⟩
    | some t' =>
      simp only [minArrival, hps] at h
      have hv : min t0 t' = m := Option.some.inj h
      rcases Nat.le_total t0 t' with hle | hle
      · have ht : t0 = m := by omega
        subst ht
        exact ⟨pn0, List.mem_cons_self ..⟩
      · have ht : t' = m := by omega
        subst ht
        obtain ⟨pn, hpn⟩ := ih hps
        exact ⟨pn, List.mem_cons_of_mem _ hpn⟩

theorem minArrival_le_of_mem {l : List (Nat × Time)} {pn : Nat} {t : Time}
    (h : (pn, t) ∈ l) : ∃ m, minArrival l = some m ∧ m ≤ t := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨pn0, t0⟩ := p
    rw [List.mem_cons] at h
    cases hps : minArrival ps with
    | none =>
      refine ⟨t0, by simp [minArrival, hps], ?_⟩
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h; omega
      · rw [minArrival_eq_none_iff.mp hps] at h; simp at h
    | some t' =>
      refine ⟨min t0 t', by simp [minArrival, hps], ?_⟩
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h; omega
      · obtain ⟨m, hm, hle⟩ := ih h
        rw [hps] at hm
        have := Option.some.inj hm
        omega

/-- Adding packets can only move the earliest arrival earlier. -/
theorem minArrival_mono {l l' : List (Nat × Time)} (hsub : ∀ p ∈ l, p ∈ l')
    {m : Time} (h : minArrival l = some m) : ∃ m', minArrival l' = some m' ∧ m' ≤ m := by
  obtain ⟨pn, hpn⟩ := minArrival_mem h
  exact minArrival_le_of_mem (hsub _ hpn)

/-- §13.2.1, line 5075: "An endpoint MUST acknowledge all ack-eliciting Initial
    and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT
    packets within its advertised max_ack_delay".  The moment by which a packet
    that arrived at `t` must have been acknowledged. -/
def State.ackDelayBudget (s : State) : Time :=
  match s.space with
  | .initial | .handshake => 0                  -- "immediately"
  | .appData => s.maxAckDelay

def State.deadlineOf (s : State) (t : Time) : Time := t + s.ackDelayBudget

theorem State.deadlineOf_mono (s : State) {t t' : Time} (h : t ≤ t') :
    s.deadlineOf t ≤ s.deadlineOf t' := by simp only [State.deadlineOf]; omega

def State.isNewLargest (s : State) (pn : Nat) : Bool :=
  match s.largest with
  | none => true
  | some m => decide (m < pn)

/-- §13.2.1, lines 5105 and 5108: the two situations in which an ACK frame
    should be generated without delay — the packet number is below one already
    received, or above it with missing packets in between. -/
def State.outOfOrder (s : State) (pn : Nat) : Bool :=
  match s.largestAckEliciting with
  | none => false
  | some m =>
    if pn < m then true
    else if m + 1 ≤ pn - 1 then !Ranges.subsetOf ⟨m + 1, pn - 1⟩ s.received
    else false

/-- Record a packet that has been fully processed (§13.1, line 5020).
    `largestTime` follows the largest packet number because §13.2.5, line 5271
    measures the ACK Delay field from *that* packet; the acknowledgement
    obligation is `outstanding`, which a later packet can only add to. -/
def State.record (s : State) (pn : Nat) (t : Time) (ae : Bool) : State :=
  { s with
    received := Ranges.insert s.received pn
    largest := some (maxOpt s.largest pn)
    largestTime := if s.isNewLargest pn then t else s.largestTime
    largestAckEliciting :=
      if ae then some (maxOpt s.largestAckEliciting pn) else s.largestAckEliciting
    outstanding := if ae then s.outstanding ++ [(pn, t)] else s.outstanding
    ackImmediately := s.ackImmediately || (ae && s.outOfOrder pn) }

/-- Discharge exactly the packets an ACK frame covers.  §19.3, line 7231:
    "Receivers send ACK frames (types 0x02 and 0x03) to inform senders of packets
    they have received and processed" — an ACK that names some of the outstanding packets settles
    those and no others. -/
def State.discharge (s : State) (l : List Rng) : State :=
  { s with
    outstanding := s.outstanding.filter (fun p => !Ranges.mem l p.1)
    ackImmediately :=
      s.ackImmediately && !(s.outstanding.filter (fun p => !Ranges.mem l p.1)).isEmpty }

/-- The state after we sent an ACK frame with these fields.  A frame whose
    ranges do not compute (§19.3.1, line 7375) is one we would never send and
    discharges nothing. -/
def State.afterAckSent (s : State) (largest first : Nat) (rs : List AckRange) : State :=
  match acked largest first rs with
  | none => s
  | some l => s.discharge l

@[simp] theorem State.record_outstanding (s : State) (pn : Nat) (t : Time) (ae : Bool) :
    (s.record pn t ae).outstanding =
      if ae then s.outstanding ++ [(pn, t)] else s.outstanding := rfl

@[simp] theorem State.record_deadlineOf (s : State) (pn : Nat) (t : Time) (ae : Bool)
    (u : Time) : (s.record pn t ae).deadlineOf u = s.deadlineOf u := rfl

@[simp] theorem State.discharge_outstanding (s : State) (l : List Rng) :
    (s.discharge l).outstanding = s.outstanding.filter (fun p => !Ranges.mem l p.1) := rfl

/-- Sending an ACK frame touches only the outstanding set and the
    "send one now" hint; everything the receive side records is untouched. -/
@[simp] theorem State.afterAckSent_received (s : State) (largest first : Nat)
    (rs : List AckRange) : (s.afterAckSent largest first rs).received = s.received := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_largest (s : State) (largest first : Nat)
    (rs : List AckRange) : (s.afterAckSent largest first rs).largest = s.largest := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_largestAckEliciting (s : State) (largest first : Nat)
    (rs : List AckRange) :
    (s.afterAckSent largest first rs).largestAckEliciting = s.largestAckEliciting := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_space (s : State) (largest first : Nat)
    (rs : List AckRange) : (s.afterAckSent largest first rs).space = s.space := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_maxAckDelay (s : State) (largest first : Nat)
    (rs : List AckRange) : (s.afterAckSent largest first rs).maxAckDelay = s.maxAckDelay := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_largestSent (s : State) (largest first : Nat)
    (rs : List AckRange) : (s.afterAckSent largest first rs).largestSent = s.largestSent := by
  unfold State.afterAckSent; split <;> rfl

theorem State.mem_outstanding_afterAckSent {s : State} {largest first : Nat}
    {rs : List AckRange} {p : Nat × Time}
    (h : p ∈ (s.afterAckSent largest first rs).outstanding) : p ∈ s.outstanding := by
  unfold State.afterAckSent at h
  split at h
  · exact h
  · rw [State.discharge_outstanding] at h
    exact (List.mem_filter.mp h).1

def bumpSent : Option Nat → Nat → Option Nat
  | none, pn => some pn
  | some m, pn => some (max m pn)

/-- §13.1, line 5030: as much of "an acknowledgment for a packet it did not
    send" as an endpoint that remembers only the largest packet number it has
    sent is "able to detect". -/
def acksUnsent (s : State) (largest : Nat) : Bool :=
  match s.largestSent with
  | none => true
  | some m => decide (m < largest)

/-- §17.1, line 6027: "After an acknowledgment is received for a packet number
    space".  An acknowledgment of a packet we did not send, which §13.1 lets an
    endpoint tolerate (`Step.ackOk`), acknowledges nothing we sent and is not
    counted — an endpoint that counted it would size its packet numbers
    against a number it never used. -/
def State.afterAckRecv (s : State) (largest : Nat) : State :=
  { s with largestAcked :=
      if acksUnsent s largest then s.largestAcked else bumpSent s.largestAcked largest }

inductive Event where
  /-- A packet numbered `pn` arrived at time `t`, protection was removed, and
      (if it is not a duplicate) its frames are processed. -/
  | recvPacket (pn : Nat) (t : Time) (ackEliciting : Bool)
  /-- An ACK frame carried in a packet of this space. -/
  | recvAck (largest first : Nat) (ranges : List AckRange)
  /-- We sent a packet numbered `pn` in this space. -/
  | sentPacket (pn : Nat)
  /-- We sent an ACK frame for this space, with these fields (§19.3). -/
  | sentAck (largest first : Nat) (ranges : List AckRange)
  /-- §12.3, line 4717: we choose to stop remembering packet numbers below
      `m`, and therefore to drop every packet below it. -/
  | raiseMinimum (m : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- §13.1, line 5020: the packet's frames have been processed and its number
      is now acknowledgeable. -/
  | processed (pn : Nat) (ackEliciting : Bool)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §12.3, line 4709: "A receiver MUST discard a newly unprotected packet
      unless it is certain that it has not processed another packet with the
      same packet number from the same packet number space." -/
  | duplicate {s pn t ae} (h : Ranges.mem s.received pn = true) :
      Step s (.recvPacket pn t ae) .drop
  /-- §12.3, line 4717: "The data required for detecting duplicates can be
      limited by maintaining a minimum packet number below which all packets
      are immediately dropped."  An endpoint that maintains such a minimum can
      no longer be "certain that it has not processed another packet with the
      same packet number" (line 4709), so it drops. -/
  | belowMinimum {s pn t ae} (h : Ranges.mem s.received pn = false) (h2 : pn < s.minPn) :
      Step s (.recvPacket pn t ae) .drop
  /-- §13.1, line 5020: "A packet MUST NOT be acknowledged until packet
      protection has been successfully removed and all frames contained in the
      packet have been processed."  Recording the packet number is what makes
      it acknowledgeable.  Permitted for any packet number not already
      processed, including one below the minimum: this model does not prune
      `received`, so it is still certain (see NOTE 3). -/
  | process {s pn t ae} (h : Ranges.mem s.received pn = false) :
      Step s (.recvPacket pn t ae) (.ok (s.record pn t ae) [.processed pn ae])
  /-- §19.3.1, line 7375: "If any computed packet number is negative, an
      endpoint MUST generate a connection error of type
      FRAME_ENCODING_ERROR." -/
  | ackMalformed {s largest first rs} (h : acked largest first rs = none) :
      Step s (.recvAck largest first rs) (.error .frameEncodingError)
  /-- §13.1, line 5030: "An endpoint SHOULD treat receipt of an acknowledgment
      for a packet it did not send as a connection error of type
      PROTOCOL_VIOLATION, if it is able to detect the condition." -/
  | ackUnsent {s largest first rs} (h : acked largest first rs ≠ none)
      (h2 : acksUnsent s largest = true) :
      Step s (.recvAck largest first rs) (.error .protocolViolation)
  /-- The same sentence is a SHOULD, so not raising the error is permitted too;
      and a well-formed ACK for packets we did send is simply processed (loss
      detection is [QUIC-RECOVERY], out of scope). -/
  | ackOk {s largest first rs} (h : acked largest first rs ≠ none) :
      Step s (.recvAck largest first rs) (.ok (s.afterAckRecv largest) [])
  /-- Bookkeeping for §13.1's "a packet it did not send". -/
  | sent {s pn} :
      Step s (.sentPacket pn) (.ok { s with largestSent := bumpSent s.largestSent pn } [])
  /-- §13.2.1, line 5075: sending an ACK frame discharges the obligation for
      exactly the packets that frame acknowledges — no more. -/
  | ackSent {s largest first rs} :
      Step s (.sentAck largest first rs) (.ok (s.afterAckSent largest first rs) [])
  /-- §12.3, line 4717: raising the minimum is always permitted — it is the
      "can" of that sentence — and never lowers it. -/
  | raiseMin {s m} :
      Step s (.raiseMinimum m) (.ok { s with minPn := max s.minPn m } [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvPacket pn t ae =>
    if Ranges.mem s.received pn then [.drop]
    else if pn < s.minPn then [.drop, .ok (s.record pn t ae) [.processed pn ae]]
    else [.ok (s.record pn t ae) [.processed pn ae]]
  | .recvAck largest first rs =>
    match acked largest first rs with
    | none => [.error .frameEncodingError]
    | some _ =>
      if acksUnsent s largest then [.error .protocolViolation, .ok (s.afterAckRecv largest) []]
      else [.ok (s.afterAckRecv largest) []]
  | .sentPacket pn => [.ok { s with largestSent := bumpSent s.largestSent pn } []]
  | .sentAck largest first rs => [.ok (s.afterAckSent largest first rs) []]
  | .raiseMinimum m => [.ok { s with minPn := max s.minPn m } []]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvPacket pn t ae =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .duplicate ‹_›
      · rename_i hd
        simp only [Bool.not_eq_true] at hd
        split at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .belowMinimum hd ‹_›
          · exact .process hd
        · simp only [List.mem_singleton] at h; subst h; exact .process hd
    | recvAck largest first rs =>
      simp only [outcomes] at h
      split at h
      · rename_i heq
        simp only [List.mem_singleton] at h; subst h; exact .ackMalformed heq
      · rename_i l heq
        have hne : acked largest first rs ≠ none := by rw [heq]; simp
        split at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .ackUnsent hne ‹_›
          · exact .ackOk hne
        · simp only [List.mem_singleton] at h; subst h; exact .ackOk hne
    | sentPacket pn => simp only [outcomes, List.mem_singleton] at h; subst h; exact .sent
    | sentAck largest first rs =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .ackSent
    | raiseMinimum m => simp only [outcomes, List.mem_singleton] at h; subst h; exact .raiseMin
  · intro h
    cases h with
    | duplicate h => simp [outcomes, h]
    | belowMinimum h h2 => simp [outcomes, h, h2]
    | @process pn t ae h =>
      by_cases hm : pn < s.minPn <;> simp [outcomes, h, hm]
    | @ackMalformed largest first rs h => simp [outcomes, h]
    | @ackUnsent largest first rs h h2 =>
      cases hac : acked largest first rs with
      | none => exact absurd hac h
      | some l => simp [outcomes, hac, h2]
    | @ackOk largest first rs h =>
      cases hac : acked largest first rs with
      | none => exact absurd hac h
      | some l =>
        by_cases hu : acksUnsent s largest = true <;> simp [outcomes, hac, hu]
    | sent => simp [outcomes]
    | ackSent => simp [outcomes]
    | raiseMin => simp [outcomes]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- The recorded packet numbers are a well-formed range set, and `largest` is
    really the largest of them (§13.2.3, line 5218). -/
def Inv (s : State) : Prop :=
  Ranges.wf s.received = true
  ∧ (∀ n, Ranges.mem s.received n = true → ∃ m, s.largest = some m ∧ n ≤ m)
  ∧ (∀ m, s.largest = some m → Ranges.mem s.received m = true)
  ∧ (∀ m, s.largestAckEliciting = some m → Ranges.mem s.received m = true)
  -- an outstanding acknowledgement obligation is always for a packet we
  -- actually processed (§13.1, line 5020)
  ∧ (∀ p ∈ s.outstanding, Ranges.mem s.received p.1 = true)

@[simp] theorem record_received (s : State) (pn : Nat) (t : Time) (ae : Bool) :
    (s.record pn t ae).received = Ranges.insert s.received pn := rfl

@[simp] theorem record_largest (s : State) (pn : Nat) (t : Time) (ae : Bool) :
    (s.record pn t ae).largest = some (maxOpt s.largest pn) := rfl

@[simp] theorem record_largestAE (s : State) (pn : Nat) (t : Time) (ae : Bool) :
    (s.record pn t ae).largestAckEliciting =
      if ae then some (maxOpt s.largestAckEliciting pn) else s.largestAckEliciting := rfl

/-- Whatever `maxOpt` picks is itself recorded once `pn` is inserted. -/
private theorem mem_insert_maxOpt {l : List Rng} (hw : Ranges.wf l = true) {o : Option Nat}
    (ho : ∀ m, o = some m → Ranges.mem l m = true) (pn : Nat) :
    Ranges.mem (Ranges.insert l pn) (maxOpt o pn) = true := by
  rcases o with _ | m0
  · exact Ranges.mem_insert_self (Ranges.wfFrom_zero_of_wf hw) pn
  · show Ranges.mem (Ranges.insert l pn) (max m0 pn) = true
    rcases Nat.le_total pn m0 with hle | hle
    · have he : max m0 pn = m0 := by omega
      rw [he]
      exact Ranges.mem_insert_mono (Ranges.wfFrom_zero_of_wf hw) pn (ho m0 rfl)
    · have he : max m0 pn = pn := by omega
      rw [he]
      exact Ranges.mem_insert_self (Ranges.wfFrom_zero_of_wf hw) pn

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hw, h2, h3, h4, h5⟩ := hi
  cases h with
  | @process pn t ae hp =>
    refine ⟨Ranges.wf_insert hw pn, ?_, ?_, ?_, ?_⟩
    · intro n hn
      refine ⟨maxOpt s.largest pn, rfl, ?_⟩
      rcases (Ranges.mem_insert (Ranges.wfFrom_zero_of_wf hw) pn n).mp hn with hn | hn
      · obtain ⟨m, hm, hnm⟩ := h2 n hn
        exact Nat.le_trans hnm (le_maxOpt_of_eq hm pn)
      · subst hn; exact le_maxOpt _ _
    · intro m hm
      rw [record_largest] at hm
      have : m = maxOpt s.largest pn := (Option.some.inj hm).symm
      subst this
      exact mem_insert_maxOpt hw h3 pn
    · intro m hm
      rw [record_largestAE] at hm
      split at hm
      · have : m = maxOpt s.largestAckEliciting pn := (Option.some.inj hm).symm
        subst this
        exact mem_insert_maxOpt hw h4 pn
      · exact Ranges.mem_insert_mono (Ranges.wfFrom_zero_of_wf hw) pn (h4 m hm)
    · intro p hp
      rw [State.record_outstanding] at hp
      split at hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact Ranges.mem_insert_mono (Ranges.wfFrom_zero_of_wf hw) pn (h5 p hp)
        · simp only [List.mem_singleton] at hp; subst hp
          exact Ranges.mem_insert_self (Ranges.wfFrom_zero_of_wf hw) pn
      · exact Ranges.mem_insert_mono (Ranges.wfFrom_zero_of_wf hw) pn (h5 p hp)
  | ackOk => exact ⟨hw, h2, h3, h4, h5⟩
  | sent => exact ⟨hw, h2, h3, h4, h5⟩
  | @ackSent largest first rs =>
    refine ⟨by rw [State.afterAckSent_received]; exact hw, ?_, ?_, ?_, ?_⟩
    · intro n hn
      rw [State.afterAckSent_received] at hn
      rw [State.afterAckSent_largest]
      exact h2 n hn
    · intro m hm
      rw [State.afterAckSent_largest] at hm
      rw [State.afterAckSent_received]
      exact h3 m hm
    · intro m hm
      rw [State.afterAckSent_largestAckEliciting] at hm
      rw [State.afterAckSent_received]
      exact h4 m hm
    · intro p hp
      rw [State.afterAckSent_received]
      exact h5 p (State.mem_outstanding_afterAckSent hp)
  | raiseMin => exact ⟨hw, h2, h3, h4, h5⟩

/-! ## 6. Send side -/

/-- What an ACK frame carried in a packet of *this* space may say.

* §19.3.1, line 7375: no computed packet number may be negative.
* §13.1, line 5026: "a receiver acknowledges receipt by sending one or more ACK
  frames containing the packet number of the received packet" — every
  acknowledged packet number must be one we received and processed.

Non-ACK frames are unconstrained. -/
def AckFrameSendable (s : State) : Frame → Prop
  | .ack largest _ first ranges _ =>
    ∃ l, acked largest first ranges.toList = some l
        ∧ ∀ r ∈ l, Ranges.subsetOf r s.received = true
  | _ => True

def ackFrameSendable (s : State) : Frame → Bool
  | .ack largest _ first ranges _ =>
    match acked largest first ranges.toList with
    | none => false
    | some l => l.all (fun r => Ranges.subsetOf r s.received)
  | _ => true

theorem ackFrameSendable_iff (s : State) (f : Frame) :
    ackFrameSendable s f = true ↔ AckFrameSendable s f := by
  cases f
  case ack largest delay first ranges ecn =>
    simp only [ackFrameSendable, AckFrameSendable]
    cases h : acked largest first ranges.toList with
    | none => simp
    | some l => simp [List.all_eq_true]
  all_goals simp [ackFrameSendable, AckFrameSendable]

/-- Nothing about a single frame can be decided without knowing which packet
    number space the packet belongs to, and `Component.MaySend` does not see
    one.  With one instance of this component per space (§12.3, line 4662),
    a frame-only predicate would have to hold in *all three* instances, which
    would forbid every ACK frame; the rule is therefore in `MaySendPacket`,
    which is handed the real `OutPacket.ptype`. -/
def MaySend (_ : State) (_ : Frame) : Prop := True

@[noinline]
def maySend (_ : State) (_ : Frame) : Bool := true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-- §12.3, line 4685: "Subsequent packets sent in the same packet number space
    MUST increase the packet number by at least one."; line 4692: "A QUIC
    endpoint MUST NOT reuse a packet number within the same packet number space
    in one connection."; line 4693: "If the packet number for sending reaches
    2^62 - 1, the sender MUST close the connection without sending a
    CONNECTION_CLOSE frame or any further packets" — the number at which the
    text requires stopping is itself unusable, so the bound is `pn < maxPn`.
    The silent close belongs to WP6 Termination. -/
def maySendPacketNumber (s : State) (pn : Nat) : Bool :=
  (match s.largestSent with | none => true | some m => decide (m < pn)) && decide (pn < maxPn)

/-- §17.1, line 6023: "Prior to receiving an acknowledgment for a packet number
    space, the full packet number MUST be included; it is not to be truncated
    as described below."; line 6027: "After an acknowledgment is received for a
    packet number space, the sender MUST use a packet number size able to
    represent more than twice as large a range than the difference between the
    largest acknowledged packet and packet number being sent."  `len` is the
    size in bytes, 1 to 4 (line 6015). -/
def maySendPacketNumberSize (s : State) (pn len : Nat) : Bool :=
  decide (1 ≤ len ∧ len ≤ 4) &&
    match s.largestAcked with
    | none => decide (pn < 2 ^ (8 * len))
    | some a => decide (2 * (pn - a) < 2 ^ (8 * len))

/-- §12.3, line 4693: the packet number for sending has reached 2^62 - 1, so
    this space is spent and the connection must close silently.  Exported for
    WP6 (the close) and WP12 (the composition). -/
def pnExhausted (s : State) : Bool :=
  match s.largestSent with
  | none => false
  | some m => decide (maxPn ≤ m + 1)

/-- The whole packet we are about to send, as far as *this* space is concerned.
    A packet of another space says nothing about this instance.

* §12.3, line 4693: "If the packet number for sending reaches 2^62 - 1, the
  sender MUST close the connection without sending a CONNECTION_CLOSE frame or
  any further packets" — once this space is spent, no packet of it goes out.  `OutPacket`
  carries no packet number, so the per-number rule stays in
  `maySendPacketNumber`.
* §13.2.6, line 5293: "ACK frames MUST only be carried in a packet that has the
  same packet number space as the packet being acknowledged" — an ACK frame in
  a packet of this space is checked against *this* space's `received`, which is
  exactly that rule. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  p.ptype.space = some s.space →
    pnExhausted s = false ∧ ∀ f ∈ p.frames, AckFrameSendable s f

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  !decide (p.ptype.space = some s.space)
    || (!pnExhausted s && p.frames.all (fun f => ackFrameSendable s f))

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  simp only [maySendPacket, MaySendPacket, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true]
  constructor
  · rintro (h | ⟨h1, h2⟩) hsp
    · exact absurd hsp h
    · exact ⟨h1, fun f hf => (ackFrameSendable_iff _ _).mp (h2 f hf)⟩
  · intro h
    by_cases hsp : p.ptype.space = some s.space
    · obtain ⟨h1, h2⟩ := h hsp
      exact Or.inr ⟨h1, fun f hf => (ackFrameSendable_iff _ _).mpr (h2 f hf)⟩
    · exact Or.inl hsp

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

/-! ## 8. Named theorems -/

/-- (b) An ACK frame we may send never acknowledges a packet number we have not
    received: §13.1, line 5020 ("A packet MUST NOT be acknowledged until … all
    frames contained in the packet have been processed"). -/
theorem ackFrameSendable_sound {s : State} {largest delay first : Nat} {ranges : Array AckRange}
    {ecn : Option Ecn} (h : AckFrameSendable s (.ack largest delay first ranges ecn)) {n : Nat}
    (hn : Acks largest first ranges.toList n) : Ranges.mem s.received n = true := by
  obtain ⟨l, hl, hsub⟩ := h
  obtain ⟨l', hl', hmem⟩ := hn
  rw [hl] at hl'
  have : l = l' := Option.some.inj hl'
  subst this
  obtain ⟨r, hr, h1, h2⟩ := Ranges.exists_of_mem hmem
  exact Ranges.mem_of_subsetOf (hsub r hr) h1 h2

/-- (b), at packet level and with the real packet type: every packet number an
    ACK frame in a packet of this space acknowledges is one this space
    processed — which is also §13.2.6, line 5293 ("ACK frames MUST only be
    carried in a packet that has the same packet number space as the packet
    being acknowledged"). -/
theorem maySendPacket_ack_sound {s : State} {p : OutPacket} (h : MaySendPacket s p)
    (hsp : p.ptype.space = some s.space)
    {largest delay first : Nat} {ranges : Array AckRange} {ecn : Option Ecn}
    (hf : Frame.ack largest delay first ranges ecn ∈ p.frames)
    {n : Nat} (hn : Acks largest first ranges.toList n) : Ranges.mem s.received n = true :=
  ackFrameSendable_sound ((h hsp).2 _ hf) hn

/-- §13.2.3, line 5213: "A receiver MUST retain an ACK Range unless it can
    ensure that it will not subsequently accept packets with numbers in that
    range."  Nothing in this model ever forgets a packet number. -/
theorem received_mono {s s' : State} {e : Event} {fx : List Effect} (hi : Inv s)
    (h : Step s e (.ok s' fx)) {n : Nat} (hm : Ranges.mem s.received n = true) :
    Ranges.mem s'.received n = true := by
  cases h with
  | process hp => exact Ranges.mem_insert_mono (Ranges.wfFrom_zero_of_wf hi.1) _ hm
  | ackOk => exact hm
  | sent => exact hm
  | ackSent => rw [State.afterAckSent_received]; exact hm
  | raiseMin => exact hm

/-- §13.2.3, line 5218: "Receivers can discard all ACK Ranges, but they MUST
    retain the largest packet number that has been successfully processed". -/
theorem largest_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) {m : Nat} (hm : s.largest = some m) :
    ∃ m', s'.largest = some m' ∧ m ≤ m' := by
  cases h with
  | @process pn t ae hp => exact ⟨maxOpt s.largest pn, rfl, le_maxOpt_of_eq hm pn⟩
  | ackOk => exact ⟨m, hm, Nat.le_refl _⟩
  | sent => exact ⟨m, hm, Nat.le_refl _⟩
  | ackSent => exact ⟨m, by rw [State.afterAckSent_largest]; exact hm, Nat.le_refl _⟩
  | raiseMin => exact ⟨m, hm, Nat.le_refl _⟩

/-- §12.3, line 4717: the minimum packet number never goes down, so a packet
    number this endpoint has started dropping is never accepted again. -/
theorem minPn_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.minPn ≤ s'.minPn := by
  cases h with
  | process => exact Nat.le_refl _
  | ackOk => exact Nat.le_refl _
  | sent => exact Nat.le_refl _
  | ackSent =>
    show s.minPn ≤ (s.afterAckSent _ _ _).minPn
    unfold State.afterAckSent; split <;> exact Nat.le_refl _
  | @raiseMin m => exact Nat.le_max_left _ _

/-- §17.1's "largest acknowledged packet" is a packet that was sent: what the
    size rule is measured against never runs ahead of `largestSent`.  Not part
    of `Inv` (nothing in this component needs it); `Endpoint`'s
    `decode_of_maySendNumber` does. -/
def AckedWasSent (s : State) : Prop :=
  ∀ k ∈ s.largestAcked, ∃ m, s.largestSent = some m ∧ k ≤ m

theorem ackedWasSent_step {s s' : State} {e : Event} {fx : List Effect}
    (hi : AckedWasSent s) (h : Step s e (.ok s' fx)) : AckedWasSent s' := by
  cases h with
  | process => exact hi
  | @ackOk largest first rs _ =>
    intro k hk
    simp only [State.afterAckRecv] at hk ⊢
    cases hu : acksUnsent s largest with
    | true => rw [hu] at hk; exact hi k hk
    | false =>
      rw [hu] at hk
      simp only [Bool.false_eq_true, ↓reduceIte] at hk
      cases hs : s.largestSent with
      | none => simp [acksUnsent, hs] at hu
      | some m =>
        have hlm : largest ≤ m := by simpa [acksUnsent, hs] using hu
        refine ⟨m, rfl, ?_⟩
        cases ha : s.largestAcked with
        | none =>
          simp only [ha, bumpSent, Option.mem_def, Option.some.injEq] at hk
          omega
        | some a =>
          obtain ⟨m', hm', ham⟩ := hi a (by simp [ha])
          have : m' = m := by rw [hs] at hm'; exact (Option.some.inj hm').symm
          simp only [ha, bumpSent, Option.mem_def, Option.some.injEq] at hk
          omega
  | @sent pn =>
    intro k hk
    obtain ⟨m, hm, hkm⟩ := hi k hk
    exact ⟨max m pn, by simp [hm, bumpSent], Nat.le_trans hkm (Nat.le_max_left _ _)⟩
  | @ackSent largest first rs =>
    intro k hk
    have hA : (s.afterAckSent largest first rs).largestAcked = s.largestAcked := by
      unfold State.afterAckSent; split <;> rfl
    rw [hA] at hk
    rw [State.afterAckSent_largestSent]
    exact hi k hk
  | raiseMin => exact hi

/-- A packet number is only ever added by processing a packet — §13.1: it is
    the processing of the packet that makes it acknowledgeable. -/
theorem received_changes_only_on_recvPacket {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hne : s'.received ≠ s.received) :
    ∃ pn t ae, e = .recvPacket pn t ae := by
  cases h with
  | @process pn t ae hp => exact ⟨pn, t, ae, rfl⟩
  | ackOk => exact absurd rfl hne
  | sent => exact absurd rfl hne
  | ackSent => exact absurd (State.afterAckSent_received ..) hne
  | raiseMin => exact absurd rfl hne

theorem reachable_received_mono {s₀ s : State} (hi : Inv s₀)
    (h : component.Reachable s₀ s) {n : Nat} (hm : Ranges.mem s₀.received n = true) :
    Ranges.mem s.received n = true := by
  refine Component.Reachable.rec
    (motive := fun (x : State) (_ : component.Reachable s₀ x) =>
      Ranges.mem x.received n = true) hm ?_ h
  intro a b e fx hr hs ih
  exact received_mono (component.inv_of_reachable hi hr) hs ih

/-- (c) §12.3, line 4709: a packet number is processed at most once per space.
    Once a packet numbered `pn` has been processed, every later receipt of `pn`
    in any reachable state is discarded. -/
theorem processed_at_most_once {s s' s'' : State} {pn : Nat} {t t' : Time} {ae ae' : Bool}
    {fx : List Effect} (hi : Inv s)
    (h1 : Step s (.recvPacket pn t ae) (.ok s' fx))
    (hr : component.Reachable s' s'')
    {o : Out} (h2 : Step s'' (.recvPacket pn t' ae') o) : o = .drop := by
  have hi' : Inv s' := step_inv s _ s' fx hi h1
  have hmem : Ranges.mem s'.received pn = true := by
    cases h1 with
    | process hp => exact Ranges.mem_insert_self (Ranges.wfFrom_zero_of_wf hi.1) pn
  have hmem'' : Ranges.mem s''.received pn = true := reachable_received_mono hi' hr hmem
  cases h2 with
  | duplicate => rfl
  | belowMinimum => rfl
  | process hp => rw [hmem''] at hp; exact absurd hp (by simp)

/-- §13.2.6, line 5298: "Packets that a client sends with 0-RTT packet
    protection MUST be acknowledged by the server in packets protected by 1-RTT
    keys."  Proved from the two components together: `PacketType.space` puts
    only 0-RTT and 1-RTT in the application data space, and Table 3 keeps ACK
    out of a 0-RTT packet (`FrameRules.ack_not_in_zeroRtt`), so the only packet
    type left is 1-RTT. -/
theorem appData_ack_in_oneRtt {s : State} {fs : FrameRules.State} {p : OutPacket}
    (hsp : s.space = .appData) (hp : p.ptype.space = some s.space)
    (hfr : FrameRules.MaySendPacket fs p)
    {largest delay first : Nat} {ranges : Array AckRange} {ecn : Option Ecn}
    (hack : Frame.ack largest delay first ranges ecn ∈ p.frames) : p.ptype = .oneRtt := by
  have hallow := (hfr.2 _ hack).1
  rw [hsp] at hp
  cases hc : p.ptype with
  | initial => rw [hc] at hp; simp [PacketType.space] at hp
  | zeroRtt =>
    rw [hc, FrameRules.ack_not_in_zeroRtt] at hallow
    exact Bool.noConfusion hallow
  | handshake => rw [hc] at hp; simp [PacketType.space] at hp
  | oneRtt => rfl
  | retry => rw [hc] at hp; simp [PacketType.space] at hp
  | versionNegotiation => rw [hc] at hp; simp [PacketType.space] at hp

/-! ### §13.2 acknowledgment frequency: recommendations, not requirements -/

/-- The SHOULDs and MAYs of §13.2 that only *recommend* a moment to send an ACK
    frame.  They are deliberately outside `Step` and `MaySend`: an endpoint that
    ignores them still conforms.  `sendAckNow` is the decision to emit an ACK
    frame for this space right now; `sendingPacket` says a packet is going out
    anyway. -/
structure Recommended (s : State) (sendingPacket sendAckNow : Bool) : Prop where
  /-- §13.2.2, line 5163: "A receiver SHOULD send an ACK frame after receiving
      at least two ack-eliciting packets." -/
  twoAckEliciting : 2 ≤ s.ackElicitingSinceAck → sendAckNow = true
  /-- §13.2.1, line 5101: "an endpoint SHOULD generate and send an ACK frame
      without delay when it receives an ack-eliciting packet either: * when the
      received packet has a packet number less than another ack-eliciting packet
      that has been received, or * when the packet has a packet number larger
      than the highest-numbered ack-eliciting packet that has been received and
      there are missing packets between that packet and this packet." -/
  immediate : s.ackImmediately = true → sendAckNow = true
  /-- §13.2, line 5052: "When sending a packet for any reason, an endpoint
      SHOULD attempt to include an ACK frame if one has not been sent
      recently."  §13.2.1, line 5125: "An endpoint SHOULD send an ACK frame
      with other frames when there are new ack-eliciting packets to
      acknowledge."  The next sentence is the MAY that balances it — "When
      only non-ack-eliciting packets need to be acknowledged, an endpoint MAY
      wait until an ack-eliciting packet has been received to include an ACK
      frame with outgoing frames" — which is why this clause fires only when
      an ack-eliciting packet is pending. -/
  withOtherFrames : sendingPacket = true → s.ackElicitingPending = true → sendAckNow = true

/-- §13.2.3, line 5223: "A receiver SHOULD include an ACK Range containing the
    largest received packet number in every ACK frame." -/
def RecommendedAck (s : State) (largest : Nat) : Prop := s.largest = some largest

/-! ### §13.2 requirements that are properties of a trace, not of one step -/

/-- §13.2.1, line 5075: "An endpoint MUST acknowledge all ack-eliciting Initial
    and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT
    packets within its advertised max_ack_delay, with the following exception."
    The exception (line 5078) is buffering for want of keys, which is WP11's.

    The deadline of a state is the earliest deadline of its outstanding
    packets: a packet that arrives later can add an earlier obligation but can
    never postpone one (`ackDeadline_record_le`), and it is `none` exactly when
    nothing is owed. -/
def ackDeadline (s : State) : Option Time := (minArrival s.outstanding).map s.deadlineOf

/-- The same MUST, as a property of the moment an ACK frame is sent. -/
def AcknowledgedInTime (s : State) (sentAt tolerance : Time) : Prop :=
  ∀ d, ackDeadline s = some d → sentAt ≤ d + tolerance

/-- §13.2.1, line 5075, as a property of a state and a clock reading: an
    ack-eliciting packet is past its deadline and still unacknowledged.

    `tolerance` is the processing time the checker allows the implementation.
    §13.2.1's "immediately" is a *zero intentional delay* — §13.2.5, line 5271
    measures "the delays intentionally introduced" — not a zero elapsed time,
    and this model has no notion of what an endpoint costs to run.  With
    `tolerance = 0` the predicate is the literal text; for the Initial and
    Handshake spaces, where `ackDelayBudget = 0`, a checker must supply a
    positive tolerance or the predicate is unsatisfiable for any real
    endpoint. -/
def ackOverdue (s : State) (now tolerance : Time) : Bool :=
  match ackDeadline s with
  | none => false
  | some d => decide (d + tolerance < now)

def AckOverdue (s : State) (now tolerance : Time) : Prop :=
  ∃ d, ackDeadline s = some d ∧ d + tolerance < now

theorem ackOverdue_iff (s : State) (now tolerance : Time) :
    ackOverdue s now tolerance = true ↔ AckOverdue s now tolerance := by
  simp only [ackOverdue, AckOverdue]
  cases h : ackDeadline s with
  | none => simp
  | some d => simp

theorem acknowledgedInTime_iff (s : State) (sentAt tolerance : Time) :
    AcknowledgedInTime s sentAt tolerance ↔ ackOverdue s sentAt tolerance = false := by
  simp only [AcknowledgedInTime, ackOverdue]
  cases h : ackDeadline s with
  | none => simp
  | some d => simp [Nat.not_lt]

/-- The obligation that no single step can express and that WP12 must carry:
    §13.2.1, line 5075's MUST is about *sending* an acknowledgment, so a
    deadline checked only when an ACK happens to go out does not force one to
    go out.  A timed run is a sequence of (state, clock) observations; the
    endpoint conforms only if no observation is overdue. -/
def AckObligationMet (run : List (State × Time)) (tolerance : Time) : Prop :=
  ∀ p ∈ run, ackOverdue p.1 p.2 tolerance = false

/-- §13.2.1, line 5064: "Every packet SHOULD be acknowledged at least once".
    The MUST half of that sentence is `ackDeadline`; this is the SHOULD half,
    which covers non-ack-eliciting packets too and is a liveness property of a
    whole run, not of a state.  `acksSent` is every ACK frame this space has
    emitted, as `(largest, first, ranges)`. -/
def EventuallyAcknowledged (s : State) (acksSent : List (Nat × Nat × List AckRange)) : Prop :=
  ∀ n, Ranges.mem s.received n = true → ∃ a ∈ acksSent, Acks a.1 a.2.1 a.2.2 n

@[simp] theorem State.afterAckSent_ackDelayBudget (s : State) (largest first : Nat)
    (rs : List AckRange) :
    (s.afterAckSent largest first rs).ackDelayBudget = s.ackDelayBudget := by
  unfold State.afterAckSent; split <;> rfl

@[simp] theorem State.afterAckSent_deadlineOf (s : State) (largest first : Nat)
    (rs : List AckRange) (u : Time) :
    (s.afterAckSent largest first rs).deadlineOf u = s.deadlineOf u := by
  simp [State.deadlineOf]

/-! ### The acknowledgment obligation, pinned down -/

/-- `ackElicitingPending` is exactly "something is still owed": it is derived
    from `outstanding`, not stored beside it. -/
theorem ackElicitingPending_iff (s : State) :
    s.ackElicitingPending = true ↔ s.outstanding ≠ [] := by
  simp [State.ackElicitingPending]

theorem ackDeadline_eq_none_iff (s : State) : ackDeadline s = none ↔ s.outstanding = [] := by
  rw [← minArrival_eq_none_iff]
  unfold ackDeadline
  cases minArrival s.outstanding <;> simp

/-- Every outstanding ack-eliciting packet is covered: the state's deadline is
    at or before the deadline of that packet on its own.  Nothing can be
    forgotten while it is still outstanding. -/
theorem ackDeadline_le_deadlineOf {s : State} {pn : Nat} {t : Time}
    (h : (pn, t) ∈ s.outstanding) : ∃ d, ackDeadline s = some d ∧ d ≤ s.deadlineOf t := by
  obtain ⟨m, hm, hle⟩ := minArrival_le_of_mem h
  refine ⟨s.deadlineOf m, ?_, s.deadlineOf_mono hle⟩
  unfold ackDeadline; rw [hm]; rfl

/-- (i) §13.2.1, line 5075: receiving a further packet can only bring the
    acknowledgment deadline *forward*, never postpone it.  This is the property
    the `largestTime`-based deadline broke: a later non-ack-eliciting packet
    used to move an earlier ack-eliciting packet's deadline out. -/
theorem ackDeadline_record_le (s : State) (pn : Nat) (t : Time) (ae : Bool) {d : Time}
    (h : ackDeadline s = some d) :
    ∃ d', ackDeadline (s.record pn t ae) = some d' ∧ d' ≤ d := by
  simp only [ackDeadline, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  have hsub : ∀ p ∈ s.outstanding, p ∈ (s.record pn t ae).outstanding := by
    intro p hp
    rw [State.record_outstanding]
    split
    · exact List.mem_append_left _ hp
    · exact hp
  obtain ⟨m', hm', hle⟩ := minArrival_mono hsub hm
  refine ⟨s.deadlineOf m', ?_, s.deadlineOf_mono hle⟩
  unfold ackDeadline; rw [hm']; rfl

/-- (ii) §13.2.1, line 5075: an ACK frame discharges exactly the outstanding
    packets it acknowledges, and no others. -/
theorem outstanding_afterAckSent {s : State} {largest first : Nat} {rs : List AckRange}
    {l : List Rng} (h : acked largest first rs = some l) :
    (s.afterAckSent largest first rs).outstanding =
      s.outstanding.filter (fun p => !Ranges.mem l p.1) := by
  unfold State.afterAckSent; rw [h]; rfl

theorem mem_outstanding_afterAckSent {s : State} {largest first : Nat} {rs : List AckRange}
    {l : List Rng} (h : acked largest first rs = some l) (p : Nat × Time) :
    p ∈ (s.afterAckSent largest first rs).outstanding ↔
      (p ∈ s.outstanding ∧ Ranges.mem l p.1 = false) := by
  rw [outstanding_afterAckSent h, List.mem_filter]
  simp

/-- A partial ACK leaves the rest owed: an outstanding packet the frame does
    not cover is still outstanding, and the deadline is still set and still no
    later than that packet's own. -/
theorem ackDeadline_afterAckSent_of_uncovered {s : State} {largest first : Nat}
    {rs : List AckRange} {l : List Rng} (h : acked largest first rs = some l)
    {pn : Nat} {t : Time} (hp : (pn, t) ∈ s.outstanding) (hnc : Ranges.mem l pn = false) :
    ∃ d, ackDeadline (s.afterAckSent largest first rs) = some d ∧ d ≤ s.deadlineOf t := by
  have hmem : (pn, t) ∈ (s.afterAckSent largest first rs).outstanding :=
    (mem_outstanding_afterAckSent h (pn, t)).mpr ⟨hp, hnc⟩
  obtain ⟨d, hd, hle⟩ := ackDeadline_le_deadlineOf hmem
  exact ⟨d, hd, by simpa using hle⟩

/-- (iii) §12.3, line 4693: 2^62 - 1 is the number at which the sender must
    stop, so it may not itself be used. -/
theorem maySendPacketNumber_maxPn (s : State) : maySendPacketNumber s maxPn = false := by
  simp [maySendPacketNumber]

/-- `pnExhausted` is exactly "no packet number is left in this space". -/
theorem pnExhausted_iff (s : State) :
    pnExhausted s = true ↔ ∀ pn, maySendPacketNumber s pn = false := by
  cases hl : s.largestSent with
  | none =>
    simp only [pnExhausted, hl, maySendPacketNumber, Bool.false_eq_true, false_iff]
    intro hc
    have := hc 0
    simp [maxPn] at this
  | some m =>
    simp only [pnExhausted, hl, maySendPacketNumber, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · intro h pn; omega
    · intro h
      have := h (m + 1)
      omega

/-- Once the space is spent, no packet of it may be sent — §12.3, line 4693:
    "If the packet number for sending reaches 2^62 - 1, the sender MUST close
    the connection without sending a CONNECTION_CLOSE frame or any further
    packets". -/
theorem not_maySendPacket_of_exhausted {s : State} {p : OutPacket}
    (h : pnExhausted s = true) (hsp : p.ptype.space = some s.space) : ¬ MaySendPacket s p := by
  intro hm
  rw [(hm hsp).1] at h
  exact Bool.noConfusion h

/-- A packet whose payload is nothing but ACK frames. -/
def ackOnly (fs : List Frame) : Bool :=
  !fs.isEmpty && fs.all (fun f => match f with | .ack .. => true | _ => false)

/-- §13.2.1, line 5083: "Since packets containing only ACK frames are not
    congestion controlled, an endpoint MUST NOT send more than one such packet
    in response to receiving an ack-eliciting packet."  `sent` is the payloads
    sent in response to one received packet. -/
def AtMostOneAckOnly (sent : List (List Frame)) : Prop :=
  (sent.filter ackOnly).length ≤ 1

/-- §13.2.1, line 5087: "An endpoint MUST NOT send a non-ack-eliciting packet
    in response to a non-ack-eliciting packet, even if there are packet gaps
    that precede the received packet." -/
def NoAckOfNonAckEliciting (recvAckEliciting : Bool) (sent : List (List Frame)) : Prop :=
  recvAckEliciting = false → ∀ fs ∈ sent, FrameRules.packetAckEliciting fs = true

/-- §13.2.1, line 5131: "A receiver MUST NOT send an ack-eliciting frame in all
    packets that would otherwise be non-ack-eliciting, to avoid an infinite
    feedback loop of acknowledgments."  Each entry pairs a payload with whether
    its other frames would have left the packet non-ack-eliciting. -/
def NotAlwaysAckEliciting (sent : List (List Frame × Bool)) : Prop :=
  (∀ p ∈ sent, p.2 = true → FrameRules.packetAckEliciting p.1 = true) →
    ∀ p ∈ sent, p.2 = false

/-- §13.2.5, line 5280: "An endpoint MUST NOT include delays that it does not
    control when populating the ACK Delay field in an ACK frame."  `delay` is
    the decoded value of the field, in microseconds. -/
def AckDelayOk (s : State) (now : Time) (delay : Time) : Prop :=
  s.largest ≠ none → delay ≤ now - s.largestTime

/-! ## 9. Examples (scenarios from the text) -/

private def s0 : State :=
  { space := .appData, received := [], minPn := 0, largest := none,
    largestTime := 0, largestAckEliciting := none, outstanding := [],
    ackImmediately := false, largestSent := some 4, maxAckDelay := 25000 }

-- §12.3: a fresh packet is processed …
example : component.step s0 (.recvPacket 0 100 true)
    = .ok (s0.record 0 100 true) [.processed 0 true] := by rfl
-- … and the packet number is recorded.
example : (s0.record 0 100 true).received = [⟨0, 0⟩] := by decide
-- §12.3, line 4709: the same packet number again MUST be discarded.
example : component.step (s0.record 0 100 true) (.recvPacket 0 200 true) = .drop := by rfl
-- Out-of-order arrival: 0, 2, then 1 closes the gap and the ranges merge.
example : (((s0.record 0 100 true).record 2 110 true).record 1 120 true).received
    = [⟨0, 2⟩] := by decide
example : ((s0.record 0 100 true).record 2 110 true).received = [⟨0, 0⟩, ⟨2, 2⟩] := by decide
-- §13.2.1, line 5108: a gap before an ack-eliciting packet asks for an
-- immediate ACK.
example : ((s0.record 0 100 true).record 2 110 true).ackImmediately = true := by decide
example : (s0.record 0 100 true).ackImmediately = false := by decide
-- §13.2.2, line 5163: two ack-eliciting packets are outstanding, so an ACK is
-- recommended.
example : ((s0.record 0 100 true).record 1 110 true).ackElicitingSinceAck = 2 := by rfl

-- §13.1, line 5030: an ACK whose largest acknowledged is above anything we
-- sent.  Both outcomes are permitted (SHOULD), the error preferred.
example : component.step s0 (.recvAck 9 0 []) = .error .protocolViolation := by rfl
example : component.accepts s0 (.recvAck 9 0 []) (.ok s0 []) = true := by decide
-- An ACK for packets we did send is simply processed.
example : component.step s0 (.recvAck 3 0 []) = .ok { s0 with largestAcked := some 3 } [] := by
  rfl
-- ... and one we tolerated although we sent no such packet is not counted.
example : s0.afterAckRecv 9 = s0 := by rfl
-- §17.1, line 6023: nothing acknowledged yet, so the number goes out whole.
example : maySendPacketNumberSize s0 255 1 = true := by decide
example : maySendPacketNumberSize s0 256 1 = false := by decide
-- §17.1, line 6027: 3 acknowledged; one byte represents 256 > 2 * (130 - 3),
-- and not 2 * (131 - 3).
example : maySendPacketNumberSize { s0 with largestAcked := some 3 } 130 1 = true := by decide
example : maySendPacketNumberSize { s0 with largestAcked := some 3 } 131 1 = false := by decide
example : maySendPacketNumberSize { s0 with largestAcked := some 3 } 131 2 = true := by decide
-- §19.3.1, line 7375: a negative computed packet number is FRAME_ENCODING_ERROR.
example : component.step s0 (.recvAck 3 5 []) = .error .frameEncodingError := by rfl
example : component.step s0 (.recvAck 3 0 [⟨5, 0⟩]) = .error .frameEncodingError := by rfl

/-! ### Regressions for the three defects the audit found

`a0` is the audit's starting state: application data space, 25 ms
max_ack_delay, nothing sent yet. -/

private def a0 : State :=
  { space := .appData, received := [], minPn := 0, largest := none,
    largestTime := 0, largestAckEliciting := none, outstanding := [],
    ackImmediately := false, largestSent := none, maxAckDelay := 25000 }

-- (1) §13.2.1, line 5075.  An ack-eliciting packet at 0 µs must be
-- acknowledged by 25 000 µs.  A later *non*-ack-eliciting packet at 24 000 µs
-- adds no obligation and must not postpone that deadline: it used to give
-- 49 000.
example : ackDeadline ((a0.record 0 0 true).record 1 24000 false) = some 25000 := by rfl
-- The ACK Delay field still measures from the largest packet number received
-- (§13.2.5, line 5271), which is what `largestTime` is for.
example : ((a0.record 0 0 true).record 1 24000 false).largestTime = 24000 := by rfl
-- A later ack-eliciting packet adds a *later* deadline of its own; the state's
-- deadline stays the earliest.
example : ackDeadline ((a0.record 0 0 true).record 1 24000 true) = some 25000 := by rfl
-- An earlier-arriving packet brings the deadline forward.
example : ackDeadline ((a0.record 5 9000 true).record 6 1000 true) = some 26000 := by rfl

-- (2) §13.2.1, line 5075.  Two ack-eliciting packets; an ACK naming only
-- packet 1 is legal to send but settles only packet 1.
private def a2 : State := (a0.record 0 0 true).record 1 1000 true
example : component.maySendPacket a2 ⟨.oneRtt, [.ack 1 0 0 #[] none]⟩ = true := by decide
-- packet 0 is still outstanding, and its deadline still stands (it used to
-- become `none`)
example : (a2.afterAckSent 1 0 []).outstanding = [(0, 0)] := by rfl
example : ackDeadline (a2.afterAckSent 1 0 []) = some 25000 := by rfl
example : ackOverdue (a2.afterAckSent 1 0 []) 30000 0 = true := by rfl
-- an ACK that names both settles both
example : component.maySendPacket a2 ⟨.oneRtt, [.ack 1 1 1 #[] none]⟩ = true := by decide
example : ackDeadline (a2.afterAckSent 1 1 []) = none := by rfl
example : (a2.afterAckSent 1 1 []).ackElicitingPending = false := by rfl
-- §13.2.6, line 5293: an ACK naming packet numbers of this space may not ride
-- in a packet of another space — the Handshake instance's `received` is empty.
example : component.maySendPacket { a0 with space := .handshake }
    ⟨.handshake, [.ack 1 0 0 #[] none]⟩ = false := by decide
-- a packet of another space says nothing about this instance
example : component.maySendPacket a2 ⟨.handshake, [.ack 1 0 0 #[] none]⟩ = true := by decide
-- §13.1, line 5026: an ACK may not name a packet number we never received
example : component.maySendPacket a2 ⟨.oneRtt, [.ack 2 0 0 #[] none]⟩ = false := by decide

-- (3) §12.3, line 4693.  2^62 - 1 is the number at which the sender must stop,
-- so it is not itself usable; it used to be accepted.
example : maySendPacketNumber a0 (2 ^ 62 - 1) = false := by decide
example : maySendPacketNumber a0 (2 ^ 62 - 2) = true := by decide
example : pnExhausted { a0 with largestSent := some (2 ^ 62 - 2) } = true := by decide
example : pnExhausted { a0 with largestSent := some (2 ^ 62 - 3) } = false := by decide
-- and once the space is spent, no packet of it may be sent at all
example : component.maySendPacket { a0 with largestSent := some (2 ^ 62 - 2) }
    ⟨.oneRtt, [.ping]⟩ = false := by decide
example : component.maySendPacket { a0 with largestSent := some (2 ^ 62 - 2) }
    ⟨.initial, [.ping]⟩ = true := by decide

/-! ### The minimum packet number (§12.3, line 4717) -/

-- With no minimum maintained, a fresh packet is processed and only that.
example : component.outcomes a0 (.recvPacket 7 100 true)
    = [.ok (a0.record 7 100 true) [.processed 7 true]] := by decide
example : component.accepts a0 (.recvPacket 7 100 true) .drop = false := by decide
-- Once a minimum of 10 is maintained, an endpoint that has pruned may drop
-- packet 7, and one that has not may still process it: both are permitted, the
-- drop preferred.
private def m0 : State := { a0 with minPn := 10 }
example : component.step m0 (.recvPacket 7 100 true) = .drop := by rfl
example : component.accepts m0 (.recvPacket 7 100 true)
    (.ok (m0.record 7 100 true) [.processed 7 true]) = true := by decide
-- at or above the minimum nothing changes
example : component.outcomes m0 (.recvPacket 10 100 true)
    = [.ok (m0.record 10 100 true) [.processed 10 true]] := by decide
-- raising the minimum is always permitted and never lowers it
example : component.step a0 (.raiseMinimum 10) = .ok m0 [] := by rfl
example : (component.step m0 (.raiseMinimum 3)).next m0 = m0 := by rfl
-- a duplicate is still dropped and nothing else, minimum or no minimum
example : component.outcomes (m0.record 12 100 true) (.recvPacket 12 200 true) = [.drop] := by
  decide

/-! ## 10. Coverage and notes

Assigned range: lines 5018–5324, plus the §12.3 duplicate-suppression sentences
of lines 4709–4713.  The rest of §12.3–§12.5 is covered in
`Spec/FrameRules.lean`.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §12.3 (4685) | "Subsequent packets sent in the same packet number space MUST increase the packet number by at least one." | `maySendPacketNumber` |
| §12.3 (4692) | "A QUIC endpoint MUST NOT reuse a packet number within the same packet number space in one connection." | `maySendPacketNumber` |
| §17.1 (6023) | "Prior to receiving an acknowledgment for a packet number space, the full packet number MUST be included; it is not to be truncated as described below." | `maySendPacketNumberSize` (`largestAcked = none`); composed in `Endpoint.maySendNumbers` |
| §17.1 (6027) | "After an acknowledgment is received for a packet number space, the sender MUST use a packet number size able to represent more than twice as large a range than the difference between the largest acknowledged packet and packet number being sent." | `maySendPacketNumberSize`, `State.afterAckRecv`; `Endpoint.decode_of_maySendNumber` shows a receiver's decoder then recovers the number |
| §12.3 (4693) | "If the packet number for sending reaches 2^62 - 1, the sender MUST close the connection without sending a CONNECTION_CLOSE frame or any further packets" | `maySendPacketNumber` (rejects `maxPn` itself: `maySendPacketNumber_maxPn`), `pnExhausted` / `pnExhausted_iff`, `MaySendPacket` / `not_maySendPacket_of_exhausted`; the silent close is WP6 Termination |
| §12.3 (4709) | "A receiver MUST discard a newly unprotected packet unless it is certain that it has not processed another packet with the same packet number from the same packet number space." | `Step.duplicate`, `Step.belowMinimum`, `processed_at_most_once` |
| §12.3 (4717) | "The data required for detecting duplicates can be limited by maintaining a minimum packet number below which all packets are immediately dropped." | `State.minPn`, `Event.raiseMinimum` / `Step.raiseMin`, `Step.belowMinimum`, `minPn_mono` (NOTE 3) |
| §12.3 (4719) | "Any minimum needs to account for large variations in round trip time…" | advice, not checkable here: how far back an endpoint keeps state is an implementation choice the model leaves free — `Step.raiseMin` permits any minimum |
| §12.3 (4711) | "Duplicate suppression MUST happen after removing packet protection" | out of scope: packet protection; `Event.recvPacket` is by construction post-decryption |
| §13.1 (5020) | "A packet MUST NOT be acknowledged until packet protection has been successfully removed and all frames contained in the packet have been processed." | `Step.process` (records only on processing), `AckFrameSendable` / `MaySendPacket`, `ackFrameSendable_sound`, `maySendPacket_ack_sound`, `received_changes_only_on_recvPacket` |
| §13.1 (5026) | "a receiver acknowledges receipt by sending one or more ACK frames containing the packet number of the received packet" | `AckFrameSendable`; `Event.sentAck` carries the fields and `State.discharge` settles exactly what they name |
| §13.1 (5030) | "An endpoint SHOULD treat receipt of an acknowledgment for a packet it did not send as a connection error of type PROTOCOL_VIOLATION, if it is able to detect the condition." | SHOULD that *permits*: both `Step.ackUnsent` (preferred) and `Step.ackOk` are in `outcomes`; `acksUnsent` is the detectable part (NOTE 1) |
| §13.2 (5047) | "Endpoints acknowledge all packets they receive and process." | `Step.process` records every processed packet number |
| §13.2 (5052) | "When sending a packet for any reason, an endpoint SHOULD attempt to include an ACK frame if one has not been sent recently." | `Recommended.withOtherFrames`, approximated: the guard is "an ack-eliciting packet is pending", not "not sent recently", which is a time condition the state does not carry (NOTE 13) |
| §13.2.1 (5064) | MUST half: "ack-eliciting packets MUST be acknowledged at least once within the maximum delay … max_ack_delay" | `State.outstanding`, `ackDeadline`, `AcknowledgedInTime`, `ackOverdue` / `AckObligationMet` |
| §13.2.1 (5064) | SHOULD half: "Every packet SHOULD be acknowledged at least once" (non-ack-eliciting packets included) | `EventuallyAcknowledged` — a liveness property of a whole run, so like the other trace predicates it binds nothing until WP12 supplies the run (NOTE 11) |
| §13.2.1 (5075) | "An endpoint MUST acknowledge all ack-eliciting Initial and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT packets within its advertised max_ack_delay" | `State.outstanding` with `State.ackDelayBudget` / `State.deadlineOf` (per space), `ackDeadline`, `ackDeadline_le_deadlineOf`, `ackDeadline_record_le`, `outstanding_afterAckSent`, `ackDeadline_afterAckSent_of_uncovered`, `ackOverdue` / `AckObligationMet` |
| §13.2.1 (5078) | the exception: buffering packets whose keys are not yet available | out of scope: key availability is WP11 Handshake |
| §13.2.1 (5083) | "Since packets containing only ACK frames are not congestion controlled, an endpoint MUST NOT send more than one such packet in response to receiving an ack-eliciting packet." | `AtMostOneAckOnly` |
| §13.2.1 (5087) | "An endpoint MUST NOT send a non-ack-eliciting packet in response to a non-ack-eliciting packet" | `NoAckOfNonAckEliciting` |
| §13.2.1 (5101) | "In order to assist loss detection at the sender, an endpoint SHOULD generate and send an ACK frame without delay when it receives an ack-eliciting packet either: …" | `State.outOfOrder`, `State.ackImmediately`, `Recommended.immediate` |
| §13.2.1 (5112) | "Similarly, packets marked with the ECN Congestion Experienced (CE) codepoint in the IP header SHOULD be acknowledged immediately" | advice, not checkable here: no event carries an IP ECN codepoint — ECN is §13.4, out of scope by assignment |
| §13.2.1 (5127) | "When only non-ack-eliciting packets need to be acknowledged, an endpoint MAY wait until an ack-eliciting packet has been received to include an ACK frame with outgoing frames." | permitted: `Recommended.withOtherFrames` fires only when `ackElicitingPending`, so waiting is never a violation |
| §13.2.1 (5125) | "An endpoint SHOULD send an ACK frame with other frames when there are new ack-eliciting packets to acknowledge." | `Recommended.withOtherFrames` |
| §13.2.1 (5131) | "A receiver MUST NOT send an ack-eliciting frame in all packets that would otherwise be non-ack-eliciting" | `NotAlwaysAckEliciting` |
| §13.2.2 (5163) | "A receiver SHOULD send an ACK frame after receiving at least two ack-eliciting packets." | `Recommended.twoAckEliciting`, `State.ackElicitingSinceAck` (NOTE 9) |
| §13.2.2 (5171) | "A receiver MAY process multiple available packets before determining whether to send an ACK frame in response." | permitted: `Recommended` constrains only the decision, never the order or grouping of `recvPacket` events |
| §13.2.3 (5181) | "ACK frames SHOULD always acknowledge the most recently received packets" | `RecommendedAck` |
| §13.2.3 (5191) | "After receiving acknowledgments for an ACK frame, the receiver SHOULD stop tracking those acknowledged ACK Ranges." | advice, not checkable here: `received` is never pruned, so there is nothing to stop tracking; `State.minPn` is the sanctioned way to bound the state and nothing requires raising it (NOTE 3) |
| §13.2.3 (5198) | "A receiver can discard unacknowledged ACK Ranges to limit ACK frame size" | permitted: `MaySendPacket` never requires any particular range to be present, so a smaller ACK is always sendable; `received` itself is not pruned (NOTE 3) |
| §13.2.3 (5201) | "Receivers MAY also limit ACK frame size further to preserve space for other frames or to limit the capacity that acknowledgments consume." | permitted: same reason as line 5198 |
| §13.2.3 (5213) | "A receiver MUST retain an ACK Range unless it can ensure that it will not subsequently accept packets with numbers in that range." | `received_mono` (nothing is ever discarded, so the MUST holds vacuously) |
| §13.2.3 (5218) | "they MUST retain the largest packet number that has been successfully processed" | `largest_mono`, `Inv` clauses 2–3 |
| §13.2.3 (5223) | "A receiver SHOULD include an ACK Range containing the largest received packet number in every ACK frame." | `RecommendedAck` |
| §13.2.4 (5229) | "Section 13.2.4 describes an exemplary approach for determining what packets to acknowledge in each ACK frame." | informative, no normative keyword: the algorithm is one way to satisfy line 5191, which this model does not need (NOTE 3) |
| §13.2.5 (5271) | the endpoint measures the delay since the largest packet number was received | `State.largestTime` |
| §13.2.5 (5280) | "An endpoint MUST NOT include delays that it does not control when populating the ACK Delay field in an ACK frame." | `AckDelayOk`, a sound over-approximation: uncontrolled delay is unobservable in the model, so the bound is total elapsed time (NOTE 14) |
| §13.2.5 (5282) | "However, endpoints SHOULD include buffering delays caused by unavailability of decryption keys, since these delays can be large" | advice, not checkable here: key availability and the buffering it causes are WP11 Handshake; no event here records a packet held for want of keys |
| §13.2.5 (5286) | "When the measured acknowledgment delay is larger than its max_ack_delay, an endpoint SHOULD report the measured delay." | advice, not checkable here: the model records arrival times but never the delay an implementation actually measured, so there is nothing to compare the reported value with |
| §13.2.6 (5293) | "ACK frames MUST only be carried in a packet that has the same packet number space as the packet being acknowledged" | `MaySendPacket` (an ACK in a packet of this space is checked against *this* space's `received`), `maySendPacket_ack_sound` |
| §13.2.6 (5298) | "Packets that a client sends with 0-RTT packet protection MUST be acknowledged by the server in packets protected by 1-RTT keys." | `appData_ack_in_oneRtt`, proved from `MaySendPacket` and `FrameRules.MaySendPacket` together |
| §13.2.7 (5307) | "Packets containing PADDING frames are considered to be in flight" | `FrameRules.inFlight` / `FrameRules.packetInFlight` |
| §13.2.7 (5310) | "To avoid a deadlock, a sender SHOULD ensure that other frames are sent periodically in addition to PADDING frames to elicit acknowledgments from the receiver." | advice, not checkable here: it is about the congestion window (RFC 9002), which is out of scope by assignment, and it constrains a whole sending schedule rather than any one packet |
| §19.3 (7236) | "QUIC implementations MUST properly handle both types" (0x02 and 0x03) | `acked` ignores the ECN counts; ECN validation is §13.4, out of scope |
| §19.3.1 (7375) | "If any computed packet number is negative, an endpoint MUST generate a connection error of type FRAME_ENCODING_ERROR." | `Step.ackMalformed`, `acked`, `acked_isSome_iff_check` |
| §13.3, §13.4 | retransmission, ECN validation | out of scope by assignment |

NOTES

1. **"Able to detect" in §13.1.**  The SHOULD at line 5030 is conditional on
   the endpoint being "able to detect the condition".  An endpoint that keeps
   only the largest packet number it has sent can detect an acknowledgment
   above that number, and nothing finer; `acksUnsent` encodes exactly that, so
   `Step` is deliberately weaker than "acknowledges any packet we did not
   send".  An implementation that tracks its sent packet numbers in full and
   raises PROTOCOL_VIOLATION for a gap is not covered by `Step.ackUnsent` and
   would be reported as a mismatch by the differential harness; that is the
   text's own looseness, not a modelling error.

2. **A SHOULD that permits.**  Both `Step.ackUnsent` (raise the error) and
   `Step.ackOk` (do not) are permitted for the same event, with the error
   listed first so that `component.step` is the recommended behaviour.

3. **The minimum packet number, and what `received` does not do.**  §12.3,
   line 4717 permits bounding the duplicate-detection state with "a minimum
   packet number below which all packets are immediately dropped", and §13.2.3,
   line 5191 recommends dropping ACK Ranges once they have been acknowledged.
   An implementation that does either **drops packets this model would process**
   — the divergence runs that way round, not the other (an earlier version of
   this note had it backwards).

   Encoded as `State.minPn`, raised by `Event.raiseMinimum`:

   * `Step.belowMinimum` makes `.drop` a permitted outcome for any packet below
     the minimum that is not already a duplicate, and `outcomes` lists it
     *first*, so `component.step` is the pruning behaviour and `accepts` /
     `trackSet` follow an implementation that prunes.
   * `Step.process` is still permitted for the same packet, because this model
     does **not** prune `received`: it keeps at least as much information as
     the implementation it follows, so it is still "certain" in the sense of
     line 4709 and may process the packet.  Both outcomes are therefore listed,
     which is the usual treatment of a permission (BRIEF).
   * `minPn` alone bounds nothing in `received`, and `Ranges.insert` never
     forgets, so `received_mono`, the MUST of line 5213 and
     `processed_at_most_once` all survive unchanged: a packet number that has
     been processed is never processed again, whatever the minimum.
   * The cost of keeping `received` whole is that `MaySendPacket` lets us
     acknowledge packet numbers a pruning implementation would have forgotten.
     That is safe (`maySendPacket_ack_sound` still holds) and only makes the
     send-side predicate looser than the implementation needs.

4. **Packet numbers are not bounded in `Step`.**  §12.3 says packet numbers lie
   in `[0, 2^62-1]`, but the receive side never sees an out-of-range number:
   §17.1 decoding produces a number in range by construction.  The bound is
   therefore a send-side condition (`maySendPacketNumber`) and a precondition
   on `Event.recvPacket`, not a branch of `Step`.

5. **`Recommended` is a predicate, not a timer.**  §13.2's timing requirements
   are about when an ACK frame is sent; the assignment puts timers out of
   scope, so `ackDeadline` / `AcknowledgedInTime` state the MUST as a property
   of a moment, and `Recommended` states the SHOULDs as a property of the
   decision.  Neither constrains `Step`.

6. **§13.2.1 line 5131 needs the counterfactual.**  "would otherwise be
   non-ack-eliciting" is a statement about the packet the endpoint *would* have
   sent, which the model cannot recover from what was sent; the flag is
   therefore an explicit second component of each entry in
   `NotAlwaysAckEliciting`.

7. **Inequalities instead of equations in `Ranges.insert`.**  The branch
   conditions of `insert` are `n + 1 ≤ r.lo`, `n ≤ r.hi + 1` and
   `r'.lo ≤ n + 1` rather than the equalities they are equivalent to under
   `wfFrom`.  This is purely a proof convenience (an equation used as a
   rewrite substitutes `n` everywhere and defeats the subsequent `if`
   reductions); the function computes the same thing on every well-formed
   input.

8. **One instance per space.**  `State.space` is a field rather than a
   parameter so that `Component` stays a closed structure; WP12 will hold three
   instances and route each packet to the one for its space
   (`PacketType.space`).

9. **What "since receiving at least two ack-eliciting packets" counts.**
   §13.2.2, line 5163 does not say what resets the count.  Reading chosen:
   `State.ackElicitingSinceAck` is the number of ack-eliciting packets still
   *outstanding*, so a partial ACK reduces it by what it covered rather than
   zeroing it.  It is only a `Recommended` clause, so nothing rejects an
   implementation that counts differently; it is recorded because the earlier
   model stored an independent counter that any ACK reset to 0 even when
   packets were still owed.

10. **`largestTime` is the ACK Delay input, not the deadline input.**
    §13.2.5, line 5271 measures the delay "between the time the packet with the
    largest packet number is received and the time an acknowledgment is sent",
    so `largestTime` follows the largest packet number, including a
    non-ack-eliciting one.  The *obligation* of §13.2.1, line 5075 is per
    ack-eliciting packet, so it lives in `State.outstanding`, and `ackDeadline`
    is the earliest deadline among those.  Using `largestTime` for both let a
    later non-ack-eliciting packet postpone an earlier packet's deadline;
    `ackDeadline_record_le` now rules that out.

11. **A deadline is not an obligation to act, and neither are the other trace
    predicates.**  `ackDeadline` and
    `AcknowledgedInTime` only say that an ACK frame, *if* one is sent, is not
    late.  The MUST of §13.2.1, line 5075 also requires that one be sent at
    all, which no single `Step` can express.  `ackOverdue s now` and
    `AckObligationMet` are exported for that: WP12 must require `ackOverdue` to
    be false at every point of a timed run of the composed endpoint.
    Relatedly, `Event.sentAck` records an ACK frame the endpoint has already
    checked with `MaySend`; `State.afterAckSent` discharges nothing for a frame
    whose ranges do not compute, so a malformed ACK cannot settle anything.

12. **"Immediately" is a zero *intentional* delay.**  For the Initial and
    Handshake spaces `State.ackDelayBudget` is `0`, so `ackDeadline` is the
    arrival time itself and `ackOverdue s now 0` is true for every `now` after
    it — no real endpoint could satisfy it.  §13.2.5, line 5271 says what is
    being bounded: "the delays **intentionally introduced**".  The model has no
    notion of what an endpoint costs to run, so `ackOverdue`,
    `AcknowledgedInTime` and `AckObligationMet` take a `tolerance` the checker
    supplies: `0` is the literal text, and a harness gives the processing bound
    it is willing to allow.  The appData budget (`max_ack_delay`) is already
    positive, so only Initial and Handshake need it.

13. **Two sentences under one `Recommended` clause.**  §13.2, line 5052 ("if one
    has not been sent recently") and §13.2.1, line 5125 ("when there are new
    ack-eliciting packets to acknowledge") are both carried by
    `Recommended.withOtherFrames`, guarded by `ackElicitingPending`.  That is
    line 5125's condition exactly; line 5052's "recently" is a time condition
    the state does not carry, and adding a "time of last ACK sent" field would
    only be read by a clause that constrains nothing.  Recorded as an
    approximation rather than encoded.

14. **`AckDelayOk` is an over-approximation.**  §13.2.5, line 5280 forbids
    including delay the endpoint does not control; the model cannot tell
    controlled from uncontrolled delay, so `AckDelayOk` only requires the
    reported value not to exceed the total elapsed time since the largest
    packet arrived.  That is implied by the MUST and therefore sound, but it is
    weaker: an endpoint that reports kernel buffering delay satisfies
    `AckDelayOk` and violates line 5280.

15. **No `assembling`, and `MaySend` is `True`.**  An earlier version carried
    the packet type being assembled in `State`, duplicating
    `FrameRules.State.assembling`.  Every send-side rule here is really about a
    frame *in a packet*, and with one instance of this component per packet
    number space a frame-only predicate would have to hold in all three
    instances at once — which would forbid every ACK frame, since an ACK for
    the application data space names numbers the Initial instance never
    received.  Both rules therefore live in `Component.MaySendPacket`, which is
    handed the real `OutPacket.ptype` and can say "a packet of another space is
    none of this instance's business".  `MaySend` is `True` so that it does not
    repeat `MaySendPacket` (BRIEF) and components still compose by conjunction.
-/

end Quic.Spec.Ack
