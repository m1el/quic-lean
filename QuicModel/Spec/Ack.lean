import QuicModel.Spec.FrameRules

/-
  WP3 (b): per packet-number-space receive tracking (§12.3 duplicate
  suppression), the acknowledgment rules of §13.1 and the generation rules of
  §13.2.

  Text: draft-ietf-quic-transport-34, lines 4709–4713 (§12.3), 5018–5324
  (§13.1, §13.2.1–§13.2.7), with the ACK frame arithmetic of §19.3.1.

  Table 3 and the packet-type legality of frames are in
  `QuicModel/Spec/FrameRules.lean`.
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
    §19.3, line 7300: "the smallest packet acknowledged in the range is
    determined by subtracting the First ACK Range value from the Largest
    Acknowledged". -/
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
  /-- The packet type currently being assembled, for `MaySend` (§13.2.6). -/
  assembling : PacketType
  /-- §12.3, line 4709: the packet numbers already processed in this space. -/
  received : List Rng
  /-- §13.2.3, line 5218: "they MUST retain the largest packet number that has
      been successfully processed". -/
  largest : Option Nat
  /-- §13.2.5, line 5271: when the packet with the largest packet number was
      received; the basis of the ACK Delay field. -/
  largestTime : Time
  /-- The largest ack-eliciting packet number received (§13.2.1, line 5101). -/
  largestAckEliciting : Option Nat
  /-- §13.2, line 5048: an ack-eliciting packet is waiting to be acknowledged. -/
  ackElicitingPending : Bool
  /-- §13.2.2, line 5163: ack-eliciting packets received since we last sent an
      ACK frame. -/
  ackElicitingSinceAck : Nat
  /-- §13.2.1, line 5101: reordering or a gap was seen, so an ACK should go out
      without delay. -/
  ackImmediately : Bool
  /-- §13.1, line 5030: the largest packet number we have sent in this space. -/
  largestSent : Option Nat
  /-- §18.2: the max_ack_delay we advertised, in microseconds. -/
  maxAckDelay : Time
  deriving DecidableEq, Repr

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

/-- Record a packet that has been fully processed (§13.1, line 5020). -/
def State.record (s : State) (pn : Nat) (t : Time) (ae : Bool) : State :=
  { s with
    received := Ranges.insert s.received pn
    largest := some (maxOpt s.largest pn)
    largestTime := if s.isNewLargest pn then t else s.largestTime
    largestAckEliciting :=
      if ae then some (maxOpt s.largestAckEliciting pn) else s.largestAckEliciting
    ackElicitingPending := s.ackElicitingPending || ae
    ackElicitingSinceAck := s.ackElicitingSinceAck + (if ae then 1 else 0)
    ackImmediately := s.ackImmediately || (ae && s.outOfOrder pn) }

def State.afterAckSent (s : State) : State :=
  { s with ackElicitingPending := false, ackElicitingSinceAck := 0, ackImmediately := false }

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

inductive Event where
  /-- A packet numbered `pn` arrived at time `t`, protection was removed, and
      (if it is not a duplicate) its frames are processed. -/
  | recvPacket (pn : Nat) (t : Time) (ackEliciting : Bool)
  /-- An ACK frame carried in a packet of this space. -/
  | recvAck (largest first : Nat) (ranges : List AckRange)
  /-- We sent a packet numbered `pn` in this space. -/
  | sentPacket (pn : Nat)
  /-- We sent an ACK frame for this space. -/
  | sentAck
  /-- We start assembling a packet of type `pt`. -/
  | beginPacket (pt : PacketType)
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
  /-- §13.1, line 5020: "A packet MUST NOT be acknowledged until packet
      protection has been successfully removed and all frames contained in the
      packet have been processed."  Recording the packet number is what makes
      it acknowledgeable. -/
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
      Step s (.recvAck largest first rs) (.ok s [])
  /-- Bookkeeping for §13.1's "a packet it did not send". -/
  | sent {s pn} :
      Step s (.sentPacket pn) (.ok { s with largestSent := bumpSent s.largestSent pn } [])
  /-- §13.2.2, line 5163: the count of unacknowledged ack-eliciting packets
      restarts when an ACK frame goes out. -/
  | ackSent {s} : Step s .sentAck (.ok s.afterAckSent [])
  /-- Bookkeeping for `MaySend`: the packet under construction. -/
  | begin {s pt} : Step s (.beginPacket pt) (.ok { s with assembling := pt } [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvPacket pn t ae =>
    if Ranges.mem s.received pn then [.drop]
    else [.ok (s.record pn t ae) [.processed pn ae]]
  | .recvAck largest first rs =>
    match acked largest first rs with
    | none => [.error .frameEncodingError]
    | some _ =>
      if acksUnsent s largest then [.error .protocolViolation, .ok s []] else [.ok s []]
  | .sentPacket pn => [.ok { s with largestSent := bumpSent s.largestSent pn } []]
  | .sentAck => [.ok s.afterAckSent []]
  | .beginPacket pt => [.ok { s with assembling := pt } []]

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
        simp only [List.mem_singleton] at h; subst h; exact .process hd
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
    | sentAck => simp only [outcomes, List.mem_singleton] at h; subst h; exact .ackSent
    | beginPacket pt => simp only [outcomes, List.mem_singleton] at h; subst h; exact .begin
  · intro h
    cases h with
    | duplicate h => simp [outcomes, h]
    | process h => simp [outcomes, h]
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
    | begin => simp [outcomes]

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
  obtain ⟨hw, h2, h3, h4⟩ := hi
  cases h with
  | @process pn t ae hp =>
    refine ⟨Ranges.wf_insert hw pn, ?_, ?_, ?_⟩
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
  | ackOk => exact ⟨hw, h2, h3, h4⟩
  | sent => exact ⟨hw, h2, h3, h4⟩
  | ackSent => exact ⟨hw, h2, h3, h4⟩
  | begin => exact ⟨hw, h2, h3, h4⟩

/-! ## 6. Send side -/

/-- What an ACK frame we put into the packet we are assembling may say.

* §13.2.6, line 5293: "ACK frames MUST only be carried in a packet that has the
  same packet number space as the packet being acknowledged"; this instance
  tracks exactly one space, so the rule is a condition on the packet type.
* §19.3.1, line 7375: no computed packet number may be negative.
* §13.1, line 5026: "a receiver acknowledges receipt by sending one or more ACK
  frames containing the packet number of the received packet" — every
  acknowledged packet number must be one we received and processed. -/
def MaySend (s : State) : Frame → Prop
  | .ack largest _ first ranges _ =>
    s.assembling.space = some s.space
    ∧ ∃ l, acked largest first ranges.toList = some l
        ∧ ∀ r ∈ l, Ranges.subsetOf r s.received = true
  | _ => True

def maySend (s : State) : Frame → Bool
  | .ack largest _ first ranges _ =>
    decide (s.assembling.space = some s.space)
      && (match acked largest first ranges.toList with
          | none => false
          | some l => l.all (fun r => Ranges.subsetOf r s.received))
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f
  case ack largest delay first ranges ecn =>
    simp only [maySend, MaySend, Bool.and_eq_true, decide_eq_true_eq]
    cases h : acked largest first ranges.toList with
    | none => simp
    | some l => simp [List.all_eq_true]
  all_goals simp [maySend, MaySend]

/-- §12.3, line 4685: "Subsequent packets sent in the same packet number space
    MUST increase the packet number by at least one."; line 4692: "A QUIC
    endpoint MUST NOT reuse a packet number within the same packet number space
    in one connection."; line 4693: "If the packet number for sending reaches
    2^62 - 1, the sender MUST close the connection without sending a
    CONNECTION_CLOSE frame or any further packets" — here only the bound; the
    close itself belongs to WP6. -/
def maySendPacketNumber (s : State) (pn : Nat) : Bool :=
  (match s.largestSent with | none => true | some m => decide (m < pn)) && decide (pn ≤ maxPn)

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

/-- (b) An ACK frame we may send never acknowledges a packet number we have not
    received: §13.1, line 5020 ("A packet MUST NOT be acknowledged until … all
    frames contained in the packet have been processed"). -/
theorem maySend_ack_sound {s : State} {largest delay first : Nat} {ranges : Array AckRange}
    {ecn : Option Ecn} (h : MaySend s (.ack largest delay first ranges ecn)) {n : Nat}
    (hn : Acks largest first ranges.toList n) : Ranges.mem s.received n = true := by
  obtain ⟨-, l, hl, hsub⟩ := h
  obtain ⟨l', hl', hmem⟩ := hn
  rw [hl] at hl'
  have : l = l' := Option.some.inj hl'
  subst this
  obtain ⟨r, hr, h1, h2⟩ := Ranges.exists_of_mem hmem
  exact Ranges.mem_of_subsetOf (hsub r hr) h1 h2

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
  | ackSent => exact hm
  | begin => exact hm

/-- §13.2.3, line 5218: "Receivers can discard all ACK Ranges, but they MUST
    retain the largest packet number that has been successfully processed". -/
theorem largest_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) {m : Nat} (hm : s.largest = some m) :
    ∃ m', s'.largest = some m' ∧ m ≤ m' := by
  cases h with
  | @process pn t ae hp => exact ⟨maxOpt s.largest pn, rfl, le_maxOpt_of_eq hm pn⟩
  | ackOk => exact ⟨m, hm, Nat.le_refl _⟩
  | sent => exact ⟨m, hm, Nat.le_refl _⟩
  | ackSent => exact ⟨m, hm, Nat.le_refl _⟩
  | begin => exact ⟨m, hm, Nat.le_refl _⟩

/-- A packet number is only ever added by processing a packet — §13.1: it is
    the processing of the packet that makes it acknowledgeable. -/
theorem received_changes_only_on_recvPacket {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hne : s'.received ≠ s.received) :
    ∃ pn t ae, e = .recvPacket pn t ae := by
  cases h with
  | @process pn t ae hp => exact ⟨pn, t, ae, rfl⟩
  | ackOk => exact absurd rfl hne
  | sent => exact absurd rfl hne
  | ackSent => exact absurd rfl hne
  | begin => exact absurd rfl hne

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
  | process hp => rw [hmem''] at hp; exact absurd hp (by simp)

/-- §13.2.6, line 5293: "ACK frames MUST only be carried in a packet that has
    the same packet number space as the packet being acknowledged". -/
theorem ack_same_space {s : State} {largest delay first : Nat} {ranges : Array AckRange}
    {ecn : Option Ecn} (h : MaySend s (.ack largest delay first ranges ecn)) :
    s.assembling.space = some s.space := h.1

/-- §13.2.6, line 5298: "Packets that a client sends with 0-RTT packet
    protection MUST be acknowledged by the server in packets protected by 1-RTT
    keys."  `hz` is `FrameRules.ack_not_in_zeroRtt` (Table 3: ACK is `IH_1`). -/
theorem appData_ack_in_oneRtt {s : State} {largest delay first : Nat} {ranges : Array AckRange}
    {ecn : Option Ecn} (hsp : s.space = .appData)
    (h : MaySend s (.ack largest delay first ranges ecn))
    (hz : s.assembling ≠ .zeroRtt) : s.assembling = .oneRtt := by
  have hs := ack_same_space h
  rw [hsp] at hs
  cases hc : s.assembling <;> rw [hc] at hs hz <;> simp_all [PacketType.space]

/-! ### §13.2 acknowledgment frequency: recommendations, not requirements -/

/-- The SHOULDs and MAYs of §13.2 that only *recommend* a moment to send an ACK
    frame.  They are deliberately outside `Step` and `MaySend`: an endpoint that
    ignores them still conforms.  `sendAckNow` is the decision to emit an ACK
    frame for this space right now. -/
structure Recommended (s : State) (sendAckNow : Bool) : Prop where
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
  /-- §13.2.1, line 5125: "An endpoint SHOULD send an ACK frame with other
      frames when there are new ack-eliciting packets to acknowledge."  The
      following sentence is the MAY that balances it: "When only
      non-ack-eliciting packets need to be acknowledged, an endpoint MAY wait
      until an ack-eliciting packet has been received". -/
  withOtherFrames : s.ackElicitingPending = true → sendAckNow = true

/-- §13.2.3, line 5223: "A receiver SHOULD include an ACK Range containing the
    largest received packet number in every ACK frame." -/
def RecommendedAck (s : State) (largest : Nat) : Prop := s.largest = some largest

/-! ### §13.2 requirements that are properties of a trace, not of one step -/

/-- §13.2.1, line 5075: "An endpoint MUST acknowledge all ack-eliciting Initial
    and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT
    packets within its advertised max_ack_delay, with the following exception."
    The exception (line 5078) is buffering for want of keys, which is WP11's. -/
def ackDeadline (s : State) : Option Time :=
  if s.ackElicitingPending then
    some (match s.space with
          | .initial | .handshake => s.largestTime
          | .appData => s.largestTime + s.maxAckDelay)
  else none

/-- The same MUST, as a property of the moment an ACK frame is sent. -/
def AcknowledgedInTime (s : State) (sentAt : Time) : Prop :=
  ∀ d, ackDeadline s = some d → sentAt ≤ d

/-- A packet whose payload is nothing but ACK frames. -/
def ackOnly (fs : List Frame) : Bool :=
  !fs.isEmpty && fs.all (fun f => match f with | .ack .. => true | _ => false)

/-- §13.2.1, line 5084: "Since packets containing only ACK frames are not
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
  { space := .appData, assembling := .oneRtt, received := [], largest := none,
    largestTime := 0, largestAckEliciting := none, ackElicitingPending := false,
    ackElicitingSinceAck := 0, ackImmediately := false, largestSent := some 4,
    maxAckDelay := 25000 }

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
-- §13.2.2, line 5163: two ack-eliciting packets, so an ACK is recommended.
example : 2 ≤ ((s0.record 0 100 true).record 1 110 true).ackElicitingSinceAck := by decide

-- §13.1, line 5030: an ACK whose largest acknowledged is above anything we
-- sent.  Both outcomes are permitted (SHOULD), the error preferred.
example : component.step s0 (.recvAck 9 0 []) = .error .protocolViolation := by rfl
example : component.accepts s0 (.recvAck 9 0 []) (.ok s0 []) = true := by rfl
-- An ACK for packets we did send is simply processed.
example : component.step s0 (.recvAck 3 0 []) = .ok s0 [] := by rfl
-- §19.3.1, line 7375: a negative computed packet number is FRAME_ENCODING_ERROR.
example : component.step s0 (.recvAck 3 5 []) = .error .frameEncodingError := by rfl
example : component.step s0 (.recvAck 3 0 [⟨5, 0⟩]) = .error .frameEncodingError := by rfl

-- §13.1 / §13.2.6: what we may put in an ACK frame.
private def s1 : State := ((s0.record 0 100 true).record 1 110 true)
example : component.maySend s1 (.ack 1 0 1 #[] none) = true := by decide
-- acknowledging a packet number we never received
example : component.maySend s1 (.ack 2 0 2 #[] none) = false := by decide
-- §13.2.6: an ACK for the application data space may not ride in a Handshake
-- packet.
example : component.maySend { s1 with assembling := .handshake } (.ack 1 0 1 #[] none) = false := by
  decide
-- §12.3, line 4692: we may not reuse a packet number we have already sent.
example : maySendPacketNumber s0 4 = false := by decide
example : maySendPacketNumber s0 5 = true := by decide

/-! ## 10. Coverage and notes

Assigned range: lines 5018–5324, plus the §12.3 duplicate-suppression sentences
of lines 4709–4713.  The rest of §12.3–§12.5 is covered in
`Spec/FrameRules.lean`.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §12.3 (4685) | "Subsequent packets sent in the same packet number space MUST increase the packet number by at least one." | `maySendPacketNumber` |
| §12.3 (4692) | "A QUIC endpoint MUST NOT reuse a packet number within the same packet number space in one connection." | `maySendPacketNumber` |
| §12.3 (4693) | packet number reaches 2^62-1 ⇒ MUST close without CONNECTION_CLOSE | `maySendPacketNumber` bounds the number by `maxPn`; the close is out of scope: WP6 Termination |
| §12.3 (4709) | "A receiver MUST discard a newly unprotected packet unless it is certain that it has not processed another packet with the same packet number from the same packet number space." | `Step.duplicate`, `processed_at_most_once` |
| §12.3 (4711) | "Duplicate suppression MUST happen after removing packet protection" | out of scope: packet protection; `Event.recvPacket` is by construction post-decryption |
| §13.1 (5020) | "A packet MUST NOT be acknowledged until packet protection has been successfully removed and all frames contained in the packet have been processed." | `Step.process` (records only on processing), `MaySend`, `maySend_ack_sound`, `received_changes_only_on_recvPacket` |
| §13.1 (5026) | "a receiver acknowledges receipt by sending one or more ACK frames containing the packet number of the received packet" | `MaySend` for `.ack` |
| §13.1 (5030) | "An endpoint SHOULD treat receipt of an acknowledgment for a packet it did not send as a connection error of type PROTOCOL_VIOLATION, if it is able to detect the condition." | `Step.ackUnsent` / `Step.ackOk`, `acksUnsent` |
| §13.2 (5047) | "Endpoints acknowledge all packets they receive and process." | `Step.process` records every processed packet number |
| §13.2 (5052) | "When sending a packet for any reason, an endpoint SHOULD attempt to include an ACK frame if one has not been sent recently." | `Recommended.withOtherFrames` |
| §13.2.1 (5064) | "Every packet SHOULD be acknowledged at least once, and ack-eliciting packets MUST be acknowledged at least once within the maximum delay … max_ack_delay" | `ackDeadline`, `AcknowledgedInTime` |
| §13.2.1 (5075) | "An endpoint MUST acknowledge all ack-eliciting Initial and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT packets within its advertised max_ack_delay" | `ackDeadline` (per space), `AcknowledgedInTime` |
| §13.2.1 (5078) | the exception: buffering packets whose keys are not yet available | out of scope: key availability is WP11 Handshake |
| §13.2.1 (5084) | "an endpoint MUST NOT send more than one such packet in response to receiving an ack-eliciting packet" | `AtMostOneAckOnly` |
| §13.2.1 (5087) | "An endpoint MUST NOT send a non-ack-eliciting packet in response to a non-ack-eliciting packet" | `NoAckOfNonAckEliciting` |
| §13.2.1 (5101) | SHOULD ACK without delay on reordering or a gap | `State.outOfOrder`, `State.ackImmediately`, `Recommended.immediate` |
| §13.2.1 (5112) | CE-marked packets SHOULD be acknowledged immediately | out of scope: ECN (§13.4) |
| §13.2.1 (5125) | "An endpoint SHOULD send an ACK frame with other frames when there are new ack-eliciting packets to acknowledge." | `Recommended.withOtherFrames` |
| §13.2.1 (5131) | "A receiver MUST NOT send an ack-eliciting frame in all packets that would otherwise be non-ack-eliciting" | `NotAlwaysAckEliciting` |
| §13.2.2 (5163) | "A receiver SHOULD send an ACK frame after receiving at least two ack-eliciting packets." | `Recommended.twoAckEliciting` |
| §13.2.2 (5171) | "A receiver MAY process multiple available packets before determining whether to send an ACK frame in response." | permitted: `Recommended` constrains only the decision, never the order of `recvPacket` events |
| §13.2.3 (5181) | "ACK frames SHOULD always acknowledge the most recently received packets" | `RecommendedAck` |
| §13.2.3 (5198) | a receiver can discard unacknowledged ACK Ranges to limit frame size | permitted but not modelled: this state never discards; see NOTE 3 |
| §13.2.3 (5213) | "A receiver MUST retain an ACK Range unless it can ensure that it will not subsequently accept packets with numbers in that range." | `received_mono` (nothing is ever discarded, so the MUST holds vacuously) |
| §13.2.3 (5218) | "they MUST retain the largest packet number that has been successfully processed" | `largest_mono`, `Inv` clauses 2–3 |
| §13.2.3 (5223) | "A receiver SHOULD include an ACK Range containing the largest received packet number in every ACK frame." | `RecommendedAck` |
| §13.2.4 (5229) | the exemplary range-limiting algorithm | informative; not modelled |
| §13.2.5 (5271) | the endpoint measures the delay since the largest packet number was received | `State.largestTime` |
| §13.2.5 (5280) | "An endpoint MUST NOT include delays that it does not control when populating the ACK Delay field in an ACK frame." | `AckDelayOk` |
| §13.2.5 (5282) | endpoints SHOULD include buffering delays caused by unavailability of decryption keys | out of scope: WP11 |
| §13.2.6 (5293) | "ACK frames MUST only be carried in a packet that has the same packet number space as the packet being acknowledged" | `MaySend`, `ack_same_space` |
| §13.2.6 (5298) | "Packets that a client sends with 0-RTT packet protection MUST be acknowledged by the server in packets protected by 1-RTT keys." | `appData_ack_in_oneRtt` (with `FrameRules.ack_not_in_zeroRtt`) |
| §13.2.7 (5307) | "Packets containing PADDING frames are considered to be in flight" | `FrameRules.inFlight` / `FrameRules.packetInFlight` |
| §13.2.7 (5311) | a sender SHOULD send other frames periodically alongside PADDING | out of scope: congestion control (RFC 9002) |
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

3. **The range set never shrinks.**  §13.2.3 permits discarding older ACK
   Ranges and keeping a minimum packet number below which packets are dropped
   (§12.3, line 4718).  This model keeps everything, which is the conservative
   reading: it satisfies the MUST of line 5213 vacuously, and it makes
   `processed_at_most_once` unconditional.  An implementation that does prune
   would accept a packet this model drops; that divergence is listed here
   rather than encoded, because the text leaves the minimum entirely to the
   implementation.

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
-/

end Quic.Spec.Ack
