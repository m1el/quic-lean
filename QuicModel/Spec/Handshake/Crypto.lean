import QuicModel.Spec.Ack

/-!
  WP11 "Handshake", part 1: one encryption level's CRYPTO stream (§19.6, §7.5).

  §19.6, line 7540: "There is a separate flow of cryptographic handshake data in
  each encryption level, each of which starts at an offset of 0.  This implies
  that each encryption level is treated as a separate CRYPTO stream of data."

  The bytes themselves are never modelled — TLS is opaque here — so a CRYPTO
  frame is a half-open byte range `[off, off + len)`.  Reassembly is therefore a
  set of byte offsets, and WP3's proved range set (`Spec.Ack.Ranges`: increasing,
  non-empty, non-adjacent closed ranges) is reused for it.  `Ranges.insert` adds
  one offset; `insertRange` adds a whole frame, and `flush` hands the in-order
  prefix to TLS.
-/
namespace Quic.Spec.Handshake

open Quic.Spec.Ack (Rng)

/-! ## Adding a whole frame to the range set -/

/-- The offsets `[off, off + len)`, added to a range set one at a time.  Folding
    `Ranges.insert` keeps every lemma of `Spec.Ack.Ranges` available; the result
    is still canonical (increasing, non-adjacent). -/
def insertRange (l : List Rng) (off len : Nat) : List Rng :=
  (List.range' off len).foldl Ack.Ranges.insert l

@[simp] theorem insertRange_zero (l : List Rng) (off : Nat) : insertRange l off 0 = l := rfl

theorem insertRange_succ (l : List Rng) (off len : Nat) :
    insertRange l off (len + 1) = insertRange (Ack.Ranges.insert l off) (off + 1) len := rfl

theorem wf_insertRange {l : List Rng} (hw : Ack.Ranges.wf l = true) (off len : Nat) :
    Ack.Ranges.wf (insertRange l off len) = true := by
  induction len generalizing l off with
  | zero => simpa using hw
  | succ n ih => rw [insertRange_succ]; exact ih (Ack.Ranges.wf_insert hw off) _

/-- The recorded set after adding a frame is exactly what it was plus the
    frame's offsets. -/
theorem mem_insertRange {l : List Rng} (hw : Ack.Ranges.wf l = true) (off len m : Nat) :
    Ack.Ranges.mem (insertRange l off len) m = true ↔
      (Ack.Ranges.mem l m = true ∨ (off ≤ m ∧ m < off + len)) := by
  induction len generalizing l off with
  | zero =>
    have hno : ¬ (off ≤ m ∧ m < off + 0) := by omega
    simp only [insertRange_zero, hno, or_false]
  | succ n ih =>
    rw [insertRange_succ, ih (Ack.Ranges.wf_insert hw off) (off + 1)]
    rw [Ack.Ranges.mem_insert (lo := 0) hw]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hm : m = off
        · exact Or.inl (Or.inr hm)
        · exact Or.inr (by omega)

theorem mem_insertRange_self {l : List Rng} (hw : Ack.Ranges.wf l = true) {off len m : Nat}
    (h1 : off ≤ m) (h2 : m < off + len) : Ack.Ranges.mem (insertRange l off len) m = true :=
  (mem_insertRange hw off len m).mpr (Or.inr ⟨h1, h2⟩)

/-! ## Handing the in-order prefix to TLS

`flush d l` drops every range that lies entirely below `d`, then extends `d`
past the range that contains or abuts it.  Because the range set is canonical,
one such extension is all there can be: the next range is separated by a gap. -/

def flush (d : Nat) : List Rng → Nat × List Rng
  | [] => (d, [])
  | r :: rs =>
    if r.hi + 1 ≤ d then flush d rs
    else if r.lo ≤ d then (r.hi + 1, rs)
    else (d, r :: rs)

/-- The delivered prefix never shrinks. -/
theorem le_flush (d : Nat) (l : List Rng) : d ≤ (flush d l).1 := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    simp only [flush]
    split
    · exact ih
    · split
      · omega
      · exact Nat.le_refl _

/-- What is left buffered is still canonical, and now lies strictly above the
    delivered prefix: the stream is fully flushed. -/
theorem wfFrom_flush {lo : Nat} {l : List Rng} (hw : Ack.Ranges.wfFrom lo l = true) (d : Nat) :
    Ack.Ranges.wfFrom ((flush d l).1 + 1) (flush d l).2 = true := by
  induction l generalizing lo with
  | nil => simp [flush]
  | cons r rs ih =>
    rw [Ack.Ranges.wfFrom_cons_iff] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    simp only [flush]
    split
    · exact ih h3
    · split
      · exact Ack.Ranges.wfFrom_mono (by omega) h3
      · rw [Ack.Ranges.wfFrom_cons_iff]
        exact ⟨by omega, h2, h3⟩

/-- Every byte the flush delivers was in the range set: nothing is invented. -/
theorem mem_of_lt_flush {l : List Rng} {d n : Nat} (h1 : d ≤ n) (h2 : n < (flush d l).1) :
    Ack.Ranges.mem l n = true := by
  induction l with
  | nil => simp only [flush] at h2; omega
  | cons r rs ih =>
    simp only [flush] at h2 ⊢
    split at h2
    · exact (Ack.Ranges.mem_cons_iff r rs n).mpr (Or.inr (ih h2))
    · split at h2
      · exact (Ack.Ranges.mem_cons_iff r rs n).mpr (Or.inl ⟨by omega, by omega⟩)
      · omega

/-- Flushing removes offsets, never adds them. -/
theorem mem_of_mem_flush {l : List Rng} {d n : Nat}
    (h : Ack.Ranges.mem (flush d l).2 n = true) : Ack.Ranges.mem l n = true := by
  induction l with
  | nil => simp [flush] at h
  | cons r rs ih =>
    simp only [flush] at h
    split at h
    · exact (Ack.Ranges.mem_cons_iff r rs n).mpr (Or.inr (ih h))
    · split at h
      · exact (Ack.Ranges.mem_cons_iff r rs n).mpr (Or.inr h)
      · exact h

/-! ## Buffered size (§7.5) -/

/-- The number of byte offsets held in a range set. -/
def bufferedBytes (l : List Rng) : Nat := (l.map (fun r => r.hi + 1 - r.lo)).sum

@[simp] theorem bufferedBytes_nil : bufferedBytes [] = 0 := rfl

/-! ## One level's CRYPTO stream -/

/-- The transport's view of the CRYPTO stream at one encryption level.  The data
    bytes are TLS's business; only offsets are kept. -/
structure Crypto where
  /-- The next offset to deliver: every byte below it has been handed to TLS in
      order (§7: "QUIC provides reliable, ordered delivery of the cryptographic
      handshake data"). -/
  delivered : Nat := 0
  /-- Byte offsets received out of order and not yet deliverable (§7.5). -/
  buf : List Rng := []
  /-- Bytes TLS has handed us to send at this level (§19.6); the send side may
      not run past it. -/
  handed : Nat := 0
  /-- The next offset we have not yet sent for the first time. -/
  sentNext : Nat := 0
  /-- §7.5, line 2716: after the handshake completes an endpoint that cannot
      buffer a CRYPTO frame "MAY discard that CRYPTO frame and all CRYPTO frames
      received in the future". -/
  discarding : Bool := false
  deriving DecidableEq, Repr

namespace Crypto

/-- The stream is canonical and fully flushed. -/
def WF (c : Crypto) : Prop := Ack.Ranges.wfFrom (c.delivered + 1) c.buf = true

theorem wf_of_WF {c : Crypto} (h : c.WF) : Ack.Ranges.wf c.buf = true :=
  Ack.Ranges.wfFrom_mono (Nat.zero_le _) h

@[simp] theorem WF_default : WF {} := by simp [WF]

/-- Receive `[off, off + len)`: buffer it, then deliver whatever prefix that
    completes. -/
def recv (c : Crypto) (off len : Nat) : Crypto :=
  let b := insertRange c.buf off len
  { c with delivered := (flush c.delivered b).1, buf := (flush c.delivered b).2 }

theorem WF_recv {c : Crypto} (h : c.WF) (off len : Nat) : (c.recv off len).WF :=
  wfFrom_flush (lo := 0) (wf_insertRange (wf_of_WF h) off len) c.delivered

theorem delivered_le_recv (c : Crypto) (off len : Nat) :
    c.delivered ≤ (c.recv off len).delivered := le_flush _ _

/-- Everything newly delivered was either already buffered or is in the frame
    just received. -/
theorem recv_delivers_received {c : Crypto} (h : c.WF) {off len n : Nat}
    (h1 : c.delivered ≤ n) (h2 : n < (c.recv off len).delivered) :
    Ack.Ranges.mem c.buf n = true ∨ (off ≤ n ∧ n < off + len) :=
  (mem_insertRange (wf_of_WF h) off len n).mp (mem_of_lt_flush h1 h2)

/-- Nothing that was not received ends up buffered. -/
theorem recv_buf_received {c : Crypto} (h : c.WF) {off len n : Nat}
    (hm : Ack.Ranges.mem (c.recv off len).buf n = true) :
    Ack.Ranges.mem c.buf n = true ∨ (off ≤ n ∧ n < off + len) :=
  (mem_insertRange (wf_of_WF h) off len n).mp (mem_of_mem_flush hm)

/-- A fully flushed stream is a fixed point of `flush`. -/
theorem flush_of_wfFrom {d : Nat} {l : List Rng} (h : Ack.Ranges.wfFrom (d + 1) l = true) :
    flush d l = (d, l) := by
  cases l with
  | nil => rfl
  | cons r rs =>
    rw [Ack.Ranges.wfFrom_cons_iff] at h
    simp only [flush]
    split
    · omega
    · split
      · omega
      · rfl

/-- An empty frame is a no-op: nothing is added and nothing new is deliverable. -/
theorem recv_zero {c : Crypto} (h : c.WF) (off : Nat) : c.recv off 0 = c := by
  simp [recv, flush_of_wfFrom h]

end Crypto

end Quic.Spec.Handshake
