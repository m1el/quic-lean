import QuicModel.Spec.Core

/-!
  Shared vocabulary for the two connection-ID sets of §5.1, plus the handful of
  list lemmas both halves need.

  WP4 models one endpoint's view of connection IDs as two components:

  * `ConnIds.Remote` — the IDs the *peer* issued to us, which we use as
    Destination Connection IDs (§5.1.2, §19.15 receive side, §19.16 send side);
  * `ConnIds.Local`  — the IDs *we* issued to the peer (§5.1.1, §19.15 send
    side, §19.16 receive side).

  Choosing which of the remote IDs to use on which path is WP10; stateless
  reset detection from the tokens is WP6; learning the initial IDs and the
  `active_connection_id_limit` from the handshake is WP11.  Here the initial
  IDs (sequence number 0, and sequence number 1 from `preferred_address`) and
  both limits are parameters of the initial state.
-/
namespace Quic.Spec.ConnIds

/-- A connection ID: 1..20 bytes (§19.15).  Bytes are a `List UInt8` rather
    than `ByteArray` so that states have a `DecidableEq` that the kernel can
    actually run for `decide`; frames are converted with `ByteArray.toList`. -/
abbrev Cid := List UInt8

/-- A 128-bit stateless reset token (§19.15); 16 bytes. -/
abbrev ResetToken := List UInt8

/-- §19.15, line 7959: "Values less than 1 and greater than 20 are invalid". -/
def cidLenOk (c : Cid) : Bool := 1 ≤ c.length && c.length ≤ 20

/-- §19.15, line 7966: "Stateless Reset Token: A 128-bit value". -/
def tokenLenOk (t : ResetToken) : Bool := t.length == 16

/-- One connection ID with the sequence number and reset token it came with. -/
structure Entry where
  seq : Nat
  cid : Cid
  token : ResetToken
  deriving DecidableEq, Repr

/-- The sequence numbers of a list of entries. -/
def seqs (es : List Entry) : List Nat := es.map (·.seq)

/-- The entry carrying a given sequence number, if any. -/
def entryOf? (es : List Entry) (n : Nat) : Option Entry := es.find? (fun e => e.seq == n)

@[simp] theorem mem_seqs {es : List Entry} {n : Nat} :
    n ∈ seqs es ↔ ∃ e ∈ es, e.seq = n := by
  simp [seqs, eq_comm]

@[simp] theorem seqs_append (a b : List Entry) : seqs (a ++ b) = seqs a ++ seqs b := by
  simp [seqs]

@[simp] theorem seqs_singleton (e : Entry) : seqs [e] = [e.seq] := rfl

theorem entryOf?_eq_none {es : List Entry} {n : Nat} :
    entryOf? es n = none ↔ n ∉ seqs es := by
  simp [entryOf?, List.find?_eq_none]

/-- If a lookup succeeds, it returns an entry of the list with that number. -/
theorem entryOf?_sound {es : List Entry} {n : Nat} {e : Entry}
    (h : entryOf? es n = some e) : e ∈ es ∧ e.seq = n := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem entryOf?_isSome {es : List Entry} {n : Nat} :
    (entryOf? es n).isSome = true ↔ n ∈ seqs es := by
  cases h : entryOf? es n with
  | none => simp [entryOf?_eq_none.mp h]
  | some e =>
    obtain ⟨hm, hs⟩ := entryOf?_sound h
    simp only [Option.isSome_some, true_iff, mem_seqs]
    exact ⟨e, hm, hs⟩

theorem nodup_append_singleton {α : Type} {l : List α} {a : α} (h : l.Nodup) (ha : a ∉ l) :
    (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.nodup_cons] at h
    simp only [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih h.2 (fun hm => ha (List.mem_cons_of_mem x hm))⟩
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 hm
    · exact ha (by simp [List.mem_singleton.mp hm])

/-- A list whose images under `f` are distinct has no two distinct members with
    the same image. -/
theorem nodup_map_inj {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hf : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, ht⟩ := h
    have hx' : ∀ y ∈ t, f y ≠ f x := by
      intro y hy hfy
      exact hx (by rw [← hfy]; simp only [List.mem_map]; exact ⟨y, hy, rfl⟩)
    rw [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact absurd hf.symm (hx' b hb)
    · rcases hb with rfl | hb
      · exact absurd hf (hx' a ha)
      · exact ih ht ha hb

/-- Sequence numbers pick out at most one entry. -/
theorem entry_eq_of_seq_eq {es : List Entry} (h : (seqs es).Nodup) {a b : Entry}
    (ha : a ∈ es) (hb : b ∈ es) (hs : a.seq = b.seq) : a = b :=
  nodup_map_inj h ha hb hs

/-- Shrinking the predicate of a `filter` cannot make the result longer. -/
theorem length_filter_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hp : p a = true
    · have hq : q a = true := h a (by simp) hp
      simp [hp, hq] <;> omega
    · simp only [Bool.not_eq_true] at hp
      by_cases hq : q a = true
      · simp [hp, hq] <;> omega
      · simp only [Bool.not_eq_true] at hq
        simp [hp, hq] <;> omega

end Quic.Spec.ConnIds
