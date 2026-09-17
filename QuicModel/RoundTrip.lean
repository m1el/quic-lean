import QuicModel.Encode

/-
  decode ∘ encode = id, proved for every well-formed frame.

  `Parses p enc v`: wherever the bytes `enc` sit inside a buffer, running `p` at
  their start returns `v` and leaves the cursor at their end.  Parsers compose
  with `>>=`, encodings with `++`, and `Parses.bind` connects the two.
-/
namespace Quic

/-! Running a parser with the progress proof forgotten commutes with `>>=`, so
    all reasoning below is about plain `Except Err (α × Nat)` values. -/

@[simp] theorem P.run_pure (a : α) (buf : ByteArray) (pos : Nat) :
    (Pure.pure a : P α).run buf pos = .ok (a, pos) := rfl

theorem P.run_bind (p : P α) (f : α → P β) (buf : ByteArray) (pos : Nat) :
    (p >>= f).run buf pos =
      match p.run buf pos with
      | .error e => .error e
      | .ok (a, p1) => (f a).run buf p1 := by
  simp only [P.run, Bind.bind, P.bind]
  cases hp : p buf pos with
  | error e => rfl
  | ok r =>
    obtain ⟨⟨a, p1⟩, h1⟩ := r
    simp only [Except.map]
    cases hf : f a buf p1 with
    | error e => rfl
    | ok r2 => obtain ⟨⟨b, p2⟩, h2⟩ := r2; rfl

theorem P.run_throw (e : Err) (buf : ByteArray) (pos : Nat) :
    (throw e : P α).run buf pos = .error e := rfl

def Parses (p : P α) (enc : ByteArray) (v : α) : Prop :=
  ∀ pre suf : ByteArray, p.run (pre ++ enc ++ suf) pre.size = .ok (v, pre.size + enc.size)

namespace Parses

theorem pure (a : α) : Parses (Pure.pure a : P α) .empty a := by
  intro pre suf
  simp

theorem bind {p : P α} {f : α → P β} {e1 e2 : ByteArray} {a : α} {b : β}
    (hp : Parses p e1 a) (hf : Parses (f a) e2 b) : Parses (p >>= f) (e1 ++ e2) b := by
  intro pre suf
  have hp := hp pre (e2 ++ suf)
  have hf := hf (pre ++ e1) suf
  have hbuf : pre ++ (e1 ++ e2) ++ suf = pre ++ e1 ++ (e2 ++ suf) := by
    simp [ByteArray.append_assoc]
  have hbuf2 : pre ++ e1 ++ e2 ++ suf = pre ++ e1 ++ (e2 ++ suf) := by
    simp [ByteArray.append_assoc]
  rw [hbuf2, ByteArray.size_append] at hf
  rw [P.run_bind, hbuf, hp]
  simp only [hf, ByteArray.size_append, Nat.add_assoc]

/-- The last step of a `do` block: `p` followed by a pure function. -/
theorem map {p : P α} {e : ByteArray} {a : α} (g : α → β) (hp : Parses p e a) :
    Parses (p >>= fun x => (Pure.pure (g x) : P β)) e (g a) := by
  have := bind (f := fun x => (Pure.pure (g x) : P β)) hp (pure (g a))
  rwa [ByteArray.append_empty] at this

/-- `bind` when the continuation consumes nothing. -/
theorem bind_empty {p : P α} {f : α → P β} {e : ByteArray} {a : α} {b : β}
    (hp : Parses p e a) (hf : Parses (f a) .empty b) : Parses (p >>= f) e b := by
  have := bind hp hf
  rwa [ByteArray.append_empty] at this

/-- `let x ← pure a` in a `do` block. -/
theorem pure_bind {f : α → P β} {e : ByteArray} {a : α} {b : β}
    (hf : Parses (f a) e b) : Parses ((Pure.pure a : P α) >>= f) e b := by
  intro pre suf
  rw [P.run_bind, P.run_pure]
  exact hf pre suf

end Parses

theorem bytes_cons (b : UInt8) (bs : List UInt8) : bytes (b :: bs) = bytes [b] ++ bytes bs := by
  apply ByteArray.ext
  simp [bytes, ByteArray.data_append]

theorem bytes_nil : bytes [] = .empty := rfl

@[simp] theorem size_bytes (l : List UInt8) : (bytes l).size = l.length := by
  simp [bytes, ByteArray.size]

theorem parses_u8 (b : UInt8) : Parses P.u8 (bytes [b]) b := by
  intro pre suf
  have hlt : pre.size < (pre ++ bytes [b] ++ suf).size := by
    simp [ByteArray.size_append]; omega
  have hget : (pre ++ bytes [b] ++ suf)[pre.size]'hlt = b := by
    rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append])]
    rw [ByteArray.getElem_append_right (by simp)]
    simp [bytes, ByteArray.getElem_eq_getElem_data]
  simp only [P.run, P.u8, hlt, dite_true, Except.map, hget, size_bytes, List.length_singleton]

theorem parses_take (bs : ByteArray) : Parses (P.take bs.size) bs bs := by
  intro pre suf
  have hle : pre.size + bs.size ≤ (pre ++ bs ++ suf).size := by
    simp [ByteArray.size_append]
  have hext : (pre ++ bs ++ suf).extract pre.size (pre.size + bs.size) = bs := by
    rw [ByteArray.append_assoc]
    have := ByteArray.extract_append_size_add (a := pre) (b := bs ++ suf) (i := 0) (j := bs.size)
    rw [Nat.add_zero] at this
    rw [this, ByteArray.extract_append_eq_left rfl]
  simp only [P.run, P.take, hle, ite_true, Except.map, hext]

theorem getElem_mid (pre rest suf : ByteArray) (b : UInt8)
    (h : pre.size < (pre ++ (bytes [b] ++ rest) ++ suf).size) :
    (pre ++ (bytes [b] ++ rest) ++ suf)[pre.size]'h = b := by
  rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega)]
  rw [ByteArray.getElem_append_right (by simp)]
  rw [ByteArray.getElem_append_left (by simp)]
  simp [bytes, ByteArray.getElem_eq_getElem_data]

/-! ### Varints -/

theorem parses_varintTail (b0 : UInt8) (tail : List UInt8)
    (h : tail.length = 2 ^ (b0.toNat >>> 6) - 1) :
    Parses (P.varintTail b0) (bytes tail)
      (beNat (bytes tail) (b0.toNat &&& 0x3f), 2 ^ (b0.toNat >>> 6)) := by
  have ht := parses_take (bytes tail)
  rw [size_bytes, h] at ht
  exact Parses.map (fun t => (beNat t (b0.toNat &&& 0x3f), 2 ^ (b0.toNat >>> 6))) ht

theorem parses_varintL (b0 : UInt8) (tail : List UInt8)
    (h : tail.length = 2 ^ (b0.toNat >>> 6) - 1) :
    Parses P.varintL (bytes (b0 :: tail))
      (beNat (bytes tail) (b0.toNat &&& 0x3f), 2 ^ (b0.toNat >>> 6)) := by
  rw [bytes_cons]
  exact Parses.bind (parses_u8 b0) (parses_varintTail b0 tail h)

/-- First-byte facts, checked for all 64 possible values of the top six bits. -/
theorem tag_bits : ∀ x, x < 64 →
    ((UInt8.ofNat x).toNat >>> 6 = 0 ∧ (UInt8.ofNat x).toNat &&& 0x3f = x) ∧
    ((UInt8.ofNat x ||| 0x40).toNat >>> 6 = 1 ∧ (UInt8.ofNat x ||| 0x40).toNat &&& 0x3f = x) ∧
    ((UInt8.ofNat x ||| 0x80).toNat >>> 6 = 2 ∧ (UInt8.ofNat x ||| 0x80).toNat &&& 0x3f = x) ∧
    ((UInt8.ofNat x ||| 0xc0).toNat >>> 6 = 3 ∧ (UInt8.ofNat x ||| 0xc0).toNat &&& 0x3f = x) := by
  decide

theorem beNat_bytes (l : List UInt8) (init : Nat) :
    beNat (bytes l) init = l.foldl (fun acc x => acc * 256 + x.toNat) init := by
  simp [beNat, bytes]

/-- §16: a varint decodes to the value it encodes, and reports its length. -/
theorem parses_varintL_encode (v : Nat) (hv : v ≤ maxVarint) :
    Parses P.varintL (encodeVarint v) (v, varintLen v) := by
  have hv : v < 4611686018427387904 := by simp [maxVarint] at hv; omega
  unfold encodeVarint varintLen
  split
  · obtain ⟨⟨h6, hm⟩, -⟩ := tag_bits (v % 256) (by omega)
    have := parses_varintL (UInt8.ofNat (v % 256)) [] (by rw [h6]; rfl)
    rw [beNat_bytes, h6, hm] at this
    have hval : List.foldl (fun acc (x : UInt8) => acc * 256 + x.toNat) (v % 256) [] = v := by
      simp; omega
    rw [hval] at this
    have henc : encodeVarintWith v 1 = bytes ((UInt8.ofNat (v % 256)) :: []) := by
      simp [encodeVarintWith, beBytes, bytes]
    rw [henc]
    exact this
  split
  · obtain ⟨-, ⟨h6, hm⟩, -⟩ := tag_bits (v / 256 % 256) (by omega)
    have := parses_varintL (UInt8.ofNat (v / 256 % 256) ||| 0x40) [UInt8.ofNat (v % 256)] (by rw [h6]; rfl)
    rw [beNat_bytes, h6, hm] at this
    have hval : List.foldl (fun acc (x : UInt8) => acc * 256 + x.toNat) (v / 256 % 256) [UInt8.ofNat (v % 256)] = v := by
      simp; omega
    rw [hval] at this
    have henc : encodeVarintWith v 2 = bytes ((UInt8.ofNat (v / 256 % 256) ||| 0x40) :: [UInt8.ofNat (v % 256)]) := by
      simp [encodeVarintWith, beBytes, bytes]
    rw [henc]
    exact this
  split
  · obtain ⟨-, -, ⟨h6, hm⟩, -⟩ := tag_bits (v / 256 / 256 / 256 % 256) (by omega)
    have := parses_varintL (UInt8.ofNat (v / 256 / 256 / 256 % 256) ||| 0x80) [UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)] (by rw [h6]; rfl)
    rw [beNat_bytes, h6, hm] at this
    have hval : List.foldl (fun acc (x : UInt8) => acc * 256 + x.toNat) (v / 256 / 256 / 256 % 256) [UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)] = v := by
      simp; omega
    rw [hval] at this
    have henc : encodeVarintWith v 4 = bytes ((UInt8.ofNat (v / 256 / 256 / 256 % 256) ||| 0x80) :: [UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]) := by
      simp [encodeVarintWith, beBytes, bytes]
    rw [henc]
    exact this
  · obtain ⟨-, -, -, ⟨h6, hm⟩⟩ := tag_bits (v / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256) (by omega)
    have := parses_varintL (UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256) ||| 0xc0) [UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)] (by rw [h6]; rfl)
    rw [beNat_bytes, h6, hm] at this
    have hval : List.foldl (fun acc (x : UInt8) => acc * 256 + x.toNat) (v / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256) [UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)] = v := by
      simp; omega
    rw [hval] at this
    have henc : encodeVarintWith v 8 = bytes ((UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256) ||| 0xc0) :: [UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 / 256 % 256), UInt8.ofNat (v / 256 / 256 % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v % 256)]) := by
      simp [encodeVarintWith, beBytes, bytes]
    rw [henc]
    exact this

theorem parses_varint (v : Nat) (hv : v ≤ maxVarint) :
    Parses P.varint (encodeVarint v) v :=
  Parses.map (fun r : Nat × Nat => r.1) (parses_varintL_encode v hv)

theorem size_encodeVarint (v : Nat) : (encodeVarint v).size = varintLen v := by
  unfold encodeVarint varintLen
  repeat' split
  all_goals simp [encodeVarintWith, beBytes, ByteArray.size]

theorem one_le_size_encodeVarint (v : Nat) : 1 ≤ (encodeVarint v).size := by
  rw [size_encodeVarint]
  unfold varintLen
  repeat' split
  all_goals omega

/-! ### ACK ranges -/

theorem parses_ackRangesAux (rs : List AckRange) (acc : Array AckRange)
    (h : ∀ r ∈ rs, r.gap ≤ maxVarint ∧ r.len ≤ maxVarint) :
    Parses (ackRangesAux rs.length acc) (encodeAckRanges rs) (acc ++ rs.toArray) := by
  induction rs generalizing acc with
  | nil => simpa [ackRangesAux, encodeAckRanges] using Parses.pure acc
  | cons r rs ih =>
    have hr := h r (by simp)
    have := ih (acc.push r) (fun x hx => h x (by simp [hx]))
    have hacc : acc.push r ++ rs.toArray = acc ++ (r :: rs).toArray := by simp
    rw [hacc] at this
    exact Parses.bind (parses_varint r.gap hr.1) (Parses.bind (parses_varint r.len hr.2) this)

theorem two_mul_le_size_encodeAckRanges (rs : List AckRange) :
    rs.length * 2 ≤ (encodeAckRanges rs).size := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have h1 := one_le_size_encodeVarint r.gap
    have h2 := one_le_size_encodeVarint r.len
    simp only [encodeAckRanges, vi, ByteArray.size_append, List.length_cons]
    omega

theorem parses_ackRanges (rs : Array AckRange)
    (h : ∀ r ∈ rs.toList, r.gap ≤ maxVarint ∧ r.len ≤ maxVarint) :
    Parses (ackRanges rs.size) (encodeAckRanges rs.toList) rs := by
  intro pre suf
  have hsz := two_mul_le_size_encodeAckRanges rs.toList
  have haux := parses_ackRangesAux rs.toList #[] h pre suf
  simp only [Array.length_toList] at haux hsz
  have hrem : ¬ rs.size * 2 >
      (pre ++ encodeAckRanges rs.toList ++ suf).size - pre.size := by
    simp only [ByteArray.size_append]; omega
  have hrun : P.remaining.run (pre ++ encodeAckRanges rs.toList ++ suf) pre.size =
      .ok ((pre ++ encodeAckRanges rs.toList ++ suf).size - pre.size, pre.size) := rfl
  unfold ackRanges
  rw [P.run_bind, hrun]
  simp only [hrem, ↓reduceIte]
  simpa [Array.mkEmpty] using haux

/-! ### Frames -/

open P in
/-- The fields of every self-delimiting frame decode back to the frame. -/
theorem parses_frameOfType (f : Frame) (hwf : f.WF) (hsd : f.SelfDelimiting) :
    Parses (frameOfType f.typeByte.toNat) f.encodeBody f := by
  cases f with
  | padding len => exact absurd hsd id
  | ping => exact Parses.pure _
  | handshakeDone => exact Parses.pure _
  | ack largest delay first ranges ecn =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hwf
    cases ecn with
    | none =>
      exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h2)
        (Parses.bind (parses_varint _ h4) (Parses.bind (parses_varint _ h3)
          (Parses.bind (parses_ackRanges ranges h5) (Parses.pure_bind (Parses.pure _))))))
    | some e =>
      obtain ⟨e1, e2, e3⟩ := h6 e rfl
      exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h2)
        (Parses.bind (parses_varint _ h4) (Parses.bind (parses_varint _ h3)
          (Parses.bind (parses_ackRanges ranges h5)
            (Parses.bind (parses_varint _ e1) (Parses.bind (parses_varint _ e2)
              (Parses.bind_empty (parses_varint _ e3)
                (Parses.pure_bind (Parses.pure _)))))))))
  | resetStream id err fs =>
    obtain ⟨h1, h2, h3⟩ := hwf
    exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h2)
      (Parses.map _ (parses_varint _ h3)))
  | stopSending id err =>
    exact Parses.bind (parses_varint _ hwf.1) (Parses.map _ (parses_varint _ hwf.2))
  | crypto off data =>
    exact Parses.bind (parses_varint _ hwf.1) (Parses.bind (parses_varint _ hwf.2)
      (Parses.map _ (parses_take data)))
  | newToken token =>
    exact Parses.bind (parses_varint _ hwf) (Parses.map _ (parses_take token))
  | maxData v => exact Parses.map _ (parses_varint _ hwf)
  | dataBlocked v => exact Parses.map _ (parses_varint _ hwf)
  | retireConnectionId v => exact Parses.map _ (parses_varint _ hwf)
  | maxStreams dir v => cases dir <;> exact Parses.map _ (parses_varint _ hwf)
  | streamsBlocked dir v => cases dir <;> exact Parses.map _ (parses_varint _ hwf)
  | maxStreamData id v =>
    exact Parses.bind (parses_varint _ hwf.1) (Parses.map _ (parses_varint _ hwf.2))
  | streamDataBlocked id v =>
    exact Parses.bind (parses_varint _ hwf.1) (Parses.map _ (parses_varint _ hwf.2))
  | pathChallenge d =>
    have := parses_take d
    rw [show d.size = 8 from hwf] at this
    exact Parses.map _ this
  | pathResponse d =>
    have := parses_take d
    rw [show d.size = 8 from hwf] at this
    exact Parses.map _ this
  | connectionClose err fty reason =>
    obtain ⟨h1, h2, h3⟩ := hwf
    cases fty with
    | none =>
      exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h3)
        (Parses.map _ (parses_take reason)))
    | some t =>
      exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ (h2 t rfl))
        (Parses.bind (parses_varint _ h3) (Parses.map _ (parses_take reason))))
  | datagram hasLen data =>
    cases hasLen with
    | false => exact absurd hsd id
    | true => exact Parses.bind (parses_varint _ hwf) (Parses.map _ (parses_take data))
  | newConnectionId seq rpt cid token =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
    have hcil : (cid.size.toUInt8).toNat = cid.size := by
      simp [Nat.toUInt8]; omega
    have htok := parses_take token
    rw [h5] at htok
    refine Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h2)
      (Parses.bind (parses_u8 _) ?_))
    simp only [hcil]
    have hok : ¬ (cid.size < 1 ∨ cid.size > 20) := by omega
    simp only [hok, ↓reduceIte]
    exact Parses.bind (parses_take cid) (Parses.map _ htok)
  | stream id off fin data =>
    obtain ⟨h1, h2, h3⟩ := hwf
    by_cases ho : off = 0
    · subst ho
      simp only [Frame.typeByte, Frame.encodeBody, ne_eq, not_true_eq_false, ↓reduceIte,
        ByteArray.empty_append]
      cases fin <;>
        exact Parses.bind (parses_varint _ h1) (Parses.pure_bind
          (Parses.bind (parses_varint _ h3) (Parses.map _ (parses_take data))))
    · simp only [Frame.typeByte, Frame.encodeBody, ne_eq, ho, not_false_eq_true, ↓reduceIte]
      cases fin <;>
        exact Parses.bind (parses_varint _ h1) (Parses.bind (parses_varint _ h2)
          (Parses.bind (parses_varint _ h3) (Parses.map _ (parses_take data))))

/-- Every frame type in the model is below 64, i.e. a one-byte varint. -/
theorem typeByte_lt (f : Frame) : f.typeByte.toNat < 64 := by
  cases f with
  | ack _ _ _ _ ecn => cases ecn <;> simp [Frame.typeByte]
  | stream _ off fin _ =>
    by_cases ho : off = 0 <;> cases fin <;> simp [Frame.typeByte, ho]
  | maxStreams d _ => cases d <;> simp [Frame.typeByte]
  | streamsBlocked d _ => cases d <;> simp [Frame.typeByte]
  | connectionClose _ fty _ => cases fty <;> simp [Frame.typeByte]
  | datagram l _ => cases l <;> simp [Frame.typeByte]
  | _ => simp [Frame.typeByte]

/-! ### Frames that run to the end of the packet

`ParsesIf S` is `Parses` restricted to suffixes satisfying `S`: PADDING decodes
back only if the next byte is not another zero, and DATAGRAM without a Length
only if nothing follows. -/

def ParsesIf (S : ByteArray → Prop) (p : P α) (enc : ByteArray) (v : α) : Prop :=
  ∀ pre suf : ByteArray, S suf →
    p.run (pre ++ enc ++ suf) pre.size = .ok (v, pre.size + enc.size)

theorem Parses.toIf {S : ByteArray → Prop} {p : P α} {e : ByteArray} {v : α}
    (h : Parses p e v) : ParsesIf S p e v := fun pre suf _ => h pre suf

theorem ParsesIf.bind {S : ByteArray → Prop} {p : P α} {f : α → P β} {e1 e2 : ByteArray}
    {a : α} {b : β} (hp : Parses p e1 a) (hf : ParsesIf S (f a) e2 b) :
    ParsesIf S (p >>= f) (e1 ++ e2) b := by
  intro pre suf hs
  have hp := hp pre (e2 ++ suf)
  have hf := hf (pre ++ e1) suf hs
  have hbuf : pre ++ (e1 ++ e2) ++ suf = pre ++ e1 ++ (e2 ++ suf) := by
    simp [ByteArray.append_assoc]
  have hbuf2 : pre ++ e1 ++ e2 ++ suf = pre ++ e1 ++ (e2 ++ suf) := by
    simp [ByteArray.append_assoc]
  rw [hbuf2, ByteArray.size_append] at hf
  rw [P.run_bind, hbuf, hp]
  simp only [hf, ByteArray.size_append, Nat.add_assoc]

theorem ParsesIf.map {S : ByteArray → Prop} {p : P α} {e : ByteArray} {a : α} (g : α → β)
    (hp : ParsesIf S p e a) : ParsesIf S (p >>= fun x => (Pure.pure (g x) : P β)) e (g a) := by
  intro pre suf hs
  rw [P.run_bind, hp pre suf hs]
  rfl

/-- What may follow a frame's encoding for it to decode back. -/
def Frame.FollowOk : Frame → ByteArray → Prop
  | .padding _, suf => ∀ h : 0 < suf.size, suf[0] ≠ 0
  | .datagram false _, suf => suf = .empty
  | _, _ => True

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

theorem zeros_succ (n : Nat) : zeros (n + 1) = bytes [0] ++ zeros n := by
  apply ByteArray.ext
  simp [zeros, bytes, ByteArray.data_append, Array.replicate_succ']

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simp [zeros, ByteArray.size]

theorem zeroRun_zeros (n : Nat) (pre suf : ByteArray) (acc : Nat)
    (hs : ∀ h : 0 < suf.size, suf[0] ≠ 0) :
    zeroRun (pre ++ zeros n ++ suf) pre.size acc = acc + n := by
  induction n generalizing pre acc with
  | zero =>
    unfold zeroRun
    have hz : zeros 0 = .empty := rfl
    simp only [hz, ByteArray.append_empty, ByteArray.size_append]
    by_cases h : 0 < suf.size
    · have hlt : pre.size < pre.size + suf.size := by omega
      have hget : (pre ++ suf)[pre.size]'(by simp [ByteArray.size_append]; omega) = suf[0] := by
        rw [ByteArray.getElem_append_right (by simp)]
        simp
      simp only [hlt, ↓reduceDIte, hget, hs h, ↓reduceIte, Nat.add_zero]
    · have hlt : ¬ pre.size < pre.size + suf.size := by omega
      simp only [hlt, ↓reduceDIte, Nat.add_zero]
  | succ n ih =>
    unfold zeroRun
    have hlt : pre.size < (pre ++ zeros (n + 1) ++ suf).size := by
      simp [ByteArray.size_append]; omega
    have hget : (pre ++ zeros (n + 1) ++ suf)[pre.size]'hlt = 0 := by
      have := getElem_mid pre (zeros n) suf 0 (by rw [← zeros_succ]; exact hlt)
      simpa only [zeros_succ] using this
    have hbuf : pre ++ zeros (n + 1) ++ suf = pre ++ bytes [0] ++ zeros n ++ suf := by
      simp [zeros_succ, ByteArray.append_assoc]
    have := ih (pre ++ bytes [0]) (acc + 1)
    simp only [ByteArray.size_append, size_bytes, List.length_singleton] at this
    simp only [hlt, ↓reduceDIte, hget, ↓reduceIte]
    rw [hbuf, this]
    omega

theorem parsesIf_skipZeros (n : Nat) :
    ParsesIf (fun suf => ∀ h : 0 < suf.size, suf[0] ≠ 0) P.skipZeros (zeros n) n := by
  intro pre suf hs
  have := zeroRun_zeros n pre suf 0 hs
  simp only [Nat.zero_add] at this
  simp only [P.run, P.skipZeros, Except.map, this, size_zeros]

theorem parsesIf_rest (bs : ByteArray) : ParsesIf (· = .empty) P.rest bs bs := by
  intro pre suf hs
  subst hs
  have hext : (pre ++ bs).extract pre.size (pre ++ bs).size = bs :=
    ByteArray.extract_append_eq_right rfl (by simp [ByteArray.size_append])
  have hmax : max pre.size (pre ++ bs).size = pre.size + bs.size := by
    simp [ByteArray.size_append]
  simp only [ByteArray.append_empty, P.run, P.rest, Except.map, hext, hmax]

/-- Every well-formed frame's fields decode back to the frame, given a
    permissible continuation. -/
theorem parsesIf_frameOfType (f : Frame) (hwf : f.WF) :
    ParsesIf f.FollowOk (frameOfType f.typeByte.toNat) f.encodeBody f := by
  cases f with
  | padding len =>
    have hlen : 1 + (len - 1) = len := by have : 1 ≤ len := hwf; omega
    have := ParsesIf.map (fun k => Frame.padding (1 + k)) (parsesIf_skipZeros (len - 1))
    rw [hlen] at this
    exact this
  | datagram hasLen data =>
    cases hasLen with
    | false => exact ParsesIf.map (Frame.datagram false) (parsesIf_rest data)
    | true => exact (parses_frameOfType _ hwf trivial).toIf
  | _ => exact (parses_frameOfType _ hwf trivial).toIf

/-- For a one-byte frame type, `frameBody` is just the dispatch on that type. -/
theorem parsesIf_frameBody {S : ByteArray → Prop} {b0 : UInt8} (hb : b0.toNat < 64)
    {e : ByteArray} {f : Frame} (h : ParsesIf S (frameOfType b0.toNat) e f) :
    ParsesIf S (frameBody b0) e f := by
  obtain ⟨⟨h6, hm⟩, -⟩ := tag_bits b0.toNat hb
  rw [UInt8.ofNat_toNat] at h6 hm
  have ht := parses_varintTail b0 [] (by rw [h6]; rfl)
  rw [beNat_bytes, h6, hm] at ht
  have hlen : ¬ (2 ^ 0 ≠ varintLen b0.toNat) := by simp [varintLen, hb]
  have := ParsesIf.bind (f := fun (r : Nat × Nat) => (do
      if r.2 ≠ varintLen r.1 then throw (Err.nonMinimalFrameType r.1)
      frameOfType r.1 : P Frame)) ht (by simpa only [List.foldl_nil, hlen, ↓reduceIte] using h)
  rw [bytes_nil, ByteArray.empty_append] at this
  exact this

/-- `decodeFrame`, with its progress proof forgotten. -/
theorem decodeFrame_val (buf : ByteArray) (pos : Nat) (h : pos < buf.size) :
    (decodeFrame buf pos).map (·.val) = (frameBody buf[pos]).run buf (pos + 1) := by
  unfold decodeFrame P.run
  simp only [h, ↓reduceDIte]
  cases frameBody buf[pos] buf (pos + 1) with
  | error e => rfl
  | ok r => obtain ⟨r, hr⟩ := r; rfl

/-- **Round trip.**  A well-formed frame decodes back to itself wherever its
    encoding sits in a packet payload, and the cursor lands exactly at its end,
    provided what follows is permissible (`Frame.FollowOk`: anything at all,
    except after PADDING and length-less DATAGRAM). -/
theorem decodeFrame_encodeFrame (f : Frame) (hwf : f.WF) (pre suf : ByteArray)
    (hs : f.FollowOk suf) :
    (decodeFrame (pre ++ encodeFrame f ++ suf) pre.size).map (·.val) =
      .ok (f, pre.size + (encodeFrame f).size) := by
  have hlt : pre.size < (pre ++ encodeFrame f ++ suf).size := by
    simp [encodeFrame, ByteArray.size_append]; omega
  rw [decodeFrame_val _ _ hlt]
  have hb : (pre ++ encodeFrame f ++ suf)[pre.size]'hlt = f.typeByte :=
    getElem_mid pre f.encodeBody suf f.typeByte hlt
  rw [hb]
  have := parsesIf_frameBody (typeByte_lt f) (parsesIf_frameOfType f hwf)
    (pre ++ bytes [f.typeByte]) suf hs
  simp only [ByteArray.size_append, size_bytes, List.length_singleton] at this
  simpa only [encodeFrame, ByteArray.append_assoc, ByteArray.size_append, size_bytes,
    List.length_singleton, Nat.add_assoc] using this

/-- Self-delimiting frames round-trip in any context. -/
theorem decodeFrame_encodeFrame_at (f : Frame) (hwf : f.WF) (hsd : f.SelfDelimiting)
    (pre suf : ByteArray) :
    (decodeFrame (pre ++ encodeFrame f ++ suf) pre.size).map (·.val) =
      .ok (f, pre.size + (encodeFrame f).size) := by
  refine decodeFrame_encodeFrame f hwf pre suf ?_
  cases f with
  | padding _ => exact absurd hsd id
  | datagram l _ => cases l with
    | false => exact absurd hsd id
    | true => trivial
  | _ => trivial

/-- Every well-formed frame round-trips as the whole payload. -/
theorem decodeFrame_encodeFrame_exact (f : Frame) (hwf : f.WF) :
    (decodeFrame (encodeFrame f) 0).map (·.val) = .ok (f, (encodeFrame f).size) := by
  have := decodeFrame_encodeFrame f hwf .empty .empty (by
    cases f with
    | padding _ => intro h; simp at h
    | datagram l _ => cases l <;> simp [Frame.FollowOk]
    | _ => trivial)
  rw [ByteArray.empty_append, ByteArray.append_empty] at this
  have h0 : ByteArray.empty.size + (encodeFrame f).size = (encodeFrame f).size := by simp
  rw [h0] at this
  exact this

end Quic
