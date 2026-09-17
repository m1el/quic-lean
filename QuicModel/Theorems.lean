import QuicModel.Packet

/-
  General theorems about the executable model (every input, not test vectors).
  The functions named here are the same ones the fuzz harness calls.
-/
namespace Quic

/-- A varint is encoded in 1, 2, 4 or 8 bytes. -/
theorem varintLen_cases (v : Nat) :
    varintLen v = 1 ∨ varintLen v = 2 ∨ varintLen v = 4 ∨ varintLen v = 8 := by
  unfold varintLen
  repeat' split
  all_goals simp

/-- `take` succeeds exactly when the bytes are there, and then lands `n` further. -/
theorem take_ok {n : Nat} {buf : ByteArray} {pos : Nat} {r : Res pos ByteArray}
    (h : P.take n buf pos = .ok r) : r.val.2 = pos + n ∧ pos + n ≤ buf.size := by
  unfold P.take at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

/-- §19.3.1: if the ACK range check passes, all gaps and ranges fit below
    `smallest`, i.e. no computed packet number is negative. -/
theorem checkAckRanges_none {smallest : Nat} {rs : List AckRange}
    (h : checkAckRanges smallest rs = none) :
    (rs.map fun r => r.gap + 2 + r.len).sum ≤ smallest := by
  induction rs generalizing smallest with
  | nil => simp
  | cons r rs ih =>
    unfold checkAckRanges at h
    split at h
    · cases h
    · split at h
      · cases h
      · have := ih h
        simp only [List.map_cons, List.sum_cons]
        omega

/-- §17.1 / A.3: the recovered packet number agrees with the bits that were on
    the wire. -/
theorem decodePacketNumber_mod (expected truncated len : Nat)
    (h : truncated < 2 ^ (8 * len)) :
    decodePacketNumber expected truncated len % 2 ^ (8 * len) = truncated := by
  unfold decodePacketNumber
  generalize 2 ^ (8 * len) = win at *
  have hwin : 0 < win := by omega
  have hbase : expected - expected % win = win * (expected / win) := by
    have := Nat.div_add_mod expected win
    omega
  simp only [hbase]
  split
  · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.add_mod_right, Nat.mod_eq_of_lt h]
  · split
    · rename_i hc
      obtain ⟨_, hge⟩ := hc
      have hq : 1 ≤ expected / win := by
        rcases Nat.eq_zero_or_pos (expected / win) with h0 | h0
        · rw [h0] at hge; omega
        · exact h0
      obtain ⟨q, hq'⟩ : ∃ q, expected / win = q + 1 := ⟨expected / win - 1, by omega⟩
      rw [hq', Nat.mul_add, Nat.mul_one]
      have : win * q + win + truncated - win = win * q + truncated := by omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]

end Quic
