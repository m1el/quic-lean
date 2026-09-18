import QuicModel.Spec.Ecn.Send

/-
  WP14 (b), parts 8-9: the named theorems and the scenarios of §13.4.
-/
namespace Quic.Spec.Ecn

/-! ## 8. Named theorems -/

/-- §13.4.1, line 5509 with line 5524: the ECT(0) count goes up by exactly one
    per *processed* packet whose IP header carried ECT(0), by nothing otherwise,
    and by nothing at all when the endpoint has no access to the field
    (line 5500). -/
theorem recordRecv_ect0 (s : State) (cp : Codepoint) (pr : Bool) :
    (s.recordRecv cp pr).ect0 = s.ect0 + (if s.reportsEcn && pr then cp.ect0Delta else 0) := by
  unfold State.recordRecv; split <;> simp_all

/-- §13.4.1, line 5525: "As such, duplicate QUIC packets are not processed and
    do not increase ECN counts". -/
theorem recordRecv_duplicate (s : State) (cp : Codepoint) : s.recordRecv cp false = s := by
  simp [State.recordRecv]

theorem recordRecv_mono (s : State) (cp : Codepoint) (pr : Bool) :
    s.ect0 ≤ (s.recordRecv cp pr).ect0 ∧ s.ect1 ≤ (s.recordRecv cp pr).ect1 ∧
      s.ce ≤ (s.recordRecv cp pr).ce := by
  unfold State.recordRecv
  split
  · exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- **(a), one step.**  The received ECN counts never decrease. -/
theorem counts_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) :
    s.ect0 ≤ s'.ect0 ∧ s.ect1 ≤ s'.ect1 ∧ s.ce ≤ s'.ce := by
  cases h
  case recvPacket cp pr => exact recordRecv_mono s cp pr
  all_goals exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- **(a).**  In every reachable state the received ECN counts are at least what
    they were initially — in particular a restart of validation
    (`Event.beginValidation`) does not reset them, which §19.3.2, line 7407
    requires since an ACK frame reports the *total* received in the space. -/
theorem counts_mono_reachable {s₀ s : State} (h : component.Reachable s₀ s) :
    s₀.ect0 ≤ s.ect0 ∧ s₀.ect1 ≤ s.ect1 ∧ s₀.ce ≤ s.ce := by
  refine component.reachable_induction (motive := fun t =>
    s₀.ect0 ≤ t.ect0 ∧ s₀.ect1 ≤ t.ect1 ∧ s₀.ce ≤ t.ce)
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩ ?_ h
  rintro t t' e fx _ hstep ⟨h0, h1, h2⟩
  obtain ⟨g0, g1, g2⟩ := counts_mono hstep
  exact ⟨Nat.le_trans h0 g0, Nat.le_trans h1 g1, Nat.le_trans h2 g2⟩

theorem skipValidation_of_failed {s : State} (h : s.phase = .failed) (l : Nat) :
    skipValidation s l = true := by simp [skipValidation, h]

/-- **(b).**  Validation never *succeeds* again by itself: once the phase is
    `failed`, every step leaves it `failed` except an explicit
    `Event.beginValidation`, which is §13.4.2.2, line 5630's "Even if validation
    fails, an endpoint MAY revalidate ECN for the same path at any later time in
    the connection" (and §13.4.2, line 5561's new path). -/
theorem failed_persists {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hf : s.phase = .failed) :
    s'.phase = .failed ∨ ∃ t, e = .beginValidation t := by
  cases h with
  | @beginValidation t => exact Or.inr ⟨t, rfl⟩
  | @recvPacket cp pr =>
    left
    show (State.recordRecv s cp pr).phase = _
    unfold State.recordRecv; split <;> exact hf
  | @sentPacket m => exact Or.inl hf
  | @lostOk n => exact Or.inl hf
  | @lostFail n _ => exact Or.inl rfl
  | @ackNotValidated l c n _ => exact Or.inl hf
  | @testingEnded => left; simp [State.afterTestingEnded, Phase.afterTesting, hf]
  | @ackFail l c n h0 _ => exact absurd (skipValidation_of_failed hf l) (by rw [h0]; simp)
  | @ackOk l c n h0 _ => exact absurd (skipValidation_of_failed hf l) (by rw [h0]; simp)
  | @ackCapable l c n h0 _ _ =>
    exact absurd (skipValidation_of_failed hf l) (by rw [h0]; simp)
  | @ackRemarkFail l c n h0 _ _ =>
    exact absurd (skipValidation_of_failed hf l) (by rw [h0]; simp)

/-- …and what the text *does* allow: `beginValidation` puts the path back into
    the testing state, from which ECT codepoints are set again. -/
theorem beginValidation_restarts (s : State) (t : Trigger) :
    Step s (.beginValidation t) (.ok s.restart []) ∧ s.restart.phase = .testing :=
  ⟨.beginValidation, rfl⟩

/-- **(c).**  An ACK frame carrying ECN counts that `MaySendPacket` accepts, in a
    packet of this component's space, reports exactly the counts received in
    that space (§19.3.2, line 7407). -/
theorem ack_ecn_counts_exact {s : State} {p : OutPacket} {largest delay first : Nat}
    {ranges : Array AckRange} {e : Ecn}
    (hm : MaySendPacket s p) (hsp : p.ptype.space = some s.space)
    (hf : Frame.ack largest delay first ranges (some e) ∈ p.frames) :
    e.ect0 = s.ect0 ∧ e.ect1 = s.ect1 ∧ e.ce = s.ce := by
  have h := hm hsp _ hf
  simp only [ackEcnOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- §13.4.2.1, line 5613: "An endpoint MUST NOT fail ECN validation as a result
    of processing an ACK frame that does not increase the largest acknowledged
    packet number."  No permitted outcome of such a frame changes the phase. -/
theorem no_fail_on_reordered_ack {s s' : State} {largest : Nat} {c : Option Ecn}
    {n : NewlyAcked} {fx : List Effect} (hinc : increasesLargest s largest = false)
    (h : Step s (.recvAck largest c n) (.ok s' fx)) : s'.phase = s.phase ∧ fx = [] := by
  have hskip : skipValidation s largest = true := by simp [skipValidation, hinc]
  cases h with
  | ackNotValidated => exact ⟨rfl, rfl⟩
  | ackFail h0 _ => rw [hskip] at h0; exact absurd h0 (by simp)
  | ackOk h0 _ => rw [hskip] at h0; exact absurd h0 (by simp)
  | ackCapable h0 _ _ => rw [hskip] at h0; exact absurd h0 (by simp)
  | ackRemarkFail h0 _ _ => rw [hskip] at h0; exact absurd h0 (by simp)

/-- §13.4.2.2, line 5626: every failure both records the failed phase and emits
    `disableEcn`; and after it, marking a packet is no longer permitted. -/
theorem failure_disables {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hfx : Effect.ecnValidationFailed ∈ fx) :
    s'.phase = .failed ∧ Effect.disableEcn ∈ fx ∧ ¬ MayMarkEcn s' true := by
  have key : s'.phase = Phase.failed ∧ Effect.disableEcn ∈ fx := by
    cases h with
    | ackFail => exact ⟨rfl, by simp⟩
    | ackRemarkFail => exact ⟨rfl, by simp⟩
    | lostFail => exact ⟨rfl, by simp⟩
    | recvPacket => exact absurd hfx (by simp)
    | sentPacket => exact absurd hfx (by simp)
    | ackNotValidated => exact absurd hfx (by simp)
    | ackOk => exact absurd hfx (by simp)
    | ackCapable => exact absurd hfx (by simp)
    | lostOk => exact absurd hfx (by simp)
    | beginValidation => exact absurd hfx (by simp)
    | testingEnded => exact absurd hfx (by simp)
  exact ⟨key.1, key.2, fun hc => hc rfl key.1⟩

/-- §13.4.2, line 5549 with §13.4.2.2, line 5626: if every ECN-marked packet
    sent on the path has been declared lost, failing validation is permitted —
    and is the preferred outcome. -/
theorem all_marked_lost_fails {s : State} {n : Nat} (h : allMarkedLost (s.recordLost n) = true) :
    component.step s (.lostMarked n) =
      .ok (s.recordLost n).fail [.ecnValidationFailed, .disableEcn] := by
  simp [Component.step, outcomes, h]

/-- …and line 5557's "it can disable marking" / line 5566's "Other methods … are
    possible" keep not failing available. -/
theorem all_marked_lost_may_continue {s : State} {n : Nat} :
    component.accepts s (.lostMarked n) (.ok (s.recordLost n) []) = true := by
  rw [Component.accepts_iff]
  exact .lostOk

/-! ## 9. Examples (scenarios from the text) -/

private def s0 : State := { space := .appData }

-- §13.4.1, line 5509: an ECT(0)-marked packet is counted; line 5524: a duplicate
-- (not processed) is not.
example : component.step s0 (.recvPacket .ect0 true) = .ok { s0 with ect0 := 1 } [] := by rfl
example : component.step s0 (.recvPacket .ect0 false) = .ok s0 [] := by rfl
-- §13.4.1, line 5500: an endpoint with no access to the field counts nothing.
example : component.step { s0 with reportsEcn := false } (.recvPacket .ce true) =
    .ok { s0 with reportsEcn := false } [] := by rfl

-- §19.3.2, line 7407: an ACK frame must report the totals for its space.
private def s1 : State := { space := .appData, ect0 := 3, ect1 := 0, ce := 1 }
example : maySendPacket s1 ⟨.oneRtt, [.ack 5 0 0 #[] (some ⟨3, 0, 1⟩)]⟩ = true := by decide
example : maySendPacket s1 ⟨.oneRtt, [.ack 5 0 0 #[] (some ⟨3, 0, 0⟩)]⟩ = false := by decide
-- …but an ACK without counts is always sendable (line 5500), and an ACK for
-- another packet number space is none of this instance's business.
example : maySendPacket s1 ⟨.oneRtt, [.ack 5 0 0 #[] none]⟩ = true := by decide
example : maySendPacket s1 ⟨.initial, [.ack 5 0 0 #[] (some ⟨9, 9, 9⟩)]⟩ = true := by decide

-- §13.4.2.1, line 5583: an ACK that newly acknowledges an ECT-marked packet but
-- carries no counts fails validation, and ECN is disabled.
private def s2 : State := { space := .appData, sentEct0 := 2, phase := .unknown }
example : component.step s2 (.recvAck 1 none ⟨1, 1, 0⟩) =
    .ok s2.fail [.ecnValidationFailed, .disableEcn] := by rfl
example : mayMarkEcn s2.fail true = false := by decide
-- …and an ACK that acknowledges no marked packet does not (line 5583 is
-- conditional on one being newly acknowledged).
example : component.accepts s2 (.recvAck 1 none ⟨1, 0, 0⟩)
    (.ok (s2.recordCounts 1 none ⟨1, 0, 0⟩) []) = true := by decide

-- §13.4.2.1, line 5589: one ECT(0) packet newly acknowledged, but neither the
-- ECT(0) nor the CE count went up: validation fails.
example : component.step s2 (.recvAck 1 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩) =
    .ok s2.fail [.ecnValidationFailed, .disableEcn] := by rfl
-- The network remarked it to CE instead: the sum of the increases is 1, so it
-- passes, and §13.4.2.2 line 5634 lets the path become "capable".
example : component.step s2 (.recvAck 1 (some ⟨0, 0, 1⟩) ⟨1, 1, 0⟩) =
    .ok (s2.recordCounts 1 (some ⟨0, 0, 1⟩) ⟨1, 1, 0⟩).capable [.ecnValidated] := by rfl
-- …but staying "unknown" is equally permitted (Appendix A.4 is informative).
example : component.accepts s2 (.recvAck 1 (some ⟨0, 0, 1⟩) ⟨1, 1, 0⟩)
    (.ok (s2.recordCounts 1 (some ⟨0, 0, 1⟩) ⟨1, 1, 0⟩) []) = true := by decide

-- §13.4.2.1, line 5613: a reordered ACK — one that does not increase the largest
-- acknowledged packet number — MUST NOT fail validation.
private def s3 : State :=
  { space := .appData, sentEct0 := 4, largestAcked := some 10, peerEct0 := 4, phase := .capable }
example : component.step s3 (.recvAck 7 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩) =
    .ok (s3.recordAckedOnly ⟨1, 1, 0⟩) [] := by rfl
example : component.accepts s3 (.recvAck 7 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩)
    (.ok s3.fail [.ecnValidationFailed, .disableEcn]) = false := by decide
-- The same counts in an ACK that *does* advance the largest acknowledged number
-- fail, even from "capable" — §13.4.2.2, line 5636: "an endpoint MUST disable
-- ECN if validation later fails".
example : component.step s3 (.recvAck 11 (some ⟨0, 0, 0⟩) ⟨1, 1, 0⟩) =
    .ok s3.fail [.ecnValidationFailed, .disableEcn] := by rfl

-- §13.4.2.1, line 5617: a count for a codepoint we never applied *can* fail
-- validation — and continuing is equally permitted.
private def s4 : State := { space := .appData, sentEct0 := 2, phase := .unknown }
example : component.accepts s4 (.recvAck 1 (some ⟨1, 3, 0⟩) ⟨1, 1, 0⟩)
    (.ok s4.fail [.ecnValidationFailed, .disableEcn]) = true := by decide
example : component.accepts s4 (.recvAck 1 (some ⟨1, 3, 0⟩) ⟨1, 1, 0⟩)
    (.ok (s4.recordCounts 1 (some ⟨1, 3, 0⟩) ⟨1, 1, 0⟩).capable [.ecnValidated]) = true := by
  decide

-- §13.4.2, line 5549: all marked packets deemed lost.
private def s5 : State := { space := .appData, sentEct0 := 3, phase := .testing }
example : component.step s5 (.lostMarked 3) =
    .ok (s5.recordLost 3).fail [.ecnValidationFailed, .disableEcn] := by rfl
example : component.accepts s5 (.lostMarked 2) (.ok (s5.recordLost 2) []) = true := by decide

-- §13.4.2.2, line 5630: revalidation is permitted at any later time, and does
-- not reset the *received* counts (§19.3.2, line 7407).
private def s6 : State :=
  { space := .appData, ect0 := 7, ce := 2, phase := .failed, sentEct0 := 5, markedLost := 5 }
example : component.step s6 (.beginValidation .revalidation) = .ok s6.restart [] := by rfl
example : s6.restart.phase = .testing ∧ s6.restart.ect0 = 7 ∧ s6.restart.ce = 2 := by decide
-- …while an ordinary event never leaves the failed state.
example : (s6.recordRecv .ce true).phase = .failed := by decide
example : mayMarkEcn s6 true = false := by decide
example : mayMarkEcn s6 false = true := by decide

-- Following an implementation we cannot see inside.
example : component.track s0 (.recvPacket .ce true) (.ok []) = some { s0 with ce := 1 } := by
  decide

end Quic.Spec.Ecn
