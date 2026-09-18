import QuicModel.Spec.Ecn.Basic

/-
  WP14 (b), parts 2-5: the validation checks of §13.4.2.1, the `Step` relation,
  `outcomes` / `outcomes_iff`, and the invariant.
-/
namespace Quic.Spec.Ecn

/-! ## 2. The specification -/

def peerEct0Of (s : State) : Option Ecn → Nat
  | none => s.peerEct0
  | some e => e.ect0

def peerEct1Of (s : State) : Option Ecn → Nat
  | none => s.peerEct1
  | some e => e.ect1

def peerCeOf (s : State) : Option Ecn → Nat
  | none => s.peerCe
  | some e => e.ce

/-- §13.4.1, line 5509: "On receiving an IP packet with an ECT(0), ECT(1) or CE
    codepoint, an ECN-enabled endpoint accesses the ECN field and increases the
    corresponding ECT(0), ECT(1), or CE count." -/
def State.recordRecv (s : State) (cp : Codepoint) (processed : Bool) : State :=
  if s.reportsEcn && processed then
    { s with
      ect0 := s.ect0 + cp.ect0Delta
      ect1 := s.ect1 + cp.ect1Delta
      ce := s.ce + cp.ceDelta }
  else s

def State.recordSent (s : State) (m : Mark) : State :=
  { s with
    sentEct0 := s.sentEct0 + m.ect0Delta
    sentEct1 := s.sentEct1 + m.ect1Delta }

def State.recordLost (s : State) (n : Nat) : State :=
  { s with markedLost := s.markedLost + n }

/-- An ACK frame that is not used for validation still tells us which marked
    packets have arrived. -/
def State.recordAckedOnly (s : State) (n : NewlyAcked) : State :=
  { s with markedAcked := s.markedAcked + n.ect0 + n.ect1 }

/-- §13.4.2.1, line 5577: remember the counts of "the last successfully
    processed ACK frame". -/
def State.recordCounts (s : State) (largest : Nat) (c : Option Ecn) (n : NewlyAcked) : State :=
  { s with
    peerEct0 := peerEct0Of s c
    peerEct1 := peerEct1Of s c
    peerCe := peerCeOf s c
    largestAcked := some largest
    markedAcked := s.markedAcked + n.ect0 + n.ect1 }

def State.fail (s : State) : State := { s with phase := .failed }
def State.capable (s : State) : State := { s with phase := .capable }

/-- §13.4.2, line 5561 and §13.4.2.2, line 5630.  The *received* counts are not
    reset: §19.3.2, line 7407 requires an ACK frame to report the total received
    in the space, and Appendix A.4, line 10262 says "existing ECN counts are
    remembered as a baseline". -/
def State.restart (s : State) : State :=
  { s with phase := .testing, sentEct0 := 0, sentEct1 := 0, markedAcked := 0, markedLost := 0 }

def State.afterTestingEnded (s : State) : State :=
  { s with phase := s.phase.afterTesting }

/-- §13.4.2.1, line 5613: "An endpoint MUST NOT fail ECN validation as a result
    of processing an ACK frame that does not increase the largest acknowledged
    packet number." -/
def increasesLargest (s : State) (largest : Nat) : Bool :=
  match s.largestAcked with
  | none => true
  | some m => decide (m < largest)

/-- The ACK frame is not used for validation at all: either validation has
    already failed (§13.4.2.2, line 5626, ECN is disabled) or the frame does not
    increase the largest acknowledged packet number (line 5613). -/
def skipValidation (s : State) (largest : Nat) : Bool :=
  decide (s.phase = .failed) || !increasesLargest s largest

/-- The two MUST-fail checks of §13.4.2.1.

    * line 5583: "If an ACK frame newly acknowledges a packet that the endpoint
      sent with either the ECT(0) or ECT(1) codepoint set, ECN validation fails
      if the corresponding ECN counts are not present in the ACK frame."
    * line 5589: "ECN validation also fails if the sum of the increase in ECT(0)
      and ECN-CE counts is less than the number of newly acknowledged packets
      that were originally sent with an ECT(0) marking.  Similarly, ECN
      validation fails if the sum of the increases to ECT(1) and ECN-CE counts
      is less than the number of newly acknowledged packets sent with an ECT(1)
      marking."

    The second check is written over the integers as
    `(new.ect0 - old.ect0) + (new.ce - old.ce) < newly.ect0`; rearranged into
    `Nat` it is the inequality below, which is also what makes a *decrease* in
    a count a failure whenever any marked packet is newly acknowledged
    (NOTE 4). -/
def failsValidation (s : State) (c : Option Ecn) (n : NewlyAcked) : Bool :=
  match c with
  | none => decide (0 < n.ect0 + n.ect1)
  | some e =>
    decide (e.ect0 + e.ce < s.peerEct0 + s.peerCe + n.ect0) ||
    decide (e.ect1 + e.ce < s.peerEct1 + s.peerCe + n.ect1)

/-- §13.4.2.1, line 5617: "ECN validation *can* fail if the received total count
    for either ECT(0) or ECT(1) exceeds the total number of packets sent with
    each corresponding ECT codepoint."  A permission, so it is an *additional*
    outcome and never the only one. -/
def mayFailRemark (s : State) (c : Option Ecn) : Bool :=
  match c with
  | none => false
  | some e => decide (s.sentEct0 < e.ect0) || decide (s.sentEct1 < e.ect1)

/-- Appendix A.4, line 10273: "From the "unknown" state, successful validation
    of the ECN counts an ACK frame … causes the ECN state for the path to become
    "capable", unless no marked packet has been acknowledged."  Informative, so
    a permission. -/
def canBecomeCapable (s : State) (c : Option Ecn) (n : NewlyAcked) : Bool :=
  decide (s.phase = .unknown) && c.isSome && decide (0 < n.ect0 + n.ect1)

/-- §13.4.2, line 5549: "The endpoint monitors whether all packets sent with an
    ECT codepoint are eventually deemed lost …, indicating that ECN validation
    has failed." -/
def allMarkedLost (s : State) : Bool :=
  decide (0 < s.markedSent) && decide (s.markedLost = s.markedSent)

inductive Step : State → Event → Out → Prop
  /-- §13.4.1, line 5509: "On receiving an IP packet with an ECT(0), ECT(1) or CE
      codepoint, an ECN-enabled endpoint accesses the ECN field and increases the
      corresponding ECT(0), ECT(1), or CE count."  With line 5500 (no access, no
      counts) and line 5524 (duplicates are not counted). -/
  | recvPacket {s cp pr} :
      Step s (.recvPacket cp pr) (.ok (s.recordRecv cp pr) [])
  /-- §13.4.2, line 5539: "The endpoint sets an ECT(0) codepoint in the IP header
      of early outgoing packets sent on a new path to the peer". -/
  | sentPacket {s m} :
      Step s (.sentPacket m) (.ok (s.recordSent m) [])
  /-- §13.4.2.2, line 5626 (ECN already disabled) or §13.4.2.1, line 5613 ("An
      endpoint MUST NOT fail ECN validation as a result of processing an ACK
      frame that does not increase the largest acknowledged packet number"): the
      frame is not used for validation, and nothing about the ECN state
      changes. -/
  | ackNotValidated {s largest c n} (h : skipValidation s largest = true) :
      Step s (.recvAck largest c n) (.ok (s.recordAckedOnly n) [])
  /-- §13.4.2.1, lines 5583 and 5589, with §13.4.2.2, line 5626: "If validation
      fails, then the endpoint MUST disable ECN." -/
  | ackFail {s largest c n} (h : skipValidation s largest = false)
      (hf : failsValidation s c n = true) :
      Step s (.recvAck largest c n) (.ok s.fail [.ecnValidationFailed, .disableEcn])
  /-- §13.4.2.1, line 5577: the counts of a successfully processed ACK frame
      become the baseline for the next one. -/
  | ackOk {s largest c n} (h : skipValidation s largest = false)
      (hf : failsValidation s c n = false) :
      Step s (.recvAck largest c n) (.ok (s.recordCounts largest c n) [])
  /-- §13.4.2.2, line 5634: "Upon successful validation, an endpoint MAY continue
      to set an ECT codepoint in subsequent packets it sends, with the
      expectation that the path is ECN-capable."  Appendix A.4, line 10272 names
      the transition; it is a permission, so `ackOk` remains available. -/
  | ackCapable {s largest c n} (h : skipValidation s largest = false)
      (hf : failsValidation s c n = false) (hc : canBecomeCapable s c n = true) :
      Step s (.recvAck largest c n) (.ok (s.recordCounts largest c n).capable [.ecnValidated])
  /-- §13.4.2.1, line 5617: "ECN validation can fail if the received total count
      for either ECT(0) or ECT(1) exceeds the total number of packets sent with
      each corresponding ECT codepoint."  A permission: `ackOk` (and `ackCapable`
      where it applies) stay available for the same frame. -/
  | ackRemarkFail {s largest c n} (h : skipValidation s largest = false)
      (hf : failsValidation s c n = false) (hr : mayFailRemark s c = true) :
      Step s (.recvAck largest c n) (.ok s.fail [.ecnValidationFailed, .disableEcn])
  /-- RFC 9002 declared more marked packets lost; nothing has failed yet. -/
  | lostOk {s n} :
      Step s (.lostMarked n) (.ok (s.recordLost n) [])
  /-- §13.4.2, line 5549: "The endpoint monitors whether all packets sent with an
      ECT codepoint are eventually deemed lost …, indicating that ECN validation
      has failed", with §13.4.2.2, line 5626.  Listed first, so it is the
      preferred behaviour; line 5557's "it *can* disable marking on the
      assumption that the marking caused the loss" and line 5566's "Other methods
      of probing paths for ECN support are possible" keep `lostOk` available
      (NOTE 5). -/
  | lostFail {s n} (h : allMarkedLost (s.recordLost n) = true) :
      Step s (.lostMarked n) (.ok (s.recordLost n).fail [.ecnValidationFailed, .disableEcn])
  /-- §13.4.2, line 5561: "An endpoint thus attempts to use ECN and validates
      this for each new connection, when switching to a server's preferred
      address, and on active connection migration to a new path"; §13.4.2.2,
      line 5630: "Even if validation fails, an endpoint MAY revalidate ECN for
      the same path at any later time in the connection." -/
  | beginValidation {s t} :
      Step s (.beginValidation t) (.ok s.restart [])
  /-- Appendix A.4, line 10272: "After the testing period ends, the ECN state for
      the path becomes "unknown"." -/
  | testingEnded {s} :
      Step s .testingEnded (.ok s.afterTestingEnded [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvPacket cp pr => [.ok (s.recordRecv cp pr) []]
  | .sentPacket m => [.ok (s.recordSent m) []]
  | .beginValidation _ => [.ok s.restart []]
  | .testingEnded => [.ok s.afterTestingEnded []]
  | .lostMarked n =>
    if allMarkedLost (s.recordLost n) then
      [.ok (s.recordLost n).fail [.ecnValidationFailed, .disableEcn], .ok (s.recordLost n) []]
    else [.ok (s.recordLost n) []]
  | .recvAck largest c n =>
    if skipValidation s largest then [.ok (s.recordAckedOnly n) []]
    else if failsValidation s c n then [.ok s.fail [.ecnValidationFailed, .disableEcn]]
    else if canBecomeCapable s c n then
      (if mayFailRemark s c then
        [.ok (s.recordCounts largest c n).capable [.ecnValidated],
         .ok (s.recordCounts largest c n) [],
         .ok s.fail [.ecnValidationFailed, .disableEcn]]
      else
        [.ok (s.recordCounts largest c n).capable [.ecnValidated],
         .ok (s.recordCounts largest c n) []])
    else
      (if mayFailRemark s c then
        [.ok (s.recordCounts largest c n) [],
         .ok s.fail [.ecnValidationFailed, .disableEcn]]
      else [.ok (s.recordCounts largest c n) []])

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvPacket cp pr => simp only [outcomes, List.mem_singleton] at h; subst h; exact .recvPacket
    | sentPacket m => simp only [outcomes, List.mem_singleton] at h; subst h; exact .sentPacket
    | beginValidation t =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .beginValidation
    | testingEnded => simp only [outcomes, List.mem_singleton] at h; subst h; exact .testingEnded
    | lostMarked n =>
      simp only [outcomes] at h
      split at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .lostFail ‹_›
        · simp only [List.mem_singleton] at h; subst h; exact .lostOk
      · simp only [List.mem_singleton] at h; subst h; exact .lostOk
    | recvAck largest c n =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .ackNotValidated ‹_›
      · rename_i h0
        simp only [Bool.not_eq_true] at h0
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .ackFail h0 ‹_›
        · rename_i h1
          simp only [Bool.not_eq_true] at h1
          split at h
          · rename_i h2
            split at h
            · rcases List.mem_cons.mp h with rfl | h
              · exact .ackCapable h0 h1 h2
              · rcases List.mem_cons.mp h with rfl | h
                · exact .ackOk h0 h1
                · simp only [List.mem_singleton] at h; subst h
                  exact .ackRemarkFail h0 h1 ‹_›
            · rcases List.mem_cons.mp h with rfl | h
              · exact .ackCapable h0 h1 h2
              · simp only [List.mem_singleton] at h; subst h; exact .ackOk h0 h1
          · split at h
            · rcases List.mem_cons.mp h with rfl | h
              · exact .ackOk h0 h1
              · simp only [List.mem_singleton] at h; subst h
                exact .ackRemarkFail h0 h1 ‹_›
            · simp only [List.mem_singleton] at h; subst h; exact .ackOk h0 h1
  · intro h
    cases h with
    | recvPacket => simp [outcomes]
    | sentPacket => simp [outcomes]
    | beginValidation => simp [outcomes]
    | testingEnded => simp [outcomes]
    | lostOk => simp only [outcomes]; split <;> simp
    | lostFail hh => simp [outcomes, hh]
    | ackNotValidated hh => simp [outcomes, hh]
    | ackFail hh hf => simp [outcomes, hh, hf]
    | ackOk hh hf =>
      simp only [outcomes, hh, hf, Bool.false_eq_true, ite_false]
      split <;> split <;> simp
    | ackCapable hh hf hc =>
      simp only [outcomes, hh, hf, hc, Bool.false_eq_true, ite_false, ite_true]
      split <;> simp
    | ackRemarkFail hh hf hr =>
      simp only [outcomes, hh, hf, hr, Bool.false_eq_true, ite_false, ite_true]
      split <;> simp

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant

§13.4.1, line 5500: "If an endpoint does not implement ECN support or does not
have access to received ECN fields, it does not report ECN counts for packets it
receives."  Such an endpoint's counts stay at zero, so the ACK frames it may
send (`MaySendPacket`) can only carry zeroes — which is why the text adds, at
line 5506, that "Failing to report the ECN counts will cause the sender to
disable use of ECN for this connection". -/

def Inv (s : State) : Prop :=
  s.reportsEcn = false → (s.ect0 = 0 ∧ s.ect1 = 0 ∧ s.ce = 0)

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | @recvPacket cp pr =>
    intro hr
    have hpr : (s.recordRecv cp pr).reportsEcn = s.reportsEcn := by
      unfold State.recordRecv; split <;> rfl
    rw [hpr] at hr
    have hz := hi hr
    show ((s.recordRecv cp pr).ect0 = 0 ∧ _ ∧ _)
    unfold State.recordRecv
    rw [hr]
    simpa using hz
  | _ => exact fun hr => hi hr

end Quic.Spec.Ecn
