import QuicModel.Spec.Retransmission.Step

/-
  WP14 (a), parts 9-10: the named theorems and the scenarios of §13.3.
-/
namespace Quic.Spec.Retransmission

/-! ## 9. Named theorems -/

/-- **(d), first half.**  After a packet is declared lost, what is owed is
    exactly what was owed before, plus the information the text repairs that
    this packet was the most recent carrier of. -/
theorem owed_after_lost {s s' : State} {pkt : PktId} {fx : List Effect}
    (h : Step s (.lost pkt) (.ok s' fx)) (i : Info) :
    Owes s' i ↔ (Owes s i ∨ i ∈ s.lostOwed pkt) := by
  cases h
  exact mem_addAll _ _ _

/-- …and `lostOwed` is exactly `newlyOwed` of what the packet carried. -/
theorem lostOwed_eq {s : State} {pkt : PktId} {k : Nat} {is : List Info}
    (h : s.inFlight.get? pkt = some (k, is)) : s.lostOwed pkt = s.newlyOwed k is := by
  unfold State.lostOwed; rw [h]

/-- A packet that is not in flight owes nothing (NOTE 1). -/
theorem lostOwed_of_not_inFlight {s : State} {pkt : PktId}
    (h : s.inFlight.get? pkt = none) : s.lostOwed pkt = [] := by
  unfold State.lostOwed; rw [h]

/-- Only information the text repairs is ever added. -/
theorem repairable_of_mem_newlyOwed {s : State} {k : Nat} {is : List Info} {i : Info}
    (h : i ∈ s.newlyOwed k is) : s.repairable i = true ∧ i ∈ is := by
  have h1 := List.mem_filter.mp h
  refine ⟨?_, h1.1⟩
  have h2 := h1.2
  simp only [Bool.and_eq_true] at h2
  exact h2.1.1

/-- **(d), second half.**  ACK, PING, PADDING, PATH_CHALLENGE, PATH_RESPONSE and
    CONNECTION_CLOSE are never owed, in any reachable state.  This is `Inv`, so
    it needs only that the initial state satisfies it. -/
theorem never_owed {s₀ s : State} (h0 : Inv s₀) (hr : component.Reachable s₀ s)
    {i : Info} (hi : i.neverRepaired = true) : ¬ Owes s i := by
  intro ho
  have hinv : Inv s := component.inv_of_reachable h0 hr
  have := hinv i ho
  rw [hi] at this
  exact Bool.noConfusion this

/-- The six categories `never_owed` covers, spelled out from the text. -/
theorem neverRepaired_categories :
    Info.ack.neverRepaired = true ∧ Info.ping.neverRepaired = true ∧
    Info.padding.neverRepaired = true ∧ Info.pathChallenge.neverRepaired = true ∧
    Info.pathResponse.neverRepaired = true ∧ Info.connectionClose.neverRepaired = true := by
  decide

/-- §13.3, line 5406: a blocked signal whose scope no longer blocks is not
    repaired. -/
theorem repairable_blocked_false {s : State} {sc : BlockedScope} {i : Info}
    (hb : i.blockedScope = some sc) (hnb : has s.blocked sc = false) :
    s.repairable i = false := by
  cases i
  case dataBlocked =>
    simp only [Info.blockedScope, Option.some.injEq] at hb
    subst hb; simpa [State.repairable] using hnb
  case streamDataBlocked id =>
    simp only [Info.blockedScope, Option.some.injEq] at hb
    subst hb; simpa [State.repairable] using hnb
  case streamsBlocked dir =>
    simp only [Info.blockedScope, Option.some.injEq] at hb
    subst hb; simpa [State.repairable] using hnb
  all_goals (exfalso; simp [Info.blockedScope] at hb)

/-- **(e).**  An obligation is never simply forgotten: whenever a step removes
    information from `owed`, the step either re-sent it, or the information has
    become acknowledged, or one of §13.3's own alternative endings now holds. -/
theorem owes_cleared {s s' : State} {e : Event} {fx : List Effect} {i : Info}
    (h : Step s e (.ok s' fx)) (ho : Owes s i) (hn : ¬ Owes s' i) :
    Retransmits e i ∨ Discharged s' i ∨ Superseded s' i := by
  cases h with
  | @sent pkt fs =>
    by_cases hin : i ∈ fs.map (Info.of pkt.space)
    · exact Or.inl ⟨pkt, fs, rfl, hin⟩
    · refine Or.inr (Or.inr ?_)
      have hmem : i ∈ removeAll s.owed (fs.map (Info.of pkt.space)) :=
        mem_removeAll.mpr ⟨ho, hin⟩
      have hsup := filter_removed hmem hn
      show (State.afterSent s pkt fs).repairable i = false
      cases i <;> simp [keepAfterReset, supersededByReset] at hsup
      case streamData id off len fin =>
        have : has (addAll s.resetSent (resetsOf (fs.map (Info.of pkt.space)))) id = true :=
          has_eq_true.mpr (mem_addAll_right hsup)
        simp [State.repairable, State.afterSent, this]
  | @acked pkt =>
    refine Or.inr (Or.inl ?_)
    have h1 : i ∉ removeAll s.owed (s.carried pkt) := hn
    simp only [mem_removeAll, not_and, Decidable.not_not] at h1
    exact mem_addAll_right (h1 ho)
  | @lost pkt => exact absurd (mem_addAll_left ho) hn
  | @sendDataAcked id =>
    refine Or.inr (Or.inr ?_)
    have hfil := filter_removed ho hn
    show (State.afterSendDataAcked s id).repairable i = false
    cases i <;> simp [keepAfterDataAcked] at hfil
    case resetStream id' err fs =>
      subst hfil
      have : has (addAll s.sendDataAcked [id']) id' = true :=
        has_eq_true.mpr (mem_addAll_right (List.mem_singleton.mpr rfl))
      simp [State.repairable, State.afterSendDataAcked, this]
  | @recvPhase id p =>
    refine Or.inr (Or.inr ?_)
    have hfil := filter_removed ho hn
    show (State.afterRecvPhase s id p).repairable i = false
    cases i <;> simp [keepAfterRecvPhase] at hfil
    case stopSending id' err =>
      obtain ⟨rfl, hd⟩ := hfil
      simp [State.repairable, State.afterRecvPhase, State.recvDone, Map.get?_set_self, hd]
  | @keysDiscarded sp =>
    refine Or.inr (Or.inr ?_)
    have hfil := filter_removed ho hn
    show (State.afterKeysDiscarded s sp).repairable i = false
    cases i <;> simp [keepAfterKeysDiscarded] at hfil
    case crypto sp' off len =>
      subst hfil
      have : has (addAll s.keysGone [sp']) sp' = true :=
        has_eq_true.mpr (mem_addAll_right (List.mem_singleton.mpr rfl))
      simp [State.repairable, State.afterKeysDiscarded, this]
  | @blockedChanged sc b =>
    refine Or.inr (Or.inr ?_)
    cases b with
    | true => exact absurd ho hn
    | false =>
      have hn' : i ∉ s.owed.filter (keepAfterUnblocked sc) := hn
      have hfil := filter_removed ho hn'
      simp only [keepAfterUnblocked, decide_eq_false_iff_not, Decidable.not_not] at hfil
      have hnb : has (State.afterBlocked s sc false).blocked sc = false :=
        has_eq_false.mpr (fun hc => (mem_removeAll.mp hc).2 (List.mem_singleton.mpr rfl))
      exact repairable_blocked_false hfil hnb
  | @discardHistory => exact absurd ho hn

/-- A retransmission only *defers* the obligation: the information goes back in
    flight, and is discharged only when a packet carrying it is acknowledged. -/
theorem retransmit_not_discharge {s s' : State} {pkt : PktId} {fs : List Frame}
    {fx : List Effect} {i : Info}
    (h : Step s (.sentFrames pkt fs) (.ok s' fx)) (hd : ¬ Discharged s i) :
    ¬ Discharged s' i := by
  cases h; exact hd

/-- §13.3, line 5452: "it is not forbidden to retransmit copies of frames from
    lost packets."  A frame that was permitted is permitted again after being
    sent — the `MaySend` idempotence the BRIEF requires. -/
theorem maySend_resent {s : State} {pkt : PktId} {f : Frame}
    (hok : MaySend s f) : MaySend (s.afterSent pkt [f]) f := by
  cases f
  case resetStream id err fs =>
    simp only [MaySend] at hok ⊢
    simp only [State.afterSent, List.map_cons, List.map_nil, Info.of, recordResets]
    cases hg : s.resetContent.get? (⟨id⟩ : StreamId) with
    | none => simp [Map.get?_set_self]
    | some p => exact hok
  all_goals trivial

/-- `MaySend` governs RESET_STREAM and nothing else: §13.3 has no other rule
    forbidding a frame, and lines 5452/5457 say so explicitly. -/
theorem maySend_of_not_reset {s : State} {f : Frame}
    (h : ∀ id err fs, f ≠ .resetStream id err fs) : MaySend s f := by
  cases f <;> simp only [MaySend] <;> try trivial
  case resetStream id err fs => exact absurd rfl (h id err fs)

/-- §13.3, line 5457: "A receiver MUST accept packets containing an outdated
    frame, such as a MAX_DATA frame carrying a smaller maximum data than one
    found in an older packet."  The send-side half: this component never refuses
    an outdated value. -/
theorem maySend_outdated (s : State) (v : Nat) : MaySend s (.maxData v) := trivial

/-! ## 10. Examples (scenarios from the text) -/

private def p0 : PktId := ⟨.appData, 0⟩
private def p1 : PktId := ⟨.appData, 1⟩
private def s0 : State := {}

-- §13.3, line 5445: "The HANDSHAKE_DONE frame MUST be retransmitted until it is
-- acknowledged."  Sent, lost: owed; re-sent: no longer owed but back in flight;
-- acknowledged: discharged.
private def sA : State := (s0.afterSent p0 [.handshakeDone]).afterLost p0
example : owes sA .handshakeDone = true := by decide
example : (sA.afterSent p1 [.handshakeDone]).owed = [] := by decide
example : Discharged ((sA.afterSent p1 [.handshakeDone]).afterAcked p1) .handshakeDone := by
  decide

-- §13.3, line 5343: "Application data sent in STREAM frames is retransmitted in
-- new STREAM frames unless the endpoint has sent a RESET_STREAM for that
-- stream."  A RESET_STREAM in a later packet supersedes the owed STREAM data.
private def sB : State :=
  (s0.afterSent p0 [.stream 4 0 false ByteArray.empty]).afterLost p0
example : owes sB (.streamData ⟨4⟩ 0 0 false) = true := by decide
example : owes (sB.afterSent p1 [.resetStream 4 3 0]) (.streamData ⟨4⟩ 0 0 false) = false := by
  decide

-- §13.3, line 5418: "Responses to path validation using PATH_RESPONSE frames
-- are sent just once", and line 5348/5442: ACK, PING and PADDING are not
-- repaired either.
private def sC : State :=
  (s0.afterSent p0 [.pathResponse ByteArray.empty, .ack 0 0 0 #[] none, .ping,
      .padding 5, .connectionClose 0 none ByteArray.empty]).afterLost p0
example : sC.owed = [] := by decide

-- §13.3, line 5381: a lost MAX_DATA is repaired, and what is owed is the *scope*
-- — the frame that repairs it carries the current value, not the lost one.
private def sD : State := (s0.afterSent p0 [.maxData 100]).afterLost p0
example : owes sD .maxData = true := by decide
example : owes (sD.afterSent p1 [.maxData 4000]) .maxData = false := by decide

-- §13.3, line 5406: "New frames are sent if packets containing the most recent
-- frame for a scope is lost, but only while the endpoint is blocked on the
-- corresponding limit."
private def sE : State := s0.afterSent p0 [.dataBlocked 100]
example : owes (sE.afterLost p0) .dataBlocked = false := by decide
example : owes ((sE.afterBlocked .conn true).afterLost p0) .dataBlocked = true := by decide
-- … and becoming unblocked retires the debt.
example : owes (((sE.afterBlocked .conn true).afterLost p0).afterBlocked .conn false)
    .dataBlocked = false := by decide

-- §13.3, lines 5381/5403: only the *most recent* carrier of a scope creates a
-- debt.  MAX_DATA in p0 and then in p1; losing the older p0 owes nothing.
private def sF : State := (s0.afterSent p0 [.maxData 100]).afterSent p1 [.maxData 200]
example : owes (sF.afterLost p0) .maxData = false := by decide
example : owes (sF.afterLost p1) .maxData = true := by decide

-- §13.3, line 5339: CRYPTO data for a discarded packet number space is gone.
private def i0 : PktId := ⟨.initial, 0⟩
private def sG : State := (s0.afterSent i0 [.crypto 0 ByteArray.empty]).afterLost i0
example : owes sG (.crypto .initial 0 0) = true := by decide
example : owes (sG.afterKeysDiscarded .initial) (.crypto .initial 0 0) = false := by decide

-- §13.3, line 5362: STOP_SENDING is owed until the receiving part is done.
private def sH : State := (s0.afterSent p0 [.stopSending 4 7]).afterLost p0
example : owes sH (.stopSending ⟨4⟩ 7) = true := by decide
example : owes (sH.afterRecvPhase ⟨4⟩ .dataRecvd) (.stopSending ⟨4⟩ 7) = false := by decide
example : owes (sH.afterRecvPhase ⟨4⟩ .sizeKnown) (.stopSending ⟨4⟩ 7) = true := by decide

-- §13.3, line 5355: RESET_STREAM is owed until acknowledged or until all stream
-- data is acknowledged.
private def sI : State := (s0.afterSent p0 [.resetStream 4 3 10]).afterLost p0
example : owes sI (.resetStream ⟨4⟩ 3 10) = true := by decide
example : owes (sI.afterSendDataAcked ⟨4⟩) (.resetStream ⟨4⟩ 3 10) = false := by decide

-- §13.3, line 5359: "The content of a RESET_STREAM frame MUST NOT change when it
-- is sent again."
example : maySend sI (.resetStream 4 3 10) = true := by decide
example : maySend sI (.resetStream 4 9 10) = false := by decide
example : maySend sI (.resetStream 4 3 11) = false := by decide
example : maySend sI (.resetStream 5 9 11) = true := by decide

-- Following an implementation whose state we cannot see.
example : component.track s0 (.sentFrames p0 [.handshakeDone]) (.ok []) =
    some (s0.afterSent p0 [.handshakeDone]) := by decide

end Quic.Spec.Retransmission
