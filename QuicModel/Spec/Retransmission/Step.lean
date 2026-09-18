import QuicModel.Spec.Retransmission.Basic

/-
  WP14 (a), parts 3-8: `outcomes` and `outcomes_iff`, the invariant, the send
  side, the `Component` value, and the retransmission obligation §13.3 line 5445
  hands to WP12.
-/
namespace Quic.Spec.Retransmission

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .sentFrames pkt fs => [.ok (s.afterSent pkt fs) []]
  | .acked pkt => [.ok (s.afterAcked pkt) (s.ackedEffects pkt)]
  | .lost pkt => [.ok (s.afterLost pkt) (s.lostEffects pkt)]
  | .sendPartDataAcked id => [.ok (s.afterSendDataAcked id) []]
  | .recvPartPhase id p => [.ok (s.afterRecvPhase id p) []]
  | .keysDiscarded sp => [.ok (s.afterKeysDiscarded sp) []]
  | .blockedChanged sc b => [.ok (s.afterBlocked sc b) []]
  | .discardHistory => [.ok { s with ackedInfo := [] } []]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e <;> simp only [outcomes, List.mem_singleton] at h <;> subst h
    · exact .sent
    · exact .acked
    · exact .lost
    · exact .sendDataAcked
    · exact .recvPhase
    · exact .keysDiscarded
    · exact .blockedChanged
    · exact .discardHistory
  · intro h
    cases h <;> simp [outcomes]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp [outcomes]

/-! ## 5. Invariant

Nothing that §13.3 says is never repaired can ever be owed. -/

def Inv (s : State) : Prop := ∀ i ∈ s.owed, i.neverRepaired = false

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | @sent pkt fs =>
    intro i hm
    exact hi i (mem_of_mem_removeAll (mem_of_mem_filter hm))
  | @acked pkt =>
    intro i hm
    exact hi i (mem_of_mem_removeAll hm)
  | @lost pkt =>
    intro i hm
    rcases (mem_addAll _ _ _).mp hm with h1 | h1
    · exact hi i h1
    · have h2 : ∀ k is, i ∈ s.newlyOwed k is → i.neverRepaired = false := by
        intro k is hk
        have h3 := (List.mem_filter.mp hk).2
        simp only [Bool.and_eq_true] at h3
        exact neverRepaired_of_repairable h3.1.1
      revert h1
      unfold State.lostOwed
      cases s.inFlight.get? pkt with
      | none => intro h1; cases h1
      | some p => intro h1; exact h2 p.1 p.2 h1
  | @sendDataAcked id => intro i hm; exact hi i (mem_of_mem_filter hm)
  | @recvPhase id p => intro i hm; exact hi i (mem_of_mem_filter hm)
  | @keysDiscarded sp => intro i hm; exact hi i (mem_of_mem_filter hm)
  | @blockedChanged sc b =>
    intro i hm
    revert hm
    show i ∈ (if b then s.owed else s.owed.filter (keepAfterUnblocked sc)) → _
    cases b with
    | true => intro hm; exact hi i hm
    | false => intro hm; exact hi i (mem_of_mem_filter hm)
  | @discardHistory => intro i hm; exact hi i hm

/-! ## 6. Send side

§13.3's send-side sentences are, almost without exception, either *permissions*
or rules owned by the component that owns the frame (see the header).  Two of
them say so in as many words:

* line 5452: "Even though a sender is encouraged to assemble frames containing
  up-to-date information every time it sends a packet, it is not forbidden to
  retransmit copies of frames from lost packets."
* line 5457: "A receiver MUST accept packets containing an outdated frame, such
  as a MAX_DATA frame carrying a smaller maximum data than one found in an older
  packet."

So the only MUST NOT of §13.3 that is a send-side rule about a frame's *content*
is line 5359, and it is checkable from this component's state. -/

/-- §13.3, line 5359: "The content of a RESET_STREAM frame MUST NOT change when
    it is sent again."  `Spec/Stream/Send.lean` pins the same sentence from the
    sending part's phase; the two agree and compose by conjunction. -/
def MaySend (s : State) : Frame → Prop
  | .resetStream id err fs =>
    match s.resetContent.get? ⟨id⟩ with
    | none => True
    | some p => p = (err, fs)
  | _ => True

def maySend (s : State) : Frame → Bool
  | .resetStream id err fs =>
    match s.resetContent.get? ⟨id⟩ with
    | none => true
    | some p => decide (p = (err, fs))
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f
  case resetStream id err fs =>
    simp only [maySend, MaySend]
    cases s.resetContent.get? (⟨id⟩ : StreamId) <;> simp
  all_goals simp [maySend, MaySend]

/-- The SHOULDs of §13.3 that constrain a frame this component models.  A
    conforming implementation may ignore every one of them, so none of them is
    in `MaySend`. -/
structure Recommended (s : State) (sp : PnSpace) (f : Frame) : Prop where
  /-- §13.3, line 5461: "A sender SHOULD avoid retransmitting information from
      packets once they are acknowledged."  Only for information whose identity
      is its content (NOTE 3). -/
  notAlreadyAcked :
    (Info.of sp f).isVerbatim = true → (Info.of sp f) ∉ s.ackedInfo
  /-- §13.3, line 5406: "… but only while the endpoint is blocked on the
      corresponding limit." -/
  blockedOnlyWhileBlocked :
    ∀ sc, (Info.of sp f).blockedScope = some sc → sc ∈ s.blocked
  /-- §13.3, line 5393: "An endpoint SHOULD stop sending MAX_STREAM_DATA frames
      when the receiving part of the stream enters a "Size Known" or
      "Reset Recvd" state."  Also carried by `Stream.Recv.RecommendedSend`. -/
  maxStreamDataStopped :
    ∀ id, Info.of sp f = .maxStreamData id → s.recvPastRecv id = false

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

/-! ## 8. The retransmission obligation -/

/-- Information the endpoint still owes a (re)transmission of. -/
def Owes (s : State) (i : Info) : Prop := i ∈ s.owed

def owes (s : State) (i : Info) : Bool := has s.owed i

theorem owes_iff (s : State) (i : Info) : owes s i = true ↔ Owes s i := by
  simp [owes, Owes]

instance (s : State) (i : Info) : Decidable (Owes s i) :=
  decidable_of_iff _ (owes_iff s i)

/-- The information §13.3 says is sent *until acknowledged*, i.e. where failing
    to send it again is a violation and not merely wasteful: line 5338 CRYPTO
    "until all data has been acknowledged"; line 5355 RESET_STREAM "sent until
    acknowledged or until all stream data is acknowledged"; line 5362
    STOP_SENDING "sent until the receiving part …"; line 5445 "The
    HANDSHAKE_DONE frame MUST be retransmitted until it is acknowledged."  The
    remaining bullets say only that an updated value "is sent", which this model
    records in `owed` but does not turn into an obligation (NOTE 4). -/
def MustRetransmit : Info → Bool
  | .crypto .. | .resetStream .. | .stopSending .. | .handshakeDone => true
  | _ => false

/-- §13.3, line 5333: the obligation is discharged by an acknowledgment. -/
def Discharged (s : State) (i : Info) : Prop := i ∈ s.ackedInfo

def discharged (s : State) (i : Info) : Bool := has s.ackedInfo i

theorem discharged_iff (s : State) (i : Info) : discharged s i = true ↔ Discharged s i := by
  simp [discharged, Discharged]

instance (s : State) (i : Info) : Decidable (Discharged s i) :=
  decidable_of_iff _ (discharged_iff s i)

/-- …or by the text's own alternative endings: the keys were discarded
    (line 5339), a RESET_STREAM superseded the STREAM data (line 5343), all
    stream data is acknowledged (line 5355), the receiving part reached
    "Data Recvd"/"Reset Recvd" (line 5362), the endpoint is no longer blocked
    (line 5406). -/
def Superseded (s : State) (i : Info) : Prop := s.repairable i = false

/-- The trace-level requirement WP12 must impose, in the shape of
    `Ack.EventuallyAcknowledged`: a single step cannot force a frame to be sent,
    so §13.3's "until acknowledged" is a property of a whole run. -/
def RepairObligationMet (run : List State) : Prop :=
  ∀ i, MustRetransmit i = true → (∃ s ∈ run, Owes s i) →
    ∃ s ∈ run, (Discharged s i ∨ Superseded s i)

/-- The event re-sent this information. -/
def Retransmits (e : Event) (i : Info) : Prop :=
  ∃ pkt fs, e = .sentFrames pkt fs ∧ i ∈ fs.map (Info.of pkt.space)

end Quic.Spec.Retransmission
