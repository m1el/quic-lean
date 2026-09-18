import QuicModel.Spec.Endpoint.Component

/-!
  WP12 "Endpoint", part 6b: **the obligations a single step cannot express**.

  PLAN §4b: "a per-step predicate cannot force something to happen. WP12 must
  state liveness-style MUSTs … as requirements on timed traces, fed by exported
  predicates such as `AckOverdue`."

  A *conforming trace* is a sequence of `(State × Time)` observations, one after
  every event, and the endpoint conforms only if `Obligations` holds at **every**
  point of it (`ObligationsMet`).  Two things are worth being explicit about:

  * The harness can never demand that a frame be sent.  It can only check that
    an obligation never becomes *overdue*: the predicates below are all of the
    form "nothing is past its deadline", so an implementation that sends the
    frame early, late-but-in-time, or coalesced with something else all pass,
    and only one that never sends it fails — at the moment the deadline passes.
  * `tolerance` is the processing time the checker allows (`Ack` NOTES 12).
    §13.2.1's "immediately" is a zero *intentional* delay, and for the Initial
    and Handshake spaces `Ack.State.ackDelayBudget` is `0`, so with
    `tolerance = 0` the predicate is unsatisfiable for any real endpoint.  The
    harness supplies the bound it is willing to allow.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ### §13.2.1, line 5075: acknowledge in time, per packet number space -/

/-- `Ack.ackOverdue` for all three instances (`Ack` NOTES 11). -/
def ackOverdue (s : State) (now tolerance : Time) : Bool :=
  Ack.ackOverdue s.ackInitial now tolerance || Ack.ackOverdue s.ackHandshake now tolerance ||
  Ack.ackOverdue s.ackAppData now tolerance

theorem ackOverdue_iff (s : State) (now tolerance : Time) :
    ackOverdue s now tolerance = false ↔ ∀ sp, Ack.ackOverdue (s.ack sp) now tolerance = false := by
  simp only [ackOverdue, Bool.or_eq_false_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ sp; cases sp <;> assumption
  · intro h; exact ⟨⟨h .initial, h .handshake⟩, h .appData⟩

/-! ### §3.5, line 1263: a RESET_STREAM is owed after a STOP_SENDING

§3.5, line 1258: "An endpoint that receives a STOP_SENDING frame MUST send a
RESET_STREAM frame if the stream is in the Ready or Send state."  WP2 records
the request in `Stream.Send.State.resetCode` and leaves the sending part in a
non-`Reset Sent` phase; the obligation is discharged by
`Stream.Send.Event.sentResetStream`, which moves it to `Reset Sent`. -/

def resetOwedOn (st : Stream.State) : Bool :=
  match st.send with
  | some ss =>
    ss.resetCode.isSome &&
      !(ss.phase == Stream.Send.Phase.resetSent || ss.phase == Stream.Send.Phase.resetRecvd)
  | none => false

/-- The streams that owe a RESET_STREAM right now. -/
def resetsOwed (s : State) : List StreamId :=
  (s.st.streams.filter (fun e => resetOwedOn e.2)).map (·.1)

/-- Unlike the acknowledgment deadline, §3.5 fixes no time by which the
    RESET_STREAM must go out, so the obligation is "not still owed at the end of
    the run" rather than "not overdue now".  `ResetsSettled` is what a whole
    trace must end in. -/
def ResetsSettled (s : State) : Prop := resetsOwed s = []

def resetsSettled (s : State) : Bool := resetsOwed s == []

theorem resetsSettled_iff (s : State) : resetsSettled s = true ↔ ResetsSettled s := by
  simp [resetsSettled, ResetsSettled]

/-! ### §13.3, line 5445 (WP14a) and §13.4.1, line 5504 (WP14b)

Both are, like §13.2.1's, obligations to *send* something, so both are stated
over a run and neither is a per-state predicate.  §8.2.1 line 3163's second,
expanded path validation is deliberately absent: `PathValidation` NOTES 3
records that it and §8.2.3 line 3221 are obligations to start *another*
validation at an unspecified later time, that a liveness obligation with no
deadline cannot be stated as a `Step` constraint, and that it needs the size of
the datagram a challenge was sent in to be carried in `Challenge`.  There is
nothing to conjoin, and this file does not invent one. -/

/-- §13.3, line 5445: the information this endpoint still owes a
    retransmission of, restricted to the kinds §13.3 says are sent *until
    acknowledged* (`Retransmission.MustRetransmit`). -/
def repairOwed (s : State) : List Retransmission.Info :=
  s.rtx.owed.filter Retransmission.MustRetransmit

def RepairSettled (s : State) : Prop := repairOwed s = []

def repairSettled (s : State) : Bool := repairOwed s == []

theorem repairSettled_iff (s : State) : repairSettled s = true ↔ RepairSettled s := by
  simp [repairSettled, RepairSettled]

/-- §13.4.1, line 5504: counts have been received and not yet reported, in some
    packet number space. -/
def ecnFeedbackOwed (s : State) : Bool :=
  Ecn.feedbackOwed s.ecnInitial || Ecn.feedbackOwed s.ecnHandshake ||
  Ecn.feedbackOwed s.ecnAppData

/-! ### The whole obligation -/

/-- What must hold at every point of a conforming timed run.  Only §13.2.1's
    deadline is a *per-state* obligation: the others fix no time by which the
    frame must go out, so they are conditions on the end of the run
    (`ObligationsMet`). -/
def Obligations (s : State) (now tolerance : Time) : Prop :=
  ∀ sp, Ack.ackOverdue (s.ack sp) now tolerance = false

def obligations (s : State) (now tolerance : Time) : Bool := !ackOverdue s now tolerance

theorem obligations_iff (s : State) (now tolerance : Time) :
    obligations s now tolerance = true ↔ Obligations s now tolerance := by
  simp only [obligations, Obligations, Bool.not_eq_true']
  exact ackOverdue_iff s now tolerance

/-- A timed run is a sequence of observations, one after each event. -/
abbrev Run := List (State × Time)

/-- §13.2.1, line 5075 and §3.5, line 1258 as properties of a whole run: nothing
    is ever overdue, and nothing is still owed at the end. -/
def ObligationsMet (run : Run) (tolerance : Time) : Prop :=
  (∀ p ∈ run, Obligations p.1 p.2 tolerance) ∧
    ∀ p, run.getLast? = some p → ResetsSettled p.1 ∧ RepairSettled p.1

def obligationsMet (run : Run) (tolerance : Time) : Bool :=
  run.all (fun p => obligations p.1 p.2 tolerance) &&
    (match run.getLast? with
     | none => true
     | some p => resetsSettled p.1 && repairSettled p.1)

theorem obligationsMet_iff (run : Run) (tolerance : Time) :
    obligationsMet run tolerance = true ↔ ObligationsMet run tolerance := by
  simp only [obligationsMet, ObligationsMet, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => (obligations_iff _ _ _).mp (h1 p hp), fun p hp => ?_⟩
    rw [hp] at h2
    simp only [Bool.and_eq_true] at h2
    exact ⟨(resetsSettled_iff _).mp h2.1, (repairSettled_iff _).mp h2.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => (obligations_iff _ _ _).mpr (h1 p hp), ?_⟩
    cases hl : run.getLast? with
    | none => rfl
    | some p =>
      obtain ⟨hr, hp⟩ := h2 p hl
      simp only [Bool.and_eq_true]
      exact ⟨(resetsSettled_iff _).mpr hr, (repairSettled_iff _).mpr hp⟩

/-- The exported form WP13 calls: `ackOverdue` is the only obligation the
    harness can observe from outside, because it is the only one whose deadline
    the trace carries. -/
theorem ackOverdue_sound {run : Run} {tolerance : Time} (h : ObligationsMet run tolerance)
    {p : State × Time} (hp : p ∈ run) : ackOverdue p.1 p.2 tolerance = false :=
  (ackOverdue_iff _ _ _).mpr (h.1 p hp)

/-! ### The two component-level run obligations, over the projected run

`Retransmission.RepairObligationMet` and `Ecn.FeedbackObligationMet` are stated
over runs of *their* states; the endpoint's run projects onto them.  `Ecn`'s
also needs the ACK frames the endpoint sent in each space, which the harness
records from the `OUT` lines of the trace. -/

def rtxRun (run : Run) : List Retransmission.State := run.map (fun p => p.1.rtx)

def ecnRun (sp : PnSpace) (run : List (State × Frame)) : List (Ecn.State × Frame) :=
  run.map (fun p => (p.1.ecn sp, p.2))

/-- §13.3, line 5445 over a whole run. -/
def RepairObligationMet (run : Run) : Prop :=
  Retransmission.RepairObligationMet (rtxRun run)

/-- §13.4.1, line 5504 over a whole run, per packet number space. -/
def FeedbackObligationMet (run : List (State × Frame)) : Prop :=
  ∀ sp, Ecn.FeedbackObligationMet (ecnRun sp run)

end Quic.Spec.Endpoint
