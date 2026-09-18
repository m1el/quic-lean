import QuicModel.Spec.StreamTable.Inv

/-
  WP9 StreamTable, part 3 of 5: the send side (§6) and the `Component` (§7).
-/
namespace Quic.Spec.StreamTable


/-! ## 6. Send side

Frames this component governs: the two connection-level limit frames, the two
connection/stream-count blocked frames, and — by conjunction with WP2's
per-stream `MaySend` — every frame that names a stream.

Two readings of the text are worth stating up front.

* **A smaller limit may be advertised.**  §4.1, line 1357: "Once a receiver
  advertises a limit for the connection or a stream, it is not an error to
  advertise a smaller limit, but the smaller limit has no effect", and §4.6,
  line 1559: "Once a receiver advertises a stream limit using the MAX_STREAMS
  frame, advertising a smaller limit has no effect.  A receiver MUST ignore any
  MAX_STREAMS frame that does not increase the stream limit."  Neither sentence
  forbids sending it, so `MaySend` does not require an increase — unlike
  `Spec/Template.lean`, which this file supersedes (see NOTES).
* **A blocked frame carries the limit in force.**  §13.3, line 5409: "These
  frames always include the limit that is causing blocking at the time that they
  are transmitted." -/

/-- §4.6, line 1553 with §4.1, line 1330: what the connection level adds to a
    stream's own `MaySend` for a frame that consumes send credit. -/
def sendCredit (s : State) (id : StreamId) (k : Nat) : Prop :=
  s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer

def sendCreditB (s : State) (id : StreamId) (k : Nat) : Bool :=
  decide (s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer)

/-- A frame naming a stream may be sent only for a stream that exists, within
    the peer's stream limit (§4.6, line 1553), and if the stream itself permits
    it (WP2). -/
def streamMaySend (s : State) (id : StreamId) (f : Frame) : Prop :=
  s.has id = true ∧ s.withinPeerStreamLimit id = true ∧ Stream.MaySend (s.get id) f

def streamMaySendB (s : State) (id : StreamId) (f : Frame) : Bool :=
  s.has id && s.withinPeerStreamLimit id && Stream.maySend (s.get id) f

def MaySend (s : State) : Frame → Prop
  | .maxData v => v ≤ maxVarint
  | .maxStreams _ v => v ≤ maxStreamsLimit
  | .dataBlocked v => v = s.maxDataPeer
  | .streamsBlocked dir v => v ≤ maxStreamsLimit ∧ v = s.maxStreamsPeer.get dir
  | .stream id offset fin data =>
      streamMaySend s ⟨id⟩ (.stream id offset fin data) ∧
        sendCredit s ⟨id⟩ (offset + data.size)
  | .resetStream id code fs =>
      streamMaySend s ⟨id⟩ (.resetStream id code fs) ∧ sendCredit s ⟨id⟩ fs
  | .streamDataBlocked id v => streamMaySend s ⟨id⟩ (.streamDataBlocked id v)
  | .maxStreamData id v => streamMaySend s ⟨id⟩ (.maxStreamData id v)
  | .stopSending id code => streamMaySend s ⟨id⟩ (.stopSending id code)
  | _ => True

def maySend (s : State) : Frame → Bool
  | .maxData v => decide (v ≤ maxVarint)
  | .maxStreams _ v => decide (v ≤ maxStreamsLimit)
  | .dataBlocked v => decide (v = s.maxDataPeer)
  | .streamsBlocked dir v => decide (v ≤ maxStreamsLimit) && decide (v = s.maxStreamsPeer.get dir)
  | .stream id offset fin data =>
      streamMaySendB s ⟨id⟩ (.stream id offset fin data) && sendCreditB s ⟨id⟩ (offset + data.size)
  | .resetStream id code fs =>
      streamMaySendB s ⟨id⟩ (.resetStream id code fs) && sendCreditB s ⟨id⟩ fs
  | .streamDataBlocked id v => streamMaySendB s ⟨id⟩ (.streamDataBlocked id v)
  | .maxStreamData id v => streamMaySendB s ⟨id⟩ (.maxStreamData id v)
  | .stopSending id code => streamMaySendB s ⟨id⟩ (.stopSending id code)
  | _ => true

theorem streamMaySend_iff (s : State) (id : StreamId) (f : Frame) :
    streamMaySendB s id f = true ↔ streamMaySend s id f := by
  simp [streamMaySendB, streamMaySend, Stream.maySend_iff, and_assoc]

theorem sendCredit_iff (s : State) (id : StreamId) (k : Nat) :
    sendCreditB s id k = true ↔ sendCredit s id k := by
  simp [sendCreditB, sendCredit]

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;>
    simp [maySend, MaySend, streamMaySend_iff, sendCredit_iff]

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

/-! ### The SHOULDs that are about *when*, not *whether*

§4.1, line 1371 and §4.6, line 1569 recommend a blocked frame when actually
blocked; §4.2's autotuning advice and §4.3 are performance guidance with no
observable rule.  None of them restricts `MaySend`. -/

def Recommended (s : State) : Frame → Prop
  -- §4.1, line 1368: "If a sender has sent data up to the limit, it will be
  -- unable to send new data and is considered blocked."
  | .dataBlocked _ => s.sentTotal = s.maxDataPeer
  -- §4.6, line 1569: "An endpoint that is unable to open a new stream due to
  -- the peer's limits SHOULD send a STREAMS_BLOCKED frame."
  | .streamsBlocked dir _ => s.opened.get s.role dir = s.maxStreamsPeer.get dir
  | _ => True


end Quic.Spec.StreamTable
