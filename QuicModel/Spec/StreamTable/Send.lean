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

* **A smaller limit may be advertised.**  §4.1, line 1364: "Once a receiver
  advertises a limit for the connection or a stream, it is not an error to
  advertise a smaller limit, but the smaller limit has no effect", and §4.6,
  line 1551: "Once a receiver advertises a stream limit using the MAX_STREAMS
  frame, advertising a smaller limit has no effect"; §4.6, line 1552: "A
  receiver MUST ignore any MAX_STREAMS frame that does not increase the stream
  limit."  Neither sentence forbids sending it, so `MaySend` does not require an
  increase — unlike `Spec/Template.lean`, which this file supersedes (see NOTES).
* **A blocked frame carries the limit in force.**  §13.3, line 5409: "These
  frames always include the limit that is causing blocking at the time that they
  are transmitted."
* **A frame naming a stream that does not exist is `False`, by modelling choice
  and not by the text.**  Review finding S-5: nothing in the assigned range
  forbids sending a frame on a stream the sender has itself opened, so this
  conjunct is an artefact of the model needing per-stream state before it can
  say anything.  It is a live obligation on WP13 — see NOTES 4 in
  `Spec/StreamTable.lean`. -/

/-- §4.6, line 1546 with §4.1, line 1330: what the connection level adds to a
    stream's own `MaySend` for a frame that consumes send credit. -/
def sendCredit (s : State) (id : StreamId) (k : Nat) : Prop :=
  s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer

def sendCreditB (s : State) (id : StreamId) (k : Nat) : Bool :=
  decide (s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer)

/-- A frame naming a stream may be sent only for a stream that exists, within
    the peer's stream limit (§4.6, line 1546), and if the stream itself permits
    it (WP2).  `s.has id = true` is the modelling conjunct of finding S-5, not a
    sentence of the text: WP13 must synthesise `Event.appOpenStream` before the
    first frame on a locally-initiated stream. -/
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

/-! ### 6b. Several frames at once

`MaySend` judges one frame against the state as it stands, so two frames that
each fit the remaining connection credit both pass it although together they do
not (audit D34-5).  §4.1, line 1330: "Senders MUST NOT send data in excess of
either limit", and line 1336 counts the connection limit across all streams, so
a packet or datagram is judged on the credit all of its frames consume
together.  What a batch consumes is, per stream, the distance from
`sentHighest` to the highest offset any of its frames reaches: a retransmission
or an overlap consumes nothing, so summing frame lengths would be wrong. -/

/-- The stream and end offset of a frame that consumes connection send credit:
    exactly the frames `MaySend` applies `sendCredit` to. -/
def creditEnd? : Frame → Option (StreamId × Nat)
  | .stream id offset _ data => some (⟨id⟩, offset + data.size)
  | .resetStream id _ fs => some (⟨id⟩, fs)
  | _ => none

/-- The highest end offset `ends` reaches on stream `id`. -/
def batchHighest (ends : List (StreamId × Nat)) (id : StreamId) : Nat :=
  ends.foldr (fun e m => if e.1 = id then max e.2 m else m) 0

/-- The connection credit `ends` consumes together.  Each entry contributes what
    it adds beyond both what the stream has already sent and what the entries
    after it reach on the same stream, so every stream is counted once, up to
    its highest offset, in whatever order the frames come. -/
def batchIncrease (s : State) : List (StreamId × Nat) → Nat
  | [] => 0
  | e :: rest =>
    (e.2 - max (sentHighest (s.get e.1)) (batchHighest rest e.1)) + batchIncrease s rest

/-- §4.1, line 1330, for all the frames of one packet or datagram. -/
def MaySendAll (s : State) (fs : List Frame) : Prop :=
  s.sentTotal + batchIncrease s (fs.filterMap creditEnd?) ≤ s.maxDataPeer

def maySendAll (s : State) (fs : List Frame) : Bool :=
  decide (s.sentTotal + batchIncrease s (fs.filterMap creditEnd?) ≤ s.maxDataPeer)

theorem maySendAll_iff (s : State) (fs : List Frame) :
    maySendAll s fs = true ↔ MaySendAll s fs := by simp [maySendAll, MaySendAll]

theorem batchHighest_le_batchIncrease (s : State) (ends : List (StreamId × Nat))
    (id : StreamId) : batchHighest ends id - sentHighest (s.get id) ≤ batchIncrease s ends := by
  induction ends with
  | nil => simp [batchHighest, batchIncrease]
  | cons e rest ih =>
    have hb : batchHighest (e :: rest) id =
        if e.1 = id then max e.2 (batchHighest rest id) else batchHighest rest id := rfl
    rw [hb]
    show _ ≤ (e.2 - max (sentHighest (s.get e.1)) (batchHighest rest e.1)) + batchIncrease s rest
    split
    · next h => subst h; omega
    · omega

theorem le_batchHighest {ends : List (StreamId × Nat)} {e : StreamId × Nat} (h : e ∈ ends) :
    e.2 ≤ batchHighest ends e.1 := by
  induction ends with
  | nil => cases h
  | cons x rest ih =>
    have hb : batchHighest (x :: rest) e.1 =
        if x.1 = e.1 then max x.2 (batchHighest rest e.1) else batchHighest rest e.1 := rfl
    rw [hb]
    rcases List.mem_cons.mp h with rfl | h
    · simp only [ite_true]; omega
    · have := ih h
      split <;> omega

/-- The batch rule subsumes the per-frame one: every frame of a permitted batch
    has the connection credit `MaySend` asks of it alone. -/
theorem sendCredit_of_maySendAll {s : State} {fs : List Frame} (h : MaySendAll s fs)
    {f : Frame} (hf : f ∈ fs) {id : StreamId} {k : Nat} (he : creditEnd? f = some (id, k)) :
    sendCredit s id k := by
  have hm : (id, k) ∈ fs.filterMap creditEnd? := List.mem_filterMap.mpr ⟨f, hf, he⟩
  have h1 := le_batchHighest hm
  have h2 := batchHighest_le_batchIncrease s (fs.filterMap creditEnd?) id
  unfold MaySendAll at h
  unfold sendCredit
  simp only at h1
  omega

/-- For a single frame the batch rule is `sendCredit`, no more. -/
theorem maySendAll_singleton (s : State) (f : Frame) (id : StreamId) (k : Nat)
    (he : creditEnd? f = some (id, k)) : MaySendAll s [f] ↔ sendCredit s id k := by
  simp [MaySendAll, sendCredit, List.filterMap, he, batchIncrease, batchHighest]

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

§4.1, line 1376 and §4.6, line 1561 recommend a blocked frame when actually
blocked, and §4.1, line 1381 recommends repeating it periodically; §4.2's
autotuning advice and §4.3 are performance guidance with no observable rule.
None of them restricts `MaySend`. -/

def Recommended (s : State) : Frame → Prop
  -- §4.1, line 1375: "If a sender has sent data up to the limit, it will be
  -- unable to send new data and is considered blocked."
  | .dataBlocked _ => s.sentTotal = s.maxDataPeer
  -- §4.6, line 1561: "An endpoint that is unable to open a new stream due to
  -- the peer's limits SHOULD send a STREAMS_BLOCKED frame."
  | .streamsBlocked dir _ => s.opened.get s.role dir = s.maxStreamsPeer.get dir
  | _ => True


end Quic.Spec.StreamTable
