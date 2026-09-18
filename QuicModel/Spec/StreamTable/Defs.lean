import QuicModel.Spec.Stream

/-
  WP9 StreamTable, part 1 of 3: state, events, effects and the routing
  vocabulary.

  Subject: all the streams of one connection, as seen by one endpoint — stream
  creation and implicit opening (§2.1), the stream-count limits of §4.6, and
  connection-level flow control (§4.1, §4.5, §19.9).  One instance of
  `Spec.Stream.component` (WP2) per stream; this package routes events to them
  and adds everything only the connection knows.

  Parts 2–4 (`Step`, `outcomes`, `outcomes_iff`) are in `StreamTable/Step.lean`,
  parts 5–10 in `Spec/StreamTable.lean`.
-/
namespace Quic.Spec.StreamTable

/-- §4.6, line 1543 / §19.11, line 7802: "This value cannot exceed 2^60, as it
    is not possible to encode stream IDs larger than 2^62-1." -/
def maxStreamsLimit : Nat := 2 ^ 60

/-! ## 1. State, events, effects -/

/-- The six §18.2 transport parameters this package needs, as plain numbers
    (`QuicModel/Spec/TransportParams.lean` has the wire format and the field
    names; WP12 will pass them in).  One `Limits` value per endpoint. -/
structure Limits where
  /-- `initial_max_data` (0x04). -/
  maxData : Nat
  /-- `initial_max_stream_data_bidi_local` (0x05): the limit for bidirectional
      streams opened by the endpoint that *sends* this parameter. -/
  maxStreamDataBidiLocal : Nat
  /-- `initial_max_stream_data_bidi_remote` (0x06): the limit for bidirectional
      streams opened by the endpoint that *receives* this parameter. -/
  maxStreamDataBidiRemote : Nat
  /-- `initial_max_stream_data_uni` (0x07). -/
  maxStreamDataUni : Nat
  /-- `initial_max_streams_bidi` (0x08). -/
  maxStreamsBidi : Nat
  /-- `initial_max_streams_uni` (0x09). -/
  maxStreamsUni : Nat
  deriving DecidableEq, Repr

/-- §4.6, line 1535: "Separate limits apply to unidirectional and bidirectional
    streams."  A per-direction pair of counters. -/
structure Counts where
  bidi : Nat
  uni : Nat
  deriving DecidableEq, Repr

namespace Counts

def get (c : Counts) : StreamDir → Nat
  | .bidi => c.bidi
  | .uni => c.uni

def set (c : Counts) : StreamDir → Nat → Counts
  | .bidi, v => { c with bidi := v }
  | .uni, v => { c with uni := v }

@[simp] theorem get_set (c : Counts) (d d' : StreamDir) (v : Nat) :
    (c.set d v).get d' = if d = d' then v else c.get d' := by
  cases d <;> cases d' <;> rfl

end Counts

/-- The four stream-type counters of §2.1, Table 1, indexed by the initiator of
    the stream and its directionality. -/
structure Opened where
  byClient : Counts
  byServer : Counts
  deriving DecidableEq, Repr

namespace Opened

def get (o : Opened) : Role → StreamDir → Nat
  | .client, d => o.byClient.get d
  | .server, d => o.byServer.get d

def set (o : Opened) : Role → StreamDir → Nat → Opened
  | .client, d, v => { o with byClient := o.byClient.set d v }
  | .server, d, v => { o with byServer := o.byServer.set d v }

@[simp] theorem get_set (o : Opened) (r r' : Role) (d d' : StreamDir) (v : Nat) :
    (o.set r d v).get r' d' = if r = r' ∧ d = d' then v else o.get r' d' := by
  cases r <;> cases r' <;> cases d <;> cases d' <;>
    simp [get, set, Counts.get, Counts.set]

end Opened

/-- Two stream IDs of different initiators: one of them is the peer's. -/
theorem eq_peer_of_ne {r r' : Role} (h : ¬ r = r') : r = r'.peer := by
  cases r <;> cases r' <;> simp_all [Role.peer]

theorem role_ne_peer (r : Role) : ¬ r = r.peer := by cases r <;> simp [Role.peer]

/-- All the streams of one connection at one endpoint.

`streams` holds the state of every stream that has taken a step; a stream that
exists but has no entry is at its initial state (`freshStream`), which is what
`get` returns.  Whether a stream *exists* is decided by the high-water marks
`opened`, not by the table: §2.1, line 712 opens every
lower-numbered stream of a type implicitly, and §2.1, line 687 forbids reusing a
stream ID, so "exists" is exactly "its index is below the high-water mark for
its type" — see the NOTES in `Spec/StreamTable.lean`. -/
structure State where
  /-- Which endpoint we are. -/
  role : Role
  /-- Our own transport parameters: what we let the peer send and open. -/
  ours : Limits
  /-- The peer's transport parameters: what we may send and open. -/
  theirs : Limits
  /-- Per-stream state, for streams that have taken a step. -/
  streams : Map StreamId Stream.State
  /-- §2.1, line 712: the high-water mark of each of the four stream types —
      how many streams of that type have ever been opened. -/
  opened : Opened
  /-- §4.6: the cumulative stream limit we have advertised to the peer. -/
  maxStreamsLocal : Counts
  /-- §4.6: the cumulative stream limit the peer has advertised to us. -/
  maxStreamsPeer : Counts
  /-- §4.1, line 1349: the connection-level limit we have advertised (MAX_DATA
      we have sent; initially our `initial_max_data`). -/
  maxDataLocal : Nat
  /-- §19.9, line 7710: "A receiver maintains a cumulative sum of bytes received
      on all streams" — the sum of the highest received offsets over all
      streams, including closed and reset ones (§4.5, line 1495: "The receiver
      MUST use the final size of the stream to account for all bytes sent on the
      stream in its connection level flow controller"). -/
  recvTotal : Nat
  /-- The connection-level limit the peer has advertised to us. -/
  maxDataPeer : Nat
  /-- The same sum for data we have sent. -/
  sentTotal : Nat
  deriving DecidableEq, Repr

/-- §4.6, line 1535 and §4.1, line 1331: "A receiver sets initial limits for all
    streams through transport parameters during the handshake." -/
def init (role : Role) (ours theirs : Limits) : State :=
  { role, ours, theirs, streams := [],
    opened := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩,
    maxStreamsLocal := ⟨ours.maxStreamsBidi, ours.maxStreamsUni⟩,
    maxStreamsPeer := ⟨theirs.maxStreamsBidi, theirs.maxStreamsUni⟩,
    maxDataLocal := ours.maxData, recvTotal := 0,
    maxDataPeer := theirs.maxData, sentTotal := 0 }

namespace State

/-- §18.2: the stream-level limit *we* advertised for this stream, i.e. how much
    the peer may send on it. -/
def recvMaxOf (s : State) (id : StreamId) : Nat :=
  match id.dir with
  | .uni => s.ours.maxStreamDataUni
  | .bidi =>
      if id.initiator = s.role then s.ours.maxStreamDataBidiLocal
      else s.ours.maxStreamDataBidiRemote

/-- The mirror image: the limit the peer advertised for this stream, i.e. how
    much we may send on it. -/
def sendMaxOf (s : State) (id : StreamId) : Nat :=
  match id.dir with
  | .uni => s.theirs.maxStreamDataUni
  | .bidi =>
      if id.initiator = s.role then s.theirs.maxStreamDataBidiRemote
      else s.theirs.maxStreamDataBidiLocal

/-- A stream at its initial state (WP2's `Stream.init`, with the two initial
    limits this connection's transport parameters give it). -/
def freshStream (s : State) (id : StreamId) : Stream.State :=
  Stream.init id s.role (s.sendMaxOf id) (s.recvMaxOf id)

/-- §2.1, line 712: a stream exists once its index is below the high-water mark
    of its type — which is what makes implicit opening decidable. -/
def has (s : State) (id : StreamId) : Bool :=
  decide (id.index < s.opened.get id.initiator id.dir)

/-- The state of a stream: its entry in the table, or its initial state if it
    has not taken a step yet.  Only meaningful when `has s id`. -/
def get (s : State) (id : StreamId) : Stream.State :=
  (s.streams.get? id).getD (s.freshStream id)

def setStream (s : State) (id : StreamId) (st : Stream.State) : State :=
  { s with streams := s.streams.set id st }

/-- §2.1, line 712: "A stream ID that is used out of order results in all
    streams of that type with lower-numbered stream IDs also being opened." -/
def openThrough (s : State) (id : StreamId) : State :=
  { s with
      opened := s.opened.set id.initiator id.dir
        (max (s.opened.get id.initiator id.dir) (id.index + 1)) }

/-- §4.6, line 1553: "Endpoints MUST NOT exceed the limit set by their peer." -/
def withinPeerStreamLimit (s : State) (id : StreamId) : Bool :=
  !decide (id.initiator = s.role) || decide (id.index < s.maxStreamsPeer.get id.dir)

end State

/-- Events.  Received frames that name a stream and the local actions of WP2 are
    both routed by stream ID through `Event.stream`; the connection-level frames
    and the two "raise our limits" actions are separate. -/
inductive Event where
  /-- A frame or a local action concerning one stream (§19.4, §19.5, §19.8,
      §19.10, §19.13 and all of WP2's application events). -/
  | stream (id : StreamId) (e : Stream.Event)
  /-- §19.9 MAX_DATA received. -/
  | recvMaxData (v : Nat)
  /-- §19.12 DATA_BLOCKED received. -/
  | recvDataBlocked (v : Nat)
  /-- §19.11 MAX_STREAMS received. -/
  | recvMaxStreams (dir : StreamDir) (v : Nat)
  /-- §19.14 STREAMS_BLOCKED received. -/
  | recvStreamsBlocked (dir : StreamDir) (v : Nat)
  /-- §2.1: the application opens a new stream of this type. -/
  | appOpenStream (dir : StreamDir)
  /-- §4.1, line 1349: we transmitted a MAX_DATA frame advertising this limit. -/
  | sentMaxData (v : Nat)
  /-- §4.6, line 1537: we transmitted a MAX_STREAMS frame. -/
  | sentMaxStreams (dir : StreamDir) (v : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- An effect of one stream (WP2), tagged with the stream it came from. -/
  | stream (id : StreamId) (e : Stream.Effect)
  /-- A stream came into existence, whether explicitly or implicitly (§2.1,
      line 712).  One per stream, in increasing order of stream ID. -/
  | streamOpened (id : StreamId)
  /-- §4.1: the peer raised the connection-level limit; more may be sent. -/
  | dataCreditAvailable (max : Nat)
  /-- §4.6: the peer raised the stream limit; more streams may be opened. -/
  | streamsAvailable (dir : StreamDir) (max : Nat)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ### Routing vocabulary -/

/-- Is this event a frame from the peer (as opposed to a local action)?  A frame
    for a stream that does not exist is an error; a local action on one is
    impossible.  (WP2 splits the same way; see `Send.Event.isPeerFrame`.) -/
def peerFrame : Stream.Event → Bool
  | .send e => e.isPeerFrame
  | .recv e => e.isPeerFrame

/-- §4.1, line 1352 / §4.5, line 1495: the connection-level credit a stream has
    consumed on the receive side is its highest received offset — which a
    RESET_STREAM sets to the final size. -/
def recvHighest (st : Stream.State) : Nat :=
  match st.recv with
  | some rs => rs.highest
  | none => 0

/-- The same on the send side (§4.5, line 1479: "one higher than the offset of
    the byte with the largest offset sent on the stream"). -/
def sentHighest (st : Stream.State) : Nat :=
  match st.send with
  | some ss => ss.sent
  | none => 0

/-- The absolute offset a received frame accounts for at the connection level,
    if it carries data at all. -/
def recvEnd : Stream.Event → Option Nat
  | .recv (.recvStream offset len _) => some (offset + len)
  | .recv (.recvResetStream _ fs) => some fs
  | _ => none

/-- The same for a frame we transmit. -/
def sentEnd : Stream.Event → Option Nat
  | .send (.sentStream offset len _) => some (offset + len)
  | .send (.sentResetStream _ fs) => some fs
  | _ => none

theorem sentEnd_eq_none_of_recvEnd {e : Stream.Event} {k : Nat} (h : recvEnd e = some k) :
    sentEnd e = none := by
  cases e with
  | send e => cases e <;> simp [recvEnd] at h
  | recv e => cases e <;> rfl

/-- §19.9, line 7712: "An endpoint MUST terminate a connection with a
    FLOW_CONTROL_ERROR error if it receives more data than the maximum data
    value that it has sent."  The frame's contribution is what it adds to the
    stream's highest received offset. -/
def connRecvViolation (s : State) (st : Stream.State) (e : Stream.Event) : Bool :=
  match recvEnd e with
  | none => false
  | some k => decide (s.maxDataLocal < s.recvTotal + (k - recvHighest st))

/-- §4.1, line 1330: "Senders MUST NOT send data in excess of either limit."
    A frame that would exceed the peer's MAX_DATA is not sent. -/
def connSendBlocked (s : State) (st : Stream.State) (e : Stream.Event) : Bool :=
  match sentEnd e with
  | none => false
  | some k => decide (s.maxDataPeer < s.sentTotal + (k - sentHighest st))

theorem sentEnd_eq_none_of_peerFrame {e : Stream.Event} (h : peerFrame e = true) :
    sentEnd e = none := by
  cases e with
  | send e => cases e <;> simp_all [peerFrame, sentEnd, Stream.Send.Event.isPeerFrame]
  | recv e => rfl

/-- A frame from the peer never consumes send-side credit. -/
theorem connSendBlocked_false_of_peerFrame {s : State} {st : Stream.State} {e : Stream.Event}
    (h : peerFrame e = true) : connSendBlocked s st e = false := by
  simp [connSendBlocked, sentEnd_eq_none_of_peerFrame h]

theorem connSendBlocked_false_of_recvViolation {s : State} {st : Stream.State}
    {e : Stream.Event} (h : connRecvViolation s st e = true) :
    connSendBlocked s st e = false := by
  simp only [connRecvViolation] at h
  cases he : recvEnd e with
  | none => rw [he] at h; exact absurd h (by simp)
  | some k => simp [connSendBlocked, sentEnd_eq_none_of_recvEnd he]

/-- The connection-level totals move with the stream's own accounting. -/
def afterStep (s : State) (id : StreamId) (st st' : Stream.State) : State :=
  { s.setStream id st' with
      recvTotal := s.recvTotal + (recvHighest st' - recvHighest st),
      sentTotal := s.sentTotal + (sentHighest st' - sentHighest st) }

/-- §2.1, line 712: one `streamOpened` per stream that opening `id` creates,
    in increasing order of stream ID. -/
def openedEffects (s : State) (id : StreamId) : List Effect :=
  (List.range' (s.opened.get id.initiator id.dir)
      (id.index + 1 - s.opened.get id.initiator id.dir)).map
    (fun n => Effect.streamOpened (StreamId.make id.initiator id.dir n))

/-- Lift one stream's outcome to the table: `base` is the table after any
    implicit opening, `pre` the effects that opening produced. -/
def lift (base : State) (id : StreamId) (st : Stream.State) (pre : List Effect) :
    Outcome Stream.State Stream.Effect → Out
  | .ok st' fx => .ok (afterStep base id st st') (pre ++ fx.map (Effect.stream id))
  | .error c => .error c
  | .drop => .drop

/-- Every outcome one stream permits, lifted. -/
def delegate (base : State) (id : StreamId) (st : Stream.State) (pre : List Effect)
    (e : Stream.Event) : List Out :=
  (Stream.outcomes st e).map (lift base id st pre)

def isErr : Out → Bool
  | .error _ => true
  | _ => false

theorem delegate_ne (base : State) (id : StreamId) (st : Stream.State) (pre : List Effect)
    (e : Stream.Event) : delegate base id st pre e ≠ [] := by
  simp only [delegate, ne_eq, List.map_eq_nil_iff]
  exact Stream.outcomes_ne st e

/-- The next stream ID of a type that the application will open. -/
def State.nextLocal (s : State) (dir : StreamDir) : StreamId :=
  StreamId.make s.role dir (s.opened.get s.role dir)

end Quic.Spec.StreamTable
