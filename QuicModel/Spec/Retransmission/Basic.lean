import QuicModel.Spec.Core

/-
  WP14 (a), parts 0-2: the list helpers, the state/event/effect vocabulary of
  §13.3 and the `Step` relation.  See `Spec/Retransmission.lean` for the
  package's header, coverage table and notes.
-/
namespace Quic.Spec.Retransmission

/-! ## 0. Small list helpers

`owed`, `ackedInfo` and the flag lists are sets kept as duplicate-free lists so
that two states carrying the same information compare equal (`track` needs
that).  `Spec.Map` is used where a key maps to a value. -/

section Lists
variable {α : Type} [DecidableEq α]

/-- Decidable membership as a `Bool`. -/
def has (l : List α) (x : α) : Bool := decide (x ∈ l)

@[simp] theorem has_eq_true {l : List α} {x : α} : has l x = true ↔ x ∈ l := by
  simp [has]

@[simp] theorem has_eq_false {l : List α} {x : α} : has l x = false ↔ x ∉ l := by
  simp [has]

/-- Add every element of `xs` that is not there yet, keeping the order. -/
def addAll (l : List α) : List α → List α
  | [] => l
  | x :: xs => addAll (if x ∈ l then l else l ++ [x]) xs

theorem mem_addAll (xs : List α) (l : List α) (y : α) :
    y ∈ addAll l xs ↔ y ∈ l ∨ y ∈ xs := by
  induction xs generalizing l with
  | nil => simp [addAll]
  | cons x xs ih =>
    rw [addAll, ih]
    split
    · rename_i h
      constructor
      · rintro (hl | hx)
        · exact Or.inl hl
        · exact Or.inr (List.mem_cons_of_mem _ hx)
      · rintro (hl | hx)
        · exact Or.inl hl
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl h
          · exact Or.inr hx
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact or_assoc

theorem mem_addAll_left {xs l : List α} {y : α} (h : y ∈ l) : y ∈ addAll l xs :=
  (mem_addAll xs l y).mpr (Or.inl h)

theorem mem_addAll_right {xs l : List α} {y : α} (h : y ∈ xs) : y ∈ addAll l xs :=
  (mem_addAll xs l y).mpr (Or.inr h)

/-- Drop every element of `xs`. -/
def removeAll (l xs : List α) : List α := l.filter (fun y => !has xs y)

@[simp] theorem mem_removeAll {l xs : List α} {y : α} :
    y ∈ removeAll l xs ↔ (y ∈ l ∧ y ∉ xs) := by
  simp [removeAll, List.mem_filter]

theorem mem_of_mem_removeAll {l xs : List α} {y : α} (h : y ∈ removeAll l xs) : y ∈ l :=
  (mem_removeAll.mp h).1

end Lists

theorem mem_of_mem_filter {α : Type} {l : List α} {p : α → Bool} {y : α}
    (h : y ∈ l.filter p) : y ∈ l :=
  (List.mem_filter.mp h).1

/-- If an element of `l` is missing from `l.filter p` then `p` rejected it. -/
theorem filter_removed {α : Type} {l : List α} {p : α → Bool} {y : α}
    (ho : y ∈ l) (hn : y ∉ l.filter p) : p y = false := by
  cases hp : p y
  · rfl
  · exact absurd (List.mem_filter.mpr ⟨ho, hp⟩) hn

/-! ## 1. State, events, effects -/

/-- A packet, identified the way loss detection identifies one: a packet number
    in a packet number space (§12.3). -/
structure PktId where
  space : PnSpace
  pn : Nat
  deriving DecidableEq, Repr

/-- The limits §13.3, line 5403 scopes a blocked signal to: "DATA_BLOCKED frames
    have connection scope, STREAM_DATA_BLOCKED frames have stream scope, and
    STREAMS_BLOCKED frames are scoped to a specific stream type." -/
inductive BlockedScope where
  | conn
  | stream (id : StreamId)
  | streams (dir : StreamDir)
  deriving DecidableEq, Repr

/-- The phases of the *receiving* part of a stream (§3.2) that §13.3 names. -/
inductive RecvPhase where
  | recv | sizeKnown | dataRecvd | resetRecvd
  deriving DecidableEq, Repr

/-- §13.3, line 5362: "Data Recvd" or "Reset Recvd". -/
def RecvPhase.done : RecvPhase → Bool
  | .dataRecvd | .resetRecvd => true
  | _ => false

/-- §13.3, line 5393: past "Recv" — "Size Known" or "Reset Recvd" (and
    "Data Recvd", which follows "Size Known"). -/
def RecvPhase.pastRecv : RecvPhase → Bool
  | .recv => false
  | _ => true

/-- "The information that might be carried in frames" (§13.3, line 5329), at the
    granularity at which the text says it is repaired.

    The distinction that matters is between information whose *identity* is the
    frame's content — CRYPTO byte ranges, STREAM byte ranges, a RESET_STREAM, a
    connection ID sequence number, a token, HANDSHAKE_DONE — and information
    that is a *current value* in a scope: §13.3, line 5381 says "The current
    connection maximum data is sent in MAX_DATA frames.  An updated value is
    sent …", so what is repaired after a loss is the scope, not the old value.
    The value-carrying constructors therefore drop the value (NOTE 2). -/
inductive Info where
  /-- §13.3, line 5338: "Data sent in CRYPTO frames is retransmitted …". -/
  | crypto (space : PnSpace) (offset len : Nat)
  /-- §13.3, line 5343: "Application data sent in STREAM frames …". -/
  | streamData (id : StreamId) (offset len : Nat) (fin : Bool)
  /-- §13.3, line 5348: "ACK frames carry the most recent set of acknowledgments". -/
  | ack
  /-- §13.3, line 5355: "Cancellation of stream transmission, as carried in a
      RESET_STREAM frame …".  Carries the content, which line 5359 pins. -/
  | resetStream (id : StreamId) (err finalSize : Nat)
  /-- §13.3, line 5362: "a request to cancel stream transmission, as encoded in
      a STOP_SENDING frame". -/
  | stopSending (id : StreamId) (err : Nat)
  /-- §13.3, line 5367: "Connection close signals …". -/
  | connectionClose
  /-- §13.3, line 5381: "The current connection maximum data …". -/
  | maxData
  /-- §13.3, line 5389: "The current maximum stream data offset …". -/
  | maxStreamData (id : StreamId)
  /-- §13.3, line 5397: "The limit on streams of a given type …". -/
  | maxStreams (dir : StreamDir)
  /-- §13.3, line 5403: "Blocked signals …", connection scope. -/
  | dataBlocked
  /-- §13.3, line 5403: blocked signal, stream scope. -/
  | streamDataBlocked (id : StreamId)
  /-- §13.3, line 5403: blocked signal, stream-type scope. -/
  | streamsBlocked (dir : StreamDir)
  /-- §13.3, line 5412: "A liveness or path validation check using
      PATH_CHALLENGE frames …". -/
  | pathChallenge
  /-- §13.3, line 5418: "Responses to path validation using PATH_RESPONSE
      frames are sent just once." -/
  | pathResponse
  /-- §13.3, line 5422: "New connection IDs are sent in NEW_CONNECTION_ID frames
      and retransmitted if the packet containing them is lost.
      Retransmissions of this frame carry the same sequence number value." -/
  | newConnectionId (seq : Nat)
  /-- §13.3, line 5425: "Likewise, retired connection IDs are sent in
      RETIRE_CONNECTION_ID frames and retransmitted if the packet containing
      them is lost." -/
  | retireConnectionId (seq : Nat)
  /-- §13.3, line 5437: "NEW_TOKEN frames are retransmitted if the packet
      containing them is lost.  No special support is made for detecting
      reordered and duplicated NEW_TOKEN frames other than a direct comparison
      of the frame contents." — so the token itself is the identity. -/
  | newToken (token : List UInt8)
  /-- §13.3, line 5442: "PING and PADDING frames contain no information". -/
  | ping
  /-- §13.3, line 5442. -/
  | padding
  /-- §13.3, line 5445: "The HANDSHAKE_DONE frame MUST be retransmitted until it
      is acknowledged." -/
  | handshakeDone
  /-- RFC 9221 DATAGRAM; outside the assigned text (NOTE 7). -/
  | datagramFrame
  deriving DecidableEq, Repr

/-- The information a frame carries, given the packet number space it is sent in
    (which CRYPTO data needs: §13.3, line 5339). -/
def Info.of (sp : PnSpace) : Frame → Info
  | .padding _ => .padding
  | .ping => .ping
  | .ack .. => .ack
  | .resetStream id err fs => .resetStream ⟨id⟩ err fs
  | .stopSending id err => .stopSending ⟨id⟩ err
  | .crypto off d => .crypto sp off d.size
  | .newToken t => .newToken t.toList
  | .stream id off fin d => .streamData ⟨id⟩ off d.size fin
  | .maxData _ => .maxData
  | .maxStreamData id _ => .maxStreamData ⟨id⟩
  | .maxStreams dir _ => .maxStreams dir
  | .dataBlocked _ => .dataBlocked
  | .streamDataBlocked id _ => .streamDataBlocked ⟨id⟩
  | .streamsBlocked dir _ => .streamsBlocked dir
  | .newConnectionId seq _ _ _ => .newConnectionId seq
  | .retireConnectionId seq => .retireConnectionId seq
  | .pathChallenge _ => .pathChallenge
  | .pathResponse _ => .pathResponse
  | .connectionClose .. => .connectionClose
  | .handshakeDone => .handshakeDone
  | .datagram _ _ => .datagramFrame

/-- Information whose repair is a byte-identical repeat rather than a fresh
    frame carrying a current value.  §13.3, line 5461's "SHOULD avoid
    retransmitting information from packets once they are acknowledged" applies
    to exactly these: a MAX_DATA frame with a *new* value is new information even
    though its scope has been acknowledged before (NOTE 3). -/
def Info.isVerbatim : Info → Bool
  | .crypto .. | .streamData .. | .resetStream .. | .stopSending ..
  | .newConnectionId _ | .retireConnectionId _ | .newToken _ | .handshakeDone => true
  | _ => false

/-- The information §13.3 says is *never* sent again because a packet carrying it
    was lost: ACK (line 5348), CONNECTION_CLOSE (line 5367), PATH_CHALLENGE
    (line 5412), PATH_RESPONSE (line 5418), PING and PADDING (line 5442). -/
def Info.neverRepaired : Info → Bool
  | .ack | .connectionClose | .pathChallenge | .pathResponse
  | .ping | .padding | .datagramFrame => true
  | _ => false

/-- The blocked scope a piece of information belongs to, if any (§13.3, line 5403). -/
def Info.blockedScope : Info → Option BlockedScope
  | .dataBlocked => some .conn
  | .streamDataBlocked id => some (.stream id)
  | .streamsBlocked dir => some (.streams dir)
  | _ => none

structure State where
  /-- A monotone counter stamping each send, so that "the most recently sent
      MAX_DATA frame" (§13.3, line 5381) and "the most recent frame for a scope"
      (line 5403) can be identified. -/
  seq : Nat := 0
  /-- Packets sent and neither acknowledged nor declared lost, with their send
      stamp and the information they carried (§13.3, line 5332). -/
  inFlight : Map PktId (Nat × List Info) := []
  /-- The stamp of the most recent send of each piece of information. -/
  lastSent : Map Info Nat := []
  /-- Information whose most recent carrier was declared lost and that has been
      neither re-sent nor acknowledged nor superseded since. -/
  owed : List Info := []
  /-- Information acknowledged at least once (§13.3, line 5333 and line 5461). -/
  ackedInfo : List Info := []
  /-- Streams for which a RESET_STREAM has been sent (§13.3, line 5343). -/
  resetSent : List StreamId := []
  /-- The content a RESET_STREAM was first sent with (§13.3, line 5359). -/
  resetContent : Map StreamId (Nat × Nat) := []
  /-- Sending parts whose data the peer has acknowledged in full — the
      "Data Recvd" half of §13.3, line 5355. -/
  sendDataAcked : List StreamId := []
  /-- The phase of each receiving part (§13.3, lines 5362 and 5393). -/
  recvPhase : Map StreamId RecvPhase := []
  /-- The limits the endpoint is currently blocked on (§13.3, line 5406). -/
  blocked : List BlockedScope := []
  /-- Packet number spaces whose keys have been discarded (§13.3, line 5339). -/
  keysGone : List PnSpace := []
  deriving DecidableEq, Repr

/-- §13.3, line 5362: the receiving part has reached "Data Recvd" or
    "Reset Recvd", so no further STOP_SENDING is sent. -/
def State.recvDone (s : State) (id : StreamId) : Bool :=
  match s.recvPhase.get? id with
  | some p => p.done
  | none => false

/-- §13.3, line 5393: the receiving part has left "Recv". -/
def State.recvPastRecv (s : State) (id : StreamId) : Bool :=
  match s.recvPhase.get? id with
  | some p => p.pastRecv
  | none => false

inductive Event where
  /-- A packet of `pkt.space` with number `pkt.pn` carrying `fs` went out. -/
  | sentFrames (pkt : PktId) (fs : List Frame)
  /-- [QUIC-RECOVERY] reports that `pkt` was acknowledged (§13.3, line 5333). -/
  | acked (pkt : PktId)
  /-- [QUIC-RECOVERY] reports that `pkt` was declared lost (§13.3, line 5333).
      *Why* it was declared lost is RFC 9002's business, not this model's. -/
  | lost (pkt : PktId)
  /-- §13.3, line 5355: "all stream data is acknowledged by the peer". -/
  | sendPartDataAcked (id : StreamId)
  /-- §13.3, lines 5362 and 5393: the receiving part changed phase. -/
  | recvPartPhase (id : StreamId) (phase : RecvPhase)
  /-- §13.3, line 5339: "Data in CRYPTO frames for Initial and Handshake packets
      is discarded when keys for the corresponding packet number space are
      discarded." -/
  | keysDiscarded (space : PnSpace)
  /-- §13.3, line 5406: the endpoint became, or stopped being, blocked on a
      limit. -/
  | blockedChanged (scope : BlockedScope) (blocked : Bool)
  /-- §13.3, line 5465: "A sender can discard this information after a period of
      time elapses that adequately allows for reordering … or on other events,
      such as reaching a memory limit." -/
  | discardHistory
  deriving DecidableEq

inductive Effect where
  /-- §13.3, line 5332: "New frames and packets are used to carry information
      that is determined to have been lost." -/
  | repair (i : Info)
  /-- §13.3, line 5333: "sending ceases when a packet containing that
      information is acknowledged." -/
  | ceaseSending (i : Info)
  /-- §13.3, line 5471: "Upon detecting losses, a sender MUST take appropriate
      congestion control action."  *What* the action is, is RFC 9002's. -/
  | congestionControlAction
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ## 2. The specification

Every event has exactly one outcome: §13.3 describes bookkeeping that follows
from loss detection and nowhere offers the receiver a choice.  The looseness of
the section is all on the *send* side (lines 5452 and 5461 explicitly permit
both retransmitting a copy and not retransmitting at all), which `MaySend` and
`Recommended` carry. -/

/-- Is this information sent again when the packet carrying it is lost?
    One clause per bullet of §13.3. -/
def State.repairable (s : State) : Info → Bool
  -- line 5338 "retransmitted … until all data has been acknowledged", with
  -- line 5339 "discarded when keys for the corresponding packet number space
  -- are discarded".
  | .crypto sp _ _ => !has s.keysGone sp
  -- line 5343 "retransmitted in new STREAM frames unless the endpoint has sent
  -- a RESET_STREAM for that stream".
  | .streamData id _ _ _ => !has s.resetSent id
  -- line 5348 "ACK frames carry the most recent set of acknowledgments"; an old
  -- ACK frame is not repaired.
  | .ack => false
  -- line 5355 "sent until acknowledged or until all stream data is
  -- acknowledged by the peer".
  | .resetStream id _ _ => !has s.sendDataAcked id
  -- line 5362 "sent until the receiving part of the stream enters either a
  -- 'Data Recvd' or 'Reset Recvd' state".
  | .stopSending id _ => !s.recvDone id
  -- line 5367 "Connection close signals … are not sent again when packet loss
  -- is detected, but as described in Section 10."
  | .connectionClose => false
  -- lines 5381, 5389, 5397: an updated value is sent.
  | .maxData => true
  | .maxStreamData _ => true
  | .maxStreams _ => true
  -- line 5406 "New frames are sent if packets containing the most recent frame
  -- for a scope is lost, but only while the endpoint is blocked on the
  -- corresponding limit."
  | .dataBlocked => has s.blocked .conn
  | .streamDataBlocked id => has s.blocked (.stream id)
  | .streamsBlocked dir => has s.blocked (.streams dir)
  -- line 5412: a new PATH_CHALLENGE carries a *different* payload, so the lost
  -- frame itself is not repaired; line 5418 "sent just once".
  | .pathChallenge => false
  | .pathResponse => false
  -- line 5422.
  | .newConnectionId _ => true
  | .retireConnectionId _ => true
  -- line 5437.
  | .newToken _ => true
  -- line 5442 "lost PING or PADDING frames do not require repair".
  | .ping => false
  | .padding => false
  -- line 5445 "MUST be retransmitted until it is acknowledged".
  | .handshakeDone => true
  -- RFC 9221 §5; outside the assigned text (NOTE 7).
  | .datagramFrame => false

theorem neverRepaired_of_repairable {s : State} {i : Info} (h : s.repairable i = true) :
    i.neverRepaired = false := by
  cases i <;> simp_all [State.repairable, Info.neverRepaired]

/-- Stamp every piece of information with the current send counter. -/
def setAll (m : Map Info Nat) (n : Nat) : List Info → Map Info Nat
  | [] => m
  | i :: is => setAll (m.set i n) n is

/-- The streams a batch of frames sends a RESET_STREAM for (§13.3, line 5343). -/
def resetsOf (is : List Info) : List StreamId :=
  is.filterMap (fun i => match i with | .resetStream id _ _ => some id | _ => none)

/-- Is this STREAM data for one of the streams just reset?  §13.3, line 5345:
    "Once an endpoint sends a RESET_STREAM frame, no further STREAM frames are
    needed." -/
def supersededByReset (ids : List StreamId) : Info → Bool
  | .streamData id _ _ _ => has ids id
  | _ => false

/-! The predicates the state transformers filter `owed` with, named so that the
proofs below can talk about them. -/

/-- §13.3, line 5345: the STREAM data of a stream that was just reset. -/
def keepAfterReset (ids : List StreamId) (i : Info) : Bool := !supersededByReset ids i

/-- §13.3, line 5355: the RESET_STREAM of a stream whose data is all acknowledged. -/
def keepAfterDataAcked (id : StreamId) : Info → Bool
  | .resetStream id' _ _ => decide (id' ≠ id)
  | _ => true

/-- §13.3, line 5362: the STOP_SENDING of a receiving part that is finished. -/
def keepAfterRecvPhase (id : StreamId) (done : Bool) : Info → Bool
  | .stopSending id' _ => !(decide (id' = id) && done)
  | _ => true

/-- §13.3, line 5339: CRYPTO data of a discarded packet number space. -/
def keepAfterKeysDiscarded (sp : PnSpace) : Info → Bool
  | .crypto sp' _ _ => decide (sp' ≠ sp)
  | _ => true

/-- §13.3, line 5406: a blocked signal whose limit no longer blocks. -/
def keepAfterUnblocked (sc : BlockedScope) (i : Info) : Bool :=
  decide (i.blockedScope ≠ some sc)

/-- Record the content each RESET_STREAM was *first* sent with (§13.3, line 5359). -/
def recordResets (m : Map StreamId (Nat × Nat)) : List Info → Map StreamId (Nat × Nat)
  | [] => m
  | .resetStream id e f :: is =>
    recordResets (match m.get? id with | none => m.set id (e, f) | some _ => m) is
  | _ :: is => recordResets m is

/-- §13.3, line 5332: a packet goes out carrying `fs`. -/
def State.afterSent (s : State) (pkt : PktId) (fs : List Frame) : State :=
  { s with
    seq := s.seq + 1
    inFlight := s.inFlight.set pkt (s.seq, fs.map (Info.of pkt.space))
    lastSent := setAll s.lastSent s.seq (fs.map (Info.of pkt.space))
    owed := (removeAll s.owed (fs.map (Info.of pkt.space))).filter
      (keepAfterReset (resetsOf (fs.map (Info.of pkt.space))))
    resetSent := addAll s.resetSent (resetsOf (fs.map (Info.of pkt.space)))
    resetContent := recordResets s.resetContent (fs.map (Info.of pkt.space)) }

/-- The information a packet carried, or nothing if it is not in flight (already
    acknowledged, already declared lost, or never sent — see NOTE 1). -/
def State.carried (s : State) (pkt : PktId) : List Info :=
  match s.inFlight.get? pkt with
  | none => []
  | some (_, is) => is

/-- §13.3, line 5333: "sending ceases when a packet containing that information
    is acknowledged." -/
def State.afterAcked (s : State) (pkt : PktId) : State :=
  { s with
    inFlight := s.inFlight.erase pkt
    owed := removeAll s.owed (s.carried pkt)
    ackedInfo := addAll s.ackedInfo (s.carried pkt) }

def State.ackedEffects (s : State) (pkt : PktId) : List Effect :=
  (s.carried pkt).map Effect.ceaseSending

/-- The information a lost packet causes to be sent again: what the text repairs
    (`repairable`), that this packet was the most recent carrier of (lines 5381,
    5389, 5397 and 5406 all say "the most recent"), and that has not already been
    acknowledged in the verbatim sense of line 5333. -/
def State.newlyOwed (s : State) (k : Nat) (is : List Info) : List Info :=
  is.filter (fun i =>
    s.repairable i && decide (s.lastSent.get? i = some k) &&
      !(i.isVerbatim && has s.ackedInfo i))

/-- What a lost packet owes, `[]` if it was not in flight. -/
def State.lostOwed (s : State) (pkt : PktId) : List Info :=
  match s.inFlight.get? pkt with
  | none => []
  | some (k, is) => s.newlyOwed k is

/-- §13.3, line 5333: "information is sent again when a packet containing that
    information is determined to be lost". -/
def State.afterLost (s : State) (pkt : PktId) : State :=
  { s with
    inFlight := s.inFlight.erase pkt
    owed := addAll s.owed (s.lostOwed pkt) }

def State.lostEffects (s : State) (pkt : PktId) : List Effect :=
  match s.inFlight.get? pkt with
  | none => []
  | some _ => Effect.congestionControlAction :: (s.lostOwed pkt).map Effect.repair

/-- §13.3, line 5355: the peer has all the stream's data, so the RESET_STREAM is
    no longer owed. -/
def State.afterSendDataAcked (s : State) (id : StreamId) : State :=
  { s with
    sendDataAcked := addAll s.sendDataAcked [id]
    owed := s.owed.filter (keepAfterDataAcked id) }

/-- §13.3, line 5362: the receiving part reached "Data Recvd" or "Reset Recvd",
    so the STOP_SENDING is no longer owed. -/
def State.afterRecvPhase (s : State) (id : StreamId) (p : RecvPhase) : State :=
  { s with
    recvPhase := s.recvPhase.set id p
    owed := s.owed.filter (keepAfterRecvPhase id p.done) }

/-- §13.3, line 5339: CRYPTO data of a discarded packet number space is gone. -/
def State.afterKeysDiscarded (s : State) (sp : PnSpace) : State :=
  { s with
    keysGone := addAll s.keysGone [sp]
    owed := s.owed.filter (keepAfterKeysDiscarded sp) }

/-- §13.3, line 5406: blocked signals are repaired "only while the endpoint is
    blocked on the corresponding limit". -/
def State.afterBlocked (s : State) (sc : BlockedScope) (b : Bool) : State :=
  { s with
    blocked := if b then addAll s.blocked [sc] else removeAll s.blocked [sc]
    owed := if b then s.owed else s.owed.filter (keepAfterUnblocked sc) }

inductive Step : State → Event → Out → Prop
  /-- §13.3, line 5332: "New frames and packets are used to carry information
      that is determined to have been lost."  Sending a frame records what it
      carried, clears the corresponding debt, and — line 5345 — supersedes the
      STREAM data of any stream it resets. -/
  | sent {s pkt fs} :
      Step s (.sentFrames pkt fs) (.ok (s.afterSent pkt fs) [])
  /-- §13.3, line 5333: "sending ceases when a packet containing that
      information is acknowledged." -/
  | acked {s pkt} :
      Step s (.acked pkt) (.ok (s.afterAcked pkt) (s.ackedEffects pkt))
  /-- §13.3, line 5333: "information is sent again when a packet containing that
      information is determined to be lost"; and line 5471: "Upon detecting
      losses, a sender MUST take appropriate congestion control action." -/
  | lost {s pkt} :
      Step s (.lost pkt) (.ok (s.afterLost pkt) (s.lostEffects pkt))
  /-- §13.3, line 5355: "sent until acknowledged or until all stream data is
      acknowledged by the peer (that is, either the "Reset Recvd" or
      "Data Recvd" state is reached on the sending part of the stream)." -/
  | sendDataAcked {s id} :
      Step s (.sendPartDataAcked id) (.ok (s.afterSendDataAcked id) [])
  /-- §13.3, line 5362: "a request to cancel stream transmission, as encoded in a
      STOP_SENDING frame, is sent until the receiving part of the stream enters
      either a "Data Recvd" or "Reset Recvd" state". -/
  | recvPhase {s id p} :
      Step s (.recvPartPhase id p) (.ok (s.afterRecvPhase id p) [])
  /-- §13.3, line 5339: "Data in CRYPTO frames for Initial and Handshake packets
      is discarded when keys for the corresponding packet number space are
      discarded." -/
  | keysDiscarded {s sp} :
      Step s (.keysDiscarded sp) (.ok (s.afterKeysDiscarded sp) [])
  /-- §13.3, line 5406: "New frames are sent if packets containing the most
      recent frame for a scope is lost, but only while the endpoint is blocked
      on the corresponding limit." -/
  | blockedChanged {s sc b} :
      Step s (.blockedChanged sc b) (.ok (s.afterBlocked sc b) [])
  /-- §13.3, line 5465: "A sender can discard this information after a period of
      time elapses that adequately allows for reordering". -/
  | discardHistory {s} :
      Step s .discardHistory (.ok { s with ackedInfo := [] } [])

end Quic.Spec.Retransmission
