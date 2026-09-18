import QuicModel.Spec.Core

/-
  WP14 (a): §13.3 Retransmission of Information — the *cross-cutting* rules.

  Text: draft-ietf-quic-transport-34, lines 5325–5474.

  Loss detection and congestion control are [QUIC-RECOVERY] (RFC 9002) and stay
  abstract: `Event.lost` says only that a packet was declared lost, and
  `Event.acked` that one was acknowledged.  What this component owns is what the
  transport text says happens *to the information* those packets carried.

  The per-frame send rules the individual frame types have are owned elsewhere
  and are not repeated here (components compose by conjunction):

  * `Spec/Stream/Send.lean`  — no STREAM data after RESET_STREAM (§3.1, §3.5).
  * `Spec/StreamTable.lean`  — §13.3 line 5403: a blocked frame carries the
    limit in force when it is transmitted.
  * `Spec/PathValidation.lean` — §8.2.2 line 3205: at most one PATH_RESPONSE per
    received PATH_CHALLENGE, which is §13.3 line 5418's "sent just once".
  * `Spec/ConnIds/*.lean`     — NEW_CONNECTION_ID / RETIRE_CONNECTION_ID repeats.
  * `Spec/Ack.lean`           — ACK frame contents (§13.2).
  * `Spec/Termination*.lean`  — CONNECTION_CLOSE, which §13.3 line 5367 hands to
    §10 wholesale.

  Exported for the composed endpoint (WP12):
  `Owes` / `owes` / `MustRetransmit` / `RepairObligationMet` — §13.3 line 5445's
  "MUST be retransmitted until it is acknowledged" is an obligation to *send*
  something, which no single step can force, exactly like `Ack.ackOverdue`.
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
  /-- §13.3, line 5422: "Likewise, retired connection IDs are sent in
      RETIRE_CONNECTION_ID frames and retransmitted …". -/
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
    (which CRYPTO data needs: §13.3, line 5340). -/
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
  /-- Information acknowledged at least once (§13.3, line 5335 and line 5461). -/
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
  /-- Packet number spaces whose keys have been discarded (§13.3, line 5340). -/
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
  /-- [QUIC-RECOVERY] reports that `pkt` was acknowledged (§13.3, line 5335). -/
  | acked (pkt : PktId)
  /-- [QUIC-RECOVERY] reports that `pkt` was declared lost (§13.3, line 5333).
      *Why* it was declared lost is RFC 9002's business, not this model's. -/
  | lost (pkt : PktId)
  /-- §13.3, line 5355: "all stream data is acknowledged by the peer". -/
  | sendPartDataAcked (id : StreamId)
  /-- §13.3, lines 5362 and 5393: the receiving part changed phase. -/
  | recvPartPhase (id : StreamId) (phase : RecvPhase)
  /-- §13.3, line 5340: "Data in CRYPTO frames for Initial and Handshake packets
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
  /-- §13.3, line 5335: "sending ceases when a packet containing that
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
  -- line 5340 "discarded when keys for the corresponding packet number space
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

/-- §13.3, line 5340: CRYPTO data of a discarded packet number space. -/
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

/-- §13.3, line 5335: "sending ceases when a packet containing that information
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
    acknowledged in the verbatim sense of line 5335. -/
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

/-- §13.3, line 5340: CRYPTO data of a discarded packet number space is gone. -/
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
  /-- §13.3, line 5335: "sending ceases when a packet containing that
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
  /-- §13.3, line 5340: "Data in CRYPTO frames for Initial and Handshake packets
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

/-- §13.3, line 5335: the obligation is discharged by an acknowledgment. -/
def Discharged (s : State) (i : Info) : Prop := i ∈ s.ackedInfo

def discharged (s : State) (i : Info) : Bool := has s.ackedInfo i

theorem discharged_iff (s : State) (i : Info) : discharged s i = true ↔ Discharged s i := by
  simp [discharged, Discharged]

instance (s : State) (i : Info) : Decidable (Discharged s i) :=
  decidable_of_iff _ (discharged_iff s i)

/-- …or by the text's own alternative endings: the keys were discarded
    (line 5340), a RESET_STREAM superseded the STREAM data (line 5343), all
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

-- §13.3, line 5340: CRYPTO data for a discarded packet number space is gone.
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

/-! ## 11. Coverage and notes

Assigned range: lines 5325–5474 (§13.3).  §13.4 is `Spec/Ecn.lean`.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §13.3 (5327) | "QUIC packets that are determined to be lost are not retransmitted whole.  The same applies to the frames that are contained within lost packets." | `Event.lost` produces `Effect.repair` per *information item*, never a packet; there is no "resend packet" event at all |
| §13.3 (5332) | "New frames and packets are used to carry information that is determined to have been lost.  In general, information is sent again when a packet containing that information is determined to be lost and sending ceases when a packet containing that information is acknowledged." | `Step.lost` / `State.afterLost` / `State.newlyOwed`; `Step.acked` / `State.afterAcked` |
| §13.3 (5338) | "Data sent in CRYPTO frames is retransmitted according to the rules in [QUIC-RECOVERY], until all data has been acknowledged." | `State.repairable` (`.crypto`), `MustRetransmit`; the *rules* are RFC 9002, out of scope |
| §13.3 (5340) | "Data in CRYPTO frames for Initial and Handshake packets is discarded when keys for the corresponding packet number space are discarded." | `Step.keysDiscarded` / `State.afterKeysDiscarded`; the key schedule itself is WP11 |
| §13.3 (5343) | "Application data sent in STREAM frames is retransmitted in new STREAM frames unless the endpoint has sent a RESET_STREAM for that stream.  Once an endpoint sends a RESET_STREAM frame, no further STREAM frames are needed." | `State.repairable` (`.streamData`), `supersededByReset`; the *prohibition* on STREAM after RESET_STREAM is §3.1/§3.5 and belongs to `Spec/Stream/Send.lean` |
| §13.3 (5348) | "ACK frames carry the most recent set of acknowledgments and the acknowledgment delay from the largest acknowledged packet" | `State.repairable .ack = false`; the contents of an ACK frame are `Spec/Ack.lean` |
| §13.3 (5350) | "Delaying the transmission of packets containing ACK frames or resending old ACK frames can cause the peer to generate an inflated RTT sample or unnecessarily disable ECN." | informative, no normative keyword: the consequence of the previous sentence; `State.repairable .ack = false` is the behaviour it argues for |
| §13.3 (5355) | "Cancellation of stream transmission, as carried in a RESET_STREAM frame, is sent until acknowledged or until all stream data is acknowledged by the peer" | `State.repairable` (`.resetStream`), `Step.sendDataAcked`, `MustRetransmit` |
| §13.3 (5359) | "The content of a RESET_STREAM frame MUST NOT change when it is sent again." | `MaySend` / `State.resetContent` / `recordResets`; also `Stream.Send.maySendReset` (WP2 owns the phase-based form) |
| §13.3 (5362) | "Similarly, a request to cancel stream transmission, as encoded in a STOP_SENDING frame, is sent until the receiving part of the stream enters either a "Data Recvd" or "Reset Recvd" state" | `State.repairable` (`.stopSending`), `Step.recvPhase`, `MustRetransmit` |
| §13.3 (5367) | "Connection close signals, including packets that contain CONNECTION_CLOSE frames, are not sent again when packet loss is detected, but as described in Section 10." | `State.repairable .connectionClose = false`, `never_owed`; the §10 rules that *do* apply are `Spec/Termination/Send.lean` (`MaySendPacket` in the closing state) |
| §13.3 (5381) | "The current connection maximum data is sent in MAX_DATA frames.  An updated value is sent in a MAX_DATA frame if the packet containing the most recently sent MAX_DATA frame is declared lost, or when the endpoint decides to update the limit." | `Info.maxData` (value dropped: NOTE 2), `State.repairable`, `State.newlyOwed`'s `lastSent` test ("most recently sent") |
| §13.3 (5384) | "Care is necessary to avoid sending this frame too often as the limit can increase frequently" | advice, not checkable here: "too often" is a rate over a run, and the model has no send schedule |
| §13.3 (5389) | "The current maximum stream data offset is sent in MAX_STREAM_DATA frames.  Like MAX_DATA, an updated value is sent when the packet containing the most recent MAX_STREAM_DATA frame for a stream is lost or when the limit is updated" | `Info.maxStreamData`, `State.repairable`, `lastSent` |
| §13.3 (5393) | "An endpoint SHOULD stop sending MAX_STREAM_DATA frames when the receiving part of the stream enters a "Size Known" or "Reset Recvd" state." | `Recommended.maxStreamDataStopped`; also `Stream.Recv.RecommendedSend` |
| §13.3 (5397) | "The limit on streams of a given type is sent in MAX_STREAMS frames.  Like MAX_DATA, an updated value is sent when a packet containing the most recent MAX_STREAMS for a stream type frame is declared lost" | `Info.maxStreams`, `State.repairable`, `lastSent` |
| §13.3 (5403) | "Blocked signals are carried in DATA_BLOCKED, STREAM_DATA_BLOCKED, and STREAMS_BLOCKED frames.  DATA_BLOCKED frames have connection scope, STREAM_DATA_BLOCKED frames have stream scope, and STREAMS_BLOCKED frames are scoped to a specific stream type." | `BlockedScope`, `Info.blockedScope` |
| §13.3 (5406) | "New frames are sent if packets containing the most recent frame for a scope is lost, but only while the endpoint is blocked on the corresponding limit." | `State.repairable` (blocked cases), `Step.blockedChanged`, `Recommended.blockedOnlyWhileBlocked` (NOTE 5) |
| §13.3 (5409) | "These frames always include the limit that is causing blocking at the time that they are transmitted." | `Spec/StreamTable.lean` `MaySend` (WP9 owns it); not repeated here |
| §13.3 (5412) | "A liveness or path validation check using PATH_CHALLENGE frames is sent periodically until a matching PATH_RESPONSE frame is received … PATH_CHALLENGE frames include a different payload each time they are sent." | `State.repairable .pathChallenge = false`, `never_owed`; the periodic retry is `Spec/PathValidation.lean` (§8.2.1) |
| §13.3 (5418) | "Responses to path validation using PATH_RESPONSE frames are sent just once." | `State.repairable .pathResponse = false`, `never_owed`; the MUST NOT form is §8.2.2 line 3205 in `Spec/PathValidation.lean` |
| §13.3 (5422) | "New connection IDs are sent in NEW_CONNECTION_ID frames and retransmitted if the packet containing them is lost.  Retransmissions of this frame carry the same sequence number value." | `Info.newConnectionId seq` (the sequence number *is* the identity), `State.repairable = true`; `Spec/ConnIds/Local.lean` owns that the sequence number determines the frame |
| §13.3 (5425) | "Likewise, retired connection IDs are sent in RETIRE_CONNECTION_ID frames and retransmitted if the packet containing them is lost." | `Info.retireConnectionId seq`, `State.repairable = true`; `Spec/ConnIds/Remote.lean` |
| §13.3 (5437) | "NEW_TOKEN frames are retransmitted if the packet containing them is lost.  No special support is made for detecting reordered and duplicated NEW_TOKEN frames other than a direct comparison of the frame contents." | `Info.newToken token`, `State.repairable = true` |
| §13.3 (5442) | "PING and PADDING frames contain no information, so lost PING or PADDING frames do not require repair." | `State.repairable .ping = .padding = false`, `never_owed` |
| §13.3 (5445) | "The HANDSHAKE_DONE frame MUST be retransmitted until it is acknowledged." | `State.repairable .handshakeDone = true`, `MustRetransmit`, `Owes` / `owes`, `RepairObligationMet` (NOTE 4) |
| §13.3 (5448) | "Endpoints SHOULD prioritize retransmission of data over sending new data, unless priorities specified by the application indicate otherwise" | advice, not checkable here: it orders two sends against each other, and this model has no send queue and no application priorities (§2.3 is out of scope) |
| §13.3 (5452) | "Even though a sender is encouraged to assemble frames containing up-to-date information every time it sends a packet, it is not forbidden to retransmit copies of frames from lost packets." | permission: `MaySend` never rejects a repeat (`maySend_resent`, `maySend_of_not_reset`) |
| §13.3 (5454) | "A sender that retransmits copies of frames needs to handle decreases in available payload size due to change in packet number length, connection ID length, and path MTU." | advice, no normative keyword: packet sizing is `Spec/DatagramSize.lean` (WP7) |
| §13.3 (5457) | "A receiver MUST accept packets containing an outdated frame, such as a MAX_DATA frame carrying a smaller maximum data than one found in an older packet." | send half: `maySend_outdated`.  Receive half is a MUST on *every other* component, discharged there: `Template.Step.maxStreamsStale`, `StreamTable` and `Stream.Recv` ignore stale limits rather than erroring, `ConnIds` accepts a repeated NEW_CONNECTION_ID (NOTE 6) |
| §13.3 (5461) | "A sender SHOULD avoid retransmitting information from packets once they are acknowledged.  This includes packets that are acknowledged after being declared lost" | `Recommended.notAlreadyAcked`, and `State.newlyOwed`'s `ackedInfo` test (NOTE 3) |
| §13.3 (5465) | "A sender can discard this information after a period of time elapses that adequately allows for reordering, such as a PTO …, or on other events, such as reaching a memory limit." | permission: `Event.discardHistory` / `Step.discardHistory`; *when* to do it is left free |
| §13.3 (5471) | "Upon detecting losses, a sender MUST take appropriate congestion control action.  The details of loss detection and congestion control are described in [QUIC-RECOVERY]." | `Effect.congestionControlAction`, emitted by `Step.lost` for every packet that was in flight; the action itself is RFC 9002, out of scope by assignment |

NOTES

1. **What "the packet was declared lost" means.**  Nothing in this component
   decides that a packet is lost; `Event.lost` is the report from RFC 9002's
   loss detection, and `Event.acked` the report from its acknowledgment
   processing.  `Step` is therefore total in the event: a `lost` or `acked` for a
   packet that is not in flight (already acknowledged, already declared lost, or
   never sent through this component) changes nothing and produces no effects.
   That is deliberate — line 5461 explicitly contemplates a packet being
   acknowledged *after* being declared lost, and this model must not treat the
   second report as an error.

2. **Value-carrying information drops its value.**  §13.3 distinguishes two
   kinds of bullet.  "Data sent in CRYPTO frames is retransmitted" (5338) and
   "Retransmissions of this frame carry the same sequence number value" (5424)
   are about a fixed piece of content.  "The current connection maximum data is
   sent in MAX_DATA frames.  An updated value is sent …" (5381) is about a scope
   whose current value is re-read at transmission time.  `Info` reflects exactly
   that: `Info.maxData`, `Info.maxStreamData id`, `Info.maxStreams dir` and the
   three blocked constructors carry no value, so re-sending MAX_DATA with a
   *different* value clears the same debt, which is what the text describes.
   The cost is that this component cannot see that a MAX_DATA with a new value
   is "new information" for the purposes of line 5335; see NOTE 3.

3. **"Once they are acknowledged" applies only to verbatim information.**  Read
   literally over `Info`, line 5461 would say that once *any* MAX_DATA has been
   acknowledged no MAX_DATA should ever be sent again, which is absurd — the
   next one carries a new limit.  `Info.isVerbatim` marks the constructors whose
   identity is their content, and both `State.newlyOwed` and
   `Recommended.notAlreadyAcked` are restricted to those.  The `lastSent` test
   does the corresponding work for the value-carrying constructors: only the
   most recent carrier of a scope creates a debt (lines 5381, 5389, 5397, 5406
   all say "the most recent"), so an older packet being declared lost after a
   newer one went out owes nothing.

4. **`owed` is bookkeeping; `MustRetransmit` is the obligation.**  Only four
   bullets of §13.3 say information is sent *until* something happens: CRYPTO
   (5338), RESET_STREAM (5355), STOP_SENDING (5362) and HANDSHAKE_DONE (5445,
   the section's only MUST about retransmission).  `RepairObligationMet` is
   stated for exactly those.  The other bullets say an updated value "is sent",
   which this model records so that `Effect.repair` is observable and so that
   `MaySend`-level components can see the debt, but which it does not turn into
   a liveness requirement — an endpoint that never re-sends a lost MAX_DATA
   loses throughput, not conformance.  Like `Ack.ackOverdue` this predicate
   binds nothing until WP12 supplies the run.

5. **"Only while blocked" is not a `MaySend` rule.**  Line 5406's clause
   restricts the *repair* of a blocked signal, not the sending of blocked frames
   in general: §19.12–§19.14 nowhere forbid a DATA_BLOCKED frame, and `MaySend`
   must never be stricter than the text (BRIEF).  It is therefore encoded twice
   in the places where it is exactly right — in `State.repairable`, which is
   about repair, and in `Recommended.blockedOnlyWhileBlocked`, which rejects
   nothing.  `Spec/StreamTable.lean` separately pins the *value* such a frame
   carries (line 5409).

6. **Line 5457 binds every other component, not this one.**  "A receiver MUST
   accept packets containing an outdated frame" is a prohibition on treating a
   stale frame as an error.  It is discharged wherever a stale frame is
   processed — `Template.Step.maxStreamsStale` ("MUST be ignored" as `.ok s []`,
   never `.error`), `StreamTable`, `Stream.Recv`, `ConnIds` — and this component
   only has to not make it false, which `maySend_outdated` records.  A reviewer
   checking line 5457 should read those `Step` relations, not this file.

7. **DATAGRAM frames are outside the assigned text.**  RFC 9221 postdates
   draft-34, so §13.3's list has no bullet for DATAGRAM.  `Info.datagramFrame`
   is classified as not repaired, following RFC 9221 §5 ("DATAGRAM frames …
   are not retransmitted upon loss detection"), and is flagged here rather than
   silently folded into one of §13.3's categories.

8. **One instance per connection, packets keyed by space.**  Unlike `Ack`, this
   component is not replicated per packet number space: §13.3's information is
   mostly connection-scoped (a stream's data, a connection ID, a token) and only
   CRYPTO data is per space.  Packets are therefore identified by a `PktId`
   carrying both the space and the number, and `Info.crypto` carries the space
   so that line 5340 can discard exactly the right data.

9. **`MaySendPacket` is the default.**  §13.3 has no rule about a packet as a
   whole: the one sentence that is about packets (line 5367, connection close)
   defers to §10, which `Spec/Termination/Send.lean` encodes as a
   `MaySendPacket`.  Adding a second, weaker copy here would only risk
   disagreeing with it.
-/

end Quic.Spec.Retransmission
