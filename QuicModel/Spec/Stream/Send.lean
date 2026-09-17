import QuicModel.Spec.Core

/-
  WP2 Stream, part 1 of 3: the *sending* part of one stream, as seen by one
  endpoint (§3.1, §3.3, §3.5, and the stream-level half of §4.1, §4.4, §4.5).

  Follows the ten-part order of `Spec/Template.lean`.

  Scope: one stream, one direction.  Creating streams, stream counts and
  connection-level flow control are WP9; retransmission scheduling is §13.3.
-/
namespace Quic.Spec.Stream.Send

/-! ## 1. State, events, effects -/

/-- §3.1, line 900 (Figure 2): the six states of a sending part. -/
inductive Phase where
  | ready | send | dataSent | dataRecvd | resetSent | resetRecvd
  deriving DecidableEq, Repr

namespace Phase

/-- §3.1, lines 949, 973: "Data Recvd" and "Reset Recvd" are terminal. -/
def terminal : Phase → Bool
  | .dataRecvd | .resetRecvd => true
  | _ => false

/-- §3.3, line 1114: "A sender MUST NOT send a STREAM or STREAM_DATA_BLOCKED
    frame for a stream in the 'Reset Sent' state or any terminal state, that is,
    after sending a RESET_STREAM frame."  RESET_STREAM itself may still be
    retransmitted from "Reset Sent" (that state is not terminal), so this
    predicate is only about the two data-carrying frame types. -/
def mayCarryData : Phase → Bool
  | .ready | .send | .dataSent => true
  | _ => false

/-- The states before a FIN has been transmitted: "Ready" and "Send".  These are
    the states in which the application may still write (§2.4) and in which
    stream flow-control credit is still useful (§3.1, line 944: in "Data Sent"
    the endpoint "can safely ignore any MAX_STREAM_DATA frames"). -/
def beforeFin : Phase → Bool
  | .ready | .send => true
  | _ => false

def isDataSent : Phase → Bool
  | .dataSent => true
  | _ => false

def isResetSent : Phase → Bool
  | .resetSent => true
  | _ => false

/-- §3.1, line 927: "Sending the first STREAM or STREAM_DATA_BLOCKED frame
    causes a sending part of a stream to enter the 'Send' state." -/
def afterSend : Phase → Phase
  | .ready => .send
  | p => p

end Phase

/-- The sending part of one stream.  `id` and `role` are carried so that
    `MaySend` can tell frames for *this* stream from frames for another. -/
structure State where
  /-- §2.1 the stream this is a part of. -/
  id : StreamId
  /-- Which endpoint we are. -/
  role : Role
  phase : Phase
  /-- §4.1: the peer's stream flow-control limit — the maximum absolute byte
      offset we may send on this stream.  Starts at the peer's
      `initial_max_stream_data_*` transport parameter, raised by
      MAX_STREAM_DATA. -/
  maxData : Nat
  /-- §2.4: one past the offset of the last byte the application has written. -/
  written : Nat
  /-- §2.4: the application has ended the stream, so `written` is its size. -/
  finWritten : Bool
  /-- §4.5, line 1479: "one higher than the offset of the byte with the largest
      offset sent on the stream, or zero if no bytes were sent." -/
  sent : Nat
  /-- §4.5: the final size, once a FIN or a RESET_STREAM has been *sent*. -/
  finalSize : Option Nat
  /-- §3.5: the application error code of a reset that the application asked for
      or that a STOP_SENDING frame solicited, and of the reset once sent. -/
  resetCode : Option Nat
  deriving DecidableEq, Repr

/-- A freshly created sending part: §3.1, line 920 "The 'Ready' state represents
    a newly created stream that is able to accept data from the application."
    `initialMax` is the peer's `initial_max_stream_data_*` for this stream. -/
def init (id : StreamId) (role : Role) (initialMax : Nat) : State :=
  { id, role, phase := .ready, maxData := initialMax, written := 0,
    finWritten := false, sent := 0, finalSize := none, resetCode := none }

inductive Event where
  /-- §2.4, line 811: the application writes `len` more bytes. -/
  | appWrite (len : Nat)
  /-- §2.4, line 815: the application ends the stream (clean termination). -/
  | appEnd
  /-- §2.4, line 818: the application resets the stream (abrupt termination). -/
  | appReset (code : Nat)
  /-- §19.10 MAX_STREAM_DATA received from the peer. -/
  | recvMaxStreamData (v : Nat)
  /-- §19.5 STOP_SENDING received from the peer. -/
  | recvStopSending (code : Nat)
  /-- We transmitted a STREAM frame with these offset/length/FIN. -/
  | sentStream (offset len : Nat) (fin : Bool)
  /-- We transmitted a STREAM_DATA_BLOCKED frame reporting this limit. -/
  | sentStreamDataBlocked (limit : Nat)
  /-- We transmitted a RESET_STREAM frame. -/
  | sentResetStream (code finalSize : Nat)
  /-- §3.1, line 947: "all stream data has been successfully acknowledged".
      Loss recovery is out of scope, so this is an abstract event. -/
  | ackAllData
  /-- §3.1, line 971: "a packet containing a RESET_STREAM has been
      acknowledged".  Abstract, as above. -/
  | ackReset
  deriving DecidableEq, Repr

/-- Events that are frames arriving from the peer (as opposed to local actions).
    Used by the composite in `Spec/Stream.lean`: a frame that arrives for a
    sending part that does not exist is a STREAM_STATE_ERROR, whereas a local
    action for a part that does not exist simply cannot happen. -/
def Event.isPeerFrame : Event → Bool
  | .recvMaxStreamData _ | .recvStopSending _ => true
  | _ => false

inductive Effect where
  /-- The application may now write up to this absolute offset (§4.1). -/
  | creditAvailable (max : Nat)
  /-- §3.5: the peer asked us to stop sending; a RESET_STREAM is now owed. -/
  | peerStopSending (code : Nat)
  /-- The application asked for the stream to be reset (§2.4). -/
  | resetRequested (code : Nat)
  /-- The stream's data is now completely acknowledged (§3.1 "Data Recvd"). -/
  | allDataAcked
  /-- The RESET_STREAM is acknowledged (§3.1 "Reset Recvd"). -/
  | resetAcked
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ### Guards

The conditions under which the endpoint is permitted to send each of the three
frame types of §3.3.  They are shared between `Step` (as hypotheses), `outcomes`
(as `if` conditions) and `MaySend`, so that the state machine and the send-side
predicate cannot drift apart; `step_ok_iff_maySend` below makes that precise. -/

/-- §2.4: the application can write only before it has ended or reset the
    stream, i.e. in "Ready" or "Send" with no FIN written yet. -/
def canWrite (s : State) : Bool := s.phase.beforeFin && !s.finWritten

/-- §3.3, line 1112: "A sender MUST NOT send any of these frames from a
    terminal state"; §3.3, line 1114: no STREAM after a RESET_STREAM.
    §4.1, line 1330: "Senders MUST NOT send data in excess of either limit."
    §4.5, line 1499: "An endpoint MUST NOT send data on a stream at or beyond
    the final size."  §4.5, line 1516: "Once a final size for a stream is known,
    it cannot change." -/
def maySendStream (s : State) (offset len : Nat) (fin : Bool) : Bool :=
  s.phase.mayCarryData
    && decide (offset + len ≤ s.written)
    && decide (offset + len ≤ s.maxData)
    && (!fin || (s.finWritten && decide (offset + len = s.written)))
    && (match s.finalSize with
        | none => true
        | some f => decide (offset + len ≤ f) && (!fin || decide (offset + len = f)))

/-- §3.3, line 1112/1114 as above; §19.13, line 7858 and §4.1, line 1372: the
    frame reports the stream-level limit at which the sender is blocked. -/
def maySendBlocked (s : State) (limit : Nat) : Bool :=
  s.phase.mayCarryData && decide (limit = s.maxData)

/-- §3.3, line 1112: not from a terminal state — "Reset Sent" is not terminal,
    so a RESET_STREAM may be repeated.  §4.5, line 1486: the Final Size field
    carries the final size, which §4.5, line 1516 says cannot change; before one
    is known it is the highest offset sent (§4.5, line 1479). -/
def maySendReset (s : State) (_code finalSize : Nat) : Bool :=
  !s.phase.terminal
    && (match s.finalSize with
        | none => decide (finalSize = s.sent)
        | some f => decide (finalSize = f))

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §2.4, line 811: "write data". -/
  | write {s len} (h : canWrite s = true) :
      Step s (.appWrite len) (.ok { s with written := s.written + len } [])
  /-- Writing after the stream has been ended or reset is not something the
      transport can do; the request has no effect. -/
  | writeRefused {s len} (h : canWrite s = false) :
      Step s (.appWrite len) .drop
  /-- §2.4, line 815: "end the stream (clean termination)". -/
  | endStream {s} (h : canWrite s = true) :
      Step s .appEnd (.ok { s with finWritten := true } [])
  | endRefused {s} (h : canWrite s = false) :
      Step s .appEnd .drop
  /-- §3.1, line 962: "From any of the 'Ready', 'Send', or 'Data Sent' states,
      an application can signal that it wishes to abandon transmission of stream
      data ... the endpoint sends a RESET_STREAM frame". -/
  | reset {s code} (h : s.phase.mayCarryData = true) :
      Step s (.appReset code) (.ok { s with resetCode := some code } [.resetRequested code])
  /-- §2.4, line 818: a RESET_STREAM results "if the stream was not already in a
      terminal state"; from "Reset Sent" one is already on its way. -/
  | resetRefused {s code} (h : s.phase.mayCarryData = false) :
      Step s (.appReset code) .drop
  /-- §4.1, line 1361: "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA
      frames that do not increase flow control limits"; §3.1, line 944: in
      "Data Sent" and later "the endpoint can safely ignore any MAX_STREAM_DATA
      frames it receives from its peer for a stream in this state". -/
  | maxStreamDataIgnored {s v} (h : (s.phase.beforeFin && decide (s.maxData < v)) = false) :
      Step s (.recvMaxStreamData v) (.ok s [])
  /-- §4.1, line 1349: "A receiver can advertise a larger limit for a stream by
      sending a MAX_STREAM_DATA frame". -/
  | maxStreamDataRaise {s v} (h : (s.phase.beforeFin && decide (s.maxData < v)) = true) :
      Step s (.recvMaxStreamData v) (.ok { s with maxData := v } [.creditAvailable v])
  /-- §3.5, line 1258: "An endpoint that receives a STOP_SENDING frame MUST send
      a RESET_STREAM frame if the stream is in the Ready or Send state.  If the
      stream is in the 'Data Sent' state, the endpoint MAY defer sending the
      RESET_STREAM frame".  The obligation is recorded in `resetCode`; the
      frame itself leaves by `sentResetStream`. -/
  | stopSending {s code} (h : s.phase.mayCarryData = true) :
      Step s (.recvStopSending code) (.ok { s with resetCode := some code } [.peerStopSending code])
  /-- §3.3, line 1118: "A sender could receive either of these two frames in any
      state as a result of delayed delivery of packets."  In "Reset Sent" and
      the terminal states no reset is owed, so the frame has no effect. -/
  | stopSendingLate {s code} (h : s.phase.mayCarryData = false) :
      Step s (.recvStopSending code) (.ok s [])
  /-- §3.1, line 927: the first STREAM frame moves "Ready" to "Send";
      §3.1, line 938: "After the application indicates that all stream data has
      been sent and a STREAM frame containing the FIN bit is sent, the sending
      part of the stream enters the 'Data Sent' state." -/
  | sendStream {s offset len fin} (h : maySendStream s offset len fin = true) :
      Step s (.sentStream offset len fin)
        (.ok { s with
                phase := if fin then .dataSent else s.phase.afterSend
                sent := max s.sent (offset + len)
                finalSize := if fin then some (offset + len) else s.finalSize } [])
  /-- A frame the rules of §3.3/§4.1/§4.5 forbid is not sent, so nothing
      happens. -/
  | sendStreamForbidden {s offset len fin} (h : maySendStream s offset len fin = false) :
      Step s (.sentStream offset len fin) .drop
  /-- §3.1, line 927: STREAM_DATA_BLOCKED also moves "Ready" to "Send";
      §3.1, line 934: "An endpoint in the 'Send' state generates
      STREAM_DATA_BLOCKED frames if it is blocked from sending by stream flow
      control limits." -/
  | sendBlocked {s limit} (h : maySendBlocked s limit = true) :
      Step s (.sentStreamDataBlocked limit) (.ok { s with phase := s.phase.afterSend } [])
  | sendBlockedForbidden {s limit} (h : maySendBlocked s limit = false) :
      Step s (.sentStreamDataBlocked limit) .drop
  /-- §3.1, line 966: "the endpoint sends a RESET_STREAM frame, which causes the
      stream to enter the 'Reset Sent' state"; §3.1, line 968: "An endpoint MAY
      send a RESET_STREAM as the first frame that mentions a stream; this causes
      the sending part of that stream to open and then immediately transition to
      the 'Reset Sent' state." -/
  | sendReset {s code fs} (h : maySendReset s code fs = true) :
      Step s (.sentResetStream code fs)
        (.ok { s with phase := .resetSent, finalSize := some fs, resetCode := some code } [])
  | sendResetForbidden {s code fs} (h : maySendReset s code fs = false) :
      Step s (.sentResetStream code fs) .drop
  /-- §3.1, line 947: "Once all stream data has been successfully acknowledged,
      the sending part of the stream enters the 'Data Recvd' state". -/
  | allAcked {s} (h : s.phase.isDataSent = true) :
      Step s .ackAllData (.ok { s with phase := .dataRecvd } [.allDataAcked])
  /-- Outside "Data Sent" there is no such acknowledgement to receive. -/
  | allAckedNo {s} (h : s.phase.isDataSent = false) :
      Step s .ackAllData .drop
  /-- §3.1, line 971: "Once a packet containing a RESET_STREAM has been
      acknowledged, the sending part of the stream enters the 'Reset Recvd'
      state". -/
  | resetAcked {s} (h : s.phase.isResetSent = true) :
      Step s .ackReset (.ok { s with phase := .resetRecvd } [.resetAcked])
  | resetAckedNo {s} (h : s.phase.isResetSent = false) :
      Step s .ackReset .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .appWrite len =>
      if canWrite s then [.ok { s with written := s.written + len } []] else [.drop]
  | .appEnd =>
      if canWrite s then [.ok { s with finWritten := true } []] else [.drop]
  | .appReset code =>
      if s.phase.mayCarryData then
        [.ok { s with resetCode := some code } [.resetRequested code]]
      else [.drop]
  | .recvMaxStreamData v =>
      if s.phase.beforeFin && decide (s.maxData < v) then
        [.ok { s with maxData := v } [.creditAvailable v]]
      else [.ok s []]
  | .recvStopSending code =>
      if s.phase.mayCarryData then
        [.ok { s with resetCode := some code } [.peerStopSending code]]
      else [.ok s []]
  | .sentStream offset len fin =>
      if maySendStream s offset len fin then
        [.ok { s with
                phase := if fin then .dataSent else s.phase.afterSend
                sent := max s.sent (offset + len)
                finalSize := if fin then some (offset + len) else s.finalSize } []]
      else [.drop]
  | .sentStreamDataBlocked limit =>
      if maySendBlocked s limit then [.ok { s with phase := s.phase.afterSend } []]
      else [.drop]
  | .sentResetStream code fs =>
      if maySendReset s code fs then
        [.ok { s with phase := .resetSent, finalSize := some fs, resetCode := some code } []]
      else [.drop]
  | .ackAllData =>
      if s.phase.isDataSent then [.ok { s with phase := .dataRecvd } [.allDataAcked]]
      else [.drop]
  | .ackReset =>
      if s.phase.isResetSent then [.ok { s with phase := .resetRecvd } [.resetAcked]]
      else [.drop]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | appWrite len =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .write ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .writeRefused (Bool.eq_false_iff.mpr ‹_›)
    | appEnd =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .endStream ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .endRefused (Bool.eq_false_iff.mpr ‹_›)
    | appReset code =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .reset ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .resetRefused (Bool.eq_false_iff.mpr ‹_›)
    | recvMaxStreamData v =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .maxStreamDataRaise ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .maxStreamDataIgnored (Bool.eq_false_iff.mpr ‹_›)
    | recvStopSending code =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .stopSending ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .stopSendingLate (Bool.eq_false_iff.mpr ‹_›)
    | sentStream offset len fin =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .sendStream ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .sendStreamForbidden (Bool.eq_false_iff.mpr ‹_›)
    | sentStreamDataBlocked limit =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .sendBlocked ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .sendBlockedForbidden (Bool.eq_false_iff.mpr ‹_›)
    | sentResetStream code fs =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .sendReset ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .sendResetForbidden (Bool.eq_false_iff.mpr ‹_›)
    | ackAllData =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .allAcked ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .allAckedNo (Bool.eq_false_iff.mpr ‹_›)
    | ackReset =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .resetAcked ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .resetAckedNo (Bool.eq_false_iff.mpr ‹_›)
  · intro h
    cases h with
    | write h => simp [outcomes, h]
    | writeRefused h => simp [outcomes, h]
    | endStream h => simp [outcomes, h]
    | endRefused h => simp [outcomes, h]
    | reset h => simp [outcomes, h]
    | resetRefused h => simp [outcomes, h]
    | maxStreamDataIgnored h => simp [outcomes, h]
    | maxStreamDataRaise h => simp [outcomes, h]
    | stopSending h => simp [outcomes, h]
    | stopSendingLate h => simp [outcomes, h]
    | sendStream h => simp [outcomes, h]
    | sendStreamForbidden h => simp [outcomes, h]
    | sendBlocked h => simp [outcomes, h]
    | sendBlockedForbidden h => simp [outcomes, h]
    | sendReset h => simp [outcomes, h]
    | sendResetForbidden h => simp [outcomes, h]
    | allAcked h => simp [outcomes, h]
    | allAckedNo h => simp [outcomes, h]
    | resetAcked h => simp [outcomes, h]
    | resetAckedNo h => simp [outcomes, h]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- What every reachable sending part satisfies:
    * only written data is ever sent, and never beyond the peer's credit
      (§4.1, line 1330);
    * a known final size *is* the highest offset sent (§4.5, line 1479);
    * outside "Ready"/"Send" a final size is known — this is the sending-side
      counterpart of §4.5, line 1493: a sender always communicates the final
      size, by a FIN or by RESET_STREAM. -/
def Inv (s : State) : Prop :=
  s.sent ≤ s.written ∧ s.sent ≤ s.maxData ∧
  (∀ f, s.finalSize = some f → f = s.sent) ∧
  (s.phase.beforeFin = false → s.finalSize.isSome)

theorem init_inv (id : StreamId) (role : Role) (m : Nat) : Inv (init id role m) := by
  refine ⟨Nat.le_refl _, Nat.zero_le _, ?_, ?_⟩ <;> simp [init, Phase.beforeFin]

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  cases h with
  | write hc =>
    exact ⟨by simpa using Nat.le_trans h1 (Nat.le_add_right _ _), h2, h3, h4⟩
  | endStream hc =>
    refine ⟨h1, h2, h3, ?_⟩
    intro hb
    simp only [canWrite, Bool.and_eq_true] at hc
    simp only at hb
    rw [hc.1] at hb; exact absurd hb (by simp)
  | reset => exact ⟨h1, h2, h3, h4⟩
  | maxStreamDataIgnored => exact ⟨h1, h2, h3, h4⟩
  | maxStreamDataRaise hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨h1, by simp only; omega, h3, h4⟩
  | stopSending => exact ⟨h1, h2, h3, h4⟩
  | stopSendingLate => exact ⟨h1, h2, h3, h4⟩
  | @sendStream offset len fin hc =>
    simp only [maySendStream, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨-, hw⟩, hm⟩, hfin⟩, hfs⟩ := hc
    have hle : ∀ f, s.finalSize = some f → offset + len ≤ f := by
      intro f hf
      rw [hf] at hfs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfs
      exact hfs.1
    refine ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩
    · intro f hf
      simp only at hf ⊢
      cases fin with
      | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hfin
        simp at hf
        omega
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hf
        have h5 := h3 f hf
        have h6 := hle f hf
        omega
    · intro hb
      simp only at hb ⊢
      cases fin with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hb ⊢
        refine h4 ?_
        cases hp : s.phase <;> rw [hp] at hb <;> simp_all [Phase.afterSend, Phase.beforeFin]
  | sendBlocked hc =>
    refine ⟨h1, h2, h3, ?_⟩
    intro hb
    simp only [maySendBlocked, Bool.and_eq_true] at hc
    exact h4 (by
      cases hp : s.phase <;> simp only [Phase.afterSend, hp] at hb ⊢ <;> simp_all [Phase.beforeFin])
  | @sendReset code fs hc =>
    simp only [maySendReset, Bool.and_eq_true] at hc
    refine ⟨h1, h2, ?_, by simp⟩
    intro f hf
    simp only [Option.some.injEq] at hf
    subst hf
    obtain ⟨-, hfs⟩ := hc
    revert hfs
    cases hfin : s.finalSize with
    | none => simp
    | some f0 => simp only [decide_eq_true_eq]; intro hff; subst hff; exact h3 _ hfin
  | allAcked hc =>
    refine ⟨h1, h2, h3, fun _ => h4 ?_⟩
    cases hp : s.phase <;> simp_all [Phase.isDataSent, Phase.beforeFin]
  | resetAcked hc =>
    refine ⟨h1, h2, h3, fun _ => h4 ?_⟩
    cases hp : s.phase <;> simp_all [Phase.isResetSent, Phase.beforeFin]

/-! ## 6. Send side

§3.3, lines 1105–1116: the sending part governs exactly STREAM,
STREAM_DATA_BLOCKED and RESET_STREAM.  Frames for another stream, and frames of
any other type, are not this component's business. -/

def MaySend (s : State) : Frame → Prop
  | .stream id offset fin data =>
      if id = s.id.val then maySendStream s offset data.size fin = true else True
  | .streamDataBlocked id v => if id = s.id.val then maySendBlocked s v = true else True
  | .resetStream id code fs => if id = s.id.val then maySendReset s code fs = true else True
  | _ => True

def maySend (s : State) : Frame → Bool
  | .stream id offset fin data =>
      if id = s.id.val then maySendStream s offset data.size fin else true
  | .streamDataBlocked id v => if id = s.id.val then maySendBlocked s v else true
  | .resetStream id code fs => if id = s.id.val then maySendReset s code fs else true
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp only [maySend, MaySend] <;> repeat' split
  all_goals simp

/-! ## 7. The component -/

def component : Component where
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

/-! ## 8. Named theorems -/

/-- **(a) The final size is immutable.**  §4.5, line 1516: "Once a final size
    for a stream is known, it cannot change."  No permitted step changes a final
    size that the sending part has already fixed. -/
theorem finalSize_immutable {s s' : State} {e : Event} {fx : List Effect} {f : Nat}
    (h : Step s e (.ok s' fx)) (hf : s.finalSize = some f) : s'.finalSize = some f := by
  cases h with
  | @sendStream offset len fin hc =>
    simp only [maySendStream, Bool.and_eq_true] at hc
    obtain ⟨-, hfs⟩ := hc
    rw [hf] at hfs
    simp only at hfs ⊢
    cases fin with
    | false => simpa using hf
    | true =>
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hfs
      simp [hfs.2]
  | @sendReset code fs hc =>
    simp only [maySendReset, Bool.and_eq_true] at hc
    obtain ⟨-, hfs⟩ := hc
    rw [hf] at hfs
    simp only [decide_eq_true_eq] at hfs
    simp only
    simp [hfs]
  | write => exact hf
  | endStream => exact hf
  | reset => exact hf
  | maxStreamDataIgnored => exact hf
  | maxStreamDataRaise => exact hf
  | stopSending => exact hf
  | stopSendingLate => exact hf
  | sendBlocked => exact hf
  | allAcked => exact hf
  | resetAcked => exact hf

/-- Once a final size is known, no more data may be sent at or beyond it
    (§4.5, line 1499). -/
theorem no_data_beyond_finalSize {s : State} {offset len : Nat} {fin : Bool} {f : Nat}
    (hf : s.finalSize = some f) (h : maySendStream s offset len fin = true) :
    offset + len ≤ f := by
  simp only [maySendStream, Bool.and_eq_true] at h
  obtain ⟨-, hfs⟩ := h
  rw [hf] at hfs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfs
  exact hfs.1

/-- **(c) The terminal states absorb.**  §3.1, lines 949 and 973: "Data Recvd"
    and "Reset Recvd" are terminal.  Nothing at all changes there. -/
theorem terminal_absorbing {s s' : State} {e : Event} {fx : List Effect}
    (ht : s.phase.terminal = true) (h : Step s e (.ok s' fx)) : s' = s := by
  have hb : s.phase.beforeFin = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.beforeFin]
  have hc : s.phase.mayCarryData = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.mayCarryData]
  cases h with
  | write hw => simp_all [canWrite]
  | endStream hw => simp_all [canWrite]
  | reset hw => rw [hc] at hw; exact absurd hw (by simp)
  | maxStreamDataIgnored => rfl
  | maxStreamDataRaise hw => rw [hb] at hw; simp at hw
  | stopSending hw => rw [hc] at hw; exact absurd hw (by simp)
  | stopSendingLate => rfl
  | sendStream hw => rw [maySendStream, hc] at hw; simp at hw
  | sendBlocked hw => rw [maySendBlocked, hc] at hw; simp at hw
  | sendReset hw => rw [maySendReset, ht] at hw; simp at hw
  | allAcked hw =>
    have : s.phase.isDataSent = false := by
      cases hp : s.phase <;> simp_all [Phase.terminal, Phase.isDataSent]
    rw [this] at hw; exact absurd hw (by simp)
  | resetAcked hw =>
    have : s.phase.isResetSent = false := by
      cases hp : s.phase <;> simp_all [Phase.terminal, Phase.isResetSent]
    rw [this] at hw; exact absurd hw (by simp)

/-- The arrows of Figure 2 (§3.1, line 900), as a relation on phases. -/
def Arrow : Phase → Phase → Prop
  | .ready, .send => True        -- Send STREAM / STREAM_DATA_BLOCKED
  | .ready, .resetSent => True   -- Send RESET_STREAM
  | .send, .dataSent => True     -- Send STREAM + FIN
  | .send, .resetSent => True    -- Send RESET_STREAM
  | .dataSent, .dataRecvd => True -- Recv All ACKs
  | .dataSent, .resetSent => True -- Send RESET_STREAM
  | .resetSent, .resetRecvd => True -- Recv ACK
  | _, _ => False

/-- Reachability along the arrows of Figure 2, in zero or more steps.  §3, line
    892: "a single event or action can cause a transition through multiple
    states", so a step may follow several arrows at once (Ready → Data Sent when
    a STREAM frame with FIN is the first frame sent). -/
def Reaches : Phase → Phase → Bool
  | .ready, _ => true
  | .send, .ready => false
  | .send, _ => true
  | .dataSent, p => match p with
      | .dataSent | .dataRecvd | .resetSent | .resetRecvd => true
      | _ => false
  | .dataRecvd, .dataRecvd => true
  | .dataRecvd, _ => false
  | .resetSent, p => match p with
      | .resetSent | .resetRecvd => true
      | _ => false
  | .resetRecvd, .resetRecvd => true
  | .resetRecvd, _ => false

theorem arrow_reaches {p q : Phase} (h : Arrow p q) : Reaches p q = true := by
  cases p <;> cases q <;> simp_all [Arrow, Reaches]

/-- **(d, second half) No step leaves the diagram.**  Every permitted step moves
    the phase along a path of Figure 2's arrows. -/
theorem step_follows_diagram {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : Reaches s.phase s'.phase = true := by
  cases h with
  | write => cases hp : s.phase <;> simp [Reaches]
  | endStream => cases hp : s.phase <;> simp [Reaches]
  | reset => cases hp : s.phase <;> simp [Reaches]
  | maxStreamDataIgnored => cases hp : s.phase <;> simp [Reaches]
  | maxStreamDataRaise => cases hp : s.phase <;> simp [Reaches]
  | stopSending => cases hp : s.phase <;> simp [Reaches]
  | stopSendingLate => cases hp : s.phase <;> simp [Reaches]
  | @sendStream offset len fin hw =>
    simp only [maySendStream, Bool.and_eq_true] at hw
    have hc : s.phase.mayCarryData = true := hw.1.1.1.1
    cases fin <;> cases hp : s.phase <;>
      simp_all [Phase.mayCarryData, Phase.afterSend, Reaches]
  | @sendBlocked limit hw =>
    simp only [maySendBlocked, Bool.and_eq_true] at hw
    have hc : s.phase.mayCarryData = true := hw.1
    cases hp : s.phase <;> simp_all [Phase.mayCarryData, Phase.afterSend, Reaches]
  | @sendReset code fs hw =>
    simp only [maySendReset, Bool.and_eq_true] at hw
    have hc : s.phase.terminal = false := by simpa using hw.1
    cases hp : s.phase <;> simp_all [Phase.terminal, Reaches]
  | @allAcked hw =>
    have : s.phase = .dataSent := by cases hp : s.phase <;> simp_all [Phase.isDataSent]
    simp [this, Reaches]
  | @resetAcked hw =>
    have : s.phase = .resetSent := by cases hp : s.phase <;> simp_all [Phase.isResetSent]
    simp [this, Reaches]

/-- `Step` and `MaySend` agree: a transmission event changes the state exactly
    when the frame it reports was one the endpoint was permitted to send. -/
theorem sendStream_ok_iff_maySend {s : State} {offset len : Nat} {fin : Bool} :
    (∃ s' fx, Step s (.sentStream offset len fin) (.ok s' fx)) ↔
      maySendStream s offset len fin = true := by
  constructor
  · rintro ⟨s', fx, h⟩; cases h; assumption
  · intro h; exact ⟨_, _, .sendStream h⟩

theorem sendReset_ok_iff_maySend {s : State} {code fs : Nat} :
    (∃ s' fx, Step s (.sentResetStream code fs) (.ok s' fx)) ↔ maySendReset s code fs = true := by
  constructor
  · rintro ⟨s', fx, h⟩; cases h; assumption
  · intro h; exact ⟨_, _, .sendReset h⟩

/-- The peer's credit, as we track it, never goes down (§4.1, line 1357: "it is
    not an error to advertise a smaller limit, but the smaller limit has no
    effect"). -/
theorem maxData_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.maxData ≤ s'.maxData := by
  cases h with
  | maxStreamDataRaise hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact Nat.le_of_lt hc.2
  | _ => exact Nat.le_refl _

/-- `sent` never exceeds the peer's advertised credit — the sending half of
    §4.1, line 1330 ("Senders MUST NOT send data in excess of either limit"). -/
theorem sent_le_maxData {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    s.sent ≤ s.maxData :=
  (component.inv_of_reachable h0 h).2.1

/-! ## 9. Examples: every arrow of Figure 2 (§3.1) -/

private def s0 : State := init ⟨0⟩ .client 100

-- o → Ready: "Create Stream (Sending)".
example : s0.phase = .ready := rfl

-- Ready → Send: "Send STREAM".
example :
    component.step { s0 with written := 10 } (.sentStream 0 5 false) =
      .ok { s0 with written := 10, phase := .send, sent := 5 } [] := by decide

-- Ready → Send: "Send STREAM_DATA_BLOCKED" (blocked at the peer's limit).
example :
    component.step { s0 with maxData := 0 } (.sentStreamDataBlocked 0) =
      .ok { s0 with maxData := 0, phase := .send } [] := by decide

-- Ready → Reset Sent: "Send RESET_STREAM" as the first frame mentioning the
-- stream (§3.1, line 968).
example :
    component.step s0 (.sentResetStream 7 0) =
      .ok { s0 with phase := .resetSent, finalSize := some 0, resetCode := some 7 } [] := by
  decide

-- Send → Data Sent: "Send STREAM + FIN".
example :
    component.step { s0 with phase := .send, written := 5, finWritten := true, sent := 5 }
        (.sentStream 0 5 true) =
      .ok { s0 with phase := .dataSent, written := 5, finWritten := true, sent := 5,
                    finalSize := some 5 } [] := by
  decide

-- Send → Reset Sent: "Send RESET_STREAM"; the final size is the highest offset
-- sent so far (§4.5, line 1479).
example :
    component.step { s0 with phase := .send, written := 10, sent := 4 } (.sentResetStream 3 4) =
      .ok { s0 with phase := .resetSent, written := 10, sent := 4, finalSize := some 4,
                    resetCode := some 3 } [] := by
  decide

-- Data Sent → Reset Sent: "Send RESET_STREAM", repeating the final size the FIN
-- already fixed.
example :
    component.step { s0 with phase := .dataSent, written := 5, finWritten := true, sent := 5,
                             finalSize := some 5 } (.sentResetStream 3 5) =
      .ok { s0 with phase := .resetSent, written := 5, finWritten := true, sent := 5,
                    finalSize := some 5, resetCode := some 3 } [] := by
  decide

-- Data Sent → Data Recvd: "Recv All ACKs".
example :
    component.step { s0 with phase := .dataSent, finalSize := some 5 } .ackAllData =
      .ok { s0 with phase := .dataRecvd, finalSize := some 5 } [.allDataAcked] := by decide

-- Reset Sent → Reset Recvd: "Recv ACK".
example :
    component.step { s0 with phase := .resetSent, finalSize := some 0 } .ackReset =
      .ok { s0 with phase := .resetRecvd, finalSize := some 0 } [.resetAcked] := by decide

-- §3, line 892: one event, two transitions — Ready → Send → Data Sent.
example :
    component.step { s0 with written := 5, finWritten := true } (.sentStream 0 5 true) =
      .ok { s0 with phase := .dataSent, written := 5, finWritten := true, sent := 5,
                    finalSize := some 5 } [] := by
  decide

-- §3.5, line 1258: STOP_SENDING in "Send" obliges a RESET_STREAM …
example :
    component.step { s0 with phase := .send } (.recvStopSending 9) =
      .ok { s0 with phase := .send, resetCode := some 9 } [.peerStopSending 9] := by decide
-- … and the RESET_STREAM may then be sent, copying the error code.
example :
    component.maySend { s0 with phase := .send, resetCode := some 9 } (.resetStream 0 9 0) = true := by
  decide

-- §4.1, line 1330: no data beyond the peer's credit.
example : component.maySend { s0 with maxData := 4, written := 10 } (.stream 0 0 false ⟨#[1,2,3,4,5]⟩) = false := by
  decide
-- §4.1, line 1361: a MAX_STREAM_DATA that does not raise the limit is ignored.
example : component.step s0 (.recvMaxStreamData 100) = .ok s0 [] := by decide
example : component.step s0 (.recvMaxStreamData 200) =
    .ok { s0 with maxData := 200 } [.creditAvailable 200] := by decide
-- §3.1, line 944: in "Data Sent" MAX_STREAM_DATA is ignored outright.
example : component.step { s0 with phase := .dataSent, finalSize := some 0 } (.recvMaxStreamData 200) =
    .ok { s0 with phase := .dataSent, finalSize := some 0 } [] := by decide

-- §3.3, line 1112: nothing may be sent from a terminal state …
example : component.maySend { s0 with phase := .dataRecvd } (.resetStream 0 1 0) = false := by decide
example : component.maySend { s0 with phase := .resetRecvd } (.stream 0 0 false ⟨#[]⟩) = false := by decide
-- … and no STREAM or STREAM_DATA_BLOCKED after a RESET_STREAM …
example : component.maySend { s0 with phase := .resetSent, written := 9 } (.stream 0 0 false ⟨#[1]⟩) = false := by
  decide
example : component.maySend { s0 with phase := .resetSent } (.streamDataBlocked 0 100) = false := by decide
-- … while RESET_STREAM may be repeated from "Reset Sent": an exact repeat of
-- the frame just sent (same error code, same final size) is permitted, which is
-- what retransmitting a lost packet needs (§13.3 is otherwise out of scope).
private def sReset : State := (component.step s0 (.sentResetStream 7 0)).next s0
example : sReset.phase = .resetSent := by decide
example : component.maySend sReset (.resetStream 0 7 0) = true := by decide
-- A STREAM frame, by contrast, may never be retransmitted after the reset
-- (§3.3, line 1114).
example : component.maySend { sReset with written := 9 } (.stream 0 0 false ⟨#[1]⟩) = false := by
  decide
-- An exact repeat of a STREAM frame already sent is permitted while the sending
-- part still carries data — here a retransmission of the FIN in "Data Sent".
example :
    component.maySend { s0 with phase := .dataSent, written := 5, finWritten := true,
                                sent := 5, finalSize := some 5 }
      (.stream 0 0 true ⟨#[1, 2, 3, 4, 5]⟩) = true := by
  decide

-- A frame for a different stream is not this component's business.
example : component.maySend { s0 with phase := .resetRecvd } (.stream 4 0 false ⟨#[1]⟩) = true := by decide

-- Following an implementation whose state we cannot see.
example : component.track s0 (.recvMaxStreamData 200) (.ok [.creditAvailable 200]) =
    some { s0 with maxData := 200 } := by decide

/-! ## 10. Coverage and notes

Assigned text for this file: §2.4 (sending operations), §3.1, the sending half
of §3.3 and §3.5, and the stream-level parts of §4.1/§4.4/§4.5.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §2.4 (811) | application can write data | `Step.write` / `Step.writeRefused` |
| §2.4 (815) | end the stream → STREAM with FIN | `Step.endStream`, `maySendStream` |
| §2.4 (818) | reset the stream "if the stream was not already in a terminal state" | `Step.reset` / `Step.resetRefused` |
| §3.1 (920) | "Ready" accepts data from the application | `init`, `canWrite` |
| §3.1 (927) | first STREAM / STREAM_DATA_BLOCKED → "Send" | `Phase.afterSend`, `Step.sendStream`, `Step.sendBlocked` |
| §3.1 (934) | STREAM_DATA_BLOCKED when blocked by stream flow control | `maySendBlocked` (limit = `maxData`) |
| §3.1 (938) | STREAM with FIN → "Data Sent" | `Step.sendStream` (`fin = true`) |
| §3.1 (944) | MAX_STREAM_DATA can safely be ignored in "Data Sent" | `Step.maxStreamDataIgnored` (`Phase.beforeFin`) |
| §3.1 (947) | all data acknowledged → "Data Recvd", terminal | `Step.allAcked`, `terminal_absorbing` |
| §3.1 (962) | app abandons transmission, or STOP_SENDING → RESET_STREAM → "Reset Sent" | `Step.reset`, `Step.stopSending`, `Step.sendReset` |
| §3.1 (968) | MAY send RESET_STREAM as the first frame mentioning a stream | `maySendReset` permits it in "Ready" (example) |
| §3.1 (971) | RESET_STREAM acknowledged → "Reset Recvd", terminal | `Step.resetAcked`, `terminal_absorbing` |
| §3.3 (1112) | MUST NOT send any of the three frames from a terminal state | `Phase.mayCarryData`, `maySendReset` |
| §3.3 (1114) | MUST NOT send STREAM / STREAM_DATA_BLOCKED after RESET_STREAM | `Phase.mayCarryData` |
| §3.3 (1118) | a sender could receive MAX_STREAM_DATA / STOP_SENDING in any state | `Step.maxStreamDataIgnored`, `Step.stopSendingLate` |
| §3.5 (1258) | STOP_SENDING MUST be answered with RESET_STREAM in Ready/Send; MAY be deferred in Data Sent | `Step.stopSending` sets `resetCode`; `stopSending_obliges_reset` |
| §3.5 (1266) | SHOULD copy the error code, but any application code may be used | `maySendReset` ignores the code (example) |
| §4.1 (1330) | "Senders MUST NOT send data in excess of either limit" | `maySendStream` (stream limit); connection limit is WP9 |
| §4.1 (1357) | a smaller advertised limit is not an error and has no effect | `Step.maxStreamDataIgnored`, `maxData_mono` |
| §4.1 (1361) | MUST ignore MAX_STREAM_DATA that does not increase the limit | `Step.maxStreamDataIgnored` |
| §4.1 (1370) | SHOULD send STREAM_DATA_BLOCKED when blocked | permitted by `maySendBlocked`; the recommendation to send is advice, not encoded |
| §4.4 (1466) | RESET_STREAM has no effect on the opposite direction | the two halves are independent components; `Spec/Stream.lean` |
| §4.5 (1479) | final size = one higher than the largest offset sent | `maySendReset` (`finalSize = sent` when not yet known), `Inv` |
| §4.5 (1486) | the final size is Offset+Length of the FIN frame, or RESET_STREAM's Final Size | `Step.sendStream`, `Step.sendReset` |
| §4.5 (1493) | a sender always communicates the final size reliably | `Inv`: outside Ready/Send a final size is fixed |
| §4.5 (1499) | MUST NOT send data at or beyond the final size | `maySendStream`, `no_data_beyond_finalSize` |
| §4.5 (1516) | once known, the final size cannot change | `maySendStream`/`maySendReset`, `finalSize_immutable` |
| §2.1 (680) | MUST NOT reuse a stream ID | out of scope: WP9 (stream table) |
| §2.2 (752) | data at a given offset MUST NOT change | out of scope: byte contents are not modelled |
| §3.5 (1246) | STREAM frames after STOP_SENDING still count for flow control | receiving side, `Spec/Stream/Recv.lean` |
| §13.3 | retransmission | out of scope by assignment |

NOTES

* **Transmission as an event.**  Figure 2's arrows are labelled with frames the
  endpoint *sends*, so the state machine is driven by events that report what
  was sent (`sentStream`, `sentStreamDataBlocked`, `sentResetStream`), not by
  the application calls.  `MaySend` decides whether the frame was legal; the
  step then either applies it (`Step.sendStream`) or, if it was not legal,
  changes nothing (`Step.sendStreamForbidden` → `.drop`).
  `sendStream_ok_iff_maySend` and `sendReset_ok_iff_maySend` state that the two
  agree, so a differential harness can use `maySend` as the send-side check and
  feed the event to advance the model.
* **Application requests are separated from transmission.**  §2.4 says that
  resetting the stream "result[s] in a RESET_STREAM frame"; here `appReset`
  records the request (and the error code) and emits `resetRequested`, and the
  frame leaves on a later `sentResetStream` event.  Otherwise the arrow
  "Send RESET_STREAM" would be drawn by two different events.
* **Refused application requests are `.drop`.**  Writing to a stream that has
  been ended or reset is a local API error, not a connection error and not a
  silent success, so it is modelled as "nothing happens".  `.error` is reserved
  for connection errors, as in the template.
* **No buffering model.**  `written` is what the application has handed over and
  `sent` is the highest offset transmitted; `written - sent` stands for whatever
  is buffered.  Byte contents are not modelled, so a STREAM frame is just
  (offset, length, fin) and retransmission is an ordinary `sentStream` of a
  range already sent.
* **MAX_STREAM_DATA in "Data Sent" and later.**  §3.1 says the endpoint "can
  safely ignore" such frames; that is a permission, not a requirement, so an
  implementation that raised its limit there would also conform.  The two
  readings are indistinguishable (no more STREAM data may be sent past the final
  size anyway), so only the ignoring one is encoded, keeping `outcomes`
  deterministic and `track` unambiguous.
* **STOP_SENDING's "MUST send a RESET_STREAM" is an obligation, not a step.**
  This framework specifies what each event does, so a *future* obligation is
  recorded in the state (`resetCode`) rather than enforced.
  `stopSending_obliges_reset` below states the consequence that is checkable:
  after a STOP_SENDING in "Ready"/"Send" the endpoint is always permitted to
  send the RESET_STREAM.
* **Retransmission (§13.3) is out of scope, but repeats are not forbidden.**
  `maySendStream` constrains only (offset, length, fin) against `written`, the
  peer's credit and the final size, so re-sending a range already sent is
  permitted in "Ready", "Send" and "Data Sent" — which is what retransmitting a
  lost packet amounts to in this model.  After a RESET_STREAM has been sent it is
  not: §3.3, line 1114 says "A sender MUST NOT send a STREAM or
  STREAM_DATA_BLOCKED frame for a stream in the 'Reset Sent' state", and §3.5,
  line 1263 says that if outstanding data is declared lost the endpoint "SHOULD
  send a RESET_STREAM frame instead of retransmitting the data".  RESET_STREAM
  itself may be repeated from "Reset Sent" (that state is not terminal), with the
  same final size, since `maySendReset` pins it to the one already fixed.
* **STREAM_DATA_BLOCKED reports the current credit.**  §19.13's Maximum Stream
  Data field is "the offset of the stream at which the blocking occurred", which
  is read here as exactly the limit the peer last advertised, so `maySendBlocked`
  requires `limit = maxData`.  A sender that reported a stale limit would be
  rejected; the template's `streamsBlocked` rule reads §19.14 the same way.
* **Final size on RESET_STREAM.**  When no final size is fixed yet, `maySendReset`
  requires exactly `finalSize = sent`, reading §4.5's "one higher than the
  offset of the byte with the largest offset sent on the stream" as a
  requirement on the sender.  An implementation that has buffered but not sent
  data and declares the buffered size instead would be rejected; that reading
  was chosen because the text defines the final size in terms of bytes *sent*.
-/

/-- §3.5, line 1258: after a STOP_SENDING in "Ready" or "Send", sending the
    solicited RESET_STREAM is always permitted (the code is copied per §3.5,
    line 1266). -/
theorem stopSending_obliges_reset {s s' : State} {code : Nat} {fx : List Effect}
    (hi : Inv s) (h : Step s (.recvStopSending code) (.ok s' fx))
    (hb : s.phase.beforeFin = true) :
    s'.resetCode = some code ∧ maySendReset s' code s'.sent = true := by
  cases h with
  | stopSending hc =>
    refine ⟨rfl, ?_⟩
    have ht : s.phase.terminal = false := by
      cases hp : s.phase <;> simp_all [Phase.beforeFin, Phase.terminal]
    simp only [maySendReset, ht, Bool.not_false, Bool.true_and]
    cases hf : s.finalSize with
    | none => simp
    | some f => simp only [decide_eq_true_eq]; exact (hi.2.2.1 f hf).symm
  | stopSendingLate hc =>
    have : s.phase.mayCarryData = true := by
      cases hp : s.phase <;> simp_all [Phase.beforeFin, Phase.mayCarryData]
    rw [this] at hc; exact absurd hc (by simp)

end Quic.Spec.Stream.Send
