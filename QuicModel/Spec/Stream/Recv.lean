import QuicModel.Spec.Core

/-
  WP2 Stream, part 2 of 3: the *receiving* part of one stream, as seen by one
  endpoint (§3.2, §3.3, §3.5, and the stream-level half of §4.1, §4.4, §4.5).

  Follows the ten-part order of `Spec/Template.lean`.
-/
namespace Quic.Spec.Stream.Recv

/-! ## 1. State, events, effects -/

/-- §3.2, line 1045 (Figure 3): the six states of a receiving part. -/
inductive Phase where
  | recv | sizeKnown | dataRecvd | dataRead | resetRecvd | resetRead
  deriving DecidableEq, Repr

namespace Phase

/-- §3.2, lines 1102 and 1135: "Data Read" and "Reset Read" are terminal. -/
def terminal : Phase → Bool
  | .dataRead | .resetRead => true
  | _ => false

def isRecv : Phase → Bool
  | .recv => true
  | _ => false

def isDataRecvd : Phase → Bool
  | .dataRecvd => true
  | _ => false

def isResetRecvd : Phase → Bool
  | .resetRecvd => true
  | _ => false

/-- §3.2, line 1105: "Receiving a RESET_STREAM frame in the "Recv" or "Size
    Known" states causes the stream to enter the "Reset Recvd" state." -/
def beforeAllData : Phase → Bool
  | .recv | .sizeKnown => true
  | _ => false

/-- §3.3, line 1157: "receiver MAY send STOP_SENDING in any state where it has
    not received a RESET_STREAM frame; that is states other than "Reset Recvd"
    or "Reset Read"." -/
def mayStopSending : Phase → Bool
  | .resetRecvd | .resetRead => false
  | _ => true

end Phase

/-! ### Received data

Byte contents and reassembly are out of scope (see NOTES), but the transition
"Recv All Data" needs to know whether the stream is complete, so the *set* of
received byte ranges is kept as a canonical list of disjoint, ordered,
non-adjacent intervals `[o, e)`.  Inserting a range that is already covered
leaves the list alone, which is what makes duplicate and overlapping STREAM
frames idempotent. -/

/-- Insert `[o, e)` into an ordered list of intervals, merging on overlap or
    adjacency.  Structural recursion on the list, so it is total. -/
def insertRange (o e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(o, e)]
  | (a, b) :: rest =>
      if e < a then (o, e) :: (a, b) :: rest
      else if b < o then (a, b) :: insertRange o e rest
      else insertRange (min o a) (max e b) rest

/-- Record the bytes `[o, e)` as received; an empty range changes nothing. -/
def addRange (rs : List (Nat × Nat)) (o e : Nat) : List (Nat × Nat) :=
  if o < e then insertRange o e rs else rs

structure State where
  /-- §2.1 the stream this is a part of. -/
  id : StreamId
  /-- Which endpoint we are. -/
  role : Role
  phase : Phase
  /-- §4.1, line 1349: the limit we have advertised for this stream — a
      MAX_STREAM_DATA frame "indicates the maximum absolute byte offset of a
      stream".  Starts at our
      `initial_max_stream_data_*` transport parameter, raised by every
      MAX_STREAM_DATA we send. -/
  maxData : Nat
  /-- One past the highest offset received in any STREAM frame (or the final
      size of a RESET_STREAM); the amount of stream credit consumed so far. -/
  highest : Nat
  /-- The received byte ranges, canonical (see `insertRange`). -/
  ranges : List (Nat × Nat)
  /-- §4.5: the final size, once "Size Known" or "Reset Recvd" is reached. -/
  finalSize : Option Nat
  /-- §3.2, line 1101: how much has been delivered to the application. -/
  read : Nat
  /-- §3.5: the application error code of a STOP_SENDING we asked for or sent. -/
  stopSending : Option Nat
  deriving DecidableEq, Repr

namespace State

/-- The contiguous prefix of the stream that has been received. -/
def recvd (s : State) : Nat :=
  match s.ranges with
  | (0, e) :: _ => e
  | _ => 0

/-- §3.2, line 1095: "Once all data for the stream has been received". -/
def complete (s : State) : Bool :=
  match s.finalSize with
  | none => false
  | some f => decide (s.recvd = f)

end State

/-- A receiving part in its initial state: §3.2, line 1052 "The initial state
    for the receiving part of a stream is 'Recv'."  `initialMax` is our
    `initial_max_stream_data_*` for this stream. -/
def init (id : StreamId) (role : Role) (initialMax : Nat) : State :=
  { id, role, phase := .recv, maxData := initialMax, highest := 0, ranges := [],
    finalSize := none, read := 0, stopSending := none }

inductive Event where
  /-- §19.8 STREAM frame received: `offset`, data length, FIN bit. -/
  | recvStream (offset len : Nat) (fin : Bool)
  /-- §19.4 RESET_STREAM received, carrying the final size. -/
  | recvResetStream (code finalSize : Nat)
  /-- §19.13 STREAM_DATA_BLOCKED received. -/
  | recvStreamDataBlocked (limit : Nat)
  /-- §2.4, line 814: the application reads `len` bytes. -/
  | appRead (len : Nat)
  /-- §3.2, line 1135: the application takes delivery of the reset signal. -/
  | appReadReset
  /-- §2.4, line 816 / §3.5, line 1243: the application aborts reading. -/
  | appAbortRead (code : Nat)
  /-- We transmitted a MAX_STREAM_DATA frame advertising this limit. -/
  | sentMaxStreamData (v : Nat)
  /-- We transmitted a STOP_SENDING frame. -/
  | sentStopSending (code : Nat)
  deriving DecidableEq, Repr

/-- Events that are frames arriving from the peer; see `Send.Event.isPeerFrame`. -/
def Event.isPeerFrame : Event → Bool
  | .recvStream .. | .recvResetStream .. | .recvStreamDataBlocked .. => true
  | _ => false

inductive Effect where
  /-- Contiguous stream data is available to the application up to this offset. -/
  | dataAvailable (upTo : Nat)
  /-- §3.2, line 1095: all data for the stream has been received. -/
  | allDataReceived (finalSize : Nat)
  /-- §3.2, line 1127: the peer reset the stream; the application is told. -/
  | streamReset (code finalSize : Nat)
  /-- §3.5, line 1243: the application aborted reading, so a STOP_SENDING frame
      should be sent. -/
  | stopSendingRequested (code : Nat)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ### Accepting a STREAM frame -/

/-- §3.2, lines 1089–1096: a STREAM frame with FIN fixes the final size and
    moves "Recv" to "Size Known"; once all the data is there the part moves to
    "Data Recvd", which "might happen as a result of receiving the same STREAM
    frame that causes the transition to "Size Known"" (§3.2, line 1096).
    In "Data Recvd",
    "Data Read", "Reset Recvd" and "Reset Read" further STREAM frames do not
    move the state machine on their own (the optional "Recv All Data" arrow out
    of "Reset Recvd" is a separate, permitted, alternative outcome). -/
def Phase.afterData (p : Phase) (fin complete : Bool) : Phase :=
  match p with
  | .recv => if complete then .dataRecvd else if fin then .sizeKnown else .recv
  | .sizeKnown => if complete then .dataRecvd else .sizeKnown
  | p => p

/-- The state after a STREAM frame has been accepted. -/
def accept (s : State) (offset len : Nat) (fin : Bool) : State :=
  let s1 : State :=
    { s with highest := max s.highest (offset + len),
             ranges := addRange s.ranges offset (offset + len),
             finalSize := if fin then some (offset + len) else s.finalSize }
  { s1 with phase := s.phase.afterData fin s1.complete }

/-- What the application is told when the receiving part moves from `s` to `s'`. -/
def effectsOf (s s' : State) : List Effect :=
  (if s.recvd < s'.recvd then [Effect.dataAvailable s'.recvd] else []) ++
  (if !s.phase.isDataRecvd && s'.phase.isDataRecvd then
      [Effect.allDataReceived s'.recvd] else [])

/-! ### Guards -/

/-- §19.8, line 7684: "The largest offset delivered on a stream - the sum of the
    offset and data length - cannot exceed 2^62-1". -/
def maxOffset : Nat := 2 ^ 62 - 1

/-- §4.5, line 1517: "Once a final size for a stream is known, it cannot change.
    If a RESET_STREAM or STREAM frame is received indicating a change in the
    final size for the stream, an endpoint SHOULD respond with a
    FINAL_SIZE_ERROR"; line 1520: "A receiver SHOULD treat receipt of data at or
    beyond the final size as a FINAL_SIZE_ERROR error, even after a stream is
    closed."  A FIN below the highest offset already received is the same fault
    seen from the other side. -/
def finalSizeViolation (s : State) (e : Nat) (fin : Bool) : Bool :=
  (fin && decide (e < s.highest)) ||
  (match s.finalSize with
   | none => false
   | some f => decide (f < e) || (fin && !decide (e = f)))

/-- The same two sentences for RESET_STREAM's Final Size field. -/
def resetFinalSizeViolation (s : State) (fs : Nat) : Bool :=
  decide (fs < s.highest) ||
  (match s.finalSize with
   | none => false
   | some f => !decide (fs = f))

/-- §3.3, line 1157 (and §3.5, line 1269: "STOP_SENDING SHOULD only be sent for
    a stream that has not been reset by the peer"). -/
def maySendStopSending (s : State) (_code : Nat) : Bool := s.phase.mayStopSending

/-- §3.3, line 1156: "The receiver only sends MAX_STREAM_DATA in the "Recv"
    state", restated in §13.3, line 5393 as a SHOULD.  This is a *recommendation*
    about when to send the frame, not a prohibition: see `RecommendedSend` and
    the NOTES.  Nothing in the model forbids the frame, so this predicate is not
    used by `MaySend`. -/
def recommendedMaxStreamData (s : State) (_v : Nat) : Bool := s.phase.isRecv

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §19.8, line 7686: "Receipt of a frame that exceeds this limit MUST be
      treated as a connection error of type FRAME_ENCODING_ERROR or
      FLOW_CONTROL_ERROR."  First alternative. -/
  | streamTooLarge₁ {s offset len fin} (h : decide (maxOffset < offset + len) = true) :
      Step s (.recvStream offset len fin) (.error .frameEncodingError)
  /-- Same sentence, second alternative. -/
  | streamTooLarge₂ {s offset len fin} (h : decide (maxOffset < offset + len) = true) :
      Step s (.recvStream offset len fin) (.error .flowControlError)
  /-- §4.1, line 1368: "A receiver MUST close the connection with a
      FLOW_CONTROL_ERROR error if the sender violates the advertised connection
      or stream data limits." -/
  | streamFlowControl {s offset len fin}
      (h1 : decide (maxOffset < offset + len) = false)
      (h2 : decide (s.maxData < offset + len) = true) :
      Step s (.recvStream offset len fin) (.error .flowControlError)
  /-- §4.5, line 1517/1520: FINAL_SIZE_ERROR on a changed final size or on data
      at or beyond a known one.  No hypothesis rules out the other errors: the
      text fixes no order between §4.1, line 1368, §19.8, line 7686 and §4.5, so
      when a frame breaks several rules at once *every* error the text attaches
      to any of them is permitted (see NOTES). -/
  | streamFinalSize {s offset len fin}
      (h3 : finalSizeViolation s (offset + len) fin = true) :
      Step s (.recvStream offset len fin) (.error .finalSizeError)
  /-- §4.5, line 1522: "Generating these errors is not mandatory, because
      requiring that an endpoint generate these errors also means that the
      endpoint needs to maintain the final size state for closed streams."
      Both sentences of §4.5 are SHOULDs and neither is restricted to a closed
      stream, so *in any state* the frame may instead be ignored: it has no
      effect at all, so no data at or beyond the final size is ever accounted
      for and the final size itself cannot move.  Raising the error is the
      recommended behaviour (`Recommended`) and the first outcome. -/
  | streamFinalSizeIgnored {s offset len fin}
      (h1 : decide (maxOffset < offset + len) = false)
      (h2 : decide (s.maxData < offset + len) = false)
      (h3 : finalSizeViolation s (offset + len) fin = true) :
      Step s (.recvStream offset len fin) (.ok s [])
  /-- §3.2, lines 1082–1098: the frame is accepted; the data is buffered, a FIN
      fixes the final size ("Size Known") and completing the stream reaches
      "Data Recvd".  §2.2, line 749: "Data that has already been received can be
      discarded", so duplicates and overlaps are accepted and idempotent. -/
  | streamOk {s offset len fin}
      (h1 : decide (maxOffset < offset + len) = false)
      (h2 : decide (s.maxData < offset + len) = false)
      (h3 : finalSizeViolation s (offset + len) fin = false) :
      Step s (.recvStream offset len fin)
        (.ok (accept s offset len fin) (effectsOf s (accept s offset len fin)))
  /-- §3.2, line 1111 (Figure 3, "Recv All Data (optional)"): "Similarly, it is
      possible for remaining stream data to arrive after receiving a
      RESET_STREAM frame (the "Reset Recvd" state).  An implementation is free
      to manage this situation as it chooses." -/
  | streamResetComplete {s offset len fin}
      (h1 : decide (maxOffset < offset + len) = false)
      (h2 : decide (s.maxData < offset + len) = false)
      (h3 : finalSizeViolation s (offset + len) fin = false)
      (h4 : (s.phase.isResetRecvd && (accept s offset len fin).complete) = true) :
      Step s (.recvStream offset len fin)
        (.ok { accept s offset len fin with phase := .dataRecvd }
             (effectsOf s { accept s offset len fin with phase := .dataRecvd }))
  /-- §19.8, line 7686 applied to RESET_STREAM's Final Size. -/
  | resetTooLarge₁ {s code fs} (h : decide (maxOffset < fs) = true) :
      Step s (.recvResetStream code fs) (.error .frameEncodingError)
  | resetTooLarge₂ {s code fs} (h : decide (maxOffset < fs) = true) :
      Step s (.recvResetStream code fs) (.error .flowControlError)
  /-- §4.1, line 1368 with §4.5, line 1495: the final size is the credit the
      stream consumed, so a final size beyond the advertised limit is a flow
      control violation. -/
  | resetFlowControl {s code fs}
      (h1 : decide (maxOffset < fs) = false) (h2 : decide (s.maxData < fs) = true) :
      Step s (.recvResetStream code fs) (.error .flowControlError)
  /-- §4.5, line 1517: a RESET_STREAM "indicating a change in the final size".
      As for `streamFinalSize`, no hypothesis excludes the other errors: §4.1's
      FLOW_CONTROL_ERROR and §4.5's FINAL_SIZE_ERROR may both apply to the same
      frame and the text gives no precedence (see NOTES). -/
  | resetFinalSize {s code fs}
      (h3 : resetFinalSizeViolation s fs = true) :
      Step s (.recvResetStream code fs) (.error .finalSizeError)
  /-- §4.5, line 1522, as for STREAM frames: in any state the endpoint may
      decline to police the final size, and then the whole frame is discarded —
      neither the final size nor the reset takes effect (see NOTES). -/
  | resetFinalSizeIgnored {s code fs}
      (h1 : decide (maxOffset < fs) = false) (h2 : decide (s.maxData < fs) = false)
      (h3 : resetFinalSizeViolation s fs = true) :
      Step s (.recvResetStream code fs) (.ok s [])
  /-- §3.2, line 1105: "Receiving a RESET_STREAM frame in the "Recv" or "Size
      Known" states causes the stream to enter the "Reset Recvd" state." -/
  | resetOk {s code fs}
      (h1 : decide (maxOffset < fs) = false) (h2 : decide (s.maxData < fs) = false)
      (h3 : resetFinalSizeViolation s fs = false) (h4 : s.phase.beforeAllData = true) :
      Step s (.recvResetStream code fs)
        (.ok { s with phase := .resetRecvd, highest := fs, finalSize := some fs }
             [.streamReset code fs])
  /-- §3.2, line 1129: "A RESET_STREAM signal might be suppressed or withheld if
      stream data is completely received and is buffered to be read by the
      application.  If the RESET_STREAM is suppressed, the receiving part of the
      stream remains in "Data Recvd"."  Also covers a repeated RESET_STREAM in
      "Reset Recvd" / "Reset Read" and one arriving in "Data Read". -/
  | resetSuppressed {s code fs}
      (h1 : decide (maxOffset < fs) = false) (h2 : decide (s.maxData < fs) = false)
      (h3 : resetFinalSizeViolation s fs = false) (h4 : s.phase.beforeAllData = false) :
      Step s (.recvResetStream code fs) (.ok s [])
  /-- §3.2, line 1109 (Figure 3, "Recv RESET_STREAM (optional)"): "It is possible
      that all stream data has already been received when a RESET_STREAM is
      received (that is, in the "Data Recvd" state)"; §3.2, line 1127: "An
      implementation MAY interrupt delivery of stream data, discard any data
      that was not consumed, and signal the receipt of the RESET_STREAM." -/
  | resetAfterData {s code fs}
      (h1 : decide (maxOffset < fs) = false) (h2 : decide (s.maxData < fs) = false)
      (h3 : resetFinalSizeViolation s fs = false) (h4 : s.phase.isDataRecvd = true) :
      Step s (.recvResetStream code fs)
        (.ok { s with phase := .resetRecvd, finalSize := some fs } [.streamReset code fs])
  /-- §3.2, line 1082: "In the "Recv" state, the endpoint receives STREAM and
      STREAM_DATA_BLOCKED frames"; §3.2, line 1098: "After all data has been
      received, any STREAM or STREAM_DATA_BLOCKED frames for the stream can be
      discarded."  The frame carries no data, so in every state accepting it and
      doing nothing is permitted; opening the stream is WP9's business. -/
  | blocked {s limit} : Step s (.recvStreamDataBlocked limit) (.ok s [])
  /-- §4.1, line 1368: "A receiver MUST close the connection with a
      FLOW_CONTROL_ERROR error if the sender violates the advertised connection
      or stream data limits."  §19.13, line 7881 says the Maximum Stream Data
      field is "the offset of the stream at which the blocking occurred", so a
      value beyond the limit we advertised is the peer claiming credit that was
      never granted.  This is the wider of the two readings of line 1368 (see
      NOTES); it is therefore an *additional* permitted outcome and never the
      only one — `Step.blocked` is available for the same frame. -/
  | blockedFlowControl {s limit} (h : decide (s.maxData < limit) = true) :
      Step s (.recvStreamDataBlocked limit) (.error .flowControlError)
  /-- §3.2, line 1101: "The "Data Recvd" state persists until stream data has
      been delivered to the application.  Once stream data has been delivered,
      the stream enters the "Data Read" state". -/
  | read {s len} (h : decide (s.read + len ≤ s.recvd) = true) :
      Step s (.appRead len)
        (.ok { s with read := s.read + len,
                      phase := if (s.phase.isDataRecvd &&
                                   decide (s.finalSize = some (s.read + len))) then
                                 .dataRead else s.phase } [])
  /-- Data that has not arrived cannot be read. -/
  | readRefused {s len} (h : decide (s.read + len ≤ s.recvd) = false) :
      Step s (.appRead len) .drop
  /-- §3.2, line 1135: "Once the application receives the signal indicating that
      the stream was reset, the receiving part of the stream transitions to the
      "Reset Read" state". -/
  | readReset {s} (h : s.phase.isResetRecvd = true) :
      Step s .appReadReset (.ok { s with phase := .resetRead } [])
  | readResetRefused {s} (h : s.phase.isResetRecvd = false) :
      Step s .appReadReset .drop
  /-- §3.5, line 1243: "If the stream is in the "Recv" or "Size Known" states,
      the transport SHOULD signal this by sending a STOP_SENDING frame to prompt
      closure of the stream in the opposite direction." -/
  | abortRead {s code} (h : s.phase.beforeAllData = true) :
      Step s (.appAbortRead code)
        (.ok { s with stopSending := some code } [.stopSendingRequested code])
  /-- §3.5, line 1273: "An endpoint is expected to send another STOP_SENDING
      frame if a packet containing a previous STOP_SENDING is lost.  However,
      once either all stream data or a RESET_STREAM frame has been received for
      the stream ... sending a STOP_SENDING frame is unnecessary." -/
  | abortReadLate {s code} (h : s.phase.beforeAllData = false) :
      Step s (.appAbortRead code) (.ok s [])
  /-- §4.1, line 1349: "A receiver can advertise a larger limit for a stream by
      sending a MAX_STREAM_DATA frame"; line 1364: "it is not an error to
      advertise a smaller limit, but the smaller limit has no effect."  Sending
      the frame is permitted in *every* phase: §3.3, line 1156 and §13.3,
      line 5393 are advice about when to stop (`RecommendedSend`), while
      §13.3, line 5390 requires a lost MAX_STREAM_DATA to be re-sent and §3.1,
      line 970 expects such frames to arrive after the FIN. -/
  | sendMaxStreamData {s v} :
      Step s (.sentMaxStreamData v) (.ok { s with maxData := max s.maxData v } [])
  /-- §3.3, line 1157: STOP_SENDING may be sent in any state in which no
      RESET_STREAM has been received. -/
  | sendStopSending {s code} (h : maySendStopSending s code = true) :
      Step s (.sentStopSending code) (.ok { s with stopSending := some code } [])
  | sendStopSendingForbidden {s code} (h : maySendStopSending s code = false) :
      Step s (.sentStopSending code) .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvStream offset len fin =>
      if decide (maxOffset < offset + len) then
        if finalSizeViolation s (offset + len) fin then
          [.error .frameEncodingError, .error .flowControlError, .error .finalSizeError]
        else [.error .frameEncodingError, .error .flowControlError]
      else if decide (s.maxData < offset + len) then
        if finalSizeViolation s (offset + len) fin then
          [.error .flowControlError, .error .finalSizeError]
        else [.error .flowControlError]
      else if finalSizeViolation s (offset + len) fin then
        [.error .finalSizeError, .ok s []]
      else
        .ok (accept s offset len fin) (effectsOf s (accept s offset len fin)) ::
          (if s.phase.isResetRecvd && (accept s offset len fin).complete then
            [.ok { accept s offset len fin with phase := .dataRecvd }
                 (effectsOf s { accept s offset len fin with phase := .dataRecvd })]
           else [])
  | .recvResetStream code fs =>
      if decide (maxOffset < fs) then
        if resetFinalSizeViolation s fs then
          [.error .frameEncodingError, .error .flowControlError, .error .finalSizeError]
        else [.error .frameEncodingError, .error .flowControlError]
      else if decide (s.maxData < fs) then
        if resetFinalSizeViolation s fs then
          [.error .flowControlError, .error .finalSizeError]
        else [.error .flowControlError]
      else if resetFinalSizeViolation s fs then
        [.error .finalSizeError, .ok s []]
      else if s.phase.beforeAllData then
        [.ok { s with phase := .resetRecvd, highest := fs, finalSize := some fs }
             [.streamReset code fs]]
      else
        .ok s [] ::
          (if s.phase.isDataRecvd then
            [.ok { s with phase := .resetRecvd, finalSize := some fs } [.streamReset code fs]]
           else [])
  | .recvStreamDataBlocked limit =>
      .ok s [] :: (if decide (s.maxData < limit) then [.error .flowControlError] else [])
  | .appRead len =>
      if decide (s.read + len ≤ s.recvd) then
        [.ok { s with read := s.read + len,
                      phase := if (s.phase.isDataRecvd &&
                                   decide (s.finalSize = some (s.read + len))) then
                                 .dataRead else s.phase } []]
      else [.drop]
  | .appReadReset =>
      if s.phase.isResetRecvd then [.ok { s with phase := .resetRead } []] else [.drop]
  | .appAbortRead code =>
      if s.phase.beforeAllData then
        [.ok { s with stopSending := some code } [.stopSendingRequested code]]
      else [.ok s []]
  | .sentMaxStreamData v => [.ok { s with maxData := max s.maxData v } []]
  | .sentStopSending code =>
      if maySendStopSending s code then [.ok { s with stopSending := some code } []]
      else [.drop]

/-! ## 4. The two forms agree -/


theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvStream offset len fin =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        split at h
        · rename_i c3
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h <;> subst h
          · exact .streamTooLarge₁ c1
          · exact .streamTooLarge₂ c1
          · exact .streamFinalSize c3
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .streamTooLarge₁ c1
          · exact .streamTooLarge₂ c1
      · rename_i c1
        have c1' : decide (maxOffset < offset + len) = false := Bool.eq_false_iff.mpr c1
        split at h
        · rename_i c2
          split at h
          · rename_i c3
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .streamFlowControl c1' c2
            · exact .streamFinalSize c3
          · simp only [List.mem_singleton] at h; subst h
            exact .streamFlowControl c1' c2
        · rename_i c2
          have c2' : decide (s.maxData < offset + len) = false := Bool.eq_false_iff.mpr c2
          split at h
          · rename_i c3
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .streamFinalSize c3
            · exact .streamFinalSizeIgnored c1' c2' c3
          · rename_i c3
            have c3' : finalSizeViolation s (offset + len) fin = false := Bool.eq_false_iff.mpr c3
            simp only [List.mem_cons] at h
            rcases h with h | h
            · subst h; exact .streamOk c1' c2' c3'
            · split at h
              · rename_i c4
                simp only [List.mem_singleton] at h; subst h
                exact .streamResetComplete c1' c2' c3' c4
              · simp at h
    | recvResetStream code fs =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        split at h
        · rename_i c3
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h <;> subst h
          · exact .resetTooLarge₁ c1
          · exact .resetTooLarge₂ c1
          · exact .resetFinalSize c3
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .resetTooLarge₁ c1
          · exact .resetTooLarge₂ c1
      · rename_i c1
        have c1' : decide (maxOffset < fs) = false := Bool.eq_false_iff.mpr c1
        split at h
        · rename_i c2
          split at h
          · rename_i c3
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .resetFlowControl c1' c2
            · exact .resetFinalSize c3
          · simp only [List.mem_singleton] at h; subst h
            exact .resetFlowControl c1' c2
        · rename_i c2
          have c2' : decide (s.maxData < fs) = false := Bool.eq_false_iff.mpr c2
          split at h
          · rename_i c3
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .resetFinalSize c3
            · exact .resetFinalSizeIgnored c1' c2' c3
          · rename_i c3
            have c3' : resetFinalSizeViolation s fs = false := Bool.eq_false_iff.mpr c3
            split at h
            · rename_i c4
              simp only [List.mem_singleton] at h; subst h
              exact .resetOk c1' c2' c3' c4
            · rename_i c4
              have c4' : s.phase.beforeAllData = false := Bool.eq_false_iff.mpr c4
              simp only [List.mem_cons] at h
              rcases h with h | h
              · subst h; exact .resetSuppressed c1' c2' c3' c4'
              · split at h
                · rename_i c5
                  simp only [List.mem_singleton] at h; subst h
                  exact .resetAfterData c1' c2' c3' c5
                · simp at h
    | recvStreamDataBlocked limit =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .blocked
        · exact .blockedFlowControl c1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h; exact .blocked
    | appRead len =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h; exact .read c1
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h
        exact .readRefused (Bool.eq_false_iff.mpr c1)
    | appReadReset =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h; exact .readReset c1
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h
        exact .readResetRefused (Bool.eq_false_iff.mpr c1)
    | appAbortRead code =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h; exact .abortRead c1
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h
        exact .abortReadLate (Bool.eq_false_iff.mpr c1)
    | sentMaxStreamData v =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .sendMaxStreamData
    | sentStopSending code =>
      simp only [outcomes] at h
      split at h
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h; exact .sendStopSending c1
      · rename_i c1
        simp only [List.mem_singleton] at h; subst h
        exact .sendStopSendingForbidden (Bool.eq_false_iff.mpr c1)
  · intro h
    cases h with
    | @streamTooLarge₁ offset len fin h =>
      by_cases c3 : finalSizeViolation s (offset + len) fin = true
      · simp [outcomes, h, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h, c3]
    | @streamTooLarge₂ offset len fin h =>
      by_cases c3 : finalSizeViolation s (offset + len) fin = true
      · simp [outcomes, h, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h, c3]
    | @streamFlowControl offset len fin h1 h2 =>
      by_cases c3 : finalSizeViolation s (offset + len) fin = true
      · simp [outcomes, h1, h2, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h1, h2, c3]
    | @streamFinalSize offset len fin h3 =>
      by_cases c1 : decide (maxOffset < offset + len) = true
      · simp [outcomes, c1, h3]
      · simp only [Bool.not_eq_true] at c1
        by_cases c2 : decide (s.maxData < offset + len) = true
        · simp [outcomes, c1, c2, h3]
        · simp only [Bool.not_eq_true] at c2
          simp [outcomes, c1, c2, h3]
    | streamFinalSizeIgnored h1 h2 h3 => simp [outcomes, h1, h2, h3]
    | streamOk h1 h2 h3 => simp [outcomes, h1, h2, h3]
    | streamResetComplete h1 h2 h3 h4 => simp [outcomes, h1, h2, h3, h4]
    | @resetTooLarge₁ code fs h =>
      by_cases c3 : resetFinalSizeViolation s fs = true
      · simp [outcomes, h, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h, c3]
    | @resetTooLarge₂ code fs h =>
      by_cases c3 : resetFinalSizeViolation s fs = true
      · simp [outcomes, h, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h, c3]
    | @resetFlowControl code fs h1 h2 =>
      by_cases c3 : resetFinalSizeViolation s fs = true
      · simp [outcomes, h1, h2, c3]
      · simp only [Bool.not_eq_true] at c3
        simp [outcomes, h1, h2, c3]
    | @resetFinalSize code fs h3 =>
      by_cases c1 : decide (maxOffset < fs) = true
      · simp [outcomes, c1, h3]
      · simp only [Bool.not_eq_true] at c1
        by_cases c2 : decide (s.maxData < fs) = true
        · simp [outcomes, c1, c2, h3]
        · simp only [Bool.not_eq_true] at c2
          simp [outcomes, c1, c2, h3]
    | resetFinalSizeIgnored h1 h2 h3 => simp [outcomes, h1, h2, h3]
    | resetOk h1 h2 h3 h4 => simp [outcomes, h1, h2, h3, h4]
    | resetSuppressed h1 h2 h3 h4 => simp [outcomes, h1, h2, h3, h4]
    | @resetAfterData code fs h1 h2 h3 h4 =>
      have hb : s.phase.beforeAllData = false := by
        cases hp : s.phase <;> simp_all [Phase.beforeAllData, Phase.isDataRecvd]
      simp [outcomes, h1, h2, h3, h4, hb]
    | blocked => simp [outcomes]
    | blockedFlowControl h => simp [outcomes, h]
    | read h => simp [outcomes, h]
    | readRefused h => simp [outcomes, h]
    | readReset h => simp [outcomes, h]
    | readResetRefused h => simp [outcomes, h]
    | abortRead h => simp [outcomes, h]
    | abortReadLate h => simp [outcomes, h]
    | sendMaxStreamData => simp [outcomes]
    | sendStopSending h => simp [outcomes, h]
    | sendStopSendingForbidden h => simp [outcomes, h]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- What every reachable receiving part satisfies:
    * no byte beyond the credit we advertised has been accepted (§4.1, line
      1368 — this is theorem (b));
    * nothing at or beyond a known final size has been accepted (§4.5, line
      1520);
    * outside "Recv" the final size is known (§4.5, line 1493: "An endpoint will
      know the final size for a stream when the receiving part of the stream
      enters the "Size Known" or "Reset Recvd" state"). -/
def Inv (s : State) : Prop :=
  s.highest ≤ s.maxData ∧
  (∀ f, s.finalSize = some f → s.highest ≤ f) ∧
  (s.phase.isRecv = false → s.finalSize.isSome)

theorem init_inv (id : StreamId) (role : Role) (m : Nat) : Inv (init id role m) := by
  refine ⟨Nat.zero_le _, ?_, ?_⟩ <;> simp [init, Phase.isRecv]

/-! ### Reading the two "final size" guards -/

/-- If a STREAM frame ending at `e` is accepted while the final size `f` is
    already known, then `e ≤ f`, and if it carries a FIN then `e = f`. -/
theorem le_of_finalSizeViolation_false {s : State} {e : Nat} {fin : Bool} {f : Nat}
    (hf : s.finalSize = some f) (h : finalSizeViolation s e fin = false) :
    e ≤ f ∧ (fin = true → e = f) := by
  simp only [finalSizeViolation, hf, Bool.or_eq_false_iff] at h
  obtain ⟨-, h2⟩ := h
  simp only [decide_eq_false_iff_not, Nat.not_lt, Bool.and_eq_false_iff,
    Bool.not_eq_eq_eq_not] at h2
  refine ⟨h2.1, fun hfin => ?_⟩
  rcases h2.2 with h3 | h3
  · exact absurd hfin (by simp [h3])
  · simpa using h3

/-- A FIN below the highest offset already received is a final size error, so if
    the frame is accepted its end is at least the highest offset. -/
theorem ge_of_finalSizeViolation_false {s : State} {e : Nat}
    (h : finalSizeViolation s e true = false) : s.highest ≤ e := by
  simp only [finalSizeViolation, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.not_lt] at h
  rcases h.1 with h1 | h1
  · exact absurd h1 (by simp)
  · exact h1

theorem eq_of_resetFinalSizeViolation_false {s : State} {fs f : Nat}
    (hf : s.finalSize = some f) (h : resetFinalSizeViolation s fs = false) : fs = f := by
  simp only [resetFinalSizeViolation, hf, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not,
    Bool.not_false, decide_eq_true_eq] at h
  exact h.2

theorem highest_le_of_resetFinalSizeViolation_false {s : State} {fs : Nat}
    (h : resetFinalSizeViolation s fs = false) : s.highest ≤ fs := by
  simp only [resetFinalSizeViolation, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_lt] at h
  exact h.1

/-- Accepting a STREAM frame preserves the invariant. -/
theorem accept_inv {s : State} {offset len : Nat} {fin : Bool}
    (hi : Inv s) (h2 : offset + len ≤ s.maxData)
    (h3 : finalSizeViolation s (offset + len) fin = false) :
    Inv (accept s offset len fin) := by
  obtain ⟨i1, i2, i3⟩ := hi
  have hfin : (accept s offset len fin).finalSize =
      (if fin then some (offset + len) else s.finalSize) := rfl
  have hhi : (accept s offset len fin).highest = max s.highest (offset + len) := rfl
  have hmd : (accept s offset len fin).maxData = s.maxData := rfl
  have hph : (accept s offset len fin).phase =
      s.phase.afterData fin (accept s offset len fin).complete := rfl
  refine ⟨by rw [hhi, hmd]; omega, ?_, ?_⟩
  · intro f hf
    rw [hfin] at hf
    rw [hhi]
    cases fin with
    | true =>
      simp at hf
      have h5 := ge_of_finalSizeViolation_false h3
      omega
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hf
      have hle : s.highest ≤ f := i2 f hf
      have h6 := (le_of_finalSizeViolation_false hf h3).1
      omega
  · intro hne
    rw [hfin]
    cases fin with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [hph] at hne
      by_cases hc : (accept s offset len false).complete = true
      · have hsome : (accept s offset len false).finalSize.isSome = true := by
          simp only [State.complete] at hc
          revert hc
          cases hff : (accept s offset len false).finalSize <;> simp
        rw [hfin] at hsome
        simpa using hsome
      · simp only [Bool.not_eq_true] at hc
        rw [hc] at hne
        cases hp : s.phase <;> rw [hp] at hne <;> simp_all [Phase.afterData, Phase.isRecv]

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨h1, h2, h3⟩ := hi
  cases h with
  | streamFinalSizeIgnored => exact ⟨h1, h2, h3⟩
  | resetFinalSizeIgnored => exact ⟨h1, h2, h3⟩
  | resetSuppressed => exact ⟨h1, h2, h3⟩
  | blocked => exact ⟨h1, h2, h3⟩
  | abortRead => exact ⟨h1, h2, h3⟩
  | abortReadLate => exact ⟨h1, h2, h3⟩
  | sendStopSending => exact ⟨h1, h2, h3⟩
  | @sendMaxStreamData v => exact ⟨by simp only; omega, h2, h3⟩
  | @read len hc =>
    refine ⟨h1, h2, ?_⟩
    intro hr
    simp only at hr ⊢
    by_cases hd : (s.phase.isDataRecvd && decide (s.finalSize = some (s.read + len))) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
      simp [hd.2]
    · simp only [Bool.not_eq_true] at hd
      rw [hd] at hr
      simp only [Bool.false_eq_true, ite_false] at hr
      exact h3 hr
  | @readReset hc =>
    refine ⟨h1, h2, fun _ => h3 ?_⟩
    cases hp : s.phase <;> simp_all [Phase.isResetRecvd, Phase.isRecv]
  | @streamOk offset len fin k1 k2 k3 =>
    simp only [decide_eq_false_iff_not, Nat.not_lt] at k2
    exact accept_inv ⟨h1, h2, h3⟩ k2 k3
  | @streamResetComplete offset len fin k1 k2 k3 k4 =>
    simp only [decide_eq_false_iff_not, Nat.not_lt] at k2
    obtain ⟨i1, i2, i3⟩ := accept_inv ⟨h1, h2, h3⟩ k2 k3
    refine ⟨i1, i2, fun _ => ?_⟩
    simp only [Bool.and_eq_true, State.complete] at k4
    have := k4.2
    revert this
    cases hff : (accept s offset len fin).finalSize <;> simp
  | @resetOk code fs k1 k2 k3 k4 =>
    simp only [decide_eq_false_iff_not, Nat.not_lt] at k2
    refine ⟨by simp only; omega, ?_, by simp⟩
    intro f hf
    simp only [Option.some.injEq] at hf
    simp only
    omega
  | @resetAfterData code fs k1 k2 k3 k4 =>
    refine ⟨h1, ?_, by simp⟩
    intro f hf
    simp only [Option.some.injEq] at hf
    subst hf
    simp only
    exact highest_le_of_resetFinalSizeViolation_false k3

/-! ## 6. Send side

§3.3, lines 1120–1126: the receiving part governs exactly MAX_STREAM_DATA and
STOP_SENDING. -/

def MaySend (s : State) : Frame → Prop
  -- MAX_STREAM_DATA is *not* constrained here: §3.3, line 1156 and §13.3,
  -- line 5393 say only when it SHOULD stop being sent (`RecommendedSend`), and
  -- §13.3, line 5390 requires a lost one to be re-sent.
  | .stopSending id code => if id = s.id.val then maySendStopSending s code = true else True
  | _ => True

def maySend (s : State) : Frame → Bool
  | .stopSending id code => if id = s.id.val then maySendStopSending s code else true
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp only [maySend, MaySend] <;> repeat' split
  all_goals simp

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

/-! ## 8. Named theorems -/

/-! ### The recommendation of §4.5

§4.5, line 1517: "If a RESET_STREAM or STREAM frame is received indicating a
change in the final size for the stream, an endpoint SHOULD respond with a
FINAL_SIZE_ERROR error"; line 1520: "A receiver SHOULD treat receipt of data at
or beyond the final size as a FINAL_SIZE_ERROR error, even after a stream is
closed"; line 1522: "Generating these errors is not mandatory, because requiring
that an endpoint generate these errors also means that the endpoint needs to
maintain the final size state for closed streams."

Both are SHOULDs and neither is restricted to a closed stream, so `Step` permits
either behaviour in every state and no conforming implementation is rejected for
declining the advice.  `Recommended` records which outcome the text asks for:
carrying on as if nothing were wrong is not recommended when the final size is
violated. -/
def Recommended (s : State) : Event → Out → Prop
  | .recvStream offset len fin, .ok _ _ => finalSizeViolation s (offset + len) fin = false
  | .recvResetStream _ fs, .ok _ _ => resetFinalSizeViolation s fs = false
  | _, _ => True

/-- The reference implementation takes the advice: FINAL_SIZE_ERROR is the first
    outcome, so `component.step` raises it. -/
theorem step_recommended (s : State) (e : Event) : Recommended s e (component.step s e) := by
  cases e with
  | recvStream offset len fin =>
    by_cases c3 : finalSizeViolation s (offset + len) fin = true
    · by_cases c1 : decide (maxOffset < offset + len) = true
      · have h : component.step s (.recvStream offset len fin) = .error .frameEncodingError := by
          simp [Component.step, component, outcomes, c1, c3]
        rw [h]; trivial
      · by_cases c2 : decide (s.maxData < offset + len) = true
        · have h : component.step s (.recvStream offset len fin) = .error .flowControlError := by
            simp [Component.step, component, outcomes, c1, c2, c3]
          rw [h]; trivial
        · have h : component.step s (.recvStream offset len fin) = .error .finalSizeError := by
            simp [Component.step, component, outcomes, c1, c2, c3]
          rw [h]; trivial
    · cases hh : component.step s (.recvStream offset len fin) with
      | error c => trivial
      | drop => trivial
      | ok s' fx => exact Bool.eq_false_iff.mpr c3
  | recvResetStream code fs =>
    by_cases c3 : resetFinalSizeViolation s fs = true
    · by_cases c1 : decide (maxOffset < fs) = true
      · have h : component.step s (.recvResetStream code fs) = .error .frameEncodingError := by
          simp [Component.step, component, outcomes, c1, c3]
        rw [h]; trivial
      · by_cases c2 : decide (s.maxData < fs) = true
        · have h : component.step s (.recvResetStream code fs) = .error .flowControlError := by
            simp [Component.step, component, outcomes, c1, c2, c3]
          rw [h]; trivial
        · have h : component.step s (.recvResetStream code fs) = .error .finalSizeError := by
            simp [Component.step, component, outcomes, c1, c2, c3]
          rw [h]; trivial
    · cases hh : component.step s (.recvResetStream code fs) with
      | error c => trivial
      | drop => trivial
      | ok s' fx => exact Bool.eq_false_iff.mpr c3
  | recvStreamDataBlocked _ => trivial
  | appRead _ => trivial
  | appReadReset => trivial
  | appAbortRead _ => trivial
  | sentMaxStreamData _ => trivial
  | sentStopSending _ => trivial

/-- Declining the advice is the only thing `Step` adds: whenever a permitted
    outcome is not the recommended one, FINAL_SIZE_ERROR was permitted too. -/
theorem error_permitted_of_not_recommended {s : State} {e : Event} {o : Out}
    (h : Step s e o) (hr : ¬ Recommended s e o) : Step s e (.error .finalSizeError) := by
  cases h with
  | streamOk h1 h2 h3 => exact absurd h3 (by simpa [Recommended] using hr)
  | streamResetComplete h1 h2 h3 _ => exact absurd h3 (by simpa [Recommended] using hr)
  | streamFinalSizeIgnored h1 h2 h3 => exact .streamFinalSize h3
  | resetOk h1 h2 h3 _ => exact absurd h3 (by simpa [Recommended] using hr)
  | resetAfterData h1 h2 h3 _ => exact absurd h3 (by simpa [Recommended] using hr)
  | resetSuppressed h1 h2 h3 _ => exact absurd h3 (by simpa [Recommended] using hr)
  | resetFinalSizeIgnored h1 h2 h3 => exact .resetFinalSize h3
  | blocked => exact absurd trivial hr
  | blockedFlowControl _ => exact absurd trivial hr
  | read _ => exact absurd trivial hr
  | readRefused _ => exact absurd trivial hr
  | readReset _ => exact absurd trivial hr
  | readResetRefused _ => exact absurd trivial hr
  | abortRead _ => exact absurd trivial hr
  | abortReadLate _ => exact absurd trivial hr
  | sendMaxStreamData => exact absurd trivial hr
  | sendStopSending _ => exact absurd trivial hr
  | sendStopSendingForbidden _ => exact absurd trivial hr
  | streamTooLarge₁ _ => exact absurd trivial hr
  | streamTooLarge₂ _ => exact absurd trivial hr
  | streamFlowControl _ _ => exact absurd trivial hr
  | streamFinalSize _ => exact absurd trivial hr
  | resetTooLarge₁ _ => exact absurd trivial hr
  | resetTooLarge₂ _ => exact absurd trivial hr
  | resetFlowControl _ _ => exact absurd trivial hr
  | resetFinalSize _ => exact absurd trivial hr

/-! ### The recommendations of §3.3 and §13.3 about *sending*

§3.3, line 1156: "The receiver only sends MAX_STREAM_DATA in the "Recv" state."
§13.3, line 5393 restates it as advice: "An endpoint SHOULD stop sending
MAX_STREAM_DATA frames when the receiving part of the stream enters a "Size
Known" or "Reset Recvd" state."  Neither sentence forbids the frame, and the
text expects it to keep arriving: §13.3, line 5390 has "an updated value is sent
when the packet containing the most recent MAX_STREAM_DATA frame for a stream is
lost", and §3.1, line 970 says "MAX_STREAM_DATA frames might be received until
the peer receives the final stream offset."  So `MaySend` permits the frame in
every phase — in particular the retransmission of one already sent — and the
advice lives here. -/
def RecommendedSend (s : State) : Frame → Prop
  | .maxStreamData id v => if id = s.id.val then recommendedMaxStreamData s v = true else True
  -- §3.5, line 1269: "STOP_SENDING SHOULD only be sent for a stream that has
  -- not been reset by the peer."  This one is also enforced by `MaySend`; see
  -- the NOTES.
  | .stopSending id code => if id = s.id.val then maySendStopSending s code = true else True
  | _ => True

def recommendedSend (s : State) : Frame → Bool
  | .maxStreamData id v => if id = s.id.val then recommendedMaxStreamData s v else true
  | .stopSending id code => if id = s.id.val then maySendStopSending s code else true
  | _ => true

theorem recommendedSend_iff (s : State) (f : Frame) :
    recommendedSend s f = true ↔ RecommendedSend s f := by
  cases f <;> simp only [recommendedSend, RecommendedSend] <;> repeat' split
  all_goals simp

/-- Advice is never stricter than permission: a frame the text recommends
    sending is one the text permits sending. -/
theorem maySend_of_recommendedSend {s : State} {f : Frame} (h : recommendedSend s f = true) :
    maySend s f = true := by
  cases f <;> simp_all [recommendedSend, maySend]

/-- §3.3, line 1156 / §13.3, line 5393 as a statement about the phase: a
    MAX_STREAM_DATA for this stream is recommended only in "Recv". -/
theorem maxStreamData_recommended_only_in_recv {s : State} {v : Nat}
    (h : recommendedSend s (.maxStreamData s.id.val v) = true) : s.phase = .recv := by
  simp only [recommendedSend, reduceIte, recommendedMaxStreamData] at h
  cases hp : s.phase <;> simp_all [Phase.isRecv]

/-- …but it is never *forbidden*: a MAX_STREAM_DATA may be re-sent in any phase
    (§13.3, line 5390), and doing so still raises the advertised limit. -/
theorem maxStreamData_always_permitted (s : State) (v : Nat) : maySend s (.maxStreamData s.id.val v) = true :=
  rfl

/-- **(a) The final size is immutable** (§4.5, line 1517: "Once a final size for
    a stream is known, it cannot change"). -/
theorem finalSize_immutable {s s' : State} {e : Event} {fx : List Effect} {f : Nat}
    (h : Step s e (.ok s' fx)) (hf : s.finalSize = some f) : s'.finalSize = some f := by
  cases h with
  | @streamOk offset len fin k1 k2 k3 =>
    show (if fin then some (offset + len) else s.finalSize) = some f
    cases fin with
    | false => simpa using hf
    | true =>
      have := (le_of_finalSizeViolation_false hf k3).2 rfl
      simp [this]
  | @streamResetComplete offset len fin k1 k2 k3 k4 =>
    show (if fin then some (offset + len) else s.finalSize) = some f
    cases fin with
    | false => simpa using hf
    | true =>
      have := (le_of_finalSizeViolation_false hf k3).2 rfl
      simp [this]
  | @resetOk code fs k1 k2 k3 k4 =>
    simp [eq_of_resetFinalSizeViolation_false hf k3]
  | @resetAfterData code fs k1 k2 k3 k4 =>
    simp [eq_of_resetFinalSizeViolation_false hf k3]
  | streamFinalSizeIgnored => exact hf
  | resetFinalSizeIgnored => exact hf
  | resetSuppressed => exact hf
  | blocked => exact hf
  | read => exact hf
  | readReset => exact hf
  | abortRead => exact hf
  | abortReadLate => exact hf
  | sendMaxStreamData => exact hf
  | sendStopSending => exact hf

/-- **(b) No data beyond the advertised stream credit.**  §4.1, line 1368: "A
    receiver MUST close the connection with a FLOW_CONTROL_ERROR error if the
    sender violates the advertised connection or stream data limits."  In every
    reachable state the credit consumed is within the credit advertised. -/
theorem highest_le_maxData {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    s.highest ≤ s.maxData :=
  (component.inv_of_reachable h0 h).1

/-- The same, one step at a time: a STREAM frame that changes the state was
    within the advertised limit. -/
theorem accepted_within_credit {s s' : State} {offset len : Nat} {fin : Bool}
    {fx : List Effect} (h : Step s (.recvStream offset len fin) (.ok s' fx)) :
    offset + len ≤ s.maxData ∨ s' = s := by
  cases h with
  | streamFinalSizeIgnored => exact Or.inr rfl
  | streamOk _ k2 _ => exact Or.inl (by simpa using k2)
  | streamResetComplete _ k2 _ _ => exact Or.inl (by simpa using k2)

/-- **(c) The terminal states absorb** — the *phase* does.  §3.2, lines 1102 and
    1135: "Data Read" and "Reset Read" are terminal.  Late STREAM frames are
    still counted for flow control (§3.5, line 1250: "STREAM frames received
    after sending a STOP_SENDING frame are still counted toward connection and
    stream flow control"), and a MAX_STREAM_DATA may still be re-sent (§13.3,
    line 5390), so the rest of the state can still move; only the state machine
    cannot leave. -/
theorem terminal_absorbing {s s' : State} {e : Event} {fx : List Effect}
    (ht : s.phase.terminal = true) (h : Step s e (.ok s' fx)) : s'.phase = s.phase := by
  have hr : s.phase.isRecv = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.isRecv]
  have hd : s.phase.isDataRecvd = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.isDataRecvd]
  have hrr : s.phase.isResetRecvd = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.isResetRecvd]
  have hba : s.phase.beforeAllData = false := by
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.beforeAllData]
  cases h with
  | streamFinalSizeIgnored => rfl
  | resetFinalSizeIgnored => rfl
  | resetSuppressed => rfl
  | blocked => rfl
  | abortRead h4 => exact absurd h4 (by simp [hba])
  | abortReadLate => rfl
  | sendStopSending => rfl
  | sendMaxStreamData => rfl
  | @read len hc => simp only [hd, Bool.false_and, Bool.false_eq_true, ite_false]
  | readReset h4 => exact absurd h4 (by simp [hrr])
  | @streamOk offset len fin _ _ _ =>
    show s.phase.afterData _ _ = s.phase
    cases hp : s.phase <;> simp_all [Phase.terminal, Phase.afterData]
  | streamResetComplete _ _ _ h4 => exact absurd h4 (by simp [hrr])
  | resetOk _ _ _ h4 => exact absurd h4 (by simp [hba])
  | resetAfterData _ _ _ h4 => exact absurd h4 (by simp [hd])

/-- The arrows of Figure 3 (§3.2, line 1045). -/
def Arrow : Phase → Phase → Prop
  | .recv, .sizeKnown => True       -- Recv STREAM + FIN
  | .recv, .resetRecvd => True      -- Recv RESET_STREAM
  | .sizeKnown, .dataRecvd => True  -- Recv All Data
  | .sizeKnown, .resetRecvd => True -- Recv RESET_STREAM
  | .dataRecvd, .resetRecvd => True -- Recv RESET_STREAM (optional)
  | .resetRecvd, .dataRecvd => True -- Recv All Data (optional)
  | .dataRecvd, .dataRead => True   -- App Read All Data
  | .resetRecvd, .resetRead => True -- App Read Reset
  | _, _ => False

/-- Reachability along those arrows, in zero or more steps. -/
def Reaches : Phase → Phase → Bool
  | .recv, _ => true
  | .sizeKnown, .recv => false
  | .sizeKnown, _ => true
  | .dataRecvd, p => match p with
      | .dataRecvd | .dataRead | .resetRecvd | .resetRead => true
      | _ => false
  | .resetRecvd, p => match p with
      | .dataRecvd | .dataRead | .resetRecvd | .resetRead => true
      | _ => false
  | .dataRead, .dataRead => true
  | .dataRead, _ => false
  | .resetRead, .resetRead => true
  | .resetRead, _ => false

theorem arrow_reaches {p q : Phase} (h : Arrow p q) : Reaches p q = true := by
  cases p <;> cases q <;> simp_all [Arrow, Reaches]

theorem afterData_reaches (p : Phase) (fin c : Bool) : Reaches p (p.afterData fin c) = true := by
  cases p <;> cases fin <;> cases c <;> rfl

/-- **(d, second half) No step leaves the diagram.** -/
theorem step_follows_diagram {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : Reaches s.phase s'.phase = true := by
  cases h with
  | streamFinalSizeIgnored => cases hp : s.phase <;> simp [Reaches]
  | resetFinalSizeIgnored => cases hp : s.phase <;> simp [Reaches]
  | resetSuppressed => cases hp : s.phase <;> simp [Reaches]
  | blocked => cases hp : s.phase <;> simp [Reaches]
  | abortRead => cases hp : s.phase <;> simp [Reaches]
  | abortReadLate => cases hp : s.phase <;> simp [Reaches]
  | sendStopSending => cases hp : s.phase <;> simp [Reaches]
  | sendMaxStreamData => cases hp : s.phase <;> simp [Reaches]
  | @streamOk offset len fin _ _ _ =>
    show Reaches s.phase (s.phase.afterData _ _) = true
    exact afterData_reaches _ _ _
  | @streamResetComplete offset len fin _ _ _ h4 =>
    simp only [Bool.and_eq_true] at h4
    have hp : s.phase = .resetRecvd := by
      cases hq : s.phase <;> simp_all [Phase.isResetRecvd]
    simp only [hp]
    rfl
  | @resetOk code fs _ _ _ h4 =>
    cases hq : s.phase <;> simp_all [Phase.beforeAllData, Reaches]
  | @resetAfterData code fs _ _ _ h4 =>
    have hp : s.phase = .dataRecvd := by cases hq : s.phase <;> simp_all [Phase.isDataRecvd]
    simp only [hp]
    rfl
  | @read len hc =>
    by_cases hd : (s.phase.isDataRecvd && decide (s.finalSize = some (s.read + len))) = true
    · have hp : s.phase = .dataRecvd := by
        simp only [Bool.and_eq_true] at hd
        cases hq : s.phase <;> simp_all [Phase.isDataRecvd]
      simp only [hd]
      simp only [hp]
      rfl
    · simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.false_eq_true, ite_false]
      cases hq : s.phase <;> simp [Reaches]
  | @readReset hc =>
    have hp : s.phase = .resetRecvd := by cases hq : s.phase <;> simp_all [Phase.isResetRecvd]
    simp only [hp]
    rfl

/-! ## 9. Examples: every arrow of Figure 3 (§3.2) -/

private def r0 : State := init ⟨1⟩ .client 100

-- o → Recv (§3.2, line 1052).
example : r0.phase = .recv := rfl

-- Recv → Size Known: "Recv STREAM + FIN" — the FIN fixes the final size, but a
-- hole at [0,5) means the data is not all there yet.
private def rSize : State :=
  { r0 with phase := .sizeKnown, highest := 10, ranges := [(5, 10)], finalSize := some 10 }

example : component.step r0 (.recvStream 5 5 true) = .ok rSize [] := by decide

-- Size Known → Data Recvd: "Recv All Data" (the hole is filled).
private def rData : State :=
  { r0 with phase := .dataRecvd, highest := 10, ranges := [(0, 10)], finalSize := some 10 }

example : component.step rSize (.recvStream 0 5 false) =
    .ok rData [.dataAvailable 10, .allDataReceived 10] := by decide

-- §3.2, line 1096: "This might happen as a result of receiving the same STREAM
-- frame that causes the transition to "Size Known"" — Recv → Data Recvd at once.
example : component.step r0 (.recvStream 0 10 true) =
    .ok rData [.dataAvailable 10, .allDataReceived 10] := by decide

-- Recv → Reset Recvd: "Recv RESET_STREAM" (§3.2, line 1105).
example : component.step r0 (.recvResetStream 7 4) =
    .ok { r0 with phase := .resetRecvd, highest := 4, finalSize := some 4 }
         [.streamReset 7 4] := by decide

-- Size Known → Reset Recvd, with the same final size (§4.5, line 1517).
example : component.step rSize (.recvResetStream 7 10) =
    .ok { rSize with phase := .resetRecvd } [.streamReset 7 10] := by decide

-- Data Recvd → Reset Recvd, "Recv RESET_STREAM (optional)": both suppressing
-- the signal and acting on it are permitted (§3.2, line 1127).
example : component.accepts rData (.recvResetStream 7 10) (.ok rData []) = true := by decide
example : component.accepts rData (.recvResetStream 7 10)
    (.ok { rData with phase := .resetRecvd } [.streamReset 7 10]) = true := by decide

-- Reset Recvd → Data Recvd, "Recv All Data (optional)" (§3.2, line 1111): the
-- rest of the data arrives after the RESET_STREAM.
private def rReset : State :=
  { r0 with phase := .resetRecvd, highest := 10, ranges := [(5, 10)], finalSize := some 10 }

example : component.accepts rReset (.recvStream 0 5 false)
    (.ok { rReset with ranges := [(0, 10)] } [.dataAvailable 10]) = true := by decide
example : component.accepts rReset (.recvStream 0 5 false)
    (.ok { rReset with phase := .dataRecvd, ranges := [(0, 10)] }
         [.dataAvailable 10, .allDataReceived 10]) = true := by decide

-- Data Recvd → Data Read: "App Read All Data" (§3.2, line 1101).
example : component.step rData (.appRead 10) =
    .ok { rData with phase := .dataRead, read := 10 } [] := by decide

-- Reset Recvd → Reset Read: "App Read Reset" (§3.2, line 1135).
example : component.step rReset .appReadReset =
    .ok { rReset with phase := .resetRead } [] := by decide

-- §2.2, line 749: a duplicate STREAM frame is accepted and changes nothing …
example : component.step rData (.recvStream 0 10 true) = .ok rData [] := by decide
-- … and so is an overlapping one.
example : component.step rData (.recvStream 3 4 false) = .ok rData [] := by decide

-- §4.1, line 1368: data beyond the advertised limit is a FLOW_CONTROL_ERROR.
example : component.step r0 (.recvStream 90 20 false) = .error .flowControlError := by decide
example : component.step r0 (.recvResetStream 1 101) = .error .flowControlError := by decide

-- §4.5, line 1517: a changed final size is a FINAL_SIZE_ERROR …
example : component.step rSize (.recvStream 0 9 true) = .error .finalSizeError := by decide
example : component.step rSize (.recvResetStream 1 9) = .error .finalSizeError := by decide
-- … as is data beyond a known final size …
example : component.step rSize (.recvStream 10 1 false) = .error .finalSizeError := by decide
-- … and a FIN below data already received.
example : component.step rSize (.recvStream 0 1 true) = .error .finalSizeError := by decide
-- … including when no final size is known yet and the FIN is below data already
-- received (the reading of NOTES): the error, or ignoring the frame, in the
-- live "Recv" state.
private def rGap : State := { r0 with highest := 10, ranges := [(0, 10)] }
example : component.step rGap (.recvStream 0 5 true) = .error .finalSizeError := by decide
example : component.accepts rGap (.recvStream 0 5 true) (.ok rGap []) = true := by decide

-- §4.5, line 1522: "Generating these errors is not mandatory", in any state —
-- ignoring the frame is permitted, and then it has no effect whatever, so the
-- final size cannot move and nothing beyond it is accounted for.
example : component.accepts rSize (.recvStream 0 9 true) (.ok rSize []) = true := by decide
example : component.accepts rSize (.recvResetStream 1 9) (.ok rSize []) = true := by decide
example : component.accepts rSize (.recvStream 10 1 false) (.ok rSize []) = true := by decide
example : component.accepts { rData with phase := .dataRead, read := 10 }
    (.recvStream 10 1 false) (.ok { rData with phase := .dataRead, read := 10 } []) = true := by
  decide
-- … but it is not what §4.5 recommends, and the recommended outcome is always
-- available.
example : ¬ Recommended rSize (.recvStream 0 9 true) (.ok rSize []) := by
  show ¬ (finalSizeViolation rSize (0 + 9) true = false)
  decide
example : component.accepts rSize (.recvStream 0 9 true) (.error .finalSizeError) = true := by
  decide

-- §3.3, line 1157 with §13.3: an exact repeat of a STOP_SENDING we already sent
-- is still permitted (a lost packet is retransmitted unchanged).
example :
    component.maySend ((component.step rSize (.sentStopSending 9)).next rSize)
      (.stopSending 1 9) = true := by
  decide

-- §19.8, line 7686: an offset beyond 2^62-1 is FRAME_ENCODING_ERROR or
-- FLOW_CONTROL_ERROR.
example : component.accepts r0 (.recvStream (2 ^ 62) 1 false) (.error .frameEncodingError) = true := by
  decide
example : component.accepts r0 (.recvStream (2 ^ 62) 1 false) (.error .flowControlError) = true := by
  decide

-- §3.3, line 1156: MAX_STREAM_DATA is *recommended* only in "Recv" …
example : recommendedSend r0 (.maxStreamData 1 200) = true := by decide
example : recommendedSend rSize (.maxStreamData 1 200) = false := by decide
-- … but it is never forbidden (§13.3, line 5390: a lost MAX_STREAM_DATA is
-- re-sent; §3.1, line 970: such frames arrive after the FIN).  Regression for
-- review finding W2-2: all four of these were `false`/`.drop` before.
example : component.maySend r0 (.maxStreamData 1 200) = true := by decide
example : component.maySend rSize (.maxStreamData 1 200) = true := by decide
example : component.maySend rReset (.maxStreamData 1 200) = true := by decide
example : component.step rSize (.sentMaxStreamData 200) =
    .ok { rSize with maxData := 200 } [] := by decide
example : component.accepts rSize (.sentMaxStreamData 200)
    (.ok { rSize with maxData := 200 } []) = true := by decide
-- … and §3.3, line 1157: STOP_SENDING in any state where no RESET_STREAM has
-- been received.
example : component.maySend rSize (.stopSending 1 3) = true := by decide
example : component.maySend rReset (.stopSending 1 3) = false := by decide
-- A frame for another stream is not this component's business.
example : component.maySend rReset (.stopSending 5 3) = true := by decide

-- §3.5, line 1243: aborting the read asks for a STOP_SENDING …
example : component.step r0 (.appAbortRead 9) =
    .ok { r0 with stopSending := some 9 } [.stopSendingRequested 9] := by decide
-- … but §3.5, line 1273: after a RESET_STREAM it is unnecessary.
example : component.step rReset (.appAbortRead 9) = .ok rReset [] := by decide

-- Review finding W2-1: when a frame breaks *both* §4.1, line 1368 (the stream
-- credit) and §4.5, line 1517 (the known final size), the text gives no
-- precedence, so both error codes are permitted.  `rSize` has finalSize = 10
-- and maxData = 100; a Final Size of 150 breaks both.  ngtcp2 checks the final
-- size first (`conn_recv_reset_stream`), so before this fix the differential
-- run reported a false violation.
example : component.accepts rSize (.recvResetStream 3 150)
    (.error .flowControlError) = true := by decide
example : component.accepts rSize (.recvResetStream 3 150)
    (.error .finalSizeError) = true := by decide
-- Nothing else is permitted: §4.1, line 1368 is a MUST, so ignoring is not.
example : component.accepts rSize (.recvResetStream 3 150) (.ok rSize []) = false := by decide
-- The same for a STREAM frame, and for a Final Size beyond 2^62-1 as well.
example : component.step rSize (.recvStream 0 150 true) = .error .flowControlError := by decide
example : component.accepts rSize (.recvStream 0 150 true)
    (.error .finalSizeError) = true := by decide
example : component.accepts rSize (.recvStream 0 (2 ^ 62) true)
    (.error .finalSizeError) = true := by decide
example : component.accepts rSize (.recvResetStream 3 (2 ^ 62))
    (.error .finalSizeError) = true := by decide
-- When only one rule is broken the other error is *not* permitted.
example : component.accepts r0 (.recvResetStream 3 150) (.error .finalSizeError) = false := by
  decide
example : component.accepts rSize (.recvResetStream 3 9) (.error .flowControlError) = false := by
  decide

-- Review finding W2-3: STREAM_DATA_BLOCKED.  Accepting it and doing nothing is
-- always permitted (§3.2, lines 1082 and 1098) …
example : component.step r0 (.recvStreamDataBlocked 10000) = .ok r0 [] := by decide
-- … and, when the reported blocking offset is beyond the limit we advertised,
-- §4.1, line 1368's FLOW_CONTROL_ERROR is an additional permitted outcome
-- (ngtcp2 raises exactly this).
example : component.accepts r0 (.recvStreamDataBlocked 10000)
    (.error .flowControlError) = true := by decide
example : component.accepts r0 (.recvStreamDataBlocked 50)
    (.error .flowControlError) = false := by decide
-- The text attaches no other error to the frame; see the NOTES for the
-- FINAL_SIZE_ERROR ngtcp2 raises in "Size Known", which is an expected
-- differential mismatch rather than a model defect.
example : component.accepts rSize (.recvStreamDataBlocked 50)
    (.error .finalSizeError) = false := by decide
example : component.accepts r0 (.recvStreamDataBlocked (2 ^ 62))
    (.error .frameEncodingError) = false := by decide

-- Following an implementation whose state we cannot see.
example : component.track r0 (.recvStream 5 5 true) (.ok []) = some rSize := by rfl

/-! ## 10. Coverage and notes

Assigned text for this file: §2.2, §2.4 (receiving operations), §3.2, the
receiving half of §3.3 and §3.5, and the stream-level parts of §4.1/§4.4/§4.5.

Citations name the line on which the quoted text begins.  Where a sentence's
first word dangles at the end of the previous line, the citation is the line the
quotation itself starts on (§3.3, lines 1150 and 1157 are the two cases here).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §2.2 (739) | endpoints MUST be able to deliver an ordered byte-stream | `State.recvd`, `Effect.dataAvailable` |
| §2.2 (744) | implementations MAY deliver data out of order | out of scope: an API choice; `Step.read` models in-order delivery only (the conservative reading) |
| §2.2 (749) | data already received can be discarded; duplicates accepted | `addRange`/`insertRange`, idempotence examples |
| §2.2 (750) | data at an offset MUST NOT change; MAY be PROTOCOL_VIOLATION | out of scope: byte contents are not modelled (NOTES) |
| §2.4 (814) | the application reads data | `Step.read` / `Step.readRefused` |
| §2.4 (816) | abort reading, possibly sending STOP_SENDING | `Step.abortRead` / `Step.abortReadLate` |
| §3.2 (1047) | the receiving part is created by STREAM/STREAM_DATA_BLOCKED/RESET_STREAM | out of scope: WP9 (stream table) |
| §3.2 (1052) | the initial state for the receiving part is "Recv" | `init` |
| §3.2 (1078) | before a stream is created, all lower-numbered streams of the type MUST be created | out of scope: WP9 |
| §3.2 (1082) | in "Recv" the endpoint receives STREAM and STREAM_DATA_BLOCKED | `Step.streamOk`, `Step.blocked` |
| §3.2 (1089) | STREAM with FIN → the final size is known → "Size Known" | `Phase.afterData`, `accept` |
| §3.2 (1095) | all data received → "Data Recvd"; may happen on the same frame | `State.complete`, `Phase.afterData` |
| §3.2 (1098) | after all data, STREAM/STREAM_DATA_BLOCKED can be discarded | `Phase.afterData` catch-all, `Step.blocked` (state unchanged bar flow control) |
| §3.2 (1101) | delivered to the application → "Data Read", terminal | `Step.read`, `terminal_absorbing` |
| §3.2 (1105) | RESET_STREAM in "Recv"/"Size Known" → "Reset Recvd" | `Step.resetOk` |
| §3.2 (1109) | RESET_STREAM may arrive in "Data Recvd" | `Step.resetAfterData`, `Step.resetSuppressed` |
| §3.2 (1111) | data may arrive in "Reset Recvd"; free to manage as it chooses | `Step.streamResetComplete` |
| §3.2 (1127) | MAY interrupt delivery and signal the reset; MAY suppress it | `Step.resetAfterData` / `Step.resetSuppressed` (two outcomes) |
| §3.2 (1129) | a suppressed RESET_STREAM leaves the part in "Data Recvd" | `Step.resetSuppressed` |
| §3.2 (1135) | the application takes the reset signal → "Reset Read", terminal | `Step.readReset`, `terminal_absorbing` |
| §3.3 (1150) | a receiver could receive any of the three frames in any state | every phase has a `recvStream`/`recvResetStream`/`blocked` outcome |
| §3.3 (1156) | the receiver only sends MAX_STREAM_DATA in "Recv" | `RecommendedSend`, `maxStreamData_recommended_only_in_recv` — advice, not a prohibition (NOTES) |
| §3.3 (1157) | MAY send STOP_SENDING except in "Reset Recvd"/"Reset Read" | `maySendStopSending` |
| §3.5 (1243) | abort reading SHOULD send STOP_SENDING in "Recv"/"Size Known" | `Recommended`-style advice honoured by `Step.abortRead`, which emits `stopSendingRequested` exactly in those phases |
| §3.5 (1250) | STREAM frames after STOP_SENDING still count for flow control | `accept` runs in every phase; `terminal_absorbing` is about the phase only |
| §3.5 (1265) | an endpoint that sent STOP_SENDING MAY ignore the error code of a later RESET_STREAM | permissive, already satisfied: no `Step` constructor reads the code; it is passed to the application in `Effect.streamReset` and never acted on |
| §3.5 (1269) | STOP_SENDING SHOULD only be sent for a stream not reset by the peer | `maySendStopSending`, `RecommendedSend` (NOTES: this SHOULD is also enforced in `MaySend`) |
| §3.5 (1273) | STOP_SENDING is unnecessary outside "Recv"/"Size Known" | `Step.abortReadLate` |
| §4.1 (1330) | senders MUST NOT exceed either limit | receiving side: `Step.streamFlowControl` |
| §4.1 (1349) | MAX_STREAM_DATA advertises a larger limit | `Step.sendMaxStreamData` |
| §4.1 (1364) | a smaller limit is not an error and has no effect | `Step.sendMaxStreamData` uses `max` |
| §4.1 (1368) | violating the advertised limits MUST be FLOW_CONTROL_ERROR | `Step.streamFlowControl`, `Step.resetFlowControl`, `Step.blockedFlowControl`, `highest_le_maxData` |
| §4.4 (1467) | on RESET_STREAM the endpoint tears down state and ignores further data | `Step.resetOk`; further data is still accounted (§3.5, line 1250) |
| §4.4 (1471) | flow control state is kept for the unterminated direction | the two halves are independent components |
| §4.5 (1493) | the final size is known in "Size Known"/"Reset Recvd" | `Inv` third clause |
| §4.5 (1495) | the receiver MUST use the final size for connection-level accounting | `highest` is set to the final size on RESET_STREAM; the connection controller is WP9 |
| §4.5 (1517) | a changed final size SHOULD be FINAL_SIZE_ERROR | `finalSizeViolation`, `resetFinalSizeViolation`, `finalSize_immutable` |
| §4.5 (1520) | data at or beyond the final size SHOULD be FINAL_SIZE_ERROR, even after close | `finalSizeViolation` |
| §4.5 (1522) | generating these errors is not mandatory | `Step.streamFinalSizeIgnored`, `Step.resetFinalSizeIgnored` (every state); `Recommended`, `step_recommended` |
| §13.3 (5390) | a lost MAX_STREAM_DATA is re-sent with an updated value | `MaySend` permits MAX_STREAM_DATA in every phase; `maxStreamData_always_permitted` |
| §13.3 (5393) | SHOULD stop sending MAX_STREAM_DATA after "Size Known"/"Reset Recvd" | `RecommendedSend`, `maxStreamData_recommended_only_in_recv` |
| §19.8 (7686) | offset+length > 2^62-1 MUST be FRAME_ENCODING_ERROR or FLOW_CONTROL_ERROR | `Step.streamTooLarge₁/₂`, `Step.resetTooLarge₁/₂` |
| §19.13 (7881) | Maximum Stream Data is the offset at which the blocking occurred | `Step.blockedFlowControl` compares it with the advertised limit |
| §19.4/19.5/19.8/19.10/19.13 | wrong-direction frames MUST be STREAM_STATE_ERROR | `Spec/Stream.lean` (the composite knows the direction) |

NOTES

* **Offsets and lengths, not bytes.**  A STREAM frame is modelled as
  (offset, length, fin).  Byte contents are not modelled, so §2.2's "The data at
  a given offset MUST NOT change if it is sent multiple times" and the
  PROTOCOL_VIOLATION it permits cannot be expressed here; they are listed as out
  of scope above.
* **Reassembly.**  The assignment allows reassembly to be skipped, but the arrow
  "Recv All Data" needs to know when the stream is complete, so the set of
  received ranges is kept as a canonical ordered list of disjoint intervals
  (`insertRange`).  That is enough to decide completeness exactly, it makes
  duplicate and overlapping frames idempotent, and it never looks at the bytes.
  `State.recvd` reads the contiguous prefix off the head of that list.
* **`.drop` for refused application calls**, as in `Spec/Stream/Send.lean`:
  reading data that has not arrived, or taking a reset signal that was never
  delivered, changes nothing.
* **Which error when several rules are violated at once.**  A RESET_STREAM whose
  Final Size is both beyond the advertised stream credit (§4.1, line 1368) and
  different from a final size already known (§4.5, line 1517) breaks two rules,
  and the text gives no precedence between them: one is a MUST, the other a
  SHOULD, and both are applicable.  `outcomes` therefore lists *every* error the
  text attaches to any rule the frame breaks — FRAME_ENCODING_ERROR and
  FLOW_CONTROL_ERROR from §19.8, line 7686, FLOW_CONTROL_ERROR from §4.1,
  line 1368, FINAL_SIZE_ERROR from §4.5 — with the MUST-error first so that
  `component.step` is unchanged.  This is the same rule WP9 states in its
  NOTES ("Which error when several rules are violated").  ngtcp2 checks the
  final size *before* the flow-control limit in `conn_recv_reset_stream`
  (`lib/ngtcp2_conn.c`, the `SHUT_RD`/`last_offset` test precedes the
  `rx.max_offset` test) and the other way round for STREAM frames, so an
  `if`-chain with a fixed order would report a false violation either way.
  Note that the *non-error* outcomes are not widened: when a MUST-error applies,
  `.ok` is not permitted, so §4.5's "generating these errors is not mandatory"
  never excuses ignoring a flow-control violation.
* **FINAL_SIZE_ERROR is a SHOULD, everywhere.**  §4.5's two sentences —
  "an endpoint SHOULD respond with a FINAL_SIZE_ERROR error" (line 1517) and
  "A receiver SHOULD treat receipt of data at or beyond the final size as a
  FINAL_SIZE_ERROR error, even after a stream is closed" (line 1520) — are both
  SHOULDs, and neither is restricted to a closed stream; line 1522's remark
  about the state commitment for closed streams is the *motivation* for the
  permission, not a condition on it.  So `Step` permits declining in **every**
  receive state (`Step.streamFinalSizeIgnored`, `Step.resetFinalSizeIgnored`),
  the error stays the first element of `outcomes` so `component.step` raises it,
  and the advice itself lives in `Recommended` (`step_recommended`,
  `error_permitted_of_not_recommended`).
* **What "ignored" does**: nothing at all — the outcome is `.ok s []`.  The
  frame is discarded, so no byte at or beyond the final size enters `ranges` or
  `highest`, the final size cannot move (theorem `finalSize_immutable` needs no
  extra hypothesis), and `Inv` is preserved trivially.
* **An ignored, conflicting RESET_STREAM has no effect at all**: neither its
  Final Size nor the reset itself.  The alternative — applying the reset while
  keeping the old final size — would invent a third behaviour that the text
  never describes, and an endpoint that declines to police the final size does so
  (per §4.5's own rationale) because it no longer keeps the stream's state, so it
  has nothing to apply the reset to.  Discarding the whole frame is the simplest
  faithful reading, and it is the one that keeps the final size immutable.
* **A FIN below the highest offset received** is treated as a FINAL_SIZE_ERROR
  (`finalSizeViolation`'s first disjunct).  The text only says "receipt of data
  at or beyond the final size"; receiving the final size *after* the data is the
  same fault observed in the other order, and without this the receiving part
  could end up with `highest > finalSize`.
* **RESET_STREAM sets `highest` to the final size** (§4.5, line 1495: "The
  receiver MUST use the final size of the stream to account for all bytes sent
  on the stream in its connection level flow controller"), which is why a final
  size beyond the advertised limit is a FLOW_CONTROL_ERROR.
* **Where a STREAM frame arrives in "Reset Recvd"** the model offers two
  outcomes when it completes the stream: stay (the data is discarded) or move to
  "Data Recvd" (Figure 3's optional arrow).  They differ in their effects, so
  `Component.track` can still follow an implementation from the outside.
* **STREAM_DATA_BLOCKED: what the text attaches to it, and what it does not.**
  The only error the text names for this frame is §19.13, line 7863's
  STREAM_STATE_ERROR for a send-only stream, which the composite raises
  (`Spec/Stream.lean`).  About its *value* the text says only that the Maximum
  Stream Data field is "the offset of the stream at which the blocking occurred"
  (§19.13, line 7881).  Two readings of §4.1, line 1368 are possible: the narrow
  one, in which "violates the advertised … stream data limits" means sending
  data in excess of them (§4.1, line 1330) and a frame carrying no data can
  never violate them; and the wider one, in which a peer that reports being
  blocked at an offset we never granted has claimed credit beyond the advertised
  limit.  The wider reading is encoded, because it is the only one under which
  the frame has any check at all and because the error is added as an
  *alternative* (`Step.blocked` is still permitted for the same frame), so the
  model stays no stricter than either reading.
  Two things ngtcp2 does with this frame are deliberately **not** encoded, and
  belong on WP13's triage list as expected mismatches:
  (i) `conn_recv_stream_data_blocked` returns FINAL_SIZE_ERROR when the
  receiving part is already `SHUT_RD` (a final size is known) and the reported
  offset is beyond the highest received — §4.5 attaches FINAL_SIZE_ERROR to "a
  RESET_STREAM or STREAM frame" (line 1517) and to "receipt of data" (line
  1520), and a STREAM_DATA_BLOCKED is neither; (ii) it advances `rx.last_offset`
  to the reported offset, spending connection-level credit for data that was
  never received — §4.1, line 1355 defines that sum as "bytes received".
  A value above 2^62-1 is likewise not an error here: the field is a
  variable-length integer (§16, line 5959), so such a frame cannot be decoded,
  and the bound belongs to the frame decoder, not to this state machine.
* **MAX_STREAM_DATA may be sent in any phase.**  §3.3, line 1156 ("The receiver
  only sends MAX_STREAM_DATA in the "Recv" state") is descriptive and §13.3,
  line 5393 restates it as a SHOULD; neither forbids the frame, and §13.3,
  line 5390 positively requires a lost MAX_STREAM_DATA to be re-sent while
  §3.1, line 970 expects such frames to keep arriving until the peer has the
  final offset.  An earlier version of this file had `maySendMaxStreamData =
  phase.isRecv` and `.drop`ped the `sentMaxStreamData` event outside "Recv",
  which rejected a conforming endpoint that retransmits a lost MAX_STREAM_DATA
  after the peer's FIN.  The rule now lives in `RecommendedSend`
  (`maxStreamData_recommended_only_in_recv`), `MaySend` permits the frame
  everywhere (`maxStreamData_always_permitted`) and `Step.sendMaxStreamData`
  raises `maxData` with `max` in every phase — the value may be smaller than the
  current limit, which §4.1, line 1364 says is not an error.
* **§3.5, line 1269's SHOULD is enforced in `MaySend`.**  "STOP_SENDING SHOULD
  only be sent for a stream that has not been reset by the peer" is read
  together with §3.3, line 1157, which grants the permission only "in any state
  where it has not received a RESET_STREAM frame"; the two together are treated
  as a prohibition outside those states.  The sentence is also listed in
  `RecommendedSend` so that the composite can report it as advice if a later
  review prefers the weaker reading.
-/

end Quic.Spec.Stream.Recv
