import QuicModel.Spec.Termination.Basic

/-
  WP6 — Connection termination, part 6: the send side.
  See `Termination/Basic.lean` for the layout of the package.
-/

/-  Part 6: the send side.  -/
namespace Quic.Spec.Termination

/-! ## 6. Send side

### 6.1 Frame level -/

def isConnectionClose : Frame → Bool
  | .connectionClose _ _ _ => true
  | _ => false

/-- §10.2.2, line 4023: "While otherwise identical to the closing state, an
    endpoint in the draining state MUST NOT send any packets"; §10.2, line 3953:
    "Once its closing or draining state ends, an endpoint SHOULD discard all
    connection state", after which there is nothing left to send with.

    Nothing else is constrained frame by frame.  §10.2.1 lines 3963–3967 say
    what a closing endpoint *retains* and *sends* ("In the closing state, an
    endpoint retains only enough information to generate a packet containing a
    CONNECTION_CLOSE frame and to identify packets as belonging to the
    connection.  An endpoint in the closing state sends a packet containing a
    CONNECTION_CLOSE frame in response to any incoming packet that it attributes
    to the connection"), but no sentence forbids other frames travelling with
    it.  The real constraint is on the *packet* — it must contain a
    CONNECTION_CLOSE — and lives in `MaySendPacket`. -/
def MaySend (s : State) (_f : Frame) : Prop :=
  match s.phase with
  | .active | .closing => True
  | .draining | .closed => False

def maySend (s : State) (_f : Frame) : Bool :=
  match s.phase with
  | .active | .closing => true
  | .draining | .closed => false

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases hp : s.phase <;> simp [maySend, MaySend, hp]

/-- §10.2.1, line 3965: "An endpoint in the closing state sends a packet
    *containing a CONNECTION_CLOSE frame* in response to any incoming packet
    that it attributes to the connection."  That is all the text asks of a
    closing packet: it says nothing about the other frames in it, so neither
    does this.  Used by `MaySendPacket`. -/
def closingPacketOk (fs : List Frame) : Bool := fs.any isConnectionClose

/-- Every frame of a packet a closing endpoint may send is a frame `MaySend`
    accepts.  (Since the text forbids no frame in the closing state this is now
    immediate; it is kept because WP12 calls it.) -/
theorem maySend_of_closingPacketOk {s : State} (hp : s.phase = .closing)
    {fs : List Frame} (_h : closingPacketOk fs = true) : ∀ f ∈ fs, MaySend s f := by
  intro f _
  simp [MaySend, hp]

/-! ### 6.2 Packet level (§10.2.1, §10.2.2, §10.2.3, §19.19)

What cannot be said frame by frame: which packet a CONNECTION_CLOSE may travel
in, and what a packet sent from the closing state must contain.  All of it is
`Component.MaySendPacket`.  Handshake confirmation is read from
`State.handshakeConfirmed`, which is a field of its own precisely so that it
survives the move to the closing state, where the CONNECTION_CLOSE is sent. -/

/-- §20.1 APPLICATION_ERROR. -/
def applicationErrorCode : Nat := TransportError.applicationError.code

/-- §10.2.3, line 4084: "A CONNECTION_CLOSE of type 0x1d MUST be replaced by a
    CONNECTION_CLOSE of type 0x1c when sending the frame in Initial or Handshake
    packets."  Line 4095: "Endpoints MUST clear the value of the Reason Phrase
    field and SHOULD use the APPLICATION_ERROR code when converting to a
    CONNECTION_CLOSE of type 0x1c." -/
def convertCloseForHandshake : Frame → Frame
  | .connectionClose _ none _ =>
    .connectionClose applicationErrorCode (some 0) ByteArray.empty
  | f => f

/-- §19.19, line 8187: "The application-specific variant of CONNECTION_CLOSE
    (type 0x1d) can only be sent using 0-RTT or 1-RTT packets; see Section
    12.5." -/
def appCloseAllowedIn : PacketType → Bool
  | .zeroRtt | .oneRtt => true
  | _ => false

/-- One frame against the packet type it would travel in: §19.19 line 8187 and
    §10.2.3 line 4084, the rule for the application variant 0x1d. -/
def appCloseFrameOk (pt : PacketType) : Frame → Bool
  | .connectionClose _ none _ => appCloseAllowedIn pt
  | _ => true

/-- §10.2.3, line 4056: "After the handshake is confirmed (see Section 4.1.2 of
    [QUIC-TLS]), an endpoint MUST send any CONNECTION_CLOSE frames in a 1-RTT
    packet."  Line 4058: "However, prior to confirming the handshake, it is
    possible that more advanced packet protection keys are not available to the
    peer, so another CONNECTION_CLOSE frame MAY be sent in a packet that uses a
    lower packet protection level." -/
def closeAfterConfirmationOk (confirmed : Bool) (pt : PacketType) : Frame → Bool
  | .connectionClose _ _ _ => if confirmed then decide (pt = PacketType.oneRtt) else true
  | _ => true

/-- Both packet-type rules for a CONNECTION_CLOSE frame. -/
def maySendCloseIn (confirmed : Bool) (pt : PacketType) (f : Frame) : Bool :=
  appCloseFrameOk pt f && closeAfterConfirmationOk confirmed pt f

/-- The conversion of §10.2.3 always produces a frame that a handshake packet
    may carry. -/
theorem maySendCloseIn_convert (pt : PacketType) (f : Frame) :
    maySendCloseIn false pt (convertCloseForHandshake f) = true := by
  cases f
  case connectionClose err ft reason =>
    cases ft <;>
      simp [convertCloseForHandshake, maySendCloseIn, appCloseFrameOk, closeAfterConfirmationOk]
  all_goals
    simp [convertCloseForHandshake, maySendCloseIn, appCloseFrameOk, closeAfterConfirmationOk]

/-- `Component.MaySendPacket`: the packet-level half of the send side.

* Every CONNECTION_CLOSE frame must be legal in this packet type — §19.19
  line 8187 for the 0x1d variant, §10.2.3 line 4056 for "MUST send any
  CONNECTION_CLOSE frames in a 1-RTT packet" once the handshake is confirmed.
* §10.2.1, line 3965: a packet sent while closing must actually *contain* a
  CONNECTION_CLOSE frame, which `MaySend` cannot see.
* §10.2.2, line 4023: "While otherwise identical to the closing state, an
  endpoint in the draining state MUST NOT send any packets", and §10.2 line 3953
  leaves nothing to send with once the state is
  discarded.  This is not a repetition of `MaySend`: it also rules out a packet
  with no frames at all, which `MaySend` has nothing to say about. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  (∀ f ∈ p.frames, maySendCloseIn s.handshakeConfirmed p.ptype f = true) ∧
    (match s.phase with
     | .active => True
     | .closing => closingPacketOk p.frames = true
     | .draining => False
     | .closed => False)

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  p.frames.all (maySendCloseIn s.handshakeConfirmed p.ptype) &&
    (match s.phase with
     | .active => true
     | .closing => closingPacketOk p.frames
     | .draining => false
     | .closed => false)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  cases hp : s.phase <;>
    simp only [maySendPacket, MaySendPacket, hp, Bool.and_eq_true, List.all_eq_true] <;>
    simp

/-! ### 6.3 Datagram level: sending a stateless reset (§10.3, §10.3.3)

`Component.MaySendDatagram` is left at its default.  A stateless reset is not
built out of QUIC packets — §10.3, line 4177: "A stateless reset uses an entire
UDP datagram, starting with the first two bits of the packet header", and its
contents are unpredictable bits plus a token — so it has no
`OutDatagram.packets` to describe, and the rule below relates its size to the
size of the datagram that *triggered* it, which `OutDatagram` does not carry.
`maySendStatelessReset` therefore stays free-standing for WP12. -/

/-- §10.3, line 4220: "Endpoints MUST discard packets that are too small to be
    valid QUIC packets.  To give an example, with the set of AEAD functions
    defined in [QUIC-TLS], short header packets that are smaller than 21 bytes
    are never valid."  A stateless reset is formatted as a short-header packet
    (line 4225), so it must reach this size to be usable. -/
def minStatelessResetSize : Nat := 21

/-- §10.3.3, line 4393: "An endpoint MUST ensure that every Stateless Reset that
    it sends is smaller than the packet that triggered it, unless it maintains
    state sufficient to prevent looping."  §10.3, line 4215: "An endpoint MUST
    NOT send a stateless reset that is three times or more larger than the
    packet it receives to avoid being used for amplification."

    `preventsLooping` is the "unless" clause: an endpoint that keeps enough
    state to stop a loop (line 4398: "An endpoint can remember the number of
    Stateless Reset packets that it has sent and stop generating new Stateless
    Reset packets once a limit is reached") is bound only by the 3× rule. -/
def maySendStatelessReset (preventsLooping : Bool) (triggerSize resetSize : Nat) : Bool :=
  decide (minStatelessResetSize ≤ resetSize) &&
    (preventsLooping || decide (resetSize < triggerSize)) &&
    decide (resetSize < 3 * triggerSize)

/-- Without anti-loop state, a datagram of 21 bytes or fewer can never be
    answered with a stateless reset. -/
theorem statelessReset_needs_large_trigger {t r : Nat}
    (h : maySendStatelessReset false t r = true) : 22 ≤ t := by
  simp only [maySendStatelessReset, Bool.and_eq_true, Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  simp only [minStatelessResetSize] at h1
  omega

/-- The 3× amplification limit of §10.3 line 4215 applies either way, so even an
    endpoint that prevents looping cannot answer a very small datagram. -/
theorem statelessReset_amplification {lp : Bool} {t r : Nat}
    (h : maySendStatelessReset lp t r = true) : 8 ≤ t := by
  simp only [maySendStatelessReset, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  simp only [minStatelessResetSize] at h1
  omega

/-! ### 6.4 Advice (SHOULD that only recommends) -/

/-- SHOULDs of §10.2 that recommend rather than permit, for an endpoint in role
    `role` that entered its closing or draining state at `entry` with probe
    timeout `pto`.  `retainsOpenSocket` is line 3949's qualifier.  A conforming
    implementation is never *rejected* for ignoring these; `Step` does not
    mention them. -/
structure Recommended (s : State) (role : Role) (retainsOpenSocket : Bool)
    (entry : Time) (pto : Nat) : Prop where
  /-- §10.2, line 3939: "These states SHOULD persist for at least three times
      the current Probe Timeout (PTO) interval as defined in
      [QUIC-RECOVERY]." -/
  closePeriodLongEnough : s.inClosePeriod = true → entry + closePeriod pto ≤ s.closeDeadline
  /-- §10.2, line 3949: "Servers that retain an open socket for accepting new
      connections SHOULD NOT end the closing or draining states early." -/
  serverWithOpenSocketDoesNotEndEarly :
    role = .server → retainsOpenSocket = true → s.mayEndEarly = false

/-- §10.2.2, line 4039: the single packet an endpoint MAY send before entering
    the draining state uses "a NO_ERROR code if appropriate".  Advice only: the
    text says "if appropriate", so `Step` emits `Effect.sendFarewellClose`,
    which fixes no code, and `accepts` never rejects another choice. -/
def recommendedFarewellReason : CloseReason := .transport .noError 0

/-- §10.3, line 4205 (the sentence's first word, "An", is on line 4196, before
    a page break): "endpoint that sends a stateless reset in response to a packet
    that is 43 bytes or shorter SHOULD send a stateless reset that is one byte
    shorter than the packet it responds to."  That is the only SHOULD about
    the size of a reset; §10.3.3 line 4405 ("Reducing the size of a Stateless
    Reset below 41 bytes means that the packet could reveal to an observer that
    it is a Stateless Reset") is an observation, not a recommendation, and is
    deliberately not encoded. -/
def recommendedStatelessResetSize (triggerSize resetSize : Nat) : Prop :=
  triggerSize ≤ 43 → resetSize = triggerSize - 1

end Quic.Spec.Termination
