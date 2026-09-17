import QuicModel.Spec.Termination.Basic

/-
  WP6 — Connection termination.

  Spec text: draft-ietf-quic-transport-34 §10 (lines 3813–4413), §11 (4414–4515)
  and §19.19 (8125–8192).

  Subject: the connection's lifecycle phase as one component — the idle timeout,
  immediate close, the closing and draining states, stateless-reset detection,
  and what may be sent in each phase.

  The package follows `Spec/Template.lean`'s ten-part order, split across three
  files because it does not fit in one:

    `Termination/Basic.lean`  1. State / Event / Effect
                              2. Step
                              3. outcomes
                              4. outcomes_iff, outcomes_ne
                              5. Inv, step_inv
    `Termination/Send.lean`   6. MaySend / maySend / maySend_iff, and the
                                 packet- and datagram-level send rules
    `Termination.lean`        7. the `Component` value
                              8. named theorems
                              9. examples
                             10. coverage table and notes
-/

/-  Part 6: the send side.  -/
namespace Quic.Spec.Termination

/-! ## 6. Send side

### 6.1 Frame level -/

def isConnectionClose : Frame → Bool
  | .connectionClose _ _ _ => true
  | _ => false

def isPadding : Frame → Bool
  | .padding _ => true
  | _ => false

/-- §10.2.1, line 3961: in the closing state an endpoint "retains only enough
    information to generate a packet containing a CONNECTION_CLOSE frame and to
    identify packets as belonging to the connection", and line 3965 it "sends a
    packet containing a CONNECTION_CLOSE frame".  PADDING is permitted with it:
    the text nowhere forbids padding that packet, and §14.1 *requires* a client
    to pad any datagram carrying an Initial packet to 1200 bytes, which includes
    an Initial carrying CONNECTION_CLOSE during the handshake (§10.2.3).

    §10.2.2, line 4023: "an endpoint in the draining state MUST NOT send any
    packets"; §10.2, line 3953: once the state is discarded there is nothing
    left to send with. -/
def MaySend (s : State) (f : Frame) : Prop :=
  match s.phase with
  | .active _ => True
  | .closing =>
    (∃ err ft reason, f = .connectionClose err ft reason) ∨ (∃ n, f = .padding n)
  | .draining => False
  | .closed => False

def maySend (s : State) (f : Frame) : Bool :=
  match s.phase with
  | .active _ => true
  | .closing => isConnectionClose f || isPadding f
  | .draining => false
  | .closed => false

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases hp : s.phase <;> simp only [maySend, MaySend, hp] <;>
    cases f <;> simp [isConnectionClose, isPadding]

/-- §10.2.1, line 3965: "An endpoint in the closing state sends a packet
    *containing a CONNECTION_CLOSE frame* in response to any incoming packet".
    That a closing packet must actually carry a CONNECTION_CLOSE is a
    packet-level rule, not a frame-level one: `MaySend` cannot see the other
    frames in the packet.  Exported here for WP12 to apply when it assembles a
    packet sent from the closing state. -/
def closingPacketOk (fs : List Frame) : Bool :=
  fs.any isConnectionClose && fs.all (fun f => isConnectionClose f || isPadding f)

theorem maySend_of_closingPacketOk {s : State} (hp : s.phase = .closing)
    {fs : List Frame} (h : closingPacketOk fs = true) : ∀ f ∈ fs, MaySend s f := by
  intro f hf
  rw [← maySend_iff]
  simp only [closingPacketOk, Bool.and_eq_true, List.all_eq_true] at h
  simpa [maySend, hp] using h.2 f hf

/-! ### 6.2 Packet level (§10.2.1, §10.2.2, §10.2.3, §19.19)

What cannot be said frame by frame: which packet a CONNECTION_CLOSE may travel
in, and what a packet sent from the closing state must contain.  These become
`Component.MaySendPacket`.  Handshake confirmation is the one rule that stays
free-standing, because it is only tracked while the connection is `active`
(once closing, the phase no longer records it) — see `maySendCloseIn`. -/

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

/-- §19.19, line 8186: "The application-specific variant of CONNECTION_CLOSE
    (type 0x1d) can only be sent using 0-RTT or 1-RTT packets."  Together with
    §10.2.3, line 4084 this is the frame/packet-type rule for 0x1d. -/
def appCloseAllowedIn : PacketType → Bool
  | .zeroRtt | .oneRtt => true
  | _ => false

/-- One frame against the packet type it would travel in: §19.19 line 8186 and
    §10.2.3 line 4084, the rule for the application variant 0x1d.  This is the
    half of `maySendCloseIn` that needs no handshake state, so it is the half
    that goes into `MaySendPacket`. -/
def appCloseFrameOk (pt : PacketType) : Frame → Bool
  | .connectionClose _ none _ => appCloseAllowedIn pt
  | _ => true

/-- §10.2.3, line 4056: "After the handshake is confirmed (see Section 4.1.2 of
    [QUIC-TLS]), an endpoint MUST send any CONNECTION_CLOSE frames in a 1-RTT
    packet."  Line 4060: "However, prior to confirming the handshake, ... another
    CONNECTION_CLOSE frame MAY be sent in a packet that uses a lower packet
    protection level." -/
def closeAfterConfirmationOk (confirmed : Bool) (pt : PacketType) : Frame → Bool
  | .connectionClose _ _ _ => if confirmed then decide (pt = PacketType.oneRtt) else true
  | _ => true

/-- Both packet-type rules for a CONNECTION_CLOSE frame.  Stays free-standing
    (it is not part of `MaySendPacket`) because `confirmed` is not in the state
    once the phase leaves `active`; WP12 supplies it. -/
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

* Every frame must be legal in this packet type (§19.19, line 8186: "The
  application-specific variant of CONNECTION_CLOSE (type 0x1d) can only be sent
  using 0-RTT or 1-RTT packets").
* §10.2.1, line 3965: "An endpoint in the closing state sends a packet
  containing a CONNECTION_CLOSE frame in response to any incoming packet that it
  attributes to the connection" — a packet sent while closing must actually
  carry one, which `MaySend` cannot see.
* §10.2.2, line 4023: "an endpoint in the draining state MUST NOT send any
  packets", and §10.2 line 3953 leaves nothing to send with once the state is
  discarded.  This is not a repetition of `MaySend`: it also rules out a packet
  with no frames at all, which `MaySend` has nothing to say about. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  (∀ f ∈ p.frames, appCloseFrameOk p.ptype f = true) ∧
    (match s.phase with
     | .active _ => True
     | .closing => closingPacketOk p.frames = true
     | .draining => False
     | .closed => False)

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  p.frames.all (appCloseFrameOk p.ptype) &&
    (match s.phase with
     | .active _ => true
     | .closing => closingPacketOk p.frames
     | .draining => false
     | .closed => false)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  cases hp : s.phase <;>
    simp only [maySendPacket, MaySendPacket, hp, Bool.and_eq_true, List.all_eq_true] <;>
    simp

/-! ### 6.3 Datagram level: sending a stateless reset (§10.3, §10.3.3)

`Component.MaySendDatagram` is left at its default here.  A stateless reset is
not built out of QUIC packets — §10.3, line 4174: "A stateless reset uses an
entire UDP datagram, starting with the first two bits of the packet header",
and its contents are unpredictable bits plus a token — so it has no
`OutDatagram.packets` to describe, and the rule below relates its size to the
size of the datagram that triggered it, which `OutDatagram` does not carry.
`maySendStatelessReset` therefore stays free-standing for WP12. -/

/-- §10.3, line 4220: "Endpoints MUST discard packets that are too small to be
    valid QUIC packets ... short header packets that are smaller than 21 bytes
    are never valid."  A stateless reset is formatted as a short-header packet
    (line 4225), so it must reach this size to be usable. -/
def minStatelessResetSize : Nat := 21

/-- §10.3.3, line 4393: "An endpoint MUST ensure that every Stateless Reset that
    it sends is smaller than the packet that triggered it, unless it maintains
    state sufficient to prevent looping."  §10.3, line 4215: "An endpoint MUST
    NOT send a stateless reset that is three times or more larger than the
    packet it receives to avoid being used for amplification."

    Consequence (`statelessReset_needs_large_trigger`): a datagram of 21 bytes
    or fewer can never be answered with a stateless reset. -/
def maySendStatelessReset (triggerSize resetSize : Nat) : Bool :=
  decide (minStatelessResetSize ≤ resetSize) &&
    decide (resetSize < triggerSize) &&
    decide (resetSize < 3 * triggerSize)

theorem statelessReset_needs_large_trigger {t r : Nat}
    (h : maySendStatelessReset t r = true) : 22 ≤ t := by
  simp only [maySendStatelessReset, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  simp only [minStatelessResetSize] at h1
  omega

/-! ### 6.4 Advice (SHOULD that only recommends) -/

/-- SHOULDs of §10.2 that recommend rather than permit, for an endpoint in role
    `role` that entered its closing or draining state at `entry` with probe
    timeout `pto`.  A conforming implementation is never *rejected* for ignoring
    these; `Step` does not mention them. -/
structure Recommended (s : State) (role : Role) (entry : Time) (pto : Nat) : Prop where
  /-- §10.2, line 3939: "These states SHOULD persist for at least three times
      the current Probe Timeout (PTO) interval." -/
  closePeriodLongEnough : s.inClosePeriod = true → entry + closePeriod pto ≤ s.closeDeadline
  /-- §10.2, line 3949: "Servers that retain an open socket for accepting new
      connections SHOULD NOT end the closing or draining states early." -/
  serverDoesNotEndEarly : role = .server → s.mayEndEarly = false

/-- §10.2.2, line 4038: the single packet an endpoint MAY send before entering
    the draining state uses "a NO_ERROR code if appropriate".  Advice only: the
    text says "if appropriate", so `Step` emits `Effect.sendFarewellClose`,
    which fixes no code, and `accepts` never rejects another choice. -/
def recommendedFarewellReason : CloseReason := .transport .noError 0

/-- §10.3, line 4206: "An endpoint that sends a stateless reset in response to a
    packet that is 43 bytes or shorter SHOULD send a stateless reset that is one
    byte shorter than the packet it responds to."  §10.3.3, line 4405: "Reducing
    the size of a Stateless Reset below 41 bytes means that the packet could
    reveal to an observer that it is a Stateless Reset". -/
def recommendedStatelessResetSize (triggerSize resetSize : Nat) : Prop :=
  (triggerSize ≤ 43 → resetSize = triggerSize - 1) ∧ (43 < triggerSize → 41 ≤ resetSize)
end Quic.Spec.Termination
