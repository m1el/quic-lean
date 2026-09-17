import QuicModel.Spec.Core

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

/-  Parts 1–5: the state machine itself.  -/
namespace Quic.Spec.Termination

/-! ## 1. State, events, effects -/

/-- Why we closed.  §11.1, line 4451: "Application-specific protocol errors are
    signaled using the CONNECTION_CLOSE frame with a frame type of 0x1d.  Errors
    that are specific to the transport ... are carried in the CONNECTION_CLOSE
    frame with a frame type of 0x1c." -/
inductive CloseReason where
  /-- CONNECTION_CLOSE type 0x1c.  `frameType` is §19.19's Frame Type field;
      "A value of 0 ... is used when the frame type is unknown." -/
  | transport (err : TransportError) (frameType : Nat)
  /-- CONNECTION_CLOSE type 0x1d; the code is from the application space (§20.2). -/
  | application (code : Nat)
  deriving DecidableEq, Repr

/-- §10: "An established QUIC connection can be terminated in one of three ways."
    The four lifecycle phases of one endpoint's connection state.

    `active` is the connection before any termination has begun; its field is
    "the handshake is confirmed" (§4.1.2 of [QUIC-TLS]), which §10.2.3 needs.
    `closing` (§10.2.1) and `draining` (§10.2.2) are the spec's own names;
    `closed` is the state after the closing/draining period ends, where §10.2
    line 3953 says "an endpoint SHOULD discard all connection state". -/
inductive Phase where
  | active (confirmed : Bool)
  | closing
  | draining
  | closed
  deriving DecidableEq, Repr

/-- How far through termination a phase is; see `phase_forward`. -/
def Phase.rank : Phase → Nat
  | .active _ => 0
  | .closing => 1
  | .draining => 2
  | .closed => 3

structure State where
  phase : Phase
  /-- §18.2 `max_idle_timeout` we advertised, in µs; 0 means "not advertised". -/
  localMaxIdle : Nat
  /-- §18.2 `max_idle_timeout` the peer advertised, in µs; 0 means "not advertised". -/
  peerMaxIdle : Nat
  /-- §10.1, line 3841: when the idle timer was last restarted. -/
  idleStart : Time
  /-- §10.1, line 3842: whether an ack-eliciting packet has already been sent
      since the last packet was received and processed. -/
  ackElicitingSinceRecv : Bool
  /-- §10.2, line 3939: when the closing or draining period ends.  Only
      meaningful in `closing` and `draining`. -/
  closeDeadline : Time
  /-- The error this connection was closed with, once we know one. -/
  closedWith : Option CloseReason
  /-- §10.2, line 3946: this endpoint "has some alternative means to ensure that
      late-arriving packets do not induce a response, such as those that are
      able to close the UDP socket", and so MAY end the closing or draining
      state early. -/
  mayEndEarly : Bool
  deriving DecidableEq, Repr

/-- Every event carries `now` and the current PTO; the model never reads a clock
    and never computes a PTO (that is [QUIC-RECOVERY], out of scope). -/
inductive Event where
  /-- §10.1, line 3841: "a packet from its peer is received and processed
      successfully".  A packet that carried no CONNECTION_CLOSE frame. -/
  | recvPacket (now : Time) (pto : Nat)
  /-- §10.1, line 3842: "sending an ack-eliciting packet". -/
  | sentAckEliciting (now : Time) (pto : Nat)
  /-- Time passes; the only event that can fire a timeout. -/
  | tick (now : Time) (pto : Nat)
  /-- Another component detected a connection error (§11.1).  How the error was
      detected is that component's business; we only close on it. -/
  | localError (now : Time) (pto : Nat) (err : TransportError) (frameType : Nat)
  /-- §10.2, line 3921: "the application requests that QUIC close the
      connection", with an application error code. -/
  | appClose (now : Time) (pto : Nat) (code : Nat)
  /-- A packet carrying a CONNECTION_CLOSE frame was received and processed. -/
  | recvClose (now : Time) (pto : Nat) (reason : CloseReason)
  /-- §10.3.1, line 4322: the trailing 16 bytes of the datagram matched a
      Stateless Reset Token associated with this connection and remote address.
      The match itself is opaque here (WP4 owns tokens). -/
  | statelessReset (now : Time) (pto : Nat)
  /-- §12.3, line 4693: "If the packet number for sending reaches 2^62 - 1, the
      sender MUST close the connection without sending a CONNECTION_CLOSE frame
      or any further packets".  WP3 owns the detection (`pnExhausted` on the
      packet-number state); this component owns the consequence. -/
  | pnExhausted (now : Time) (pto : Nat)
  /-- §4.1.2 of [QUIC-TLS], as used by §10.2.3.  Supplied by WP11. -/
  | handshakeConfirmed (now : Time) (pto : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- Send a packet containing a CONNECTION_CLOSE frame carrying this reason.
      The reason is only ever the one the text itself fixes: the code supplied
      by the `localError`/`appClose` event that closed the connection, or the
      one already recorded in `closedWith` when that close is retransmitted
      (§11.1, line 4458). -/
  | sendClose (reason : CloseReason)
  /-- §10.2.2, line 4037: "An endpoint that receives a CONNECTION_CLOSE frame
      MAY send a single packet containing a CONNECTION_CLOSE frame before
      entering the draining state, using a NO_ERROR code if appropriate."
      The text does not fix the error code ("if appropriate"), so neither does
      this effect: it means "one packet carrying some CONNECTION_CLOSE frame".
      The NO_ERROR hint is `recommendedFarewellReason`. -/
  | sendFarewellClose
  /-- §10.2, line 3954: "The endpoint MAY send a stateless reset in response to
      any further incoming packets belonging to this connection." -/
  | sendStatelessReset
  /-- §10.1, line 3830 / §10.2, line 3953: the connection state is discarded. -/
  | discardState
  deriving DecidableEq, Repr

/-- Does this effect put a packet on the wire?  §10.2.2, line 4023 ("an endpoint
    in the draining state MUST NOT send any packets") is about exactly these. -/
def Effect.sendsPacket : Effect → Bool
  | .sendClose _ | .sendFarewellClose | .sendStatelessReset => true
  | .discardState => false

abbrev Out := Outcome State Effect

/-! ### Derived quantities -/

/-- §10.1, line 3833: "the effective value at an endpoint is computed as the
    minimum of the two advertised values (or the sole advertised value, if only
    one endpoint advertises a nonzero value)".  0 = no idle timeout. -/
def State.negotiatedIdle (s : State) : Nat :=
  if s.localMaxIdle = 0 then s.peerMaxIdle
  else if s.peerMaxIdle = 0 then s.localMaxIdle
  else min s.localMaxIdle s.peerMaxIdle

/-- §10.1, line 3848: "To avoid excessively small idle timeout periods,
    endpoints MUST increase the idle timeout period to be at least three times
    the current Probe Timeout (PTO)."  A disabled timeout stays disabled. -/
def State.effectiveIdle (s : State) (pto : Nat) : Nat :=
  if s.negotiatedIdle = 0 then 0 else max s.negotiatedIdle (3 * pto)

/-- §10.2, line 3939: "These states SHOULD persist for at least three times the
    current Probe Timeout (PTO) interval". -/
def closePeriod (pto : Nat) : Nat := 3 * pto

/-- Is this endpoint inside a closing or draining period? -/
def State.inClosePeriod (s : State) : Bool :=
  match s.phase with
  | .closing | .draining => true
  | _ => false

/-- Has this endpoint begun to terminate? -/
def State.terminating (s : State) : Bool :=
  match s.phase with
  | .active _ => false
  | _ => true

/-- Does a tick at `now` end the connection?  In `active` that is the idle
    timeout (§10.1); in `closing`/`draining` the end of the close period
    (§10.2). -/
def State.tickExpires (s : State) (now : Time) (pto : Nat) : Bool :=
  match s.phase with
  | .active _ =>
    !decide (s.effectiveIdle pto = 0) && decide (s.idleStart + s.effectiveIdle pto ≤ now)
  | .closing | .draining => decide (s.closeDeadline ≤ now)
  | .closed => false

/-- §10.1, line 3841: "An endpoint restarts its idle timer when a packet from
    its peer is received and processed successfully." -/
def State.restartIdle (s : State) (now : Time) : State :=
  { s with idleStart := now, ackElicitingSinceRecv := false }

/-- §10.1, line 3842: "An endpoint also restarts its idle timer when sending an
    ack-eliciting packet if no other ack-eliciting packets have been sent since
    last receiving and processing a packet." -/
def State.onAckElicitingSent (s : State) (now : Time) : State :=
  match s.phase with
  | .active _ =>
    if s.ackElicitingSinceRecv then s
    else { s with idleStart := now, ackElicitingSinceRecv := true }
  | _ => s

def State.toClosed (s : State) : State := { s with phase := .closed }

/-- §10.2, line 3931: "After sending a CONNECTION_CLOSE frame, an endpoint
    immediately enters the closing state." -/
def State.toClosing (s : State) (now : Time) (pto : Nat) (r : CloseReason) : State :=
  { s with phase := .closing, closedWith := some r,
           closeDeadline := now + closePeriod pto }

/-- §10.2, line 3933: "After receiving a CONNECTION_CLOSE frame, endpoints enter
    the draining state."  §10.2.2, line 4044: "An endpoint MAY enter the draining
    state from the closing state ... In this case, the draining state ends when
    the closing state would have ended." -/
def State.toDraining (s : State) (now : Time) (pto : Nat) (r : Option CloseReason) : State :=
  match s.phase with
  | .closing => { s with phase := .draining }
  | _ => { s with phase := .draining, closeDeadline := now + closePeriod pto,
                  closedWith := r }

/-- §10.3.1, line 4324: "the endpoint MUST enter the draining period and not
    send any further packets on this connection." -/
def State.onStatelessReset (s : State) (now : Time) (pto : Nat) : State :=
  match s.phase with
  | .active _ => { s with phase := .draining, closeDeadline := now + closePeriod pto }
  | .closing => { s with phase := .draining }
  | .draining | .closed => s

def State.confirm (s : State) : State :=
  match s.phase with
  | .active _ => { s with phase := .active true }
  | _ => s

/-- The reason we repeat in the closing state.  §11.1, line 4458: "An endpoint
    SHOULD be prepared to retransmit a packet containing a CONNECTION_CLOSE
    frame if it receives more packets on a terminated connection." -/
def State.reason (s : State) : CloseReason := s.closedWith.getD (.transport .noError 0)

/-! ### Projection lemmas for the transition helpers -/

@[simp] theorem onAckElicitingSent_phase (s : State) (now : Time) :
    (s.onAckElicitingSent now).phase = s.phase := by
  simp only [State.onAckElicitingSent]
  split
  · split <;> rfl
  · rfl

@[simp] theorem onAckElicitingSent_closedWith (s : State) (now : Time) :
    (s.onAckElicitingSent now).closedWith = s.closedWith := by
  simp only [State.onAckElicitingSent]
  split
  · split <;> rfl
  · rfl

@[simp] theorem toClosed_phase (s : State) : s.toClosed.phase = .closed := rfl

@[simp] theorem toClosing_phase (s : State) (now : Time) (pto : Nat) (r : CloseReason) :
    (s.toClosing now pto r).phase = .closing := rfl

@[simp] theorem toDraining_phase (s : State) (now : Time) (pto : Nat)
    (r : Option CloseReason) : (s.toDraining now pto r).phase = .draining := by
  simp only [State.toDraining]; split <;> rfl

theorem onStatelessReset_phase_ne_active (s : State) (now : Time) (pto : Nat) (c : Bool) :
    (s.onStatelessReset now pto).phase ≠ .active c := by
  cases hp : s.phase <;> simp [State.onStatelessReset, hp]

@[simp] theorem confirm_closedWith (s : State) : s.confirm.closedWith = s.closedWith := by
  simp only [State.confirm]; split <;> rfl

theorem confirm_active {s : State} {c : Bool} (h : s.confirm.phase = .active c) :
    ∃ c', s.phase = .active c' := by
  cases hp : s.phase with
  | active c' => exact ⟨c', rfl⟩
  | closing => simp [State.confirm, hp] at h
  | draining => simp [State.confirm, hp] at h
  | closed => simp [State.confirm, hp] at h

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §10.1, line 3841: "An endpoint restarts its idle timer when a packet from
      its peer is received and processed successfully." -/
  | recvActive {s now pto c} (hp : s.phase = .active c) :
      Step s (.recvPacket now pto) (.ok (s.restartIdle now) [])
  /-- §10.2.1, line 3965: "An endpoint in the closing state sends a packet
      containing a CONNECTION_CLOSE frame in response to any incoming packet
      that it attributes to the connection." -/
  | recvClosingRespond {s now pto} (hp : s.phase = .closing) :
      Step s (.recvPacket now pto) (.ok s [.sendClose s.reason])
  /-- §10.2.1, line 3969: "An endpoint SHOULD limit the rate at which it
      generates packets in the closing state.  For instance, an endpoint could
      wait for a progressively increasing number of received packets or amount
      of time before responding to received packets." -/
  | recvClosingSilent {s now pto} (hp : s.phase = .closing) :
      Step s (.recvPacket now pto) (.ok s [])
  /-- §10.2.2, line 4023: "an endpoint in the draining state MUST NOT send any
      packets." -/
  | recvDraining {s now pto} (hp : s.phase = .draining) :
      Step s (.recvPacket now pto) (.ok s [])
  /-- §10.2, line 3953: once the state is discarded there is nothing to answer
      with. -/
  | recvClosed {s now pto} (hp : s.phase = .closed) :
      Step s (.recvPacket now pto) (.ok s [])
  /-- §10.2, line 3954: "The endpoint MAY send a stateless reset in response to
      any further incoming packets belonging to this connection." -/
  | recvClosedReset {s now pto} (hp : s.phase = .closed) :
      Step s (.recvPacket now pto) (.ok s [.sendStatelessReset])
  /-- §10.1, line 3842: "An endpoint also restarts its idle timer when sending
      an ack-eliciting packet if no other ack-eliciting packets have been sent
      since last receiving and processing a packet." -/
  | sentAckEliciting {s now pto} :
      Step s (.sentAckEliciting now pto) (.ok (s.onAckElicitingSent now) [])
  /-- §10.1, line 3829: "the connection is silently closed and its state is
      discarded when it remains idle for longer than the minimum of both peers
      max_idle_timeout values"; §10.2, line 3939: the closing and draining
      states "SHOULD persist for at least three times the current Probe Timeout
      (PTO) interval". -/
  | tickExpire {s now pto} (h : s.tickExpires now pto = true) :
      Step s (.tick now pto) (.ok s.toClosed [.discardState])
  /-- No timer has fired yet. -/
  | tickStay {s now pto} (h : s.tickExpires now pto = false) :
      Step s (.tick now pto) (.ok s [])
  /-- §10.2, line 3946: "Endpoints that have some alternative means to ensure
      that late-arriving packets do not induce a response, such as those that
      are able to close the UDP socket, MAY end these states earlier to allow
      for faster resource recovery." -/
  | tickEndEarly {s now pto} (h : s.tickExpires now pto = false)
      (he : s.mayEndEarly = true) (hc : s.inClosePeriod = true) :
      Step s (.tick now pto) (.ok s.toClosed [.discardState])
  /-- §11.1, line 4447: "Errors that result in the connection being unusable ...
      MUST be signaled using a CONNECTION_CLOSE frame"; §10.2, line 3913:
      "Violations of the protocol lead to an immediate close." -/
  | localErrorActive {s now pto err ft c} (hp : s.phase = .active c) :
      Step s (.localError now pto err ft)
        (.ok (s.toClosing now pto (.transport err ft)) [.sendClose (.transport err ft)])
  /-- §10.2.3, line 4114: "An endpoint that has no state for the connection does
      not enter a closing or draining period on sending a CONNECTION_CLOSE
      frame."  Once terminating, a further local error changes nothing. -/
  | localErrorLate {s now pto err ft} (hp : s.terminating = true) :
      Step s (.localError now pto err ft) (.ok s [])
  /-- §10.2, line 3921: "When QUIC consequently closes the connection, a
      CONNECTION_CLOSE frame with an application-supplied error code will be
      used to signal closure to the peer." -/
  | appCloseActive {s now pto code c} (hp : s.phase = .active c) :
      Step s (.appClose now pto code)
        (.ok (s.toClosing now pto (.application code)) [.sendClose (.application code)])
  /-- An application close after termination has begun changes nothing. -/
  | appCloseLate {s now pto code} (hp : s.terminating = true) :
      Step s (.appClose now pto code) (.ok s [])
  /-- §10.2, line 3933: "After receiving a CONNECTION_CLOSE frame, endpoints
      enter the draining state." -/
  | recvCloseActive {s now pto r c} (hp : s.phase = .active c) :
      Step s (.recvClose now pto r) (.ok (s.toDraining now pto (some r)) [])
  /-- §10.2.2, line 4037: "An endpoint that receives a CONNECTION_CLOSE frame
      MAY send a single packet containing a CONNECTION_CLOSE frame before
      entering the draining state, using a NO_ERROR code if appropriate.  An
      endpoint MUST NOT send further packets." -/
  | recvCloseActiveReply {s now pto r c} (hp : s.phase = .active c) :
      Step s (.recvClose now pto r)
        (.ok (s.toDraining now pto (some r)) [.sendFarewellClose])
  /-- §10.2.2, line 4044: "An endpoint MAY enter the draining state from the
      closing state if it receives a CONNECTION_CLOSE frame ... the endpoint
      uses the same end time, but ceases transmission of any packets." -/
  | recvCloseClosingDrain {s now pto r} (hp : s.phase = .closing) :
      Step s (.recvClose now pto r) (.ok (s.toDraining now pto s.closedWith) [])
  /-- Staying in the closing state is also permitted (the move to draining is a
      MAY); §10.2.1, line 3965 then still answers the incoming packet. -/
  | recvCloseClosingRespond {s now pto r} (hp : s.phase = .closing) :
      Step s (.recvClose now pto r) (.ok s [.sendClose s.reason])
  /-- Staying in the closing state, rate-limited (§10.2.1, line 3969). -/
  | recvCloseClosingSilent {s now pto r} (hp : s.phase = .closing) :
      Step s (.recvClose now pto r) (.ok s [])
  /-- §10.2.2, line 4023: an endpoint in the draining state "MUST NOT send any
      packets". -/
  | recvCloseDraining {s now pto r} (hp : s.phase = .draining) :
      Step s (.recvClose now pto r) (.ok s [])
  /-- §10.2, line 3953. -/
  | recvCloseClosed {s now pto r} (hp : s.phase = .closed) :
      Step s (.recvClose now pto r) (.ok s [])
  /-- §10.2, line 3954. -/
  | recvCloseClosedReset {s now pto r} (hp : s.phase = .closed) :
      Step s (.recvClose now pto r) (.ok s [.sendStatelessReset])
  /-- §10.3.1, line 4323: "If the last 16 bytes of the datagram are identical in
      value to a Stateless Reset Token, the endpoint MUST enter the draining
      period and not send any further packets on this connection." -/
  | statelessReset {s now pto} :
      Step s (.statelessReset now pto) (.ok (s.onStatelessReset now pto) [])
  /-- §12.3, line 4693: "If the packet number for sending reaches 2^62 - 1, the
      sender MUST close the connection without sending a CONNECTION_CLOSE frame
      or any further packets; an endpoint MAY send a Stateless Reset
      (Section 10.3) in response to further packets that it receives."
      Straight to `closed`: no frame is sent, no closing or draining period is
      entered, and `closed` is the one phase from which the stateless reset that
      the second half of the sentence permits is still a permitted outcome
      (§10.2, line 3954). -/
  | pnExhausted {s now pto} (hp : s.phase ≠ .closed) :
      Step s (.pnExhausted now pto) (.ok s.toClosed [.discardState])
  /-- Nothing left to close. -/
  | pnExhaustedClosed {s now pto} (hp : s.phase = .closed) :
      Step s (.pnExhausted now pto) (.ok s [])
  /-- Handshake confirmation, needed by §10.2.3. -/
  | handshakeConfirmed {s now pto} :
      Step s (.handshakeConfirmed now pto) (.ok s.confirm [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvPacket now _ =>
    match s.phase with
    | .active _ => [.ok (s.restartIdle now) []]
    | .closing => [.ok s [.sendClose s.reason], .ok s []]
    | .draining => [.ok s []]
    | .closed => [.ok s [], .ok s [.sendStatelessReset]]
  | .sentAckEliciting now _ => [.ok (s.onAckElicitingSent now) []]
  | .tick now pto =>
    if s.tickExpires now pto then [.ok s.toClosed [.discardState]]
    else if s.mayEndEarly && s.inClosePeriod then
      [.ok s [], .ok s.toClosed [.discardState]]
    else [.ok s []]
  | .localError now pto err ft =>
    match s.phase with
    | .active _ =>
      [.ok (s.toClosing now pto (.transport err ft)) [.sendClose (.transport err ft)]]
    | _ => [.ok s []]
  | .appClose now pto code =>
    match s.phase with
    | .active _ =>
      [.ok (s.toClosing now pto (.application code)) [.sendClose (.application code)]]
    | _ => [.ok s []]
  | .recvClose now pto r =>
    match s.phase with
    | .active _ =>
      [.ok (s.toDraining now pto (some r)) [],
       .ok (s.toDraining now pto (some r)) [.sendFarewellClose]]
    | .closing =>
      [.ok (s.toDraining now pto s.closedWith) [], .ok s [.sendClose s.reason], .ok s []]
    | .draining => [.ok s []]
    | .closed => [.ok s [], .ok s [.sendStatelessReset]]
  | .statelessReset now pto => [.ok (s.onStatelessReset now pto) []]
  | .pnExhausted _ _ =>
    if s.phase = .closed then [.ok s []] else [.ok s.toClosed [.discardState]]
  | .handshakeConfirmed _ _ => [.ok s.confirm []]

/-! ## 4. The two forms agree -/

private theorem terminating_of_closing {s : State} (hp : s.phase = .closing) :
    s.terminating = true := by simp [State.terminating, hp]

private theorem terminating_of_draining {s : State} (hp : s.phase = .draining) :
    s.terminating = true := by simp [State.terminating, hp]

private theorem terminating_of_closed {s : State} (hp : s.phase = .closed) :
    s.terminating = true := by simp [State.terminating, hp]

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvPacket now pto =>
      cases hp : s.phase with
      | active c =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h; exact .recvActive hp
      | closing =>
        simp only [outcomes, hp, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .recvClosingRespond hp
        · exact .recvClosingSilent hp
      | draining =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h; exact .recvDraining hp
      | closed =>
        simp only [outcomes, hp, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .recvClosed hp
        · exact .recvClosedReset hp
    | sentAckEliciting now pto =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .sentAckEliciting
    | tick now pto =>
      simp only [outcomes] at h
      split at h
      · rename_i he
        simp only [List.mem_singleton] at h; subst h; exact .tickExpire he
      · rename_i he
        replace he : s.tickExpires now pto = false := by
          simpa using he
        split at h
        · rename_i hme
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hme
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .tickStay he
          · exact .tickEndEarly he h1 h2
        · simp only [List.mem_singleton] at h; subst h; exact .tickStay he
    | localError now pto err ft =>
      cases hp : s.phase with
      | active c =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h; exact .localErrorActive hp
      | closing =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .localErrorLate (terminating_of_closing hp)
      | draining =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .localErrorLate (terminating_of_draining hp)
      | closed =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .localErrorLate (terminating_of_closed hp)
    | appClose now pto code =>
      cases hp : s.phase with
      | active c =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h; exact .appCloseActive hp
      | closing =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .appCloseLate (terminating_of_closing hp)
      | draining =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .appCloseLate (terminating_of_draining hp)
      | closed =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h
        exact .appCloseLate (terminating_of_closed hp)
    | recvClose now pto r =>
      cases hp : s.phase with
      | active c =>
        simp only [outcomes, hp, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .recvCloseActive hp
        · exact .recvCloseActiveReply hp
      | closing =>
        simp only [outcomes, hp, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> subst h
        · exact .recvCloseClosingDrain hp
        · exact .recvCloseClosingRespond hp
        · exact .recvCloseClosingSilent hp
      | draining =>
        simp only [outcomes, hp, List.mem_singleton] at h; subst h; exact .recvCloseDraining hp
      | closed =>
        simp only [outcomes, hp, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .recvCloseClosed hp
        · exact .recvCloseClosedReset hp
    | statelessReset now pto =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .statelessReset
    | pnExhausted now pto =>
      simp only [outcomes] at h
      split at h
      · rename_i hq
        simp only [List.mem_singleton] at h; subst h; exact .pnExhaustedClosed hq
      · rename_i hq
        simp only [List.mem_singleton] at h; subst h; exact .pnExhausted hq
    | handshakeConfirmed now pto =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .handshakeConfirmed
  · intro h
    cases h with
    | recvActive hp => simp [outcomes, hp]
    | recvClosingRespond hp => simp [outcomes, hp]
    | recvClosingSilent hp => simp [outcomes, hp]
    | recvDraining hp => simp [outcomes, hp]
    | recvClosed hp => simp [outcomes, hp]
    | recvClosedReset hp => simp [outcomes, hp]
    | sentAckEliciting => simp [outcomes]
    | tickExpire h => simp [outcomes, h]
    | tickStay h =>
      by_cases hme : (s.mayEndEarly && s.inClosePeriod) = true <;> simp [outcomes, h, hme]
    | tickEndEarly h he hc => simp [outcomes, h, he, hc]
    | localErrorActive hp => simp [outcomes, hp]
    | localErrorLate hp =>
      cases hq : s.phase with
      | active c => simp [State.terminating, hq] at hp
      | closing => simp [outcomes, hq]
      | draining => simp [outcomes, hq]
      | closed => simp [outcomes, hq]
    | appCloseActive hp => simp [outcomes, hp]
    | appCloseLate hp =>
      cases hq : s.phase with
      | active c => simp [State.terminating, hq] at hp
      | closing => simp [outcomes, hq]
      | draining => simp [outcomes, hq]
      | closed => simp [outcomes, hq]
    | recvCloseActive hp => simp [outcomes, hp]
    | recvCloseActiveReply hp => simp [outcomes, hp]
    | recvCloseClosingDrain hp => simp [outcomes, hp]
    | recvCloseClosingRespond hp => simp [outcomes, hp]
    | recvCloseClosingSilent hp => simp [outcomes, hp]
    | recvCloseDraining hp => simp [outcomes, hp]
    | recvCloseClosed hp => simp [outcomes, hp]
    | recvCloseClosedReset hp => simp [outcomes, hp]
    | statelessReset => simp [outcomes]
    | pnExhausted hp => simp [outcomes, hp]
    | pnExhaustedClosed hp => simp [outcomes, hp]
    | handshakeConfirmed => simp [outcomes]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- An `active` connection has not been closed with anything yet: `closedWith`
    is set exactly when termination begins. -/
def Inv (s : State) : Prop := ∀ c, s.phase = .active c → s.closedWith = none

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | recvActive hp => intro c hq; simp only [State.restartIdle] at hq ⊢; exact hi c hq
  | recvClosingRespond hp => exact hi
  | recvClosingSilent hp => exact hi
  | recvDraining hp => exact hi
  | recvClosed hp => exact hi
  | recvClosedReset hp => exact hi
  | sentAckEliciting => intro c hq; simp only [onAckElicitingSent_phase] at hq
                        simpa using hi c hq
  | tickExpire _ => intro c hq; simp at hq
  | tickStay _ => exact hi
  | tickEndEarly _ _ _ => intro c hq; simp at hq
  | localErrorActive hp => intro c hq; simp at hq
  | localErrorLate hp => exact hi
  | appCloseActive hp => intro c hq; simp at hq
  | appCloseLate hp => exact hi
  | recvCloseActive hp => intro c hq; simp at hq
  | recvCloseActiveReply hp => intro c hq; simp at hq
  | recvCloseClosingDrain hp => intro c hq; simp at hq
  | recvCloseClosingRespond hp => exact hi
  | recvCloseClosingSilent hp => exact hi
  | recvCloseDraining hp => exact hi
  | recvCloseClosed hp => exact hi
  | recvCloseClosedReset hp => exact hi
  | statelessReset => intro c hq; exact absurd hq (onStatelessReset_phase_ne_active _ _ _ _)
  | pnExhausted _ => intro c hq; simp at hq
  | pnExhaustedClosed _ => exact hi
  | handshakeConfirmed =>
    intro c hq
    obtain ⟨c', hc⟩ := confirm_active hq
    simpa using hi c' hc
end Quic.Spec.Termination
