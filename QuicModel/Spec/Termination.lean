import QuicModel.Spec.Termination.Send

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

/-  Parts 7–10: the `Component` value, the named theorems, examples, and the
    coverage table for the whole package.  -/
namespace Quic.Spec.Termination

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

/-- (a) §10.2.2, line 4023: "an endpoint in the draining state MUST NOT send any
    packets."  §10.2, line 3953: after the state is discarded there is nothing
    left to send.  Nothing at all may be sent in either phase. -/
theorem maySend_false_of_draining_or_closed (s : State) (f : Frame)
    (hp : s.phase = .draining ∨ s.phase = .closed) : ¬ MaySend s f := by
  rcases hp with hp | hp <;> simp [MaySend, hp]

theorem maySend_false_of_draining_or_closed' (s : State) (f : Frame)
    (hp : s.phase = .draining ∨ s.phase = .closed) : maySend s f = false := by
  rcases hp with hp | hp <;> simp [maySend, hp]

/-- Stronger than (a) at the effect level: in the draining state no permitted
    step puts a packet on the wire (§10.2.2, line 4023). -/
theorem draining_emits_no_packet {s e s' fx} (hp : s.phase = .draining)
    (h : Step s e (.ok s' fx)) : ∀ x ∈ fx, x.sendsPacket = false := by
  have hne : ∀ c : Bool, s.phase ≠ .active c := by rw [hp]; simp
  have hnc : s.phase ≠ .closing := by rw [hp]; simp
  have hncl : s.phase ≠ .closed := by rw [hp]; simp
  cases h with
  | recvActive hp' => exact absurd hp' (hne _)
  | recvClosingRespond hp' => exact absurd hp' hnc
  | recvClosingSilent _ => simp
  | recvDraining _ => simp
  | recvClosed hp' => exact absurd hp' hncl
  | recvClosedReset hp' => exact absurd hp' hncl
  | sentAckEliciting => simp
  | tickExpire _ => simp [Effect.sendsPacket]
  | tickStay _ => simp
  | tickEndEarly _ _ _ => simp [Effect.sendsPacket]
  | localErrorActive hp' => exact absurd hp' (hne _)
  | localErrorLate _ => simp
  | appCloseActive hp' => exact absurd hp' (hne _)
  | appCloseLate _ => simp
  | recvCloseActive hp' => exact absurd hp' (hne _)
  | recvCloseActiveReply hp' => exact absurd hp' (hne _)
  | recvCloseClosingDrain hp' => exact absurd hp' hnc
  | recvCloseClosingRespond hp' => exact absurd hp' hnc
  | recvCloseClosingSilent hp' => exact absurd hp' hnc
  | recvCloseDraining _ => simp
  | recvCloseClosed hp' => exact absurd hp' hncl
  | recvCloseClosedReset hp' => exact absurd hp' hncl
  | statelessReset => simp
  | handshakeConfirmed => simp

/-- (b) §10.2.1, line 3961: in the closing state an endpoint retains "only
    enough information to generate a packet containing a CONNECTION_CLOSE
    frame"; CONNECTION_CLOSE and the PADDING that may accompany it (§14.1) are
    exactly the frames it may send. -/
theorem maySend_closing_iff (s : State) (f : Frame) (hp : s.phase = .closing) :
    MaySend s f ↔
      (∃ err ft reason, f = .connectionClose err ft reason) ∨ (∃ n, f = .padding n) := by
  simp [MaySend, hp]

/-- `MaySend` reads nothing but the phase.  With `phase_forward` this is the
    BRIEF's idempotence rule: while the phase does not change, a frame that was
    acceptable stays acceptable, so an exact repeat — in particular the
    retransmitted CONNECTION_CLOSE of §11.1 line 4458 — is always accepted. -/
theorem maySend_of_phase_eq {s s' : State} (h : s.phase = s'.phase) (f : Frame) :
    MaySend s f ↔ MaySend s' f := by
  simp only [MaySend, h]

theorem maySend_stable {s e s' fx} (_h : Step s e (.ok s' fx)) (hph : s'.phase = s.phase)
    (f : Frame) (hf : MaySend s f) : MaySend s' f :=
  (maySend_of_phase_eq hph.symm f).mp hf

/-- (c) Termination only ever moves forward:
    `active → closing → draining → closed`, with `active → draining`,
    `active → closed` and `closing → closed` also permitted, and no step going
    back. -/
theorem phase_forward {s e s' fx} (h : Step s e (.ok s' fx)) :
    s.phase.rank ≤ s'.phase.rank := by
  cases h with
  | recvActive hp => simp [State.restartIdle]
  | recvClosingRespond hp => simp
  | recvClosingSilent hp => simp
  | recvDraining hp => simp
  | recvClosed hp => simp
  | recvClosedReset hp => simp
  | sentAckEliciting => simp
  | tickExpire he => cases hp : s.phase <;> simp [Phase.rank]
  | tickStay _ => simp
  | tickEndEarly _ _ hc => cases hp : s.phase <;> simp [Phase.rank]
  | localErrorActive hp => rw [hp]; simp [Phase.rank]
  | localErrorLate _ => simp
  | appCloseActive hp => rw [hp]; simp [Phase.rank]
  | appCloseLate _ => simp
  | recvCloseActive hp => rw [hp]; simp [Phase.rank]
  | recvCloseActiveReply hp => rw [hp]; simp [Phase.rank]
  | recvCloseClosingDrain hp => rw [hp]; simp [Phase.rank]
  | recvCloseClosingRespond hp => simp
  | recvCloseClosingSilent hp => simp
  | recvCloseDraining hp => simp
  | recvCloseClosed hp => simp
  | recvCloseClosedReset hp => simp
  | statelessReset =>
    cases hph : s.phase <;> simp [State.onStatelessReset, hph, Phase.rank]
  | handshakeConfirmed =>
    cases hph : s.phase <;> simp [State.confirm, hph, Phase.rank]

/-- The handshake-confirmed bit is never cleared while the connection is
    `active`. -/
theorem confirmed_mono {s e s' fx} (h : Step s e (.ok s' fx))
    (hc : s.phase = .active true) : s'.phase ≠ .active false := by
  cases h with
  | recvActive hp => simp [State.restartIdle, hc]
  | recvClosingRespond hp => simp [hc]
  | recvClosingSilent hp => simp [hc]
  | recvDraining hp => simp [hc]
  | recvClosed hp => simp [hc]
  | recvClosedReset hp => simp [hc]
  | sentAckEliciting => simp [hc]
  | tickExpire _ => simp
  | tickStay _ => simp [hc]
  | tickEndEarly _ _ _ => simp
  | localErrorActive hp => simp
  | localErrorLate _ => simp [hc]
  | appCloseActive hp => simp
  | appCloseLate _ => simp [hc]
  | recvCloseActive hp => simp
  | recvCloseActiveReply hp => simp
  | recvCloseClosingDrain hp => simp
  | recvCloseClosingRespond hp => simp [hc]
  | recvCloseClosingSilent hp => simp [hc]
  | recvCloseDraining hp => simp [hc]
  | recvCloseClosed hp => simp [hc]
  | recvCloseClosedReset hp => simp [hc]
  | statelessReset => exact onStatelessReset_phase_ne_active _ _ _ _
  | handshakeConfirmed => simp [State.confirm, hc]

/-- (d) §10.2, line 3939: a tick at or after the recorded end of the closing or
    draining period reaches `closed`, and every permitted outcome does so. -/
theorem close_period_reaches_closed {s : State} {now : Time} {pto : Nat} {o : Out}
    (hp : s.phase = .closing ∨ s.phase = .draining)
    (hd : s.closeDeadline ≤ now) (h : Step s (.tick now pto) o) :
    o = .ok s.toClosed [.discardState] := by
  have hx : s.tickExpires now pto = true := by
    rcases hp with hp | hp <;> simp [State.tickExpires, hp, hd]
  cases h with
  | tickExpire _ => rfl
  | tickStay h0 => exact absurd hx (by simp [h0])
  | tickEndEarly h0 _ _ => exact absurd hx (by simp [h0])

theorem close_period_reaches_closed_phase {s : State} {now : Time} {pto : Nat}
    {s' : State} {fx : List Effect}
    (hp : s.phase = .closing ∨ s.phase = .draining)
    (hd : s.closeDeadline ≤ now) (h : Step s (.tick now pto) (.ok s' fx)) :
    s'.phase = .closed := by
  have := close_period_reaches_closed hp hd h
  simp only [Outcome.ok.injEq] at this
  simp [this.1]

/-- (e) §10.1, line 3829: "the connection is silently closed and its state is
    discarded when it remains idle for longer than the minimum of both peers
    max_idle_timeout values".  With a live (non-zero) effective timeout and only
    ticks arriving, every permitted outcome at `now ≥ idleStart + effective` is
    the silent close: state discarded, no frame sent. -/
theorem idle_timeout_closes {s : State} {c : Bool} {now : Time} {pto : Nat} {o : Out}
    (hp : s.phase = .active c)
    (hne : s.effectiveIdle pto ≠ 0)
    (hd : s.idleStart + s.effectiveIdle pto ≤ now)
    (h : Step s (.tick now pto) o) :
    o = .ok s.toClosed [.discardState] := by
  have hx : s.tickExpires now pto = true := by
    simp [State.tickExpires, hp, hne, hd]
  cases h with
  | tickExpire _ => rfl
  | tickStay h0 => exact absurd hx (by simp [h0])
  | tickEndEarly h0 _ _ => exact absurd hx (by simp [h0])

/-- The idle timeout is silent: no CONNECTION_CLOSE is produced. -/
theorem idle_timeout_silent {s : State} {c : Bool} {now : Time} {pto : Nat}
    {s' : State} {fx : List Effect}
    (hp : s.phase = .active c) (hne : s.effectiveIdle pto ≠ 0)
    (hd : s.idleStart + s.effectiveIdle pto ≤ now)
    (h : Step s (.tick now pto) (.ok s' fx)) :
    s'.phase = .closed ∧ ∀ x ∈ fx, x.sendsPacket = false := by
  have he := idle_timeout_closes hp hne hd h
  simp only [Outcome.ok.injEq] at he
  obtain ⟨h1, h2⟩ := he
  refine ⟨by simp [h1], ?_⟩
  rw [h2]; simp [Effect.sendsPacket]

/-- §10.1, line 3848: the effective idle timeout is never shorter than 3 PTO,
    unless it is disabled altogether. -/
theorem effectiveIdle_ge_three_pto (s : State) (pto : Nat)
    (h : s.negotiatedIdle ≠ 0) : 3 * pto ≤ s.effectiveIdle pto := by
  have hx : s.effectiveIdle pto = max s.negotiatedIdle (3 * pto) := by
    simp [State.effectiveIdle, h]
  rw [hx]
  exact Nat.le_max_right _ _

/-- §10.1, line 3833: the negotiated value is the minimum of the two advertised
    values, or the sole non-zero one. -/
theorem negotiatedIdle_eq_min (s : State)
    (hl : s.localMaxIdle ≠ 0) (hpk : s.peerMaxIdle ≠ 0) :
    s.negotiatedIdle = min s.localMaxIdle s.peerMaxIdle := by
  simp [State.negotiatedIdle, hl, hpk]

theorem negotiatedIdle_zero (s : State)
    (hl : s.localMaxIdle = 0) (hpk : s.peerMaxIdle = 0) : s.negotiatedIdle = 0 := by
  simp [State.negotiatedIdle, hl, hpk]

/-- §10.1, line 3842: the second ack-eliciting packet sent since the last
    receive does *not* restart the idle timer. -/
theorem ackEliciting_restarts_only_first (s : State) (c : Bool) (now : Time)
    (hp : s.phase = .active c) (hs : s.ackElicitingSinceRecv = true) :
    s.onAckElicitingSent now = s := by
  simp [State.onAckElicitingSent, hp, hs]

theorem ackEliciting_restarts_first (s : State) (c : Bool) (now : Time)
    (hp : s.phase = .active c) (hs : s.ackElicitingSinceRecv = false) :
    (s.onAckElicitingSent now).idleStart = now := by
  simp [State.onAckElicitingSent, hp, hs]

/-- §10.3.1, line 4323: a detected stateless reset enters the draining period
    and sends nothing. -/
theorem statelessReset_drains_silently {s : State} {c : Bool} {now : Time} {pto : Nat}
    {o : Out} (hp : s.phase = .active c ∨ s.phase = .closing)
    (h : Step s (.statelessReset now pto) o) :
    ∃ s', o = .ok s' [] ∧ s'.phase = .draining := by
  cases h with
  | statelessReset =>
    refine ⟨s.onStatelessReset now pto, rfl, ?_⟩
    rcases hp with hp | hp <;> simp [State.onStatelessReset, hp]

/-- §10.2.2, line 4046: entering draining from closing keeps the closing state's
    end time. -/
theorem drain_from_closing_keeps_deadline (s : State) (now : Time) (pto : Nat)
    (r : Option CloseReason) (hp : s.phase = .closing) :
    (s.toDraining now pto r).closeDeadline = s.closeDeadline := by
  simp [State.toDraining, hp]

/-! ## 9. Examples (scenarios from the text) -/

private def s0 : State :=
  { phase := .active true, localMaxIdle := 30000000, peerMaxIdle := 10000000,
    idleStart := 0, ackElicitingSinceRecv := false, closeDeadline := 0,
    closedWith := none, mayEndEarly := false }

-- §10.1: the effective value is the minimum of the two advertised values …
example : s0.negotiatedIdle = 10000000 := by decide
-- … but at least 3 PTO (here PTO = 5 s, so 15 s wins over the negotiated 10 s).
example : s0.effectiveIdle 5000000 = 15000000 := by decide
-- The connection is silently closed once it has been idle that long.
example : component.step s0 (.tick 15000000 5000000) =
    .ok { s0 with phase := .closed } [.discardState] := by decide
example : component.step s0 (.tick 14999999 5000000) = .ok s0 [] := by decide

-- §10.1: receiving restarts the timer and clears "ack-eliciting already sent".
example : component.step s0 (.recvPacket 7000 0) =
    .ok { s0 with idleStart := 7000, ackElicitingSinceRecv := false } [] := by decide
-- The first ack-eliciting packet after a receive restarts the timer …
example : component.step s0 (.sentAckEliciting 7000 0) =
    .ok { s0 with idleStart := 7000, ackElicitingSinceRecv := true } [] := by decide
-- … the second does not.
example :
    component.step { s0 with idleStart := 7000, ackElicitingSinceRecv := true }
      (.sentAckEliciting 9000 0) =
    .ok { s0 with idleStart := 7000, ackElicitingSinceRecv := true } [] := by decide

-- §11.1 / §10.2: a protocol violation causes an immediate close; we enter the
-- closing state for 3 PTO and send CONNECTION_CLOSE of type 0x1c.
private def sClosing : State :=
  { s0 with phase := .closing, closedWith := some (.transport .protocolViolation 0x08),
            closeDeadline := 1000 + 3 * 400 }

example : component.step s0 (.localError 1000 400 .protocolViolation 0x08) =
    .ok sClosing [.sendClose (.transport .protocolViolation 0x08)] := by decide

-- §10.2.1: in the closing state a received packet is answered with
-- CONNECTION_CLOSE, and rate-limiting (sending nothing) is also permitted.
example : component.step sClosing (.recvPacket 1500 400) =
    .ok sClosing [.sendClose (.transport .protocolViolation 0x08)] := by decide
example : component.accepts sClosing (.recvPacket 1500 400) (.ok sClosing []) = true := by decide
-- but nothing else is
example : component.accepts sClosing (.recvPacket 1500 400)
    (.ok sClosing [.sendStatelessReset]) = false := by decide

-- §10.2.2: a CONNECTION_CLOSE received while closing moves us to draining with
-- the *same* end time.
example : component.step sClosing (.recvClose 1500 400 (.transport .noError 0)) =
    .ok { sClosing with phase := .draining } [] := by decide
-- and the closing period's own deadline still closes the connection
example : component.step { sClosing with phase := .draining } (.tick (1000 + 3 * 400) 400) =
    .ok { sClosing with phase := .closed } [.discardState] := by decide

-- §10.2.2: draining sends nothing, whatever arrives.
example : component.step { sClosing with phase := .draining } (.recvPacket 1600 400) =
    .ok { sClosing with phase := .draining } [] := by decide
example : component.maySend { sClosing with phase := .draining } .ping = false := by decide
example : component.maySend { sClosing with phase := .draining }
    (.connectionClose 0 (some 0) ByteArray.empty) = false := by decide
-- closing may send CONNECTION_CLOSE, and the PADDING that §14.1 makes a client
-- add to a datagram carrying an Initial packet, but nothing else
example : component.maySend sClosing (.connectionClose 0 (some 0) ByteArray.empty) = true := by
  decide
example : component.maySend sClosing (.padding 3) = true := by decide
example : component.maySend sClosing .ping = false := by decide
-- a repeated CONNECTION_CLOSE is still acceptable: `MaySend` reads only the phase
example : component.maySend (component.step sClosing (.recvPacket 1500 400) |>.next sClosing)
    (.connectionClose 0 (some 0) ByteArray.empty) = true := by decide
-- the packet-level rule: a closing packet must actually carry a CONNECTION_CLOSE
example : closingPacketOk [.connectionClose 0 (some 0) ByteArray.empty, .padding 1100] = true := by
  decide
example : closingPacketOk [.padding 1200] = false := by decide
example : closingPacketOk [.connectionClose 0 (some 0) ByteArray.empty, .ping] = false := by decide

-- §10.3.1: a detected stateless reset drains without sending anything.
example : component.step s0 (.statelessReset 2000 400) =
    .ok { s0 with phase := .draining, closeDeadline := 2000 + 3 * 400 } [] := by decide

-- §10.2.2: on receiving CONNECTION_CLOSE while active, a single reply is the
-- permitted alternative to silence.
-- The reply's error code is not fixed by the text ("a NO_ERROR code if
-- appropriate"), so the effect does not fix it either.
example : component.accepts s0 (.recvClose 2000 400 (.application 7))
    (.ok { s0 with phase := .draining, closeDeadline := 2000 + 3 * 400,
                   closedWith := some (.application 7) }
          [.sendFarewellClose]) = true := by decide

-- §10.3 / §10.3.3: stateless reset sizes.
example : maySendStatelessReset 1200 43 = true := by decide
example : maySendStatelessReset 43 43 = false := by decide   -- not smaller than the trigger
example : maySendStatelessReset 21 20 = false := by decide   -- below the 21-byte minimum
example : maySendStatelessReset 22 21 = true := by decide

-- §10.2.3 / §19.19: an application close cannot go in an Initial packet …
example : maySendCloseIn false .initial (.connectionClose 7 none ByteArray.empty) = false := by
  decide
-- … it is converted to type 0x1c with APPLICATION_ERROR and an empty reason.
example : convertCloseForHandshake (.connectionClose 7 none ByteArray.empty) =
    .connectionClose 0xc (some 0) ByteArray.empty := by decide
-- after the handshake is confirmed, CONNECTION_CLOSE must go in a 1-RTT packet
example : maySendCloseIn true .handshake (.connectionClose 7 (some 0) ByteArray.empty) = false := by
  decide
example : maySendCloseIn true .oneRtt (.connectionClose 7 (some 0) ByteArray.empty) = true := by
  decide

-- Following an implementation we cannot see inside: it answered a packet in the
-- closing state, so it is still closing.
example : component.track sClosing (.recvPacket 1500 400)
    (.ok [.sendClose (.transport .protocolViolation 0x08)]) = some sClosing := by rfl

/-! ## 10. Coverage and notes

Assigned text: §10 and §11 (lines 3813–4515) and §19.19 (8125–8192).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §10 (3824) | "An endpoint MAY discard connection state if it does not have a validated path" | out of scope: path validation is WP5 |
| §10.1 (3829) | idle connection is "silently closed and its state is discarded" | `Step.tickExpire`, `idle_timeout_closes`, `idle_timeout_silent` |
| §10.1 (3833) | effective value = min of the two advertised, or the sole non-zero one | `State.negotiatedIdle`, `negotiatedIdle_eq_min`, `negotiatedIdle_zero` |
| §10.1 (3841) | restart the idle timer on a packet received and processed | `Step.recvActive`, `State.restartIdle` |
| §10.1 (3842) | restart on sending an ack-eliciting packet only if it is the first since the last receive | `State.onAckElicitingSent`, `ackEliciting_restarts_first/_only_first` |
| §10.1 (3848) | MUST increase the idle timeout to at least 3 PTO | `State.effectiveIdle`, `effectiveIdle_ge_three_pto` |
| §10.1.1 (3860–) | liveness testing: send PING if the peer could time out soon | advice only, no normative keyword; `Event.sentAckEliciting` is how it reaches this component |
| §10.1.2 (3875–) | deferring the idle timeout by sending PING | same; the PING's effect is `Event.sentAckEliciting` |
| §10.1.2 (3893) | application protocols SHOULD give guidance on deferring | out of scope: not a transport requirement |
| §10.2 (3927) | CONNECTION_CLOSE closes all streams implicitly | out of scope: stream states are WP2/WP9 |
| §10.2 (3931) | after sending CONNECTION_CLOSE, enter closing | `State.toClosing` (`Step.localErrorActive`, `Step.appCloseActive`) |
| §10.2 (3933) | after receiving CONNECTION_CLOSE, enter draining | `Step.recvCloseActive` |
| §10.2 (3913) | "Violations of the protocol lead to an immediate close." | `Step.localErrorActive` |
| §10.2 (3939) | closing/draining SHOULD persist ≥ 3 PTO | `closePeriod`, `State.closeDeadline`, `Recommended.closePeriodLongEnough` |
| §10.2 (3946) | MAY end these states earlier | `Step.tickEndEarly` (gated on `State.mayEndEarly`) |
| §10.2 (3949) | servers with an open socket SHOULD NOT end early | `Recommended.serverWithOpenSocketDoesNotEndEarly` (advice) |
| §10.2 (3953) | SHOULD discard all connection state once the state ends | `Effect.discardState` |
| §10.2 (3954) | MAY send a stateless reset to further incoming packets | `Step.recvClosedReset`, `Step.recvCloseClosedReset` |
| §10.2.1 (3960) | enters closing after initiating an immediate close | `State.toClosing` |
| §10.2.1 (3965) | closing answers any incoming packet with CONNECTION_CLOSE | `Step.recvClosingRespond`, `Step.recvCloseClosingRespond`; the packet-level "contains a CONNECTION_CLOSE" part is `closingPacketOk` (for WP12) |
| §10.2.1 (3969) | SHOULD limit the rate of packets generated while closing | `Step.recvClosingSilent`, `Step.recvCloseClosingSilent` (the permitted alternative) |
| §10.2.1 (3983–3985) | MAY discard other connection state / MAY retain keys | out of scope: key and CID state are WP4/WP11 |
| §10.2.1 (3988–3996) | MAY drop keys; MUST limit sent bytes to 3× received; MAY resend the identical packet | out of scope: the 3× budget is WP5 (anti-amplification); noted below |
| §10.2.1 (4008) | closing MUST either discard packets from an unvalidated address or apply the 3× limit | out of scope: WP5 owns address validation |
| §10.2.1 (4016–) | key updates while closing | out of scope: WP11 |
| §10.2.2 (4023) | draining MUST NOT send any packets | `MaySend` = `False`, `maySend_false_of_draining_or_closed`, `draining_emits_no_packet`, `Step.recvDraining`, `Step.recvCloseDraining` |
| §10.2.2 (4037) | MAY send a single CONNECTION_CLOSE before entering draining; MUST NOT send further packets | `Step.recvCloseActiveReply` emitting `Effect.sendFarewellClose` (one packet, code unconstrained) and `MaySend` = `False` afterwards |
| §10.2.2 (4038) | that packet uses "a NO_ERROR code if appropriate" | `recommendedFarewellReason` (advice; `Step` fixes no code) |
| §10.2.2 (4044) | MAY enter draining from closing, with the same end time | `Step.recvCloseClosingDrain`, `drain_from_closing_keeps_deadline` |
| §10.2.3 (4056) | after confirmation, CONNECTION_CLOSE MUST be in a 1-RTT packet | `maySendCloseIn` |
| §10.2.3 (4060–4079) | MAY/SHOULD send CONNECTION_CLOSE at lower levels before confirmation | `maySendCloseIn confirmed:=false` permits every packet type for 0x1c |
| §10.2.3 (4084, 4095) | 0x1d MUST be replaced by 0x1c in Initial/Handshake; MUST clear the reason phrase, SHOULD use APPLICATION_ERROR | `convertCloseForHandshake`, `maySendCloseIn_convert` |
| §10.2.3 (4099) | CONNECTION_CLOSE in several packet types may be coalesced | out of scope: datagram assembly is WP12 |
| §10.2.3 (4111) | MAY discard packets rather than close on errors in unauthenticated packets | out of scope: error *detection* belongs to the detecting component |
| §10.2.3 (4114) | an endpoint with no connection state does not enter closing/draining | `Step.localErrorLate` covers the "already terminating" case; the stateless server is out of scope (no state to model) |
| §10.3 (4126) | MAY send a stateless reset for a packet it cannot associate with a connection | out of scope: that is the no-connection path (WP12 dispatch); the in-connection case is `Step.recvClosedReset` |
| §10.3 (4130) | an endpoint that can send a frame MUST use CONNECTION_CLOSE | `maySendStatelessReset` is only ever reachable from `.closed` (`Step.recvClosedReset`), where `MaySend` is `False`; see `no_reset_while_sendable` note below |
| §10.3 (4143–4163) | issuing and scoping tokens; the reset packet layout | out of scope: token issuance is WP4, packet layout is the wire package |
| §10.3 (4192) | SHOULD pad all packets to ≥ 22 + min CID length | out of scope: padding policy is WP7 (sizes) |
| §10.3 (4206) | reset for a ≤43-byte trigger SHOULD be one byte shorter | `recommendedStatelessResetSize` |
| §10.3 (4215) | MUST NOT send a reset ≥ 3× the packet it receives | `maySendStatelessReset` |
| §10.3 (4220) | MUST discard packets too small to be valid QUIC packets | `minStatelessResetSize`, `statelessReset_needs_large_trigger`; discarding the packet itself is WP12 |
| §10.3 (4225) | MUST send resets formatted as short-header packets | out of scope: wire format |
| §10.3 (4226) | MUST treat any packet ending in a valid token as a stateless reset | `Event.statelessReset` (the match is opaque, as assigned) |
| §10.3 (4230) | MAY send a reset in response to a long-header packet | out of scope: no-connection path |
| §10.3.1 (4285–4301) | which tokens are remembered, MAY skip the check, MUST check when undecryptable, MUST NOT check unused/retired tokens | out of scope: token bookkeeping is WP4; this component consumes the boolean result |
| §10.3.1 (4303) | MUST compare without leaking information | out of scope: implementation technique, not observable behaviour |
| §10.3.1 (4323) | on a match MUST enter the draining period and send nothing further | `Step.statelessReset`, `statelessReset_drains_silently` |
| §10.3.2 (4329–4382) | calculating the token; MUST NOT reuse | out of scope: assigned as "generating stateless reset tokens" |
| §10.3.3 (4393) | every reset MUST be smaller than the packet that triggered it | `maySendStatelessReset` |
| §10.3.3 (4405) | below 41 bytes a reset may be recognisable | `recommendedStatelessResetSize` |
| §11 (4415, 4429, 4434) | SHOULD signal errors; SHOULD use the most appropriate code; MAY use any applicable code | the code is carried on `Event.localError`; choosing it belongs to the detecting component |
| §11 (4441) | a stateless reset MUST NOT be used by an endpoint that has the state to send a frame | see `no_reset_while_sendable` note |
| §11.1 (4447) | connection errors MUST be signalled with CONNECTION_CLOSE | `Step.localErrorActive` |
| §11.1 (4451) | 0x1d for application errors, 0x1c for transport errors | `CloseReason` |
| §11.1 (4458) | SHOULD be prepared to retransmit CONNECTION_CLOSE on further packets | `Step.recvClosingRespond` with `State.reason`; `maySend_stable` shows the repeat stays acceptable |
| §14.1 (out of range) | a client MUST pad a datagram carrying an Initial packet to 1200 bytes | not modelled here (WP7 owns sizes), but it is why `MaySend` accepts PADDING while closing |
| §11.1 (4486) | MAY discard an invalid Initial packet instead of erroring | out of scope: detection side |
| §11.2 (4494–4513) | stream errors, RESET_STREAM MUST only be instigated by the application | out of scope: streams are WP2/WP9 |
| §19.19 (8125–8160) | CONNECTION_CLOSE frame format and fields | out of scope: wire format (already done); `CloseReason` mirrors the two variants |
| §19.19 (8134) | open streams are implicitly closed | out of scope: WP2/WP9 |
| §19.19 (8186) | 0x1d can only be sent in 0-RTT or 1-RTT packets | `appCloseAllowedIn`, `maySendCloseIn` |

NOTES

- The spec has no name for the phase before termination begins; `Phase.active`
  is it.  `open` is a Lean keyword, hence the rename.  Its field is "handshake
  confirmed", which §10.2.3 needs.
- `MaySend` in the closing state accepts CONNECTION_CLOSE *and* PADDING.  The
  text never forbids padding the closing packet, and §14.1 requires a client to
  pad any datagram carrying an Initial packet to 1200 bytes — which includes an
  Initial carrying CONNECTION_CLOSE during the handshake (§10.2.3).  That a
  closing packet must actually *contain* a CONNECTION_CLOSE is a packet-level
  rule, which `MaySend : State → Frame → Prop` cannot see; it is exported as
  `closingPacketOk : List Frame → Bool` for WP12.
- `MaySend` depends on nothing but the phase (`maySend_of_phase_eq`), so a
  frame that was acceptable stays acceptable for as long as the phase does
  (`maySend_stable`).  In particular the CONNECTION_CLOSE that §11.1 line 4458
  tells an endpoint to retransmit is accepted every time it is repeated.
- The packet-type rules of §10.2.3 and §19.19 cannot live in `MaySend`, whose
  signature is `State → Frame → Prop`.  They are `maySendCloseIn` /
  `appCloseAllowedIn`, with handshake confirmation as an explicit argument
  because the `confirmed` bit is only carried while the phase is `active` (once
  closing, the phase no longer records it).  WP12 must supply it.
- "A packet received while closing": the three permitted alternatives are
  enumerated as `Step.recvClosingRespond` (answer with CONNECTION_CLOSE — the
  preferred outcome, and what `component.step` produces), `Step.recvClosingSilent`
  (suppressed by the SHOULD-level rate limit of line 3969) and, when the packet
  carried a CONNECTION_CLOSE, `Step.recvCloseClosingDrain` (move to draining and
  answer nothing).  Received packets are split into two events —
  `recvPacket` for one without a CONNECTION_CLOSE frame and `recvClose` for one
  with — because the two have different consequences in every phase.
- Entering draining on a *stateless reset* from the `active` phase starts a
  fresh 3-PTO period (`now + 3 × PTO`); from `closing` it keeps the closing
  state's end time, by analogy with §10.2.2 line 4046.  The text says only
  "MUST enter the draining period" and does not fix the deadline for this case.
- `Effect.discardState` marks §10.2 line 3953; the `closed` phase is this
  model's name for "after the closing or draining state ends".  It is kept as a
  phase rather than deleting the state because line 3954 still permits a
  stateless reset from there, and because `track` needs somewhere to go.
- `no_reset_while_sendable`: §10.3 line 4130 and §11 line 4441 forbid a
  stateless reset from an endpoint that can still send a frame.  In this model
  `Effect.sendStatelessReset` is produced only from `Phase.closed`, where
  `MaySend` is `False` for every frame (`maySend_false_of_draining_or_closed`),
  so the two rules are consistent by construction rather than by a separate
  theorem.
- The 3× anti-amplification limit that §10.2.1 restates for the closing state
  (lines 3993 and 4008) is deliberately not duplicated here: WP5 owns the
  budget, and duplicating it would give two sources of truth for WP12 to
  reconcile.
- `Event.handshakeConfirmed` is not in the assigned list of events but is
  needed to ever reach `Phase.active true`; it carries no other behaviour.
- §10.2.2 line 4038 says the single farewell packet uses "a NO_ERROR code if
  appropriate", so the text does not determine the code.  The effect
  `Effect.sendFarewellClose` therefore carries none: it means "one packet
  containing some CONNECTION_CLOSE frame", and `accepts` cannot reject a
  conforming implementation over the code it picked.  The NO_ERROR hint lives
  in `recommendedFarewellReason`.  `Effect.sendClose` does carry a reason, but
  only where the text fixes one: the code supplied by the `localError` /
  `appClose` event that closed the connection, and the same code again when
  that close is retransmitted from `closedWith` (§11.1, line 4458).
- Both deadlines are tested with `≤`, not `<`: the idle timeout fires at
  `idleStart + effective` and the close period ends at `closeDeadline`.  The
  text says "remains idle for *longer than*" (line 3829), which read literally
  is `<`; the one-microsecond difference is not observable and `≤` is what the
  named theorems are stated against.
- `State.mayEndEarly` encodes the endpoint capability of §10.2 line 3946
  ("some alternative means to ensure that late-arriving packets do not induce a
  response").  With it `false` — the default for a server that keeps its socket
  open — a tick before the deadline always keeps the phase.
-/

end Quic.Spec.Termination
