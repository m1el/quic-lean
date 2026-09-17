import QuicModel.Spec.Termination.Send

/-
  WP6 — Connection termination.

  Spec text: draft-ietf-quic-transport-34 §10 (lines 3813–4413), §11 (4414–4515)
  and §19.19 (8125–8192), plus §12.3 line 4693 (packet number exhaustion).

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
  MaySendPacket := MaySendPacket
  maySendPacket := maySendPacket
  maySendPacket_iff := maySendPacket_iff

/-! ## 8. Named theorems -/

/-! ### (a) draining and closed send nothing -/

/-- (a) §10.2.2, line 4023: "While otherwise identical to the closing state, an
    endpoint in the draining state MUST NOT send any packets."  §10.2, line 3953:
    after the state is discarded there is nothing
    left to send.  Nothing at all may be sent in either phase. -/
theorem maySend_false_of_draining_or_closed (s : State) (f : Frame)
    (hp : s.phase = .draining ∨ s.phase = .closed) : ¬ MaySend s f := by
  rcases hp with hp | hp <;> simp [MaySend, hp]

theorem maySend_false_of_draining_or_closed' (s : State) (f : Frame)
    (hp : s.phase = .draining ∨ s.phase = .closed) : maySend s f = false := by
  rcases hp with hp | hp <;> simp [maySend, hp]

theorem maySendPacket_false_of_draining_or_closed (s : State) (p : OutPacket)
    (hp : s.phase = .draining ∨ s.phase = .closed) : ¬ MaySendPacket s p := by
  rcases hp with hp | hp <;> simp [MaySendPacket, hp]

/-- Stronger than (a) at the effect level: in the draining state no permitted
    step puts a packet on the wire (§10.2.2, line 4023). -/
theorem draining_emits_no_packet {s e s' fx} (hp : s.phase = .draining)
    (h : Step s e (.ok s' fx)) : ∀ x ∈ fx, x.sendsPacket = false := by
  have hna : s.phase ≠ .active := by rw [hp]; simp
  have hnc : s.phase ≠ .closing := by rw [hp]; simp
  have hncl : s.phase ≠ .closed := by rw [hp]; simp
  cases h with
  | recvActive hp' => exact absurd hp' hna
  | recvClosingRespond hp' => exact absurd hp' hnc
  | recvClosingSilent _ => simp
  | recvDraining _ => simp
  | recvClosed hp' => exact absurd hp' hncl
  | recvClosedReset hp' => exact absurd hp' hncl
  | sentAckEliciting => simp
  | tickIdleTimeout hp' _ => exact absurd hp' hna
  | tickIdleStay hp' _ => exact absurd hp' hna
  | tickPeriodOver _ _ => simp [Effect.sendsPacket]
  | tickPeriodContinue _ => simp
  | tickEndEarly _ _ => simp [Effect.sendsPacket]
  | tickClosed hp' => exact absurd hp' hncl
  | localErrorActive hp' => exact absurd hp' hna
  | localErrorLate _ => simp
  | appCloseActive hp' => exact absurd hp' hna
  | appCloseLate _ => simp
  | recvCloseActive hp' => exact absurd hp' hna
  | recvCloseActiveReply hp' => exact absurd hp' hna
  | recvCloseClosingDrain hp' => exact absurd hp' hnc
  | recvCloseClosingRespond hp' => exact absurd hp' hnc
  | recvCloseClosingSilent hp' => exact absurd hp' hnc
  | recvCloseDraining _ => simp
  | recvCloseClosed hp' => exact absurd hp' hncl
  | recvCloseClosedReset hp' => exact absurd hp' hncl
  | statelessReset => simp
  | pnExhausted _ => simp [Effect.sendsPacket]
  | pnExhaustedClosed hp' => exact absurd hp' hncl
  | handshakeConfirmed => simp

/-! ### (b) what the closing state constrains -/

/-- (b), frame level.  §10.2.1 lines 3963–3967 say what a closing endpoint
    retains ("only enough information to generate a packet containing a
    CONNECTION_CLOSE frame and to identify packets as belonging to the
    connection") and what it sends ("a packet containing a CONNECTION_CLOSE
    frame in response to any incoming packet"), but no sentence of §10.2 or
    §10.2.1 forbids any frame.  So at frame level the closing state permits
    everything, and the real rule is the packet-level one below. -/
theorem maySend_closing (s : State) (f : Frame) (hp : s.phase = .closing) :
    MaySend s f := by simp [MaySend, hp]

/-- (b), packet level: §10.2.1, line 3965.  A packet sent while closing is
    permitted exactly when every CONNECTION_CLOSE frame in it is legal for the
    packet type and the packet contains at least one CONNECTION_CLOSE. -/
theorem maySendPacket_closing_iff (s : State) (p : OutPacket) (hp : s.phase = .closing) :
    MaySendPacket s p ↔
      (∀ f ∈ p.frames, maySendCloseIn s.handshakeConfirmed p.ptype f = true) ∧
        p.frames.any isConnectionClose = true := by
  simp [MaySendPacket, closingPacketOk, hp]

/-- `MaySend` reads nothing but the phase.  With `phase_forward` this is the
    BRIEF's idempotence rule: while the phase does not change, a frame that was
    acceptable stays acceptable, so an exact repeat — in particular the
    retransmitted CONNECTION_CLOSE of §11.1 line 4457 — is always accepted. -/
theorem maySend_of_phase_eq {s s' : State} (h : s.phase = s'.phase) (f : Frame) :
    MaySend s f ↔ MaySend s' f := by
  simp only [MaySend, h]

theorem maySend_stable {s e s' fx} (_h : Step s e (.ok s' fx)) (hph : s'.phase = s.phase)
    (f : Frame) (hf : MaySend s f) : MaySend s' f :=
  (maySend_of_phase_eq hph.symm f).mp hf

/-! ### (c) the phase only moves forward -/

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
  | tickIdleTimeout hp _ => rw [hp]; simp [Phase.rank]
  | tickIdleStay _ _ => simp
  | tickPeriodOver _ _ => cases hph : s.phase <;> simp [Phase.rank]
  | tickPeriodContinue _ => simp
  | tickEndEarly _ _ => cases hph : s.phase <;> simp [Phase.rank]
  | tickClosed hp => simp
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
  | pnExhausted _ => cases hph : s.phase <;> simp [Phase.rank]
  | pnExhaustedClosed _ => simp
  | handshakeConfirmed => simp

/-- The handshake-confirmed bit is never cleared, in any phase.  This is what
    makes §10.2.3 line 4056 expressible in `MaySendPacket`: the bit survives the
    move to the closing state, where the CONNECTION_CLOSE is actually sent. -/
theorem handshakeConfirmed_mono {s e s' fx} (h : Step s e (.ok s' fx))
    (hc : s.handshakeConfirmed = true) : s'.handshakeConfirmed = true := by
  cases h with
  | recvActive hp => simpa [State.restartIdle] using hc
  | recvClosingRespond hp => exact hc
  | recvClosingSilent hp => exact hc
  | recvDraining hp => exact hc
  | recvClosed hp => exact hc
  | recvClosedReset hp => exact hc
  | @sentAckEliciting now pto =>
    simp only [State.onAckElicitingSent]
    split
    · split <;> exact hc
    · exact hc
  | tickIdleTimeout _ _ => simpa [State.toClosed] using hc
  | tickIdleStay _ _ => exact hc
  | tickPeriodOver _ _ => simpa [State.toClosed] using hc
  | tickPeriodContinue _ => exact hc
  | tickEndEarly _ _ => simpa [State.toClosed] using hc
  | tickClosed _ => exact hc
  | localErrorActive hp => simpa [State.toClosing] using hc
  | localErrorLate _ => exact hc
  | appCloseActive hp => simpa [State.toClosing] using hc
  | appCloseLate _ => exact hc
  | recvCloseActive hp => simp only [State.toDraining]; split <;> exact hc
  | recvCloseActiveReply hp => simp only [State.toDraining]; split <;> exact hc
  | recvCloseClosingDrain hp => simp only [State.toDraining]; split <;> exact hc
  | recvCloseClosingRespond hp => exact hc
  | recvCloseClosingSilent hp => exact hc
  | recvCloseDraining hp => exact hc
  | recvCloseClosed hp => exact hc
  | recvCloseClosedReset hp => exact hc
  | statelessReset => simp only [State.onStatelessReset]; split <;> exact hc
  | pnExhausted _ => simpa [State.toClosed] using hc
  | pnExhaustedClosed _ => exact hc
  | handshakeConfirmed => rfl

/-! ### (d) the closing and draining periods end -/

/-- A tick never puts a packet on the wire, in any phase. -/
theorem tick_emits_no_packet {s now pto s' fx} (h : Step s (.tick now pto) (.ok s' fx)) :
    ∀ x ∈ fx, x.sendsPacket = false := by
  cases h with
  | tickIdleTimeout _ _ => simp [Effect.sendsPacket]
  | tickIdleStay _ _ => simp
  | tickPeriodOver _ _ => simp [Effect.sendsPacket]
  | tickPeriodContinue _ => simp
  | tickEndEarly _ _ => simp [Effect.sendsPacket]
  | tickClosed _ => simp

/-- (d), part 1: at or after the recorded end of the closing or draining period
    the move to `closed` is permitted … -/
theorem close_period_may_close {s : State} {now : Time} {pto : Nat}
    (hp : s.phase = .closing ∨ s.phase = .draining) (hd : s.closeDeadline ≤ now) :
    Step s (.tick now pto) (.ok s.toClosed [.discardState]) := by
  rcases hp with hp | hp
  · exact .tickPeriodOver (by simp [State.inClosePeriod, hp]) hd
  · exact .tickPeriodOver (by simp [State.inClosePeriod, hp]) hd

/-- (d), part 2: … and is what the reference implementation does. -/
theorem close_period_step_closes {s : State} {now : Time} {pto : Nat}
    (hp : s.phase = .closing ∨ s.phase = .draining) (hd : s.closeDeadline ≤ now) :
    component.step s (.tick now pto) = .ok s.toClosed [.discardState] := by
  rcases hp with hp | hp <;>
    simp [Component.step, component, outcomes, hp, hd]

/-- (d), part 3: the only alternative is to stay where we are.  §10.2 line 3939
    bounds the closing and draining periods only *below* ("These states SHOULD
    persist for at least three times the current Probe Timeout (PTO)
    interval"), so keeping the
    state longer is permitted and a tick can never do anything else. -/
theorem close_period_outcomes {s : State} {now : Time} {pto : Nat} {o : Out}
    (hp : s.phase = .closing ∨ s.phase = .draining) (h : Step s (.tick now pto) o) :
    o = .ok s.toClosed [.discardState] ∨ o = .ok s [] := by
  have hna : s.phase ≠ .active := by rcases hp with hp | hp <;> rw [hp] <;> simp
  have hncl : s.phase ≠ .closed := by rcases hp with hp | hp <;> rw [hp] <;> simp
  cases h with
  | tickIdleTimeout hp' _ => exact absurd hp' hna
  | tickIdleStay hp' _ => exact absurd hp' hna
  | tickPeriodOver _ _ => exact .inl rfl
  | tickPeriodContinue _ => exact .inr rfl
  | tickEndEarly _ _ => exact .inl rfl
  | tickClosed hp' => exact absurd hp' hncl

theorem close_period_reaches_closed {s : State} {now : Time} {pto : Nat}
    (hp : s.phase = .closing ∨ s.phase = .draining) (hd : s.closeDeadline ≤ now) :
    Step s (.tick now pto) (.ok s.toClosed [.discardState]) ∧
      component.step s (.tick now pto) = .ok s.toClosed [.discardState] ∧
      ∀ o, Step s (.tick now pto) o → o = .ok s.toClosed [.discardState] ∨ o = .ok s [] :=
  ⟨close_period_may_close hp hd, close_period_step_closes hp hd,
    fun _ h => close_period_outcomes hp h⟩

/-- Every permitted tick from the closing or draining period either reaches
    `closed` or leaves the state untouched. -/
theorem close_period_reaches_closed_phase {s : State} {now : Time} {pto : Nat}
    {s' : State} {fx : List Effect}
    (hp : s.phase = .closing ∨ s.phase = .draining)
    (h : Step s (.tick now pto) (.ok s' fx)) : s'.phase = .closed ∨ s' = s := by
  rcases close_period_outcomes hp h with h' | h' <;>
    simp only [Outcome.ok.injEq] at h'
  · exact .inl (by simp [h'.1])
  · exact .inr h'.1

/-! ### (e) the idle timeout -/

/-- (e) §10.1, line 3829: "If a max_idle_timeout is specified by either peer in
    its transport parameters (Section 18.2), the connection is silently closed
    and its state is discarded when it remains idle for longer than the minimum
    of both peers max_idle_timeout values."  With a live (non-zero) timeout and only
    ticks arriving, every permitted outcome once `now` is *strictly* past
    `idleStart + effective` is the silent close. -/
theorem idle_timeout_closes {s : State} {now : Time} {pto : Nat} {o : Out}
    (hp : s.phase = .active)
    (hne : s.effectiveIdle pto ≠ 0)
    (hd : s.idleStart + s.effectiveIdle pto < now)
    (h : Step s (.tick now pto) o) :
    o = .ok s.toClosed [.discardState] := by
  have hx : s.idleExpired now pto = true := by
    simp [State.idleExpired, hne, hd]
  have hna : s.phase ≠ .closing := by rw [hp]; simp
  have hnd : s.phase ≠ .draining := by rw [hp]; simp
  have hncl : s.phase ≠ .closed := by rw [hp]; simp
  cases h with
  | tickIdleTimeout _ _ => rfl
  | tickIdleStay _ h0 => exact absurd hx (by simp [h0])
  | tickPeriodOver hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickPeriodContinue hp' => simp [State.inClosePeriod, hp] at hp'
  | tickEndEarly hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickClosed hp' => exact absurd hp' hncl

/-- The idle timeout is silent: state is discarded and nothing is sent. -/
theorem idle_timeout_silent {s : State} {now : Time} {pto : Nat}
    {s' : State} {fx : List Effect}
    (hp : s.phase = .active) (hne : s.effectiveIdle pto ≠ 0)
    (hd : s.idleStart + s.effectiveIdle pto < now)
    (h : Step s (.tick now pto) (.ok s' fx)) :
    s'.phase = .closed ∧ ∀ x ∈ fx, x.sendsPacket = false := by
  have he := idle_timeout_closes hp hne hd h
  simp only [Outcome.ok.injEq] at he
  obtain ⟨h1, h2⟩ := he
  refine ⟨by simp [h1], ?_⟩
  rw [h2]; simp [Effect.sendsPacket]

/-- §10.1, line 3831 says the connection is closed when it has been idle
    "longer than the minimum of both peers max_idle_timeout values", so at the
    deadline instant itself the
    connection is still live and a tick must not be required to close it. -/
theorem idle_deadline_instant_stays {s : State} {pto : Nat}
    (hp : s.phase = .active) :
    Step s (.tick (s.idleStart + s.effectiveIdle pto) pto) (.ok s []) :=
  .tickIdleStay hp (by simp [State.idleExpired])

/-- §10.1, line 3848: the effective idle timeout is never shorter than 3 PTO,
    unless it is disabled altogether. -/
theorem effectiveIdle_ge_three_pto (s : State) (pto : Nat)
    (h : s.negotiatedIdle ≠ 0) : 3 * pto ≤ s.effectiveIdle pto := by
  have hx : s.effectiveIdle pto = max s.negotiatedIdle (3 * pto) := by
    simp [State.effectiveIdle, h]
  rw [hx]
  exact Nat.le_max_right _ _

/-- §10.1, line 3834: the negotiated value is the minimum of the two advertised
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
theorem ackEliciting_restarts_only_first (s : State) (now : Time)
    (hp : s.phase = .active) (hs : s.ackElicitingSinceRecv = true) :
    s.onAckElicitingSent now = s := by
  simp [State.onAckElicitingSent, hp, hs]

theorem ackEliciting_restarts_first (s : State) (now : Time)
    (hp : s.phase = .active) (hs : s.ackElicitingSinceRecv = false) :
    (s.onAckElicitingSent now).idleStart = now := by
  simp [State.onAckElicitingSent, hp, hs]

/-! ### Stateless reset and the unvalidated-address alternative -/

/-- §10.3.1, line 4323: a detected stateless reset enters the draining period
    and sends nothing. -/
theorem statelessReset_drains_silently {s : State} {now : Time} {pto : Nat}
    {o : Out} (hp : s.phase = .active ∨ s.phase = .closing)
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

/-- §10.2.1, line 4008: "An endpoint in the closing state MUST either discard
    packets received from an unvalidated address or limit the cumulative size of
    packets it sends to an unvalidated address to three times the size of
    packets it receives from that address."  Both alternatives are permitted;
    the byte accounting behind the second belongs to `AddressValidation`. -/
theorem closing_unvalidated_alternatives {s : State} {now : Time} {pto : Nat}
    (hp : s.phase = .closing) :
    Step s (.recvPacket now pto false) .drop ∧
      Step s (.recvPacket now pto false) (.ok s [.sendClose s.reason]) :=
  ⟨.recvClosingDiscardUnvalidated hp, .recvClosingRespond hp⟩

theorem closing_unvalidated_close_alternatives {s : State} {now : Time} {pto : Nat}
    {r : CloseReason} (hp : s.phase = .closing) :
    Step s (.recvClose now pto r false) .drop ∧
      Step s (.recvClose now pto r false) (.ok s [.sendClose s.reason]) :=
  ⟨.recvCloseClosingDiscardUnvalidated hp, .recvCloseClosingRespond hp⟩

/-! ### Packet number exhaustion (§12.3, line 4693) -/

/-- `closed` absorbs: no permitted step leaves it. -/
theorem closed_absorbing {s e s' fx} (hp : s.phase = .closed)
    (h : Step s e (.ok s' fx)) : s'.phase = .closed := by
  have hna : s.phase ≠ .active := by rw [hp]; simp
  have hnc : s.phase ≠ .closing := by rw [hp]; simp
  have hnd : s.phase ≠ .draining := by rw [hp]; simp
  cases h with
  | recvActive hp' => exact absurd hp' hna
  | recvClosingRespond hp' => exact absurd hp' hnc
  | recvClosingSilent hp' => exact absurd hp' hnc
  | recvDraining hp' => exact absurd hp' hnd
  | recvClosed _ => exact hp
  | recvClosedReset _ => exact hp
  | sentAckEliciting => simpa using hp
  | tickIdleTimeout hp' _ => exact absurd hp' hna
  | tickIdleStay hp' _ => exact absurd hp' hna
  | tickPeriodOver hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickPeriodContinue hp' => simp [State.inClosePeriod, hp] at hp'
  | tickEndEarly hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickClosed _ => exact hp
  | localErrorActive hp' => exact absurd hp' hna
  | localErrorLate _ => exact hp
  | appCloseActive hp' => exact absurd hp' hna
  | appCloseLate _ => exact hp
  | recvCloseActive hp' => exact absurd hp' hna
  | recvCloseActiveReply hp' => exact absurd hp' hna
  | recvCloseClosingDrain hp' => exact absurd hp' hnc
  | recvCloseClosingRespond hp' => exact absurd hp' hnc
  | recvCloseClosingSilent hp' => exact absurd hp' hnc
  | recvCloseDraining hp' => exact absurd hp' hnd
  | recvCloseClosed _ => exact hp
  | recvCloseClosedReset _ => exact hp
  | statelessReset => simp [State.onStatelessReset, hp]
  | pnExhausted hp' => exact absurd hp hp'
  | pnExhaustedClosed _ => exact hp
  | handshakeConfirmed => simpa using hp

/-- §10.2, line 3954 / §12.3, line 4696: from `closed` the only thing that may
    still go on the wire is a stateless reset. -/
theorem closed_emits_only_statelessReset {s e s' fx} (hp : s.phase = .closed)
    (h : Step s e (.ok s' fx)) : ∀ x ∈ fx, x.sendsPacket = true → x = .sendStatelessReset := by
  have hna : s.phase ≠ .active := by rw [hp]; simp
  have hnc : s.phase ≠ .closing := by rw [hp]; simp
  have hnd : s.phase ≠ .draining := by rw [hp]; simp
  cases h with
  | recvActive hp' => exact absurd hp' hna
  | recvClosingRespond hp' => exact absurd hp' hnc
  | recvClosingSilent hp' => exact absurd hp' hnc
  | recvDraining hp' => exact absurd hp' hnd
  | recvClosed _ => simp
  | recvClosedReset _ => simp
  | sentAckEliciting => simp
  | tickIdleTimeout hp' _ => exact absurd hp' hna
  | tickIdleStay hp' _ => exact absurd hp' hna
  | tickPeriodOver hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickPeriodContinue hp' => simp [State.inClosePeriod, hp] at hp'
  | tickEndEarly hp' _ => simp [State.inClosePeriod, hp] at hp'
  | tickClosed _ => simp
  | localErrorActive hp' => exact absurd hp' hna
  | localErrorLate _ => simp
  | appCloseActive hp' => exact absurd hp' hna
  | appCloseLate _ => simp
  | recvCloseActive hp' => exact absurd hp' hna
  | recvCloseActiveReply hp' => exact absurd hp' hna
  | recvCloseClosingDrain hp' => exact absurd hp' hnc
  | recvCloseClosingRespond hp' => exact absurd hp' hnc
  | recvCloseClosingSilent hp' => exact absurd hp' hnc
  | recvCloseDraining hp' => exact absurd hp' hnd
  | recvCloseClosed _ => simp
  | recvCloseClosedReset _ => simp
  | statelessReset => simp
  | pnExhausted hp' => exact absurd hp hp'
  | pnExhaustedClosed _ => simp
  | handshakeConfirmed => simp

/-- Every state reachable from a `closed` one is `closed`. -/
theorem reachable_closed {s₀ s : State} (hp : s₀.phase = .closed)
    (h : component.Reachable s₀ s) : s.phase = .closed :=
  component.reachable_induction (motive := fun x => x.phase = .closed) hp
    (fun _ hstep hmot => closed_absorbing hmot hstep) h

/-- §12.3, line 4693: "If the packet number for sending reaches 2^62 - 1, the
    sender MUST close the connection without sending a CONNECTION_CLOSE frame or
    any further packets".  The step itself sends nothing and lands in `closed`;
    `MaySend` is then `False` for every frame. -/
theorem pnExhausted_closes_silently {s : State} {now : Time} {pto : Nat}
    {s' : State} {fx : List Effect} (h : Step s (.pnExhausted now pto) (.ok s' fx)) :
    s'.phase = .closed ∧ (∀ x ∈ fx, x.sendsPacket = false) ∧ ∀ f : Frame, ¬ MaySend s' f := by
  cases h with
  | pnExhausted _ =>
    exact ⟨rfl, by simp [Effect.sendsPacket], fun f =>
      maySend_false_of_draining_or_closed _ f (.inr rfl)⟩
  | pnExhaustedClosed hp =>
    exact ⟨hp, by simp, fun f => maySend_false_of_draining_or_closed _ f (.inr hp)⟩

/-- §12.3, line 4695: "... or any further packets; an endpoint MAY send a
    Stateless Reset (Section 10.3) in response to further packets that it
    receives."  After packet-number exhaustion, no permitted step — now or from
    any state reachable afterwards — puts anything on the wire except a
    stateless reset. -/
theorem pnExhausted_no_further_packets {s : State} {now : Time} {pto : Nat}
    {s₁ : State} {fx₁ : List Effect} (h : Step s (.pnExhausted now pto) (.ok s₁ fx₁))
    {s₂ : State} (hr : component.Reachable s₁ s₂)
    {e : Event} {s₃ : State} {fx₃ : List Effect} (h₃ : Step s₂ e (.ok s₃ fx₃)) :
    ∀ x ∈ fx₃, x.sendsPacket = true → x = .sendStatelessReset :=
  closed_emits_only_statelessReset (reachable_closed (pnExhausted_closes_silently h).1 hr) h₃

/-- … and no packet at all may be assembled after exhaustion. -/
theorem pnExhausted_no_packet_may_be_sent {s : State} {now : Time} {pto : Nat}
    {s₁ : State} {fx₁ : List Effect} (h : Step s (.pnExhausted now pto) (.ok s₁ fx₁))
    {s₂ : State} (hr : component.Reachable s₁ s₂) (p : OutPacket) :
    ¬ MaySendPacket s₂ p := by
  have := reachable_closed (pnExhausted_closes_silently h).1 hr
  simp [MaySendPacket, this]

/-! ## 9. Examples (scenarios from the text) -/

private def s0 : State :=
  { init 30000000 10000000 false with handshakeConfirmed := true }

-- §10.1: the effective value is the minimum of the two advertised values …
example : s0.negotiatedIdle = 10000000 := by decide
-- … but at least 3 PTO (here PTO = 5 s, so 15 s wins over the negotiated 10 s).
example : s0.effectiveIdle 5000000 = 15000000 := by decide
-- §10.1 line 3831, "longer than": at the deadline instant nothing is due …
example : component.step s0 (.tick 15000000 5000000) = .ok s0 [] := by decide
example : component.accepts s0 (.tick 15000000 5000000)
    (.ok { s0 with phase := .closed } [.discardState]) = false := by decide
-- … one microsecond later the connection is silently closed.
example : component.step s0 (.tick 15000001 5000000) =
    .ok { s0 with phase := .closed } [.discardState] := by decide

-- §10.1: receiving restarts the timer and clears "ack-eliciting already sent".
example : component.step s0 (.recvPacket 7000 0 true) =
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
example : component.step sClosing (.recvPacket 1500 400 true) =
    .ok sClosing [.sendClose (.transport .protocolViolation 0x08)] := by decide
example : component.accepts sClosing (.recvPacket 1500 400 true) (.ok sClosing []) = true := by
  decide
-- §10.2.1 line 4008: from an *unvalidated* address, discarding is the other
-- permitted alternative …
example : component.accepts sClosing (.recvPacket 1500 400 false) .drop = true := by decide
-- … but not from a validated one.
example : component.accepts sClosing (.recvPacket 1500 400 true) .drop = false := by decide
-- and a stateless reset is never the answer while we still hold state (§11 l.4441)
example : component.accepts sClosing (.recvPacket 1500 400 true)
    (.ok sClosing [.sendStatelessReset]) = false := by decide

-- §10.2.2: a CONNECTION_CLOSE received while closing moves us to draining with
-- the *same* end time.
example : component.step sClosing (.recvClose 1500 400 (.transport .noError 0) true) =
    .ok { sClosing with phase := .draining } [] := by decide
-- the closing period's own deadline closes the connection …
example : component.step { sClosing with phase := .draining } (.tick (1000 + 3 * 400) 400) =
    .ok { sClosing with phase := .closed } [.discardState] := by decide
-- … but §10.2 line 3939 bounds the period only below, so persisting is fine too.
example : component.accepts { sClosing with phase := .draining } (.tick (1000 + 3 * 400) 400)
    (.ok { sClosing with phase := .draining } []) = true := by decide

-- §10.2.2: draining sends nothing, whatever arrives.
example : component.step { sClosing with phase := .draining } (.recvPacket 1600 400 true) =
    .ok { sClosing with phase := .draining } [] := by decide
example : component.maySend { sClosing with phase := .draining } .ping = false := by decide
example : component.maySend { sClosing with phase := .draining }
    (.connectionClose 0 (some 0) ByteArray.empty) = false := by decide
-- §10.2.1 forbids no frame in the closing state, so `MaySend` forbids none …
example : component.maySend sClosing (.connectionClose 0 (some 0) ByteArray.empty) = true := by
  decide
example : component.maySend sClosing (.padding 3) = true := by decide
example : component.maySend sClosing (.ack 3 0 0 #[] none) = true := by decide
example : component.maySend sClosing .ping = true := by decide
-- … the rule that bites is the packet-level one.
example : component.maySendPacket sClosing
    { ptype := .oneRtt,
      frames := [.connectionClose 0 (some 0) ByteArray.empty, .padding 1100] } = true := by decide
example : component.maySendPacket sClosing
    { ptype := .oneRtt, frames := [.padding 1200] } = false := by decide
example : component.maySendPacket sClosing
    { ptype := .oneRtt, frames := [.ack 3 0 0 #[] none,
                                   .connectionClose 0 (some 0) ByteArray.empty] } = true := by
  decide
-- §10.2.3 line 4056: the handshake is confirmed in `s0`, and the bit survives
-- into the closing state, so the close must go in a 1-RTT packet.
example : sClosing.handshakeConfirmed = true := by decide
example : component.maySendPacket sClosing
    { ptype := .handshake, frames := [.connectionClose 0 (some 0) ByteArray.empty] } = false := by
  decide
-- §19.19 line 8187: the application variant 0x1d may not travel in an Initial …
example : component.maySendPacket (init 0 0 false)
    { ptype := .initial, frames := [.connectionClose 7 none ByteArray.empty] } = false := by decide
-- … but may in a 1-RTT packet
example : component.maySendPacket (init 0 0 false)
    { ptype := .oneRtt, frames := [.connectionClose 7 none ByteArray.empty] } = true := by decide
-- §10.2.2: while draining not even an empty packet may be sent
example : component.maySendPacket { sClosing with phase := .draining }
    { ptype := .oneRtt, frames := [] } = false := by decide

-- §10.3.1: a detected stateless reset drains without sending anything.
example : component.step s0 (.statelessReset 2000 400) =
    .ok { s0 with phase := .draining, closeDeadline := 2000 + 3 * 400 } [] := by decide

-- §10.2.2 line 4037: on receiving CONNECTION_CLOSE while active, a single reply
-- is the permitted alternative to silence.  Its error code is not fixed by the
-- text ("a NO_ERROR code if appropriate"), so the effect does not fix it.
example : component.accepts s0 (.recvClose 2000 400 (.application 7) true)
    (.ok { s0 with phase := .draining, closeDeadline := 2000 + 3 * 400,
                   closedWith := some (.application 7) }
          [.sendFarewellClose]) = true := by decide

-- §12.3, line 4693: the sending packet number reaches 2^62 - 1.  The connection
-- closes at once, with no CONNECTION_CLOSE frame and no further packets …
example : component.step s0 (.pnExhausted 5000 400) =
    .ok { s0 with phase := .closed } [.discardState] := by decide
example : component.step sClosing (.pnExhausted 5000 400) =
    .ok { sClosing with phase := .closed } [.discardState] := by decide
example : component.maySend { s0 with phase := .closed } .ping = false := by decide
-- … but the MAY of line 4696 keeps the stateless reset available afterwards.
example : component.accepts { s0 with phase := .closed } (.recvPacket 6000 400 true)
    (.ok { s0 with phase := .closed } [.sendStatelessReset]) = true := by decide
example : component.accepts { s0 with phase := .closed } (.recvPacket 6000 400 true)
    (.ok { s0 with phase := .closed } [.sendClose (.transport .noError 0)]) = false := by decide

-- §10.3 / §10.3.3: stateless reset sizes.  Without anti-loop state the reset
-- must be smaller than the datagram that triggered it …
example : maySendStatelessReset false 1200 43 = true := by decide
example : maySendStatelessReset false 43 43 = false := by decide
example : maySendStatelessReset false 21 20 = false := by decide
example : maySendStatelessReset false 22 21 = true := by decide
-- … with it, only the 3× amplification limit of line 4215 applies.
example : maySendStatelessReset true 30 40 = true := by decide
example : maySendStatelessReset true 30 30 = true := by decide
example : maySendStatelessReset true 13 40 = false := by decide   -- 40 ≥ 3 × 13

-- §10.2.3 / §19.19: an application close is converted to type 0x1c with
-- APPLICATION_ERROR and an empty reason for an Initial or Handshake packet.
example : convertCloseForHandshake (.connectionClose 7 none ByteArray.empty) =
    .connectionClose 0xc (some 0) ByteArray.empty := by decide

-- Following an implementation we cannot see inside: it answered a packet in the
-- closing state, so it is still closing.
example : component.track sClosing (.recvPacket 1500 400 true)
    (.ok [.sendClose (.transport .protocolViolation 0x08)]) = some sClosing := by rfl

/-! ## 10. Coverage and notes

Assigned text: §10 and §11 (lines 3813–4515) and §19.19 (8125–8192), plus the
one sentence of §12.3 (line 4693) whose consequence is a connection close.
Cited line numbers are the line on which the quoted sentence starts.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §10 (3824) | "An endpoint MAY discard connection state if it does not have a validated path" | out of scope: path validation is WP5 |
| §10.1 (3829) | idle connection is "silently closed and its state is discarded ... when it remains idle for longer than" the effective value (the "longer than" is on 3831) | `State.idleExpired` (strict), `Step.tickIdleTimeout`, `idle_timeout_closes`, `idle_timeout_silent`, `idle_deadline_instant_stays` |
| §10.1 (3834) | effective value = min of the two advertised, or the sole non-zero one | `State.negotiatedIdle`, `negotiatedIdle_eq_min`, `negotiatedIdle_zero` |
| §10.1 (3837) | "By announcing a max_idle_timeout, an endpoint commits to initiating an immediate close ... if it abandons the connection prior to the effective value." | `Step.localErrorActive` / `Step.appCloseActive` are the only ways to abandon before the timeout, and both emit `Effect.sendClose`; the silent close is reachable only through `Step.tickIdleTimeout`, which requires `idleExpired` |
| §10.1 (3841) | restart the idle timer on a packet received and processed | `Step.recvActive`, `State.restartIdle` |
| §10.1 (3842) | restart on sending an ack-eliciting packet only if it is the first since the last receive | `State.onAckElicitingSent`, `ackEliciting_restarts_first/_only_first` |
| §10.1 (3848) | MUST increase the idle timeout to at least 3 PTO | `State.effectiveIdle`, `effectiveIdle_ge_three_pto` |
| §10.1.1 (3856) | liveness testing: send PING if the peer could time out soon | advice, not checkable here: no normative keyword, and *when* to send is the application's choice; `Event.sentAckEliciting` is how it reaches this component |
| §10.1.2 (3875) | deferring the idle timeout by sending PING | advice, not checkable here: the same, with the PING's effect entering as `Event.sentAckEliciting` |
| §10.1.2 (3893) | application protocols SHOULD provide guidance on when deferring is appropriate | advice, not checkable here: it constrains application-protocol documents, not an endpoint's outcomes |
| §10.2 (3907) | a CONNECTION_CLOSE frame closes all streams implicitly | out of scope: stream states are WP2/WP9 |
| §10.2 (3912) | after sending CONNECTION_CLOSE, enter closing | `State.toClosing` (`Step.localErrorActive`, `Step.appCloseActive`) |
| §10.2 (3913) | after receiving CONNECTION_CLOSE, enter draining | `Step.recvCloseActive` |
| §10.2 (3925) | "Violations of the protocol lead to an immediate close." | `Step.localErrorActive` |
| §10.2 (3932) | an application close carries an application-supplied error code | `Step.appCloseActive`, `CloseReason.application` |
| §10.2 (3939) | closing/draining SHOULD persist ≥ 3 PTO | `closePeriod`, `State.closeDeadline`, `Recommended.closePeriodLongEnough`; the period is bounded only below, hence `Step.tickPeriodContinue` |
| §10.2 (3946) | MAY end these states earlier | `Step.tickEndEarly` (gated on `State.mayEndEarly`) |
| §10.2 (3949) | servers **that retain an open socket for accepting new connections** SHOULD NOT end early | `Recommended.serverWithOpenSocketDoesNotEndEarly`, with the qualifier as the `retainsOpenSocket` parameter |
| §10.2 (3953) | SHOULD discard all connection state once the closing or draining state ends | `Effect.discardState` |
| §10.2 (3954) | MAY send a stateless reset in response to any further incoming packets | `Step.recvClosedReset`, `Step.recvCloseClosedReset` |
| §10.2.1 (3960) | enters closing after initiating an immediate close | `State.toClosing` |
| §10.2.1 (3963) | closing retains only enough information to generate a CONNECTION_CLOSE packet | not a send restriction: see NOTES on theorem (b) |
| §10.2.1 (3965) | closing answers any incoming packet with a packet containing CONNECTION_CLOSE | `Step.recvClosingRespond`, `Step.recvCloseClosingRespond`; "containing" is `closingPacketOk` inside `MaySendPacket`, `maySendPacket_closing_iff` |
| §10.2.1 (3969) | SHOULD limit the rate of packets generated while closing | `Step.recvClosingSilent`, `Step.recvCloseClosingSilent` (the permitted alternative) |
| §10.2.1 (3981, 3983, 3985) | MAY discard other connection state / not required to process frames / MAY retain keys | out of scope: key and CID state are WP4/WP11; "not required to process any received frame" is why `Step.recvClosingSilent` exists |
| §10.2.1 (3988) | MAY drop keys and answer any UDP datagram | out of scope: key state is WP11 |
| §10.2.1 (3992) | an endpoint that dropped keys MUST limit what it sends to 3× what it received (the MUST is on 3993) | byte accounting: `AddressValidation` owns the 3× budget; this package supplies the phase, and `Step.recvClosingSilent` is the outcome that lets an endpoint stop answering when the budget is exhausted |
| §10.2.1 (3995) | MAY send the exact same packet in response to any received packet | `Step.recvClosingRespond` always emits `Effect.sendClose s.reason`, the same packet every time; `maySend_stable` |
| §10.2.1 (4008) | closing MUST **either** discard packets from an unvalidated address **or** apply the 3× limit to that address | both alternatives: `Step.recvClosingDiscardUnvalidated` / `Step.recvCloseClosingDiscardUnvalidated` and `Step.recvClosingRespond`; `closing_unvalidated_alternatives`. The byte accounting for the second is `AddressValidation`'s |
| §10.2.1 (4013) | key updates while closing | out of scope: WP11 |
| §10.2.2 (4021) | draining is entered on receiving a CONNECTION_CLOSE | `Step.recvCloseActive`, `Step.recvCloseClosingDrain` |
| §10.2.2 (4023) | draining MUST NOT send any packets (the MUST NOT is on 4024) | `MaySend` = `False`, `maySend_false_of_draining_or_closed`, `MaySendPacket` = `False`, `draining_emits_no_packet` |
| §10.2.2 (4037) | MAY send a single CONNECTION_CLOSE before entering draining; MUST NOT send further packets | `Step.recvCloseActiveReply` emitting `Effect.sendFarewellClose` (one packet, code unconstrained) and `MaySend` = `False` afterwards |
| §10.2.2 (4039) | that packet uses "a NO_ERROR code if appropriate" | `recommendedFarewellReason` (advice; `Step` fixes no code) |
| §10.2.2 (4044) | MAY enter draining from closing, with the same end time | `Step.recvCloseClosingDrain`, `drain_from_closing_keeps_deadline` |
| §10.2.3 (4056) | after confirmation, CONNECTION_CLOSE MUST be in a 1-RTT packet | `closeAfterConfirmationOk` inside `MaySendPacket`, reading `State.handshakeConfirmed` |
| §10.2.3 (4058, 4067, 4078) | MAY/SHOULD send CONNECTION_CLOSE at lower levels before confirmation | `MaySendPacket` with `handshakeConfirmed = false` permits every packet type for 0x1c; the SHOULDs are advice, not checkable here: they recommend sending *more* copies, which no single-packet predicate can require |
| §10.2.3 (4084, 4095) | 0x1d MUST be replaced by 0x1c in Initial/Handshake; MUST clear the reason phrase, SHOULD use APPLICATION_ERROR | `convertCloseForHandshake`, `maySendCloseIn_convert` |
| §10.2.3 (4099) | CONNECTION_CLOSE in several packet types may be coalesced | out of scope: datagram assembly is WP12 |
| §10.2.3 (4111) | MAY discard packets rather than close on errors in unauthenticated packets | out of scope: error *detection* belongs to the detecting component; WP12 composes |
| §10.2.3 (4114) | an endpoint with no connection state does not enter closing/draining | `Step.localErrorLate` covers the "already terminating" case; the stateless server is out of scope (no state to model) |
| §10.3 (4125) | MAY send a stateless reset for a packet it cannot associate with a connection | out of scope: that is the no-connection path (WP12 dispatch); the in-connection case is `Step.recvClosedReset` |
| §10.3 (4129) | an endpoint that wishes to signal a fatal error MUST use CONNECTION_CLOSE if it is able | `Effect.sendStatelessReset` is produced only from `Phase.closed`, where `MaySend` is `False`; see the `no_reset_while_sendable` note |
| §10.3 (4133–4188) | issuing and scoping tokens; the stateless reset packet layout | out of scope: token issuance is WP4, packet layout is the wire package |
| §10.3 (4191) | SHOULD pad all packets to ≥ 22 + the minimum connection ID length | advice, not checkable here: it is about *every* packet's size, which is WP7/`DatagramSize`'s field, not this component's |
| §10.3 (4205) | reset for a ≤ 43-byte trigger SHOULD be one byte shorter (the sentence starts on 4196, before a page break) | `recommendedStatelessResetSize` |
| §10.3 (4215) | MUST NOT send a reset ≥ 3× the packet it receives | `maySendStatelessReset`, `statelessReset_amplification` |
| §10.3 (4220) | MUST discard packets too small to be valid QUIC packets | `minStatelessResetSize`, `statelessReset_needs_large_trigger`; discarding the received packet is WP12 |
| §10.3 (4225) | MUST send resets formatted as short-header packets | out of scope: wire format |
| §10.3 (4226) | MUST treat any packet ending in a valid token as a stateless reset | `Event.statelessReset` (the match is opaque, as assigned) |
| §10.3 (4230) | MAY send a reset in response to a long-header packet | out of scope: no-connection path |
| §10.3.1 (4282, 4293, 4298) | which tokens are remembered, MAY skip the check, MUST check when undecryptable, MUST NOT check unused/retired tokens | out of scope: token bookkeeping is WP4; this component consumes the boolean result |
| §10.3.1 (4302) | MUST compare without leaking information | out of scope: implementation technique, not observable behaviour |
| §10.3.1 (4323) | on a match MUST enter the draining period and send nothing further | `Step.statelessReset`, `statelessReset_drains_silently` |
| §10.3.2 (4329, 4352, 4361, 4374, 4377) | calculating the token; MUST NOT reuse | out of scope: assigned as "generating stateless reset tokens" |
| §10.3.3 (4393) | every reset MUST be smaller than the packet that triggered it, **unless it maintains state sufficient to prevent looping** | `maySendStatelessReset`, whose first argument is the "unless" clause |
| §10.3.3 (4405) | below 41 bytes a reset may be recognisable | an observation, not a recommendation: deliberately not encoded (see the doc comment on `recommendedStatelessResetSize`) |
| §11 (4415) | an endpoint that detects an error SHOULD signal it to its peer | `Step.localErrorActive` emits `Effect.sendClose`; the SHOULD's alternative (say nothing) is `Step.localErrorLate` once already terminating |
| §11 (4429) | the most appropriate error code SHOULD be included | advice, not checkable here: the code arrives already chosen on `Event.localError` |
| §11 (4434) | MAY use any applicable error code; a generic code can always be used in place of a specific one | `Spec.Obs.matchesSpec` in `Core` (`TransportError.isGeneric`): the harness accepts a generic code wherever the model names a specific one |
| §11 (4441) | a stateless reset MUST NOT be used by an endpoint that has the state to send a frame | see the `no_reset_while_sendable` note |
| §11.1 (4446) | connection errors MUST be signalled with CONNECTION_CLOSE | `Step.localErrorActive` |
| §11.1 (4451) | 0x1d for application errors, 0x1c for transport errors | `CloseReason` |
| §11.1 (4457) | SHOULD be prepared to retransmit CONNECTION_CLOSE on further packets | `Step.recvClosingRespond` with `State.reason`; `maySend_stable` shows the repeat stays acceptable |
| §11.1 (4464) | an endpoint that chooses not to retransmit risks the peer missing the first packet | not normative (an observation); the choice is `Step.recvClosingSilent` |
| §11.1 (4485) | MAY discard an invalid Initial packet, "even where this specification otherwise mandates a connection error" | out of scope: WP12 Endpoint. It widens *every* component's error outcomes for Initial packets, so it must be applied once at composition, not duplicated in each package |
| §11.2 (4494, 4503, 4513) | stream errors; RESET_STREAM MUST only be instigated by the application; application protocols SHOULD define rules for cancelled streams | out of scope: streams are WP2/WP9 |
| §19.19 (8127, 8137–8185) | CONNECTION_CLOSE frame format and fields | out of scope: wire format (already done); `CloseReason` mirrors the two variants |
| §19.19 (8134) | open streams are implicitly closed | out of scope: WP2/WP9 |
| §19.19 (8158) | frame type 0 means "the frame type is unknown" | `CloseReason.transport`'s `frameType`; `convertCloseForHandshake` uses 0 |
| §19.19 (8182) | the reason phrase SHOULD be a UTF-8 string | out of scope: wire format; the model does not carry reason phrases |
| §19.19 (8187) | 0x1d can only be sent in 0-RTT or 1-RTT packets | `appCloseFrameOk` → `maySendCloseIn` → `MaySendPacket` |
| §12.3 (4692) | MUST NOT reuse a packet number within a packet number space | out of scope: WP3 owns packet numbers |
| §12.3 (4693) | on reaching 2^62 - 1 the sender MUST close without a CONNECTION_CLOSE frame or any further packets | `Event.pnExhausted`, `Step.pnExhausted`, `pnExhausted_closes_silently`, `pnExhausted_no_further_packets`, `pnExhausted_no_packet_may_be_sent` (WP3 detects; this package is the consequence) |
| §12.3 (4696) | MAY send a Stateless Reset in response to further packets | `Step.recvClosedReset` / `Step.recvCloseClosedReset`, reachable because exhaustion lands in `closed`; `closed_emits_only_statelessReset` |

NOTES

- The spec has no name for the phase before termination begins; `Phase.active`
  is it (`open` is a Lean keyword).  "Handshake confirmed" is **not** part of
  the phase but a field of its own, `State.handshakeConfirmed`: §10.2.3
  line 4056 constrains the packet that carries the CONNECTION_CLOSE, which is
  sent from the `closing` state, so the bit has to survive `State.toClosing`.
  `handshakeConfirmed_mono` shows it is never cleared.
- **Theorem (b) has now been stated three ways, and this is the final one.**
  First reading: closing permits only CONNECTION_CLOSE.  Second: CONNECTION_CLOSE
  or PADDING, because §14.1 makes a client pad a datagram carrying an Initial.
  Both were stricter than the text.  §10.2 and §10.2.1 (lines 3905–3997)
  describe what a closing endpoint *retains* and *sends*; not one sentence
  forbids any frame.  A closing endpoint that coalesces an ACK with its
  CONNECTION_CLOSE violates nothing.  So `MaySend` in `closing` is `True`
  (`maySend_closing`), and the only real rule — line 3965's "a packet
  *containing* a CONNECTION_CLOSE frame" — is packet-level, in `MaySendPacket`
  via `closingPacketOk` (`maySendPacket_closing_iff`).  `closingPacketOk` also
  says nothing about the other frames, for the same reason.
- `MaySend` reads nothing but the phase (`maySend_of_phase_eq`), so a frame that
  was acceptable stays acceptable for as long as the phase does
  (`maySend_stable`); the CONNECTION_CLOSE that §11.1 line 4457 tells an
  endpoint to retransmit is accepted every time it is repeated.
- The two deadlines are treated differently, and deliberately.  The idle timeout
  uses a **strict** comparison: §10.1 line 3829 says the connection is closed
  when it "remains idle for longer than" the effective value (line 3831), so at
  `idleStart + effective` exactly nothing is due (`idle_deadline_instant_stays`),
  and only after that is the silent close the one permitted outcome
  (`idle_timeout_closes`).  The closing and draining periods, by contrast, are
  bounded only *below* — §10.2 line 3939 is a SHOULD that "These states SHOULD
  persist for at least three times the current Probe Timeout (PTO) interval" —
  so a tick at or after `closeDeadline`
  *permits* the move to `closed` and *also* permits persisting
  (`Step.tickPeriodContinue`); `close_period_reaches_closed` therefore states
  that the close is permitted, is what `component.step` does, and that the only
  other permitted outcome is to stay.
- §10.2.1 line 4008's either/or is modelled as two permitted outcomes for a
  packet received from an unvalidated address while closing: `.drop` (discard)
  and the ordinary response (`closing_unvalidated_alternatives`).  Whether the
  address is validated is a Bool on the receive events; WP5 decides it.  The
  *byte* accounting of lines 3993 and 4008 — "three times the cumulative size"
  — is `AddressValidation`'s budget, not duplicated here, but this component no
  longer claims the sentences are out of its range.
- `maySendStatelessReset` takes the "unless it maintains state sufficient to
  prevent looping" exemption of §10.3.3 line 4393 as its first argument.  With
  it `true`, only the 3× amplification limit of §10.3 line 4215 and the 21-byte
  minimum remain.
- `Component.MaySendDatagram` is left at its default.  `maySendStatelessReset`
  is about a datagram that is not made of QUIC packets at all (§10.3, line 4177:
  "A stateless reset uses an entire UDP datagram, starting with the first two
  bits of the packet header"), and it relates the reset's size to the size of
  the datagram that *triggered* it, which `Spec.OutDatagram` does not carry.  It
  stays free-standing for WP12.
- Packet-number exhaustion (§12.3, line 4693) lands directly in `closed`, not in
  `closing` or `draining`.  `closing` is out because the text forbids sending a
  CONNECTION_CLOSE frame at all, which is the only thing the closing state is
  for.  `draining` is out because §10.2.2 line 4023 makes it "MUST NOT send any
  packets", which would forbid the stateless reset that the second half of the
  same §12.3 sentence explicitly permits.  `closed` is the phase where `MaySend`
  is `False` for every frame *and* §10.2 line 3954 still permits "a stateless
  reset in response to any further incoming packets".  The event is a no-op once
  already `closed`.
- "A packet received while closing": the permitted outcomes are
  `Step.recvClosingRespond` (answer with CONNECTION_CLOSE — the preferred
  outcome, and what `component.step` produces), `Step.recvClosingSilent`
  (suppressed by the SHOULD-level rate limit of line 3969, or by an exhausted
  amplification budget), `Step.recvClosingDiscardUnvalidated` (line 4008's first
  alternative, only for an unvalidated address) and, when the packet carried a
  CONNECTION_CLOSE, `Step.recvCloseClosingDrain` (move to draining and answer
  nothing).  Received packets are split into two events — `recvPacket` for one
  without a CONNECTION_CLOSE frame and `recvClose` for one with — because the
  two have different consequences in every phase.
- `Effect.sendFarewellClose` is §10.2.2 line 4037's "single packet containing a
  CONNECTION_CLOSE frame **before entering** the draining state".  The step that
  emits it ends in `draining`, where `MaySendPacket` is `False`; WP12 must check
  that one packet against the state the step started from, not the state it
  ended in.  The effect carries no error code because line 4039 does not fix one
  ("a NO_ERROR code if appropriate"); the hint is `recommendedFarewellReason`.
  `Effect.sendClose` does carry a reason, but only where the text fixes one: the
  code supplied by the `localError`/`appClose` event, and the same code again
  when that close is retransmitted from `closedWith`.
- Entering draining on a *stateless reset* from the `active` phase starts a
  fresh 3-PTO period (`now + 3 × PTO`); from `closing` it keeps the closing
  state's end time, by analogy with §10.2.2 line 4046.  The text says only
  "MUST enter the draining period" and does not fix the deadline for this case.
- `Effect.discardState` marks §10.2 line 3953; the `closed` phase is this
  model's name for "after the closing or draining state ends".  It is kept as a
  phase rather than deleting the state because line 3954 still permits a
  stateless reset from there, and because `track` needs somewhere to go.
- `no_reset_while_sendable`: §10.3 line 4129 and §11 line 4441 forbid a
  stateless reset from an endpoint that can still send a frame.  In this model
  `Effect.sendStatelessReset` is produced only from `Phase.closed`, where
  `MaySend` is `False` for every frame (`maySend_false_of_draining_or_closed`),
  so the two rules are consistent by construction rather than by a separate
  theorem.
- `Event.handshakeConfirmed` and `Event.pnExhausted` are not in the original
  assigned list of events: the first is needed to ever set
  `State.handshakeConfirmed`, the second is §12.3 line 4693's trigger, detected
  by WP3.
- `State.mayEndEarly` encodes the endpoint capability of §10.2 line 3946
  ("some alternative means to ensure that late-arriving packets do not induce a
  response").  With it `false` a tick before the deadline always keeps the
  phase; `Recommended.serverWithOpenSocketDoesNotEndEarly` is the SHOULD NOT of
  line 3949, with its "that retain an open socket for accepting new connections"
  qualifier as an explicit parameter.
-/

end Quic.Spec.Termination
