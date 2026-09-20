import QuicModel.Spec.FrameRules

/-
  WP7a: §14 Datagram Size (lines 5640–5919).

  What is modelled here: the receive-side rules that decide the fate of a
  datagram because of its size (§14.1's "a server MUST discard an Initial packet
  carried in a datagram smaller than 1200 bytes"), the ICMP rules of §14.2.1
  that change the endpoint's maximum datagram size, and — on the send side — the
  size constraints on a datagram the endpoint is about to send (§14.1, §14.2,
  §14.4), as the component's `MaySendDatagram` over `Spec.OutDatagram`.

  The DPLPMTUD search algorithm itself (§14.3) is deliberately absent: only the
  constraints on what may be sent are specified, so `maxDatagramSize` moves here
  only when the text says it MUST NOT move (ICMP) — how it is raised is the
  implementation's business.

  File order follows `Spec/Template.lean`.
-/
namespace Quic.Spec.DatagramSize

open Quic.Spec (OutPacket OutDatagram)

/-- §14, line 5649: "QUIC MUST NOT be used if the network path cannot support a
    maximum datagram size of at least 1200 bytes."  This is also the value §14.1
    calls "the smallest allowed maximum datagram size". -/
def smallestMaxDatagramSize : Nat := 1200

/-- §18.2, line 6963: "The default for this parameter is the maximum permitted
    UDP payload of 65527." -/
def defaultMaxUdpPayloadSize : Nat := 65527

/-! ## 1. State, events, effects -/

structure State where
  /-- Which end of the connection this is; §14.1 states different rules for
      each. -/
  role : Role
  /-- §18.2: the peer's `max_udp_payload_size`, once it has been received. -/
  peerMaxUdpPayload : Option Nat
  /-- §18.2, line 6957: this endpoint's own `max_udp_payload_size`, which
      "limits the size of UDP payloads that the endpoint is willing to
      receive". -/
  localMaxUdpPayload : Nat := defaultMaxUdpPayloadSize
  /-- §14.2, line 5742: "The largest UDP payload an endpoint sends at any given
      time is referred to as the endpoint's maximum datagram size." -/
  maxDatagramSize : Nat
  /-- False once §14.2's "the PMTU ... cannot support the smallest allowed
      maximum datagram size" has been determined for this path. -/
  pathUsable : Bool
  /-- §14.2, line 5746: whether this endpoint runs DPLPMTUD or PMTUD at all.
      Line 5749's "in the absence of these mechanisms" advice applies only when
      it does not. -/
  runsPmtuDiscovery : Bool
  deriving DecidableEq, Repr

inductive Event where
  /-- §14.1: an Initial packet arrived, carried in a UDP datagram whose payload
      was `datagramSize` bytes. -/
  | recvInitial (datagramSize : Nat)
  /-- A datagram of `size` bytes arrived.  §14, line 5695: whatever its size,
      receiving it must not close the connection.  `required` is the smallest
      size the text required of the *sender* of this datagram on account of
      what it carries — 1200 for a PATH_CHALLENGE (§8.2.1, line 3154) or a
      PATH_RESPONSE (§8.2.2, line 3197) — and 0 when no such rule applies.
      Only the layer that sees the frames can know it, so the caller supplies
      it.  §14.1's rule for Initial packets is `recvInitial`'s. -/
  | recvDatagram (size : Nat) (required : Nat)
  /-- §18.2: the peer's `max_udp_payload_size` transport parameter arrived.
      Validating the value is WP1's (`TransportParams`) job, not this file's. -/
  | recvMaxUdpPayload (v : Nat)
  /-- §14.2.1: an ICMP Packet Too Big message that has already passed the
      validation of §14.2.1 claims this PMTU (as a UDP payload size). -/
  | icmpPtb (pmtu : Nat)
  /-- §14.2: PMTU discovery determined that this path cannot support the
      smallest allowed maximum datagram size.  `alternativeExists` is §14.2 line
      5762's "if an alternative path cannot be found", negated: true when the
      endpoint has another path it can move to. -/
  | pathBelowMinimum (alternativeExists : Bool)
  deriving DecidableEq, Repr

inductive Effect where
  /-- The datagram is handed on to packet processing. -/
  | deliver
  /-- §14.2: "MUST immediately cease sending QUIC packets ... on the affected
      path", except PMTU probes and CONNECTION_CLOSE. -/
  | ceaseSending
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-- §14, line 5695's "a datagram that does not meet size constraints", for a
    received datagram: it is smaller than a rule of the text required of its
    sender (line 5691, "QUIC sometimes requires datagrams to be no smaller than
    a certain size"), or larger than this endpoint said it is willing to receive
    (§18.2, line 6966: `max_udp_payload_size` "does act as an additional
    constraint on datagram size"). -/
def FailsSizeConstraint (s : State) (size required : Nat) : Prop :=
  size < required ∨ s.localMaxUdpPayload < size

instance (s : State) (size required : Nat) : Decidable (FailsSizeConstraint s size required) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §14.1, line 5727: "A server MUST discard an Initial packet that is carried
      in a UDP datagram with a payload that is smaller than the smallest allowed
      maximum datagram size of 1200 bytes." -/
  | initialTooSmallDrop {s n} (hr : s.role = .server) (hn : n < smallestMaxDatagramSize) :
      Step s (.recvInitial n) .drop
  /-- §14.1, line 5729: "A server MAY also immediately close the connection by
      sending a CONNECTION_CLOSE frame with an error code of
      PROTOCOL_VIOLATION." -/
  | initialTooSmallClose {s n} (hr : s.role = .server) (hn : n < smallestMaxDatagramSize) :
      Step s (.recvInitial n) (.error .protocolViolation)
  /-- Otherwise the Initial packet is processed: a client has no rule about the
      size of datagrams it receives, and a server's rule is met. -/
  | initialOk {s n} (h : ¬ (s.role = .server ∧ n < smallestMaxDatagramSize)) :
      Step s (.recvInitial n) (.ok s [.deliver])
  /-- §5.2, line 1878: "Invalid packets that lack strong integrity protection,
      such as Initial, Retry, or Version Negotiation, MAY be discarded."
      §11.1, line 4485: "As the AEAD on Initial packets does not provide strong
      authentication, an endpoint MAY discard an invalid Initial packet." -/
  | initialDiscard {s n} (h : ¬ (s.role = .server ∧ n < smallestMaxDatagramSize)) :
      Step s (.recvInitial n) .drop
  /-- §14, line 5695: "an endpoint MUST NOT close a connection when it receives a
      datagram that does not meet size constraints".  No size constraint of §14
      is attached to a datagram as such, so processing it is always permitted —
      the discard below is a MAY. -/
  | datagramOk {s n r} : Step s (.recvDatagram n r) (.ok s [.deliver])
  /-- §14, line 5697: "endpoint MAY however discard such datagrams" — the
      permission that goes with the MUST NOT above, and like it limited to a
      datagram "that does not meet size constraints".  A datagram that meets
      them is not discarded *here*; the discards other rules permit (failed
      decryption, duplicates, §9's and §5.2's) live with those rules. -/
  | datagramDiscard {s n r} (h : FailsSizeConstraint s n r) :
      Step s (.recvDatagram n r) .drop
  /-- §18.2, line 6966: the peer's limit "does act as an additional constraint on
      datagram size in the same way as the path MTU".  Recording it is all this
      component does with it; the value's validity is WP1's. -/
  | maxUdpPayload {s v} :
      Step s (.recvMaxUdpPayload v) (.ok { s with peerMaxUdpPayload := some v } [])
  /-- §14.2.1, line 5793: "An endpoint MUST ignore an ICMP message that claims
      the PMTU has decreased below QUIC's smallest allowed maximum datagram
      size." -/
  | icmpBelowMinimum {s p} (h : p < smallestMaxDatagramSize) :
      Step s (.icmpPtb p) (.ok s [])
  /-- §14.2.1, line 5813: "An endpoint MUST NOT increase PMTU based on ICMP
      messages." -/
  | icmpNoIncrease {s p} (h : ¬ p < smallestMaxDatagramSize) (hp : s.maxDatagramSize ≤ p) :
      Step s (.icmpPtb p) (.ok s [])
  /-- §14.2.1: a validated PTB below the current maximum datagram size reduces
      it. -/
  | icmpReduce {s p} (h : ¬ p < smallestMaxDatagramSize) (hp : p < s.maxDatagramSize) :
      Step s (.icmpPtb p) (.ok { s with maxDatagramSize := p } [])
  /-- §14.2.1, line 5814: "Any reduction in QUIC's maximum datagram size in
      response to ICMP messages MAY be provisional until QUIC's loss detection
      algorithm determines that the quoted packet has actually been lost." —
      so not acting on the message yet is also permitted. -/
  | icmpDefer {s p} (h : ¬ p < smallestMaxDatagramSize) (hp : p < s.maxDatagramSize) :
      Step s (.icmpPtb p) (.ok s [])
  /-- §14.2, line 5758: "If a QUIC endpoint determines that the PMTU ... cannot
      support the smallest allowed maximum datagram size of 1200 bytes, it MUST
      immediately cease sending QUIC packets, except for those in PMTU probes or
      those containing CONNECTION_CLOSE frames, on the affected path." -/
  | pathLost {s alt} :
      Step s (.pathBelowMinimum alt) (.ok { s with pathUsable := false } [.ceaseSending])
  /-- §14.2, line 5762: "An endpoint MAY terminate the connection if an
      alternative path cannot be found."  §8.2.4, line 3262 hedges the same
      permission: "MAY signal this using the NO_VIABLE_PATH connection error,
      noting that this is only possible if the network path exists but does not
      support the required MTU" — which is exactly this event. -/
  | pathLostTerminate {s} : Step s (.pathBelowMinimum false) (.error .noViablePath)

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvInitial n =>
    if s.role = .server ∧ n < smallestMaxDatagramSize then
      [.drop, .error .protocolViolation]
    else [.ok s [.deliver], .drop]
  | .recvDatagram n r =>
    if FailsSizeConstraint s n r then [.ok s [.deliver], .drop] else [.ok s [.deliver]]
  | .recvMaxUdpPayload v => [.ok { s with peerMaxUdpPayload := some v } []]
  | .icmpPtb p =>
    if p < smallestMaxDatagramSize then [.ok s []]
    else if s.maxDatagramSize ≤ p then [.ok s []]
    else [.ok { s with maxDatagramSize := p } [], .ok s []]
  | .pathBelowMinimum alt =>
    if alt then [.ok { s with pathUsable := false } [.ceaseSending]]
    else [.ok { s with pathUsable := false } [.ceaseSending], .error .noViablePath]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvInitial n =>
      simp only [outcomes] at h
      split at h
      · rename_i hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .initialTooSmallDrop hc.1 hc.2
        · exact .initialTooSmallClose hc.1 hc.2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .initialOk ‹_›
        · exact .initialDiscard ‹_›
    | recvDatagram n r =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .datagramOk
        · exact .datagramDiscard ‹_›
      · simp only [List.mem_singleton] at h; subst h; exact .datagramOk
    | recvMaxUdpPayload v =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .maxUdpPayload
    | icmpPtb p =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .icmpBelowMinimum ‹_›
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .icmpNoIncrease ‹_› ‹_›
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .icmpReduce ‹_› (Nat.lt_of_not_le ‹_›)
          · exact .icmpDefer ‹_› (Nat.lt_of_not_le ‹_›)
    | pathBelowMinimum alt =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .pathLost
      · rename_i halt
        simp only [Bool.not_eq_true] at halt
        subst halt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .pathLost
        · exact .pathLostTerminate
  · intro h
    cases h with
    | initialTooSmallDrop hr hn => simp [outcomes, hr, hn]
    | initialTooSmallClose hr hn => simp [outcomes, hr, hn]
    | initialOk h => simp [outcomes, h]
    | initialDiscard h => simp [outcomes, h]
    | datagramOk => simp only [outcomes]; split <;> simp
    | datagramDiscard h => simp [outcomes, h]
    | maxUdpPayload => simp [outcomes]
    | icmpBelowMinimum h => simp [outcomes, h]
    | icmpNoIncrease h hp => simp [outcomes, h, hp]
    | icmpReduce h hp =>
      have : ¬ _ ≤ _ := Nat.not_le.mpr hp
      simp [outcomes, h, this]
    | icmpDefer h hp =>
      have : ¬ _ ≤ _ := Nat.not_le.mpr hp
      simp [outcomes, h, this]
    | @pathLost alt => cases alt <;> simp [outcomes]
    | pathLostTerminate => simp [outcomes]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- §14, line 5649: a path that is in use supports at least the smallest allowed
    maximum datagram size, so the endpoint's maximum datagram size never falls
    below it — in particular ICMP can never push it lower (§14.2.1). -/
def Inv (s : State) : Prop := smallestMaxDatagramSize ≤ s.maxDatagramSize

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | initialOk => exact hi
  | datagramOk => exact hi
  | maxUdpPayload => exact hi
  | icmpBelowMinimum => exact hi
  | icmpNoIncrease => exact hi
  | icmpDefer => exact hi
  | pathLost => exact hi
  | icmpReduce h _ => exact Nat.le_of_not_lt h

/-! ## 6. Send side

No frame is governed by datagram size — the constraint is on the datagram — so
`MaySend` is `True` everywhere and the real content of this section is the
component's `MaySendDatagram` over `Spec.OutDatagram`. -/

/-- §14.1: does this datagram carry an Initial packet? -/
def carriesInitial (d : OutDatagram) : Bool := d.packets.any (fun p => p.ptype == .initial)

/-- §14.1: does it carry an *ack-eliciting* Initial packet?  Ack-elicitation is
    `FrameRules.packetAckEliciting` on that packet's frames (Table 3, §12.4). -/
def carriesAckElicitingInitial (d : OutDatagram) : Bool :=
  d.packets.any (fun p => p.ptype == .initial && FrameRules.packetAckEliciting p.frames)

/-- §14.4, line 5873: "PMTU probes are ack-eliciting packets."  A datagram is
    ack-eliciting when one of the packets in it is. -/
def ackEliciting (d : OutDatagram) : Bool :=
  d.packets.any (fun p => FrameRules.packetAckEliciting p.frames)

/-- §14.2's exception: does the datagram carry a CONNECTION_CLOSE frame? -/
def carriesConnectionClose (d : OutDatagram) : Bool :=
  d.packets.any (fun p => p.frames.any (fun f => match f with
    | .connectionClose .. => true
    | _ => false))

/-- The MUSTs of §14 about a datagram this endpoint sends. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §14.1, line 5701: "A client MUST expand the payload of all UDP datagrams
  -- carrying Initial packets to at least ... 1200 bytes ... Similarly, a server
  -- MUST expand the payload of all UDP datagrams carrying ack-eliciting Initial
  -- packets to at least ... 1200 bytes."
  (carriesInitial d = true → s.role = .client ∨ carriesAckElicitingInitial d = true →
      smallestMaxDatagramSize ≤ d.size) ∧
  -- §14.4, line 5873: "PMTU probes are ack-eliciting packets."
  (d.isPmtuProbe = true → ackEliciting d = true) ∧
  -- §14.2, line 5758: once the path is known not to support 1200 bytes, only
  -- PMTU probes and datagrams containing CONNECTION_CLOSE may still be sent.
  (s.pathUsable = false → d.isPmtuProbe = true ∨ carriesConnectionClose d = true)

def maySendDatagram (s : State) (d : OutDatagram) : Bool :=
  (!carriesInitial d || !(decide (s.role = .client) || carriesAckElicitingInitial d) ||
      decide (smallestMaxDatagramSize ≤ d.size)) &&
  (!d.isPmtuProbe || ackEliciting d) &&
  (s.pathUsable || d.isPmtuProbe || carriesConnectionClose d)

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by
  cases hci : carriesInitial d <;> cases hai : carriesAckElicitingInitial d <;>
    cases hpr : d.isPmtuProbe <;> cases hae : ackEliciting d <;>
    cases hcc : carriesConnectionClose d <;> cases hpu : s.pathUsable <;>
    cases hrole : s.role <;>
    simp [maySendDatagram, MaySendDatagram, hci, hai, hpr, hae, hcc, hpu, hrole]

/-- §14.2/§18.2 advice, which is SHOULD-strength and therefore kept out of
    `MaySendDatagram`: an implementation that ignores it still conforms. -/
def RecommendedDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §14.2, line 5753: "All QUIC packets that are not sent in a PMTU probe
  -- SHOULD be sized to fit within the maximum datagram size".
  (d.isPmtuProbe = false → d.size ≤ s.maxDatagramSize) ∧
  -- §14.2: a PMTU probe is by definition larger than the current maximum.
  (d.isPmtuProbe = true → s.maxDatagramSize < d.size) ∧
  -- §14.2, line 5749: "QUIC endpoints SHOULD NOT send datagrams larger than the
  -- smallest allowed maximum datagram size" — "in the absence of these
  -- mechanisms", i.e. when neither DPLPMTUD nor PMTUD is running.
  (s.runsPmtuDiscovery = false → d.size ≤ smallestMaxDatagramSize) ∧
  -- §14, line 5679 with §18.2, line 6966: stay within what the peer said it is
  -- willing to receive, once that value is known.
  (∀ v, s.peerMaxUdpPayload = some v → d.size ≤ v)

/-- No frame is governed by this component. -/
def MaySend (_ : State) (_ : Frame) : Prop := True
def maySend (_ : State) (_ : Frame) : Bool := true
theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

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
  MaySendDatagram := MaySendDatagram
  maySendDatagram := maySendDatagram
  maySendDatagram_iff := maySendDatagram_iff

/-! ## 8. Named theorems -/

/-- §14.1: a server never processes an Initial packet that arrived in a datagram
    smaller than 1200 bytes — the only outcomes are discarding it or closing the
    connection with PROTOCOL_VIOLATION. -/
theorem server_never_processes_small_initial {s : State} {n : Nat} {o : Out}
    (hr : s.role = .server) (hn : n < smallestMaxDatagramSize)
    (h : Step s (.recvInitial n) o) : o = .drop ∨ o = .error .protocolViolation := by
  cases h with
  | initialTooSmallDrop => exact Or.inl rfl
  | initialTooSmallClose => exact Or.inr rfl
  | initialOk hc => exact absurd ⟨hr, hn⟩ hc
  | initialDiscard hc => exact absurd ⟨hr, hn⟩ hc

/-- §14, line 5695: "an endpoint MUST NOT close a connection when it receives a
    datagram that does not meet size constraints".  For every datagram that does
    not carry an Initial packet — whatever its size — no outcome is an error. -/
theorem no_close_on_datagram_size {s : State} {n r : Nat} {o : Out}
    (h : Step s (.recvDatagram n r) o) : ∀ c, o ≠ .error c := by
  cases h <;> (intro c; simp)

/-- §14, line 5697: the discard is permitted for "such datagrams" only — a
    datagram is discarded by this component exactly when it fails a size
    constraint. -/
theorem datagram_drop_iff {s : State} {n r : Nat} :
    Step s (.recvDatagram n r) .drop ↔ FailsSizeConstraint s n r :=
  ⟨fun h => by cases h; assumption, .datagramDiscard⟩

/-- … so a datagram that meets its size constraints is handed on, and whatever
    error its content mandates cannot be evaded through this component. -/
theorem datagram_delivered_of_size_ok {s : State} {n r : Nat} {o : Out}
    (hc : ¬ FailsSizeConstraint s n r) (h : Step s (.recvDatagram n r) o) :
    o = .ok s [.deliver] := by
  cases h with
  | datagramOk => rfl
  | datagramDiscard h => exact absurd h hc

/-- §14.1 line 5727, §5.2 line 1878 and §11.1 line 4485: discarding an Initial
    packet is always permitted. -/
theorem initial_drop_always_permitted (s : State) (n : Nat) :
    Step s (.recvInitial n) .drop := by
  by_cases h : s.role = .server ∧ n < smallestMaxDatagramSize
  · exact .initialTooSmallDrop h.1 h.2
  · exact .initialDiscard h

/-- §14.2.1: ICMP never raises the endpoint's maximum datagram size. -/
theorem icmp_never_increases {s s' : State} {p : Nat} {fx : List Effect}
    (h : Step s (.icmpPtb p) (.ok s' fx)) : s'.maxDatagramSize ≤ s.maxDatagramSize := by
  cases h with
  | icmpBelowMinimum => exact Nat.le_refl _
  | icmpNoIncrease => exact Nat.le_refl _
  | icmpDefer => exact Nat.le_refl _
  | icmpReduce _ hp => exact Nat.le_of_lt hp

/-- §14.2.1: an ICMP message claiming a PMTU below the smallest allowed maximum
    datagram size changes nothing at all. -/
theorem icmp_below_minimum_ignored {s : State} {p : Nat} {o : Out}
    (hp : p < smallestMaxDatagramSize) (h : Step s (.icmpPtb p) o) : o = .ok s [] := by
  cases h with
  | icmpBelowMinimum => rfl
  | icmpNoIncrease h => exact absurd hp h
  | icmpReduce h => exact absurd hp h
  | icmpDefer h => exact absurd hp h

/-- §14.2, line 5762: the connection error is permitted only when no alternative
    path can be found; while one exists, the path is abandoned but the
    connection is not. -/
theorem no_error_while_alternative_exists {s : State} {o : Out}
    (h : Step s (.pathBelowMinimum true) o) :
    o = .ok { s with pathUsable := false } [.ceaseSending] := by
  cases h with
  | pathLost => rfl

/-- §14.1: every datagram a client sends that carries an Initial packet is at
    least 1200 bytes. -/
theorem client_initial_expanded {s : State} {d : OutDatagram}
    (hr : s.role = .client) (hi : carriesInitial d = true) (h : MaySendDatagram s d) :
    smallestMaxDatagramSize ≤ d.size := h.1 hi (Or.inl hr)

/-- §14.1: every datagram a server sends that carries an ack-eliciting Initial
    packet is at least 1200 bytes. -/
theorem server_ackEliciting_initial_expanded {s : State} {d : OutDatagram}
    (hi : carriesInitial d = true) (ha : carriesAckElicitingInitial d = true)
    (h : MaySendDatagram s d) : smallestMaxDatagramSize ≤ d.size :=
  h.1 hi (Or.inr ha)

/-- §14.2: on a path that cannot carry 1200 bytes, only PMTU probes and
    CONNECTION_CLOSE datagrams may be sent — and in particular the endpoint can
    no longer send an Initial packet on it. -/
theorem no_initial_on_dead_path {s : State} {d : OutDatagram}
    (hp : s.pathUsable = false) (_hi : carriesInitial d = true)
    (hnc : carriesConnectionClose d = false) (h : MaySendDatagram s d) :
    d.isPmtuProbe = true := by
  rcases h.2.2 hp with h' | h'
  · exact h'
  · exact absurd h' (by simp [hnc])

/-- The invariant is not vacuous: an endpoint that starts at the smallest
    allowed maximum datagram size stays at or above it forever. -/
theorem maxDatagramSize_ge_min {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) : smallestMaxDatagramSize ≤ s.maxDatagramSize :=
  component.inv_of_reachable h0 h

/-! ## 9. Examples (scenarios from the text) -/

private def srv : State :=
  { role := .server, peerMaxUdpPayload := none,
    maxDatagramSize := smallestMaxDatagramSize, pathUsable := true,
    runsPmtuDiscovery := false }
private def cli : State := { srv with role := .client }

-- §14.1: "A server MUST discard an Initial packet that is carried in a UDP
-- datagram with a payload that is smaller than ... 1200 bytes."
example : component.step srv (.recvInitial 1199) = .drop := by decide
-- … and it MAY instead close with PROTOCOL_VIOLATION, but nothing else.
example : component.accepts srv (.recvInitial 1199) (.error .protocolViolation) = true := by decide
example : component.accepts srv (.recvInitial 1199) (.ok srv [.deliver]) = false := by decide
-- A full-size Initial is processed …
example : component.step srv (.recvInitial 1200) = .ok srv [.deliver] := by decide
-- … or discarded: §5.2 line 1878 and §11.1 line 4485 permit discarding an
-- Initial packet, which lacks strong integrity protection.
example : component.accepts srv (.recvInitial 1200) .drop = true := by decide
-- A client has no size rule for Initials it receives, and may still discard.
example : component.step cli (.recvInitial 200) = .ok cli [.deliver] := by decide
example : component.accepts cli (.recvInitial 200) .drop = true := by decide
-- §14 lines 5695/5697: receiving an undersized datagram — here one that carries
-- a PATH_CHALLENGE and so had to be 1200 bytes — never closes the connection,
-- and discarding it is permitted.
example : component.step srv (.recvDatagram 20 1200) = .ok srv [.deliver] := by decide
example : component.accepts srv (.recvDatagram 20 1200) .drop = true := by decide
example : component.accepts srv (.recvDatagram 20 1200) (.error .protocolViolation) = false := by
  decide
-- The same for a datagram larger than our own `max_udp_payload_size` (§18.2).
example : component.accepts { srv with localMaxUdpPayload := 1472 } (.recvDatagram 1473 0) .drop =
    true := by decide
-- A datagram that meets its size constraints is *not* discarded on §14's
-- authority: 20 bytes with nothing in them that had to be expanded …
example : component.accepts srv (.recvDatagram 20 0) .drop = false := by decide
-- … and an expanded PATH_CHALLENGE datagram.
example : component.accepts srv (.recvDatagram 1200 1200) .drop = false := by decide
-- §14.2.1: "MUST ignore an ICMP message that claims the PMTU has decreased
-- below QUIC's smallest allowed maximum datagram size."
example : component.step { cli with maxDatagramSize := 1452 } (.icmpPtb 1000) =
    .ok { cli with maxDatagramSize := 1452 } [] := by decide
-- A validated PTB above the minimum lowers the maximum datagram size …
example : component.step { cli with maxDatagramSize := 1452 } (.icmpPtb 1280) =
    .ok { cli with maxDatagramSize := 1280 } [] := by decide
-- … and §14.2.1 lets the reduction be provisional, so ignoring it also conforms.
example : component.accepts { cli with maxDatagramSize := 1452 } (.icmpPtb 1280)
    (.ok { cli with maxDatagramSize := 1452 } []) = true := by decide
-- §14.2.1: "MUST NOT increase PMTU based on ICMP messages."
example : component.step { cli with maxDatagramSize := 1280 } (.icmpPtb 1452) =
    .ok { cli with maxDatagramSize := 1280 } [] := by decide
-- §14.2: a path that cannot carry 1200 bytes stops the flow of packets …
example : component.step cli (.pathBelowMinimum true) =
    .ok { cli with pathUsable := false } [.ceaseSending] := by decide
-- … and NO_VIABLE_PATH is permitted only when no alternative path exists.
example : component.accepts cli (.pathBelowMinimum true) (.error .noViablePath) = false := by decide
example : component.accepts cli (.pathBelowMinimum false) (.error .noViablePath) = true := by decide

-- Send side, over `Spec.OutDatagram`.
private def initialPkt (ackEliciting : Bool) : OutPacket :=
  { ptype := .initial,
    frames := if ackEliciting then [.crypto 0 .empty] else [.ack 0 0 0 #[] none] }
private def oneRttPkt : OutPacket := { ptype := .oneRtt, frames := [.ping] }
private def closePkt : OutPacket :=
  { ptype := .oneRtt, frames := [.connectionClose 0 none .empty] }

-- §14.1: a client's Initial datagram must be expanded to 1200 bytes.
example : component.maySendDatagram cli
    { size := 1200, packets := [initialPkt true] } = true := by decide
example : component.maySendDatagram cli
    { size := 1199, packets := [initialPkt true] } = false := by decide
-- §14.1: a server's *non*-ack-eliciting Initial (a pure ACK) need not be.
example : component.maySendDatagram srv
    { size := 100, packets := [initialPkt false] } = true := by decide
example : component.maySendDatagram srv
    { size := 100, packets := [initialPkt true] } = false := by decide
-- §14.4: "PMTU probes are ack-eliciting packets."
example : component.maySendDatagram cli
    { size := 1400, packets := [{ ptype := .oneRtt, frames := [.padding 100] }],
      isPmtuProbe := true } = false := by decide
example : component.maySendDatagram cli
    { size := 1400, packets := [oneRttPkt], isPmtuProbe := true } = true := by decide
-- §14.2: on a dead path only probes and CONNECTION_CLOSE may still be sent.
example : component.maySendDatagram { cli with pathUsable := false }
    { size := 100, packets := [oneRttPkt] } = false := by decide
example : component.maySendDatagram { cli with pathUsable := false }
    { size := 100, packets := [closePkt] } = true := by decide

/-! ## 10. Coverage and notes

Assigned range: lines 5640–5919 (§14) and, for the size constant, 5920–5958
(§15, whose version rules live in `Spec/VersionNegotiation.lean`).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §14 (5649) | QUIC MUST NOT be used if the path cannot support 1200 bytes | `smallestMaxDatagramSize`, `Step.pathLost`, `MaySendDatagram` third clause |
| §14 (5679) | enforcement of `max_udp_payload_size` might limit datagram size | `RecommendedDatagram` fourth clause; no normative keyword here, and §18.2 line 6966 makes it path-MTU-strength, i.e. SHOULD |
| §14 (5687) | UDP datagrams MUST NOT be fragmented at the IP layer; DF bit MUST be set | out of scope: below the transport, not observable in this model |
| §14 (5695) | MUST NOT close a connection on a datagram that fails size constraints | `Step.datagramOk`, theorem `no_close_on_datagram_size` |
| §14 (5697) | "endpoint MAY however discard such datagrams" | `Step.datagramDiscard`, gated on `FailsSizeConstraint`; theorems `datagram_drop_iff`, `datagram_delivered_of_size_ok` |
| §14.1 (5701) | a client MUST expand Initial-carrying datagrams to ≥ 1200 | `MaySendDatagram` first clause, `client_initial_expanded` |
| §14.1 (5706) | a server MUST expand ack-eliciting-Initial-carrying datagrams to ≥ 1200 | `MaySendDatagram` first clause, `server_ackEliciting_initial_expanded` |
| §14.1 (5723) | Initial datagrams MAY exceed 1200 bytes | `MaySendDatagram` bounds size only from below |
| §14.1 (5727) | a server MUST discard an Initial in a datagram < 1200 | `Step.initialTooSmallDrop`, `server_never_processes_small_initial` |
| §14.1 (5729) | a server MAY close with PROTOCOL_VIOLATION instead | `Step.initialTooSmallClose` |
| §14.1 (5733) | the server MUST also limit bytes sent before validating the address | out of scope: WP5 `AddressValidation` (anti-amplification) |
| §14.2 (5746) | an endpoint SHOULD use DPLPMTUD or PMTUD | advice, not checkable here: a choice of mechanism, not a constraint on an event or a datagram; its consequence is the next row |
| §14.2 (5749) | absent those mechanisms, SHOULD NOT send datagrams larger than 1200 | `RecommendedDatagram` third clause, gated on `State.runsPmtuDiscovery` |
| §14.2 (5753) | non-probe packets SHOULD be sized to fit the maximum datagram size | `RecommendedDatagram` first clause |
| §14.2 (5758) | MUST cease sending except probes and CONNECTION_CLOSE below 1200 PMTU | `Step.pathLost`, `MaySendDatagram` third clause, `no_initial_on_dead_path` |
| §14.2 (5762) | MAY terminate the connection if an alternative path cannot be found | `Step.pathLostTerminate`, gated on the event's `alternativeExists`; `no_error_while_alternative_exists` |
| §14.2 (5774) | SHOULD maintain a maximum datagram size per address pair | advice, not checkable here: one `State` is one path, and the table of paths is WP10 `Migration` |
| §14.2 (5778) | MAY be more conservative in computing the maximum datagram size | permitted: `MaySendDatagram` never requires a datagram to be *large*, except Initials |
| §14.2.1 (5793) | MUST ignore an ICMP message claiming PMTU < 1200 | `Step.icmpBelowMinimum`, `icmp_below_minimum_ignored` |
| §14.2.1 (5803) | SHOULD validate ICMP messages; validation MUST match addresses and ports | advice, not checkable here: the `icmpPtb` event is a message that already passed validation, and addresses and ports are not in this component's state |
| §14.2.1 (5810) | SHOULD ignore all ICMP messages that fail validation | same as the row above: a message that fails validation never becomes an event |
| §14.2.1 (5813) | MUST NOT increase PMTU based on ICMP | `Step.icmpNoIncrease`, `icmp_never_increases` |
| §14.2.1 (5814) | a reduction MAY be provisional | `Step.icmpDefer` |
| §14.3 (5837) | SHOULD set BASE_PLPMTU consistently with 1200 | advice, not checkable here: a DPLPMTUD internal parameter, and the search algorithm is out of scope by PLAN §1 |
| §14.3 (5841–5869) | DPLPMTUD MPS per address pair, BASE state, ICMP validation | out of scope by PLAN §1: only the constraints on what may be sent are modelled |
| §14.4 (5873) | PMTU probes are ack-eliciting packets | `MaySendDatagram` second clause |
| §14.4 (5889) | loss of a probe SHOULD NOT trigger a congestion reaction | out of scope: congestion control is RFC 9002 |
| §14.4.1 (5894–5918) | how to build a probe that quotes a Source Connection ID | advice, not checkable here: no normative keyword, and it constrains only what an ICMP message will quote |
| §15 (5924) | version 0x00000000 is reserved for version negotiation | `Spec/VersionNegotiation.lean` |
| §5.2 (1878) | invalid Initial/Retry/VN packets MAY be discarded | `Step.initialDiscard` (the Initial half; Retry is WP5, Version Negotiation is `Spec/VersionNegotiation.lean`) |
| §11.1 (4485) | MAY discard an invalid Initial packet, even where an error is mandated | `Step.initialDiscard`; the "even where mandated" half is WP12's, which must union this `.drop` with the error outcomes other components require |

NOTES

- §14 line 5695 ("MUST NOT close a connection when it receives a datagram that
  does not meet size constraints") and §14.1 line 5729 ("A server MAY also
  immediately close the connection by sending a CONNECTION_CLOSE frame with an
  error code of PROTOCOL_VIOLATION") contradict each other for the one case both
  cover: a server receiving an Initial in a datagram below 1200 bytes.  The
  reading encoded is that the specific rule wins — `Step.initialTooSmallClose`
  exists, and `no_close_on_datagram_size` is therefore stated only for
  `.recvDatagram`, not for `.recvInitial`.
- **Discarding is for datagrams that fail a size constraint.**  §14 line 5697's
  MAY is about "such datagrams", so `Step.datagramDiscard` carries
  `FailsSizeConstraint`.  This component cannot see which constraint a datagram
  had to meet — §8.2.1's and §8.2.2's 1200-byte rules are about frames — so the
  event carries `required`, which `Endpoint.Pipeline.requiredSize` reads off the
  datagram's frames; the upper bound is the endpoint's own
  `max_udp_payload_size`.  Until the audit of 2026-09-19 (finding B3) the
  discard was permitted for *every* datagram, which let any mandated error be
  evaded through this component and hid ngtcp2's repeated-sequence
  NEW_CONNECTION_ID deviation (`DIFFERENCES.md` A2) from the pairwise harness.
  The discards the text permits for other reasons stay with their rules:
  failed decryption and §12.2 (`Pipeline.recvParsed`), §12.3 duplicates (`Ack`),
  §9 (`Migration`), §5.2.1/§5.2.2 (`VersionNeg`), §11.1 for an invalid Initial
  (`Pipeline.packetErrOutcomes`).  `Step.initialDiscard` is still unconditional
  for Initial packets, on the strength of §5.2 line 1878 and §11.1 line 4485.
- **`.drop` is per-datagram here.**  "A server MUST discard an Initial packet" is
  about a *packet*; this model handles a datagram as a whole, so `.drop` means
  the Initial packet is discarded.  A datagram smaller than 1200 bytes cannot
  usefully coalesce anything behind a conforming Initial; a component that wants
  per-packet granularity is WP12's `Endpoint`.
- **NO_VIABLE_PATH.**  §14.2 line 5762's MAY is gated on "if an alternative path
  cannot be found", which the event now carries.  §8.2.4 line 3262 hedges the
  same permission with "only possible if the network path exists but does not
  support the required MTU" — exactly the situation `pathBelowMinimum`
  describes, which is why this component owns the error while `PathValidation`
  (its NOTES 6) deliberately does not: after a failed *probe* nothing is known
  about the MTU, so the error is not permitted there.
- The `max_udp_payload_size` limit is SHOULD-strength: §18.2 line 6966 says it
  constrains datagram size "in the same way as the path MTU", and the path-MTU
  rule (§14.2 line 5753) is a SHOULD.  It is therefore in `RecommendedDatagram`,
  not in `MaySendDatagram`, so that an implementation that overruns the peer's
  advertised limit is not rejected by the differential harness.
- §14.4's "PMTU probes are ack-eliciting packets" is declarative, not a MUST.
  It is encoded in `MaySendDatagram` anyway, because `isPmtuProbe` is the
  sender's own annotation of a datagram: a datagram that is not ack-eliciting
  simply is not a probe.  Ack-elicitation is read off the frames with
  `FrameRules.packetAckEliciting`, so the two packages cannot drift apart.
- `maxDatagramSize` only ever decreases in this component (ICMP).  Raising it is
  the DPLPMTUD search, which is out of scope; a caller that implements the
  search sets the field directly.
- Validating the peer's `max_udp_payload_size` (§18.2: "Values below 1200 are
  invalid") is WP1's, so `Step.maxUdpPayload` stores whatever arrives and `Inv`
  says nothing about it.
-/

end Quic.Spec.DatagramSize
