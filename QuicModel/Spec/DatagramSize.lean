import QuicModel.Spec.Core

/-
  WP7a: §14 Datagram Size (lines 5640–5919).

  What is modelled here: the receive-side rules that decide the fate of a
  datagram because of its size (§14.1's "a server MUST discard an Initial packet
  carried in a datagram smaller than 1200 bytes"), the ICMP rules of §14.2.1
  that change the endpoint's maximum datagram size, and — on the send side — the
  size constraints on a datagram the endpoint is about to send (§14.1, §14.2,
  §14.4).

  The DPLPMTUD search algorithm itself (§14.3) is deliberately absent: only the
  constraints on what may be sent are specified, so `maxDatagramSize` moves here
  only when the text says it MUST NOT move (ICMP) — how it is raised is the
  implementation's business.

  File order follows `Spec/Template.lean`.
-/
namespace Quic.Spec.DatagramSize

/-- §14, line 5650: "QUIC MUST NOT be used if the network path cannot support a
    maximum datagram size of at least 1200 bytes."  This is also the value §14.1
    calls "the smallest allowed maximum datagram size". -/
def smallestMaxDatagramSize : Nat := 1200

/-- §18.2, line 6963: the default `max_udp_payload_size`. -/
def defaultMaxUdpPayloadSize : Nat := 65527

/-! ## 1. State, events, effects -/

structure State where
  /-- Which end of the connection this is; §14.1 states different rules for
      each. -/
  role : Role
  /-- §18.2: the peer's `max_udp_payload_size`, once it has been received. -/
  peerMaxUdpPayload : Option Nat
  /-- §14.2: "The largest UDP payload an endpoint sends at any given time is
      referred to as the endpoint's maximum datagram size." -/
  maxDatagramSize : Nat
  /-- False once §14.2's "the PMTU ... cannot support the smallest allowed
      maximum datagram size" has been determined for this path. -/
  pathUsable : Bool
  deriving DecidableEq, Repr

inductive Event where
  /-- §14.1: an Initial packet arrived, carried in a UDP datagram whose payload
      was `datagramSize` bytes. -/
  | recvInitial (datagramSize : Nat)
  /-- Any other datagram arrived.  §14, line 5695: whatever its size, receiving
      it must not close the connection. -/
  | recvDatagram (size : Nat)
  /-- §18.2: the peer's `max_udp_payload_size` transport parameter arrived.
      Validating the value is WP1's (`TransportParams`) job, not this file's. -/
  | recvMaxUdpPayload (v : Nat)
  /-- §14.2.1: an ICMP Packet Too Big message that has already passed the
      validation of §14.2.1 claims this PMTU (as a UDP payload size). -/
  | icmpPtb (pmtu : Nat)
  /-- §14.2: PMTU discovery determined that this path cannot support the
      smallest allowed maximum datagram size. -/
  | pathBelowMinimum
  deriving DecidableEq, Repr

inductive Effect where
  /-- The datagram is handed on to packet processing. -/
  | deliver
  /-- §14.2: "MUST immediately cease sending QUIC packets ... on the affected
      path", except PMTU probes and CONNECTION_CLOSE. -/
  | ceaseSending
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

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
  /-- §14, line 5695: "an endpoint MUST NOT close a connection when it receives a
      datagram that does not meet size constraints".  No size constraint of §14
      governs a datagram that carries no Initial packet, so it is processed. -/
  | datagramOk {s n} : Step s (.recvDatagram n) (.ok s [.deliver])
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
  | pathLost {s} :
      Step s .pathBelowMinimum (.ok { s with pathUsable := false } [.ceaseSending])
  /-- §14.2, line 5762: "An endpoint MAY terminate the connection if an
      alternative path cannot be found." -/
  | pathLostTerminate {s} : Step s .pathBelowMinimum (.error .noViablePath)

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvInitial n =>
    if s.role = .server ∧ n < smallestMaxDatagramSize then
      [.drop, .error .protocolViolation]
    else [.ok s [.deliver]]
  | .recvDatagram _ => [.ok s [.deliver]]
  | .recvMaxUdpPayload v => [.ok { s with peerMaxUdpPayload := some v } []]
  | .icmpPtb p =>
    if p < smallestMaxDatagramSize then [.ok s []]
    else if s.maxDatagramSize ≤ p then [.ok s []]
    else [.ok { s with maxDatagramSize := p } [], .ok s []]
  | .pathBelowMinimum =>
    [.ok { s with pathUsable := false } [.ceaseSending], .error .noViablePath]

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
      · simp only [List.mem_singleton] at h; subst h; exact .initialOk ‹_›
    | recvDatagram n =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .datagramOk
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
    | pathBelowMinimum =>
      simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> subst h
      · exact .pathLost
      · exact .pathLostTerminate
  · intro h
    cases h with
    | initialTooSmallDrop hr hn => simp [outcomes, hr, hn]
    | initialTooSmallClose hr hn => simp [outcomes, hr, hn]
    | initialOk h => simp [outcomes, h]
    | datagramOk => simp [outcomes]
    | maxUdpPayload => simp [outcomes]
    | icmpBelowMinimum h => simp [outcomes, h]
    | icmpNoIncrease h hp => simp [outcomes, h, hp]
    | icmpReduce h hp =>
      have : ¬ _ ≤ _ := Nat.not_le.mpr hp
      simp [outcomes, h, this]
    | icmpDefer h hp =>
      have : ¬ _ ≤ _ := Nat.not_le.mpr hp
      simp [outcomes, h, this]
    | pathLost => simp [outcomes]
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
`MaySend` is `True` everywhere and the real content of this section is
`MaySendDatagram`, a predicate on the datagram the endpoint is about to send. -/

/-- The size-relevant summary of a datagram about to be sent. -/
structure OutDatagram where
  /-- UDP payload size (§14: "not the UDP or IP headers"). -/
  size : Nat
  /-- It carries an Initial packet. -/
  carriesInitial : Bool
  /-- That Initial packet is ack-eliciting (§14.1's server rule). -/
  initialAckEliciting : Bool
  /-- It is a PMTU probe (§14.2, §14.4). -/
  isProbe : Bool
  /-- It is ack-eliciting. -/
  ackEliciting : Bool
  /-- It carries a CONNECTION_CLOSE frame (§14.2's exception). -/
  carriesConnectionClose : Bool
  deriving DecidableEq, Repr

/-- The MUSTs of §14 about a datagram this endpoint sends. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §14.1, line 5701: "A client MUST expand the payload of all UDP datagrams
  -- carrying Initial packets to at least ... 1200 bytes ... Similarly, a server
  -- MUST expand the payload of all UDP datagrams carrying ack-eliciting Initial
  -- packets to at least ... 1200 bytes."
  (d.carriesInitial = true → s.role = .client ∨ d.initialAckEliciting = true →
      smallestMaxDatagramSize ≤ d.size) ∧
  -- §14.4, line 5873: "PMTU probes are ack-eliciting packets."
  (d.isProbe = true → d.ackEliciting = true) ∧
  -- §14.2, line 5758: once the path is known not to support 1200 bytes, only
  -- PMTU probes and datagrams containing CONNECTION_CLOSE may still be sent.
  (s.pathUsable = false → d.isProbe = true ∨ d.carriesConnectionClose = true)

def maySendDatagram (s : State) (d : OutDatagram) : Bool :=
  (!d.carriesInitial || !(s.role == .client || d.initialAckEliciting) ||
      smallestMaxDatagramSize ≤ d.size) &&
  (!d.isProbe || d.ackEliciting) &&
  (s.pathUsable || d.isProbe || d.carriesConnectionClose)

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by
  cases s with | mk role pm mds pu =>
  cases d with | mk size ci iae ip ae cc =>
  cases role <;> cases ci <;> cases iae <;> cases ip <;> cases ae <;> cases cc <;> cases pu <;>
    simp [maySendDatagram, MaySendDatagram]

/-- §14.2/§18.2 advice, which is SHOULD-strength and therefore kept out of
    `MaySendDatagram`: an implementation that ignores it still conforms. -/
def RecommendedDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §14.2, line 5753: "All QUIC packets that are not sent in a PMTU probe
  -- SHOULD be sized to fit within the maximum datagram size".
  (d.isProbe = false → d.size ≤ s.maxDatagramSize) ∧
  -- §14.2: a PMTU probe is by definition larger than the current maximum.
  (d.isProbe = true → s.maxDatagramSize < d.size) ∧
  -- §14, line 5679 with §18.2, line 6966: stay within what the peer said it is
  -- willing to receive, once that value is known.
  (∀ v, s.peerMaxUdpPayload = some v → d.size ≤ v)

/-- No frame is governed by this component. -/
def MaySend (_ : State) (_ : Frame) : Prop := True
def maySend (_ : State) (_ : Frame) : Bool := true
theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

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

/-- §14, line 5695: "an endpoint MUST NOT close a connection when it receives a
    datagram that does not meet size constraints".  For every datagram that does
    not carry an Initial packet — whatever its size — no outcome is an error. -/
theorem no_close_on_datagram_size {s : State} {n : Nat} {o : Out}
    (h : Step s (.recvDatagram n) o) : ∀ c, o ≠ .error c := by
  cases h; intro c; simp

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

/-- §14.1: every datagram a client sends that carries an Initial packet is at
    least 1200 bytes. -/
theorem client_initial_expanded {s : State} {d : OutDatagram}
    (hr : s.role = .client) (hi : d.carriesInitial = true) (h : MaySendDatagram s d) :
    smallestMaxDatagramSize ≤ d.size := h.1 hi (Or.inl hr)

/-- §14.1: every datagram a server sends that carries an ack-eliciting Initial
    packet is at least 1200 bytes. -/
theorem server_ackEliciting_initial_expanded {s : State} {d : OutDatagram}
    (hi : d.carriesInitial = true) (ha : d.initialAckEliciting = true)
    (h : MaySendDatagram s d) : smallestMaxDatagramSize ≤ d.size :=
  h.1 hi (Or.inr ha)

/-- §14.2: on a path that cannot carry 1200 bytes, only PMTU probes and
    CONNECTION_CLOSE datagrams may be sent — and in particular the endpoint can
    no longer send an Initial packet on it. -/
theorem no_initial_on_dead_path {s : State} {d : OutDatagram}
    (hp : s.pathUsable = false) (_hi : d.carriesInitial = true)
    (hnc : d.carriesConnectionClose = false) (h : MaySendDatagram s d) :
    d.isProbe = true := by
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
    maxDatagramSize := smallestMaxDatagramSize, pathUsable := true }
private def cli : State := { srv with role := .client }

-- §14.1: "A server MUST discard an Initial packet that is carried in a UDP
-- datagram with a payload that is smaller than ... 1200 bytes."
example : component.step srv (.recvInitial 1199) = .drop := by decide
-- … and it MAY instead close with PROTOCOL_VIOLATION, but nothing else.
example : component.accepts srv (.recvInitial 1199) (.error .protocolViolation) = true := by decide
example : component.accepts srv (.recvInitial 1199) (.ok srv [.deliver]) = false := by decide
-- A full-size Initial is processed.
example : component.step srv (.recvInitial 1200) = .ok srv [.deliver] := by decide
-- A client has no such rule: it processes a short Initial datagram from the
-- server (§14.1 constrains the sender, and only the server checks).
example : component.step cli (.recvInitial 200) = .ok cli [.deliver] := by decide
-- §14, line 5695: receiving an undersized datagram never closes the connection.
example : component.step srv (.recvDatagram 20) = .ok srv [.deliver] := by decide
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
-- §14.2: a path that cannot carry 1200 bytes stops the flow of packets.
example : component.step cli .pathBelowMinimum =
    .ok { cli with pathUsable := false } [.ceaseSending] := by decide
-- §14.1: a client's Initial datagram must be expanded to 1200 bytes.
example : maySendDatagram cli
    { size := 1200, carriesInitial := true, initialAckEliciting := true,
      isProbe := false, ackEliciting := true, carriesConnectionClose := false } = true := by decide
example : maySendDatagram cli
    { size := 1199, carriesInitial := true, initialAckEliciting := true,
      isProbe := false, ackEliciting := true, carriesConnectionClose := false } = false := by decide
-- §14.1: a server's *non*-ack-eliciting Initial (a pure ACK) need not be.
example : maySendDatagram srv
    { size := 100, carriesInitial := true, initialAckEliciting := false,
      isProbe := false, ackEliciting := false, carriesConnectionClose := false } = true := by decide
-- §14.4: "PMTU probes are ack-eliciting packets."
example : maySendDatagram cli
    { size := 1400, carriesInitial := false, initialAckEliciting := false,
      isProbe := true, ackEliciting := false, carriesConnectionClose := false } = false := by decide

/-! ## 10. Coverage and notes

Assigned range: lines 5640–5919 (§14) and, for the size constant, 5920–5958
(§15, whose version rules live in `Spec/VersionNegotiation.lean`).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §14 (5649) | QUIC MUST NOT be used if the path cannot support 1200 bytes | `smallestMaxDatagramSize`, `Step.pathLost`, `MaySendDatagram` third clause |
| §14 (5687) | UDP datagrams MUST NOT be fragmented at the IP layer; DF bit MUST be set | out of scope: below the transport, not observable in the model |
| §14 (5695) | MUST NOT close a connection on a datagram that fails size constraints; MAY discard | `Step.datagramOk`, theorem `no_close_on_datagram_size` |
| §14.1 (5701) | a client MUST expand Initial-carrying datagrams to ≥ 1200 | `MaySendDatagram` first clause, `client_initial_expanded` |
| §14.1 (5706) | a server MUST expand ack-eliciting-Initial-carrying datagrams to ≥ 1200 | `MaySendDatagram` first clause, `server_ackEliciting_initial_expanded` |
| §14.1 (5723) | Initial datagrams MAY exceed 1200 bytes | `MaySendDatagram` bounds only from below |
| §14.1 (5727) | a server MUST discard an Initial in a datagram < 1200 | `Step.initialTooSmallDrop`, `server_never_processes_small_initial` |
| §14.1 (5729) | a server MAY close with PROTOCOL_VIOLATION instead | `Step.initialTooSmallClose` |
| §14.1 (5733) | the server MUST limit bytes sent before validating the client's address | out of scope: WP5 `AddressValidation` (anti-amplification) |
| §14.2 (5746) | SHOULD use DPLPMTUD/PMTUD; SHOULD NOT exceed the smallest maximum otherwise | `RecommendedDatagram` first clause |
| §14.2 (5753) | non-probe packets SHOULD fit the maximum datagram size | `RecommendedDatagram` first clause |
| §14.2 (5758) | MUST cease sending except probes and CONNECTION_CLOSE below 1200 PMTU | `Step.pathLost`, `MaySendDatagram` third clause, `no_initial_on_dead_path` |
| §14.2 (5762) | MAY terminate the connection if no alternative path | `Step.pathLostTerminate` |
| §14.2 (5773) | SHOULD keep a maximum datagram size per address pair | out of scope: one `State` is one path; WP10 `Migration` owns the path table |
| §14.2.1 (5793) | MUST ignore an ICMP message claiming PMTU < 1200 | `Step.icmpBelowMinimum`, `icmp_below_minimum_ignored` |
| §14.2.1 (5803) | SHOULD validate ICMP messages; validation MUST match addresses/ports | out of scope: the `icmpPtb` event is a message that already passed validation (addresses and ports are not in this model) |
| §14.2.1 (5813) | MUST NOT increase PMTU based on ICMP | `Step.icmpNoIncrease`, `icmp_never_increases` |
| §14.2.1 (5814) | a reduction MAY be provisional | `Step.icmpDefer` |
| §14.3 (5829–5869) | DPLPMTUD parameters and states (BASE_PLPMTU, MPS, SEARCH_COMPLETE) | out of scope by PLAN §1: the search algorithm is excluded, only its constraints are modelled |
| §14.4 (5873) | PMTU probes are ack-eliciting packets | `MaySendDatagram` second clause |
| §14.4 (5885) | loss of a probe SHOULD NOT trigger a congestion reaction | out of scope: congestion control is RFC 9002 |
| §14.4.1 (5894–5918) | how to build a probe that quotes a Source Connection ID | out of scope: advice, no normative keyword |
| §15 (5924) | version 0x00000000 is reserved for version negotiation | `Spec/VersionNegotiation.lean` |

NOTES

- §14 line 5695 ("MUST NOT close a connection when it receives a datagram that
  does not meet size constraints") and §14.1 line 5729 ("A server MAY also
  immediately close the connection by sending a CONNECTION_CLOSE frame with an
  error code of PROTOCOL_VIOLATION") contradict each other for the one case both
  cover: a server receiving an Initial in a datagram below 1200 bytes.  The
  reading encoded is that the specific rule wins — `Step.initialTooSmallClose`
  exists, and `no_close_on_datagram_size` is therefore stated only for
  `.recvDatagram`, not for `.recvInitial`.
- "A server MUST discard an Initial packet" is about a *packet*, but this model
  handles a datagram as a whole, so `.drop` here means the Initial packet is
  discarded.  A datagram smaller than 1200 bytes cannot usefully coalesce
  anything behind a conforming Initial, so nothing is lost; a component that
  wants per-packet granularity is WP12's `Endpoint`.
- The `max_udp_payload_size` limit is SHOULD-strength: §18.2 says it constrains
  datagram size "in the same way as the path MTU", and the path-MTU rule (§14.2
  line 5753) is a SHOULD.  It is therefore in `RecommendedDatagram`, not in
  `MaySendDatagram`, so that an implementation that overruns the peer's
  advertised limit is not rejected by the differential harness.
- §14.4's "PMTU probes are ack-eliciting packets" is declarative, not a MUST.
  It is encoded in `MaySendDatagram` anyway, because `isProbe` is the model's
  own annotation of a datagram: a datagram that is not ack-eliciting simply is
  not a probe.
- `maxDatagramSize` only ever decreases in this component (ICMP).  Raising it is
  the DPLPMTUD search, which is out of scope; a caller that implements the
  search sets the field directly.
- Validating the peer's `max_udp_payload_size` (§18.2: "Values below 1200 are
  invalid") is WP1's, so `Step.maxUdpPayload` stores whatever arrives and `Inv`
  says nothing about it.
-/

end Quic.Spec.DatagramSize
