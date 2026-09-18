import QuicModel.Spec.Endpoint.Send

/-!
  WP12 "Endpoint", parts 4, 5 and 7: the specification, the invariant's
  preservation, and the `Component` value.

  **Which way round `Step` and `outcomes` are defined here, and why.**  Every
  other package writes `Step` as an inductive relation with one constructor per
  normative sentence and proves `outcomes_iff` against it.  That is the right
  shape when the package *owns* the sentences.  This package owns none: the
  receive pipeline is a *composition rule*, and an independent inductive
  presentation of it would restate the composition rather than the spec, so the
  proof would compare the pipeline with itself in two syntaxes.

  So here — and only here, as the assignment allows — `Step` is defined as
  membership in `outcomes`, and what is proved instead are the lifting
  theorems: every component's `Step` is reachable through the endpoint's
  (`Endpoint/Theorems.lean` §(b)), `Inv` is preserved by a real proof that
  applies each component's own `step_inv` to its projection
  (`rawOutcomes_inv`), and the endpoint never permits an outcome that some
  component forbids except where the text gives the *endpoint* the right
  (`addAlt`, used only for §5.2.2 line 1936, §5.2.2 line 1946 and §11.1
  line 4485).

  `Endpoint.component` is indexed by the `Quic.Protection` the decoder uses:
  `Protection` is a record of functions and has no `DecidableEq`, so it cannot
  live in `State`.  `Protection.stub tagLen` is the one the differential
  harness installs.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## 3h. `outcomes` -/

/-- Every outcome the composition permits, preferred first.  The `sendPending`
    markers are added by `withPending` as the last step, so that a component's
    "this frame is now owed" shows up once, where the component said it. -/
def outcomes (prot : Protection) (s : State) (e : Event) : List Out :=
  (rawOutcomes prot s e).map withPending

/-! ## 4. The specification -/

/-- The permitted outcomes of the composed endpoint. -/
def Step (prot : Protection) (s : State) (e : Event) (o : Out) : Prop :=
  o ∈ outcomes prot s e

theorem outcomes_iff (prot : Protection) (s : State) (e : Event) (o : Out) :
    o ∈ outcomes prot s e ↔ Step prot s e o := Iff.rfl

theorem outcomes_ne (prot : Protection) (s : State) (e : Event) : outcomes prot s e ≠ [] := by
  simpa [outcomes] using rawOutcomes_ne prot s e

/-! ## 5. The invariant is preserved

Not by re-deriving anything: `rawOutcomes_inv` is the composition of the
per-component `stepX_inv` lemmas, each of which is that component's own
`step_inv` applied to its projection, and the four cross-component clauses hold
because the wrappers of `Endpoint/Dispatch.lean` are the only writers. -/

theorem step_inv (prot : Protection) (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step prot s e (.ok s' fx)) : Inv s' := by
  simp only [Step, outcomes, List.mem_map] at h
  obtain ⟨o, ho, he⟩ := h
  obtain ⟨gx, rfl⟩ := withPending_eq_ok he
  exact rawOutcomes_inv hi prot e _ _ ho

/-! ## 7. The component -/

@[reducible] def component (prot : Protection) : Component where
  State := State
  Event := Event
  Effect := Effect
  Step := Step prot
  outcomes := outcomes prot
  outcomes_iff := outcomes_iff prot
  outcomes_ne := outcomes_ne prot
  Inv := Inv
  step_inv := step_inv prot
  MaySend := MaySend
  maySend := maySend
  maySend_iff := maySend_iff
  MaySendPacket := MaySendPacket
  maySendPacket := maySendPacket
  maySendPacket_iff := maySendPacket_iff
  MaySendDatagram := MaySendDatagram
  maySendDatagram := maySendDatagram
  maySendDatagram_iff := maySendDatagram_iff

/-- The reference implementation: the preferred permitted outcome. -/
abbrev step (prot : Protection) (s : State) (e : Event) : Out := (component prot).step s e

/-- Is this outcome permitted? -/
abbrev accepts (prot : Protection) (s : State) (e : Event) (o : Out) : Bool :=
  (component prot).accepts s e o

/-! ## 4b. The lifting theorems

`Step` is membership, so soundness and completeness of the executable form are
definitional; what is worth stating is that the reference implementation is
total and deterministic (it is a function), that it is always permitted, and
that the permitted set is never empty. -/

/-- (f), first half: `step` is a total function of the state and the event, so
    it is deterministic by construction. -/
theorem step_deterministic (prot : Protection) (s : State) (e : Event) {o₁ o₂ : Out}
    (h₁ : step prot s e = o₁) (h₂ : step prot s e = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-- (f), second half: the spec always permits something. -/
theorem outcomes_ne' (prot : Protection) (s : State) (e : Event) :
    (component prot).outcomes s e ≠ [] := outcomes_ne prot s e

theorem step_sound (prot : Protection) (s : State) (e : Event) :
    Step prot s e (step prot s e) := (component prot).step_sound s e

theorem accepts_iff (prot : Protection) (s : State) (e : Event) (o : Out) :
    accepts prot s e o = true ↔ Step prot s e o := (component prot).accepts_iff s e o

/-! ## 5b. The initial state satisfies the invariant -/

/-- The side conditions on a `Config` that the components' own initial-state
    theorems need.  WP1's `TransportParams.Valid` guarantees the first four and
    §7.5 line 2703 the fifth; the last three are §15 and §14. -/
structure ConfigOk (cfg : Config) : Prop where
  oursBidi : cfg.ours.maxStreamsBidi ≤ StreamTable.maxStreamsLimit
  oursUni : cfg.ours.maxStreamsUni ≤ StreamTable.maxStreamsLimit
  theirsBidi : cfg.theirs.maxStreamsBidi ≤ StreamTable.maxStreamsLimit
  theirsUni : cfg.theirs.maxStreamsUni ≤ StreamTable.maxStreamsLimit
  /-- §7.5, line 2703: "Implementations MUST support buffering at least 4096
      bytes of data received in out-of-order CRYPTO frames." -/
  bufLimit : 4096 ≤ cfg.bufLimit
  /-- §15, line 5924 and line 5953. -/
  vnNotSupported : VersionNeg.versionNegotiationVersion ∉ cfg.supported
  noReserved : ∀ v ∈ cfg.supported, VersionNeg.isReservedVersion v = false
  advertised : ∀ v ∈ cfg.supported, v ∈ cfg.advertised
  /-- §14, line 5649: "QUIC MUST NOT be used if the network path cannot support
      a maximum datagram size of at least 1200 bytes." -/
  minDatagram : DatagramSize.smallestMaxDatagramSize ≤ cfg.maxDatagramSize
  /-- §5.1.1, line 1721: the peer's `active_connection_id_limit` is at least the
      one connection ID it already holds. -/
  cidLimit : 1 ≤ cfg.localCidLimit

theorem initAck_inv (cfg : Config) (sp : PnSpace) : Ack.Inv (initAck cfg sp) :=
  ⟨rfl, by intro n hn; simp [initAck] at hn,
   by intro m hm; simp [initAck] at hm, by intro m hm; simp [initAck] at hm,
   by intro p hp; simp [initAck] at hp⟩

theorem init_pathIds (cfg : Config) : (init cfg).pathIds = [(initPath cfg, 0)] := rfl
theorem init_nextPathId (cfg : Config) : (init cfg).nextPathId = 1 := rfl

theorem init_inv {cfg : Config} (h : ConfigOk cfg) : Inv (init cfg) := by
  refine ⟨?_, ?_, trivial, initAck_inv cfg .initial, initAck_inv cfg .handshake,
    initAck_inv cfg .appData, ?_, ?_, AddressValidation.inv_init _ _, ?_, ?_,
    Termination.init_inv _ _ _, ⟨h.vnNotSupported, h.noReserved, h.advertised⟩,
    ?_, h.minDatagram, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  -- Handshake
  · refine ⟨?_, ?_, ?_⟩
    · intro hc
      cases hr : cfg.role <;>
        simp [init, initHandshake, hr, Handshake.initClient, Handshake.initServer] at hc
    · cases hr : cfg.role <;> simpa [init, initHandshake, hr, Handshake.initClient,
        Handshake.initServer] using h.bufLimit
    · intro l
      cases hr : cfg.role <;> cases l <;>
        simp [init, initHandshake, hr, Handshake.initClient, Handshake.initServer,
          Handshake.State.stream, Handshake.Streams.get]
  -- StreamTable
  · exact StreamTable.init_inv _ _ _ h.oursBidi h.oursUni h.theirsBidi h.theirsUni
  -- ConnIds.Local
  · exact ⟨by simp [init, ConnIds.seqs], by simp [init]⟩
  -- ConnIds.Remote
  · refine ⟨by simp [init, ConnIds.seqs], ?_⟩
    show (ConnIds.Remote.State.active _).length ≤ _
    simpa [init, ConnIds.Remote.State.active] using h.cidLimit
  -- PathValidation
  · intro c hc; simp [init, PathValidation.init] at hc
  -- Migration
  · refine ⟨?_, ?_⟩
    · intro q hq
      simp only [init, Migration.init, Option.some.injEq] at hq
      subst hq
      simp [Migration.State.statusOf, Migration.State.infoOf, init, Migration.init, Map.get?]
    · intro e₁ h₁ e₂ h₂ _
      simp only [init, Migration.init, List.mem_singleton] at h₁ h₂
      rw [h₁, h₂]
  -- VersionNeg.Client
  · intro hc; simp [init] at hc
  -- Retransmission: nothing is owed at the start
  · intro i hi; simp [init] at hi
  -- Ecn, one instance per space: no counts have been recorded
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · intro _; exact ⟨rfl, rfl, rfl⟩
  -- InvConfirmed: WP11's bit is `false` at the start, whatever the role
  · cases hr : cfg.role <;> simp [init, initHandshake, hr, Handshake.initClient,
      Handshake.initServer, Termination.init]
  · cases hr : cfg.role <;> simp [init, initHandshake, hr, Handshake.initClient,
      Handshake.initServer, Migration.init]
  -- InvRole: the one component whose role is not syntactically `cfg.role`
  · cases hr : cfg.role <;> simp [init, initHandshake, hr, Handshake.initClient,
      Handshake.initServer]
  -- InvPaths: one entry, and the counter is past it
  · rw [InvPaths, init_pathIds, init_nextPathId]
    refine ⟨?_, ?_⟩
    · intro p i hp
      simp only [Map.get?] at hp
      split at hp
      · simp only [Option.some.injEq] at hp; omega
      · simp at hp
    · intro p q i hp hq
      simp only [Map.get?] at hp hq
      split at hp
      · split at hq
        · rename_i h1 h2; exact h1.symm.trans h2
        · simp at hq
      · simp at hp

end Quic.Spec.Endpoint
