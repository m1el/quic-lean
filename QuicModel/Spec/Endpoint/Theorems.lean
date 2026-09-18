import QuicModel.Spec.Endpoint.Obligations

/-!
  WP12 "Endpoint", part 8: the named theorems.

  (a) `Inv` holds in every reachable state.
  (b) projections: every state the composition writes for a component is one
      that component's own `Step` permits, so every component theorem applies to
      the projection.
  (c) anti-amplification at endpoint level.
  (d) received stream data never exceeds the advertised credit.
  (e) `Termination` gates dispatch; after packet-number exhaustion nothing may
      be sent.
  (f) `Endpoint.step` is total and deterministic and `outcomes` is never empty.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## (a) The invariant holds everywhere -/

theorem inv_of_reachable {prot : Protection} {s₀ s : State} (h0 : Inv s₀)
    (h : (component prot).Reachable s₀ s) : Inv s :=
  (component prot).inv_of_reachable h0 h

/-- From the start of a connection whose configuration satisfies `ConfigOk`. -/
theorem inv_reachable_from_init {prot : Protection} {cfg : Config} (h : ConfigOk cfg)
    {s : State} (hr : (component prot).Reachable (init cfg) s) : Inv s :=
  inv_of_reachable (init_inv h) hr

/-- Reachability composes; the projection theorems below need it. -/
theorem reachable_trans (C : Component) {a b c : C.State}
    (h₁ : C.Reachable a b) (h₂ : C.Reachable b c) : C.Reachable a c := by
  induction h₂ with
  | refl => exact h₁
  | step _ hs ih => exact .step ih hs

/-! ## (b) Projections

The composition writes a component's state in exactly one place — the wrapper of
`Endpoint/Dispatch.lean` — and each of these says that what it writes is a state
that component's own `Step` permits.  Every theorem a package proved about its
`Step` therefore applies to the projection of an endpoint state.

Two of the thirteen are stated with the `syncConfirmed` rewrite visible:
`Termination` and `Migration` each keep a copy of WP11's "handshake confirmed"
bit, and the composition re-imposes WP11's value on them (`Endpoint.InvConfirmed`,
`Endpoint.syncConfirmed`).  Under `Inv` that rewrite is the identity except at
the moment WP11 sets the bit, where it is exactly
`Termination.Step.handshakeConfirmed` / `Migration.Step.confirmed`. -/

theorem stepHs_projects {s s' : State} {e : Handshake.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepHs s e) : ∃ gx, Handshake.Step s.hs e (.ok s'.hs gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (Handshake.outcomes_iff _ _ _).mp ho⟩

theorem stepSt_projects {s s' : State} {e : StreamTable.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepSt s e) : ∃ gx, StreamTable.Step s.st e (.ok s'.st gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (StreamTable.outcomes_iff _ _ _).mp ho⟩

theorem stepFr_projects {s s' : State} {e : FrameRules.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepFr s e) : ∃ gx, FrameRules.Step s.fr e (.ok s'.fr gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (FrameRules.outcomes_iff _ _ _).mp ho⟩

theorem stepAck_projects {s s' : State} {sp : PnSpace} {e : Ack.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepAck s sp e) :
    ∃ gx, Ack.Step (s.ack sp) e (.ok (s'.ack sp) gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  refine ⟨gx, ?_⟩
  have : (syncConfirmed (s.setAck sp x)).ack sp = x := by cases sp <;> rfl
  rw [this]
  exact (Ack.outcomes_iff _ _ _).mp ho

theorem stepCidLocal_projects {s s' : State} {e : ConnIds.Local.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepCidLocal s e) :
    ∃ gx, ConnIds.Local.Step s.cidLocal e (.ok s'.cidLocal gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (ConnIds.Local.outcomes_iff _ _ _).mp ho⟩

theorem stepCidRemote_projects {s s' : State} {e : ConnIds.Remote.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepCidRemote s e) :
    ∃ gx, ConnIds.Remote.Step s.cidRemote e (.ok s'.cidRemote gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (ConnIds.Remote.outcomes_iff _ _ _).mp ho⟩

theorem stepAv_projects {s s' : State} {e : AddressValidation.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepAv s e) :
    ∃ gx, AddressValidation.Step s.av e (.ok s'.av gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (AddressValidation.outcomes_iff _ _ _).mp ho⟩

theorem stepPv_projects {s s' : State} {e : PathValidation.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepPv s e) :
    ∃ gx, PathValidation.Step s.pv e (.ok s'.pv gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (PathValidation.outcomes_iff _ _ _).mp ho⟩

theorem stepMig_projects {s s' : State} {e : Migration.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepMig s e) :
    ∃ x gx, Migration.Step s.mig e (.ok x gx) ∧
      s'.mig = { x with handshakeConfirmed := s.hs.confirmed } := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨x, gx, (Migration.outcomes_iff _ _ _).mp ho, rfl⟩

theorem stepTerm_projects {s s' : State} {e : Termination.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepTerm s e) :
    ∃ x gx, Termination.Step s.term e (.ok x gx) ∧
      s'.term = { x with handshakeConfirmed := s.hs.confirmed } := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨x, gx, (Termination.outcomes_iff _ _ _).mp ho, rfl⟩

theorem stepVnServer_projects {s s' : State} {e : VersionNeg.Server.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepVnServer s e) :
    ∃ gx, VersionNeg.Server.Step s.vnServer e (.ok s'.vnServer gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (VersionNeg.Server.outcomes_iff _ _ _).mp ho⟩

theorem stepVnClient_projects {s s' : State} {e : VersionNeg.Client.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepVnClient s e) :
    ∃ gx, VersionNeg.Client.Step s.vnClient e (.ok s'.vnClient gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (VersionNeg.Client.outcomes_iff _ _ _).mp ho⟩

theorem stepDsz_projects {s s' : State} {e : DatagramSize.Event} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepDsz s e) :
    ∃ gx, DatagramSize.Step s.dsz e (.ok s'.dsz gx) := by
  obtain ⟨o, ho, he⟩ := mem_liftList h
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  exact ⟨gx, (DatagramSize.outcomes_iff _ _ _).mp ho⟩

/-- The hypothesis the theorems below take: the projection of the endpoint's
    run onto one component is a run of that component.  It follows from the
    thirteen lemmas above by induction over the pipeline (the wrappers are its
    only writers); the induction itself is a second pass of exactly the shape of
    `rawOutcomes_inv` and is **not mechanised here** — see the NOTES. -/
abbrev ProjectsAv (_prot : Protection) (s₀ s : State) : Prop :=
  AddressValidation.ReachableOk s₀.av s.av

abbrev ProjectsSt (_prot : Protection) (s₀ s : State) : Prop :=
  StreamTable.component.Reachable s₀.st s.st

/-! ## (c) Anti-amplification, at endpoint level

§8, line 2735: "an endpoint MUST limit the amount of data it sends to the
unvalidated address to three times the amount of data received from that
address"; §8.1, line 2773; §9.3.1, line 3431.

WP5 proves it for its own component over `ReachableOk`, whose side condition
`EventOk` is "every datagram we sent was one `MaySendTo` permitted".  At
endpoint level that side condition is "every datagram passed
`Endpoint.maySendDatagram`", and `maySendDatagram` has
`AddressValidation.MaySendTo` as its first conjunct — which is the bridge. -/

theorem maySendDatagram_implies_maySendTo {s : State} {d : OutDatagram}
    (h : MaySendDatagram s d) : AddressValidation.MaySendTo s.av d.dest d.size := h.1

/-- (c).  Every address the limit binds has been sent at most three times what
    was received from it, in every state the endpoint reaches, provided every
    datagram it sent passed `Endpoint.maySendDatagram`. -/
theorem antiAmplification {prot : Protection} {s₀ s : State}
    (h0 : AddressValidation.AntiAmp s₀.av) (h : ProjectsAv prot s₀ s) :
    AddressValidation.AntiAmp s.av :=
  AddressValidation.antiAmplification h0 h

/-- It holds from the start of a connection. -/
theorem antiAmp_init (cfg : Config) : AddressValidation.AntiAmp (init cfg).av :=
  AddressValidation.antiAmp_init _ _

/-! ## (d) Received data never exceeds the advertised credit

§19.9, line 7712: "An endpoint MUST terminate a connection with a
FLOW_CONTROL_ERROR error if it receives more data than the maximum data value
that it has sent"; §4.1, line 1352.  WP9 proves both halves, at connection level
and per stream; `Endpoint.Inv` carries them as `StreamTable.Inv`. -/

/-- (d), connection level: the cumulative data received over all streams never
    exceeds the MAX_DATA this endpoint has advertised. -/
theorem recvTotal_le_maxData {s : State} (hi : Inv s) : s.st.recvTotal ≤ s.st.maxDataLocal :=
  hi.st.1

/-- (d), send side: nor does what we have sent exceed the peer's MAX_DATA. -/
theorem sentTotal_le_maxDataPeer {s : State} (hi : Inv s) : s.st.sentTotal ≤ s.st.maxDataPeer :=
  hi.st.2.1

/-- (d), stream level: every stream in the table satisfies WP2's invariant,
    which is where "bytes delivered ≤ advertised stream credit" lives. -/
theorem stream_inv {s : State} (hi : Inv s) {id : StreamId} {st : Stream.State}
    (h : s.st.streams.get? id = some st) : Stream.Inv st := (hi.st.2.2.2.2.2.2 id st h).2.2.2

/-- (d), stream counts: neither side has opened more streams than the limit the
    other advertised (§4.6, line 1553). -/
theorem opened_le_limit {s : State} (hi : Inv s) (d : StreamDir) :
    s.st.opened.get s.st.role.peer d ≤ s.st.maxStreamsLocal.get d ∧
      s.st.opened.get s.st.role d ≤ s.st.maxStreamsPeer.get d :=
  ⟨hi.st.2.2.1 d, hi.st.2.2.2.1 d⟩

/-! ## (e) `Termination` gates dispatch, and exhaustion stops everything -/

/-- (e), first half.  §10.2.1, line 3984: "An endpoint that is closing is not
    required to process any received frame"; §10.2.2, line 4023: draining sends
    nothing; §10.2, line 3953: a closed endpoint has no state left.  In none of
    the three phases does a received datagram reach a frame: the whole of the
    pipeline after the gate is replaced by `Termination`'s own step.

    This is also what `PathValidation` NOTES 12 asks for: `recvChallenge` and
    `recvResponse` have no `.drop` in any state, which is only consistent with
    §10.2.1 line 3984 because the phase gate stops them being presented. -/
theorem no_dispatch_unless_active {prot : Protection} {now : Time} {src : Addr}
    {mp : Migration.Path} {buf : ByteArray} {s : State} (hp : s.term.phase ≠ .active) :
    phaseGate prot now src mp buf s = closedPhase prot now (addrValidated s src) buf s := by
  unfold phaseGate
  split
  · rename_i hq; exact absurd hq hp
  · rfl

/-- … and `closedPhase` only ever takes a `Termination` step: no frame, no
    stream, no connection ID, no path is touched. -/
theorem closedPhase_is_term_only (prot : Protection) (now : Time) (av : Bool)
    (buf : ByteArray) (s : State) :
    closedPhase prot now av buf s = stepTerm s (.recvClose now s.pto
        ((closeReasonOfDatagram prot s buf).getD (.transport .noError 0)) av) ∨
      closedPhase prot now av buf s = stepTerm s (.recvPacket now s.pto av) := by
  unfold closedPhase
  split
  · rename_i r hr; exact Or.inl (by rw [hr]; rfl)
  · exact Or.inr rfl

/-- (e), second half.  §12.3, line 4693: "If the packet number for sending
    reaches 2^62 - 1, the sender MUST close the connection without sending a
    CONNECTION_CLOSE frame or any further packets."  Once `Ack.pnExhausted`
    holds for a space, no packet of that space may be assembled. -/
theorem no_packet_after_pnExhausted {s : State} (hi : Inv s) {sp : PnSpace} {p : OutPacket}
    (hx : Ack.pnExhausted (s.ack sp) = true) (hsp : p.ptype.space = some sp) :
    ¬ MaySendPacket s p :=
  not_maySendPacket_of_pnExhausted hsp (hi.spaceOf sp) hx

/-- … and the `pnExhausted` event itself lands in `Phase.closed`, from which
    `MaySend` is `False` for every frame (§10.2, line 3953). -/
theorem pnExhausted_silences {s s' : State} {now : Time} {fx : List Effect}
    (h : Outcome.ok s' fx ∈ stepTerm s (.pnExhausted now s.pto)) (f : Frame) :
    ¬ MaySend s' f := by
  obtain ⟨x, gx, hstep, hterm⟩ := stepTerm_projects h
  refine maySend_false_of_draining_or_closed f (Or.inr ?_)
  rw [hterm]
  exact (Termination.pnExhausted_closes_silently hstep).1

/-! ## (f) The reference implementation is total and deterministic -/

theorem step_total (prot : Protection) (s : State) (e : Event) :
    ∃ o, Step prot s e o := ⟨step prot s e, step_sound prot s e⟩

theorem outcomes_never_empty (prot : Protection) (s : State) (e : Event) :
    outcomes prot s e ≠ [] := outcomes_ne prot s e

/-- Every permitted outcome is one of a finite, computable list — which is what
    makes `accepts` and `track` decidable for the whole endpoint. -/
theorem step_iff_mem (prot : Protection) (s : State) (e : Event) (o : Out) :
    Step prot s e o ↔ o ∈ outcomes prot s e := Iff.rfl

end Quic.Spec.Endpoint
