import QuicModel.Spec.Migration.Send

/-!
  WP10 "Migration", parts 8–9: the named theorems and the worked scenarios.
-/
namespace Quic.Spec.Migration

/-! ### More projections -/

namespace State

@[simp] theorem active_markValidating (s : State) (p : Path) :
    (s.markValidating p).active = s.active := rfl

@[simp] theorem active_markValidated (s : State) (p : Path) :
    (s.markValidated p).active = s.active := rfl

@[simp] theorem active_markFailed (s : State) (p : Path) :
    (s.markFailed p).active = s.active := by unfold markFailed; split <;> rfl

@[simp] theorem active_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).active = s.active := rfl

@[simp] theorem active_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).active = s.active := by unfold observe; split <;> rfl

@[simp] theorem active_switchTo (s : State) (p : Path) : (s.switchTo p).active = p := rfl

@[simp] theorem active_revertTo (s : State) (p : Path) : (s.revertTo p).active = p := rfl

/-- §9.3, line 3382 moves the destination, never the local address we send
    from (`State.destOf`). -/
@[simp] theorem destOf_loc (s : State) (p : Path) : (s.destOf p).loc = s.active.loc := rfl

@[simp] theorem destOf_peer (s : State) (p : Path) : (s.destOf p).peer = p.peer := rfl

@[simp] theorem active_permit (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).active = s.destOf p := by unfold permit; split <;> rfl

@[simp] theorem active_recordPeerCid (s : State) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).active = s.active := by unfold recordPeerCid; split <;> rfl

@[simp] theorem hc_recordPeerCid (s : State) (seq : Nat) (cid : CidBytes) :
    (s.recordPeerCid seq cid).handshakeConfirmed = s.handshakeConfirmed := by
  unfold recordPeerCid; split <;> rfl

@[simp] theorem lastValidated_recordCidUse (s : State) (p : Path) (n : Nat) :
    (s.recordCidUse p n).lastValidated = s.lastValidated := rfl

@[simp] theorem active_startProbe (s : State) (p : Path) : (s.startProbe p).active = s.active := rfl

@[simp] theorem active_succStay (s : State) (p : Path) : (s.succStay p).active = s.active := rfl

@[simp] theorem active_succSwitch (s : State) (p : Path) : (s.succSwitch p).active = p := rfl

@[simp] theorem active_useCid (s : State) (p : Path) (n : Nat) :
    (s.useCid p n).active = s.active := rfl

@[simp] theorem hc_markValidating (s : State) (p : Path) :
    (s.markValidating p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_markValidated (s : State) (p : Path) :
    (s.markValidated p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_markFailed (s : State) (p : Path) :
    (s.markFailed p).handshakeConfirmed = s.handshakeConfirmed := by
  unfold markFailed; split <;> rfl

@[simp] theorem hc_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).handshakeConfirmed = s.handshakeConfirmed := by
  unfold observe; split <;> rfl

@[simp] theorem hc_switchTo (s : State) (p : Path) :
    (s.switchTo p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_revertTo (s : State) (p : Path) :
    (s.revertTo p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_permit (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).handshakeConfirmed = s.handshakeConfirmed := by
  unfold permit; split <;> rfl

@[simp] theorem hc_startProbe (s : State) (p : Path) :
    (s.startProbe p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_succStay (s : State) (p : Path) :
    (s.succStay p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_succSwitch (s : State) (p : Path) :
    (s.succSwitch p).handshakeConfirmed = s.handshakeConfirmed := rfl

@[simp] theorem hc_useCid (s : State) (p : Path) (n : Nat) :
    (s.useCid p n).handshakeConfirmed = s.handshakeConfirmed := rfl

end State

/-! ### Reading the case analyses back -/

/-- Following a peer's migration (§9.3, line 3382) changes the address we send
    *to*; the local address we send *from* is unchanged, whatever local address
    of ours the packet arrived at. -/
theorem permit_active_loc (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).active.loc = s.active.loc := by simp

/-- A probing packet never reaches the two branches that move the sending
    path (§9.1, line 3340). -/
theorem recvCase_probing (s : State) (p : Path) (pn : Nat) :
    recvCase s p pn true ≠ .banned ∧ recvCase s p pn true ≠ .migrate := by
  constructor <;> (unfold recvCase; repeat' split) <;> simp_all

/-- §9.6.1, line 3701: the preferred address is taken up only "once the
    handshake is confirmed". -/
theorem succCase_confirmed {s : State} {p : Path}
    (h : succCase s p = .mustSwitch ∨ succCase s p = .maySwitch) :
    s.handshakeConfirmed = true := by
  cases hb : s.handshakeConfirmed
  · exfalso
    have t : succCase s p = .gone ∨ succCase s p = .stay := by
      unfold succCase
      split
      · exact Or.inl rfl
      · refine Or.inr ?_
        have hp : s.preferredSwitchReady p = false := by
          simp [State.preferredSwitchReady, hb]
        simp [hp]
    rcases h with h | h <;> rcases t with t | t <;> (rw [t] at h; simp at h)
  · rfl

/-- §9, line 3280: no endpoint-initiated migration before the handshake is
    confirmed. -/
theorem migCase_confirmed {s : State} {p : Path}
    (h : migCase s p = .validateFirst ∨ migCase s p = .already ∨ migCase s p = .fresh) :
    s.handshakeConfirmed = true := by
  cases hb : s.handshakeConfirmed
  · exfalso
    have t : migCase s p = .gone ∨ migCase s p = .tooEarly := by
      unfold migCase
      split
      · exact Or.inl rfl
      · exact Or.inr (by simp [hb])
    rcases h with h | h | h <;> rcases t with t | t <;> (rw [t] at h; simp at h)
  · rfl

/-- The path reverted to in §9.3.2, line 3452 is the recorded last validated
    one, and it is not the path that just failed. -/
theorem failCase_revert {s : State} {p : Path} (h : failCase s p = .revert) :
    ∃ q, s.lastValidated = some q ∧ q ≠ p := by
  cases hl : s.lastValidated with
  | none =>
    exfalso; unfold failCase at h; rw [hl] at h; (repeat' split at h) <;> simp_all
  | some q =>
    refine ⟨q, rfl, ?_⟩
    intro hq
    exfalso
    subst hq
    unfold failCase at h; rw [hl] at h; (repeat' split at h) <;> simp_all

/-- Conversely, a failure on the path we are sending on that was never validated
    is always one of §9.3.2's two cases. -/
theorem failCase_active_ne {s : State} {p : Path} (hact : p = s.active)
    (hnv : s.isValidated p = false) :
    failCase s p ≠ .otherPath ∧ failCase s p ≠ .otherPathNoneLeft := by
  unfold failCase
  split
  · exact ⟨by simp, by simp⟩
  · split
    · split
      · split <;> exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
    · rename_i hb
      have hnv' : s.isValidated s.active = false := hact ▸ hnv
      exact absurd (show (decide (p = s.active) && !s.isValidated p) = true by
        simp [hact, hnv']) hb

/-- §9.3, line 3382's switch records the path it leaves, or keeps the one it
    had. -/
theorem lastValidated_switchTo_mem {t : State} {p q : Path}
    (hq : (t.switchTo p).lastValidated = some q) :
    q = t.active ∨ t.lastValidated = some q := by
  simp only [State.switchTo] at hq
  split at hq
  · exact Or.inl (Option.some.inj hq).symm
  · exact Or.inr hq

theorem permit_lastValidated {s : State} {p q : Path} {pn : Nat} {pr : Bool} {d : Nat}
    (hq : (s.permit p pn pr d).lastValidated = some q) :
    q = s.active ∨ s.lastValidated = some q := by
  unfold State.permit at hq
  split at hq <;> rcases lastValidated_switchTo_mem hq with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

/-! ## 8. Named theorems -/

/-- Once the handshake is confirmed it stays confirmed. -/
theorem confirmed_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hc : s.handshakeConfirmed = true) :
    s'.handshakeConfirmed = true := by
  cases h <;> simp_all

/-- **(a)** §9, line 3280: "An endpoint MUST NOT initiate connection migration
    before the handshake is confirmed."  A request to migrate has no effect at
    all before then. -/
theorem no_migration_before_confirmed {s : State} {p : Path} {o : Out}
    (hc : s.handshakeConfirmed = false) (h : Step s (.requestMigrate p) o) : o = .drop := by
  cases h with
  | migGone => rfl
  | migTooEarly => rfl
  | migBanned => rfl
  | migValidateFirst h' => exact absurd (migCase_confirmed (Or.inl h')) (by simp [hc])
  | migAlready h' => exact absurd (migCase_confirmed (Or.inr (Or.inl h'))) (by simp [hc])
  | migFresh h' => exact absurd (migCase_confirmed (Or.inr (Or.inr h'))) (by simp [hc])
  | migDefer h' => exact absurd (migCase_confirmed (Or.inr (Or.inr h'))) (by simp [hc])

/-- **(a)**, send side: before the handshake is confirmed, no non-probing packet
    may leave from a local address other than the handshake's.  Stated over the
    datagram's own source address (M-2): the datagram says where it leaves
    from, and the rule judges that. -/
theorem maySendDatagram_unconfirmed {s : State} {d : OutDatagram} {pkt : OutPacket}
    (hc : s.handshakeConfirmed = false) (hin : pkt ∈ d.packets)
    (hp : FrameRules.packetProbing pkt.frames = false)
    (hl : (pathOf d).loc ≠ s.handshakePath.loc) : ¬ MaySendDatagram s d := by
  intro hm
  rcases (hm.2.1 pkt hin).1 with h | h | h
  · exact absurd h (by simp [hc])
  · exact absurd h (by simp [hp])
  · exact hl h

/-- **(a)**, the state form: before the handshake is confirmed the *local*
    address of the active path never moves, provided the last validated path is
    reached from the same local address.  Only `active.peer` can change, and
    only in response to the peer's own packets (§9, line 3312 and §9.3, line
    3382); see `active_loc_stable_from_init` for the reachable-state form. -/
def UnconfirmedLocal (l : LocalAddr) (s : State) : Prop :=
  s.handshakeConfirmed = false →
    s.active.loc = l ∧ ∀ q, s.lastValidated = some q → q.loc = l

theorem unconfirmedLocal_step {l : LocalAddr} {s s' : State} {e : Event} {fx : List Effect}
    (hu : UnconfirmedLocal l s) (h : Step s e (.ok s' fx)) : UnconfirmedLocal l s' := by
  intro hc'
  have hc : s.handshakeConfirmed = false := by
    cases hb : s.handshakeConfirmed
    · rfl
    · exact absurd (confirmed_mono h hb) (by simp [hc'])
  obtain ⟨ha, hl⟩ := hu hc
  cases h with
  | recvUnsolicitedKeep _ | recvQuiet _ | recvRefuse _ => exact ⟨by simpa using ha, by simpa using hl⟩
  | recvBannedMigrate h' | recvMigrate h' =>
    refine ⟨by simpa using ha, ?_⟩
    intro q hq
    rcases permit_lastValidated hq with rfl | hq
    · exact ha
    · exact hl q hq
  | succStay _ | succKeep _ =>
    refine ⟨by simpa using ha, ?_⟩
    intro q hq
    simp only [State.succStay] at hq
    split at hq
    · rename_i heq
      rcases Option.some.inj hq with rfl
      rw [heq]; exact ha
    · exact hl q hq
  | succMustSwitch h' => exact absurd (succCase_confirmed (Or.inl h')) (by simp [hc])
  | succSwitch h' => exact absurd (succCase_confirmed (Or.inr h')) (by simp [hc])
  | failRevert h' =>
    obtain ⟨q, hq, _⟩ := failCase_revert h'
    refine ⟨by simp [hq]; exact hl q hq, by simpa using hl⟩
  | failNoPath _ | failOtherGiveUp _ => exact ⟨by simpa using ha, by simpa using hl⟩
  | failOther _ | failOtherWait _ => exact ⟨by simpa using ha, by simpa using hl⟩
  | migValidateFirst h' => exact absurd (migCase_confirmed (Or.inl h')) (by simp [hc])
  | migAlready h' => exact absurd (migCase_confirmed (Or.inr (Or.inl h'))) (by simp [hc])
  | migFresh h' => exact absurd (migCase_confirmed (Or.inr (Or.inr h'))) (by simp [hc])
  | migDefer h' => exact absurd (migCase_confirmed (Or.inr (Or.inr h'))) (by simp [hc])
  | probeStart _ => exact ⟨by simpa using ha, by simpa using hl⟩
  | confirmed => exact absurd hc' (by simp)
  | preferredLearn _ => exact ⟨ha, hl⟩
  | cidZeroLen _ => exact ⟨ha, hl⟩
  | cidRebindKeep _ | cidFresh _ => exact ⟨ha, hl⟩
  | peerCidLearn => exact ⟨by simpa using ha, by simpa using hl⟩

/-- **(a)**, reachable form: from a fresh connection on `p₀`, every state
    reachable while the handshake is still unconfirmed sends from `p₀`'s local
    address. -/
theorem active_loc_stable_from_init {role : Role} {p₀ : Path} {n : Nat} {s : State}
    (h : component.Reachable (init role p₀ n) s) (hc : s.handshakeConfirmed = false) :
    s.active.loc = p₀.loc :=
  (Component.reachable_induction (C := component) (motive := UnconfirmedLocal p₀.loc)
    (fun _ => ⟨rfl, fun q hq => by rcases Option.some.inj hq with rfl; rfl⟩)
    (fun _ hs ih => unconfirmedLocal_step ih hs) h hc).1

/-- **(b)** §9.1, line 3340: "A packet containing only probing frames is a
    'probing packet'" — and a probing packet never changes the path an endpoint
    sends non-probing packets on. -/
theorem probing_never_migrates {s s' : State} {p : Path} {pn d : Nat} {fx : List Effect}
    (h : Step s (.recvPacket p pn true d) (.ok s' fx)) : s'.active = s.active := by
  cases h with
  | recvUnsolicitedKeep _ => simp
  | recvQuiet _ => simp
  | recvBannedMigrate h' => exact absurd h' (recvCase_probing s p pn).1
  | recvMigrate h' => exact absurd h' (recvCase_probing s p pn).2
  | recvRefuse _ => simp

/-- **(c)** §9.5, line 3603: "An endpoint MUST NOT reuse a connection ID when
    sending from more than one local address."  In every reachable state, two
    paths transmitting with the same Destination Connection ID sequence number
    leave from the same local address.

    The companion rule of line 3608 (one destination address per connection ID)
    is deliberately *not* here: the MAY of line 3611 makes it false, see the
    counterexample section below. -/
theorem dcid_one_local_address {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) {p q : Path} {n : Nat}
    (hp : (p, n) ∈ s.dcidOn) (hq : (q, n) ∈ s.dcidOn) : p.loc = q.loc := by
  have hi := Component.inv_of_reachable (C := component) h0 h
  have h1 : s.dcidFrom.get? n = some p.loc := hi.2 (p, n) hp
  have h2 : s.dcidFrom.get? n = some q.loc := hi.2 (q, n) hq
  rw [h1] at h2
  exact Option.some.inj h2

/-- **(c)**, the form the prohibition really has (M-1): §9.5, line 3603 is about
    *reuse*, so what a reachable state guarantees is a fact about the grow-only
    history — the connection ID in use on a path has never been sent from any
    other local address, whatever connection IDs that path used before. -/
theorem dcid_local_address_history {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) {p : Path} {n : Nat} (hp : (p, n) ∈ s.dcidOn) :
    s.dcidFrom.get? n = some p.loc :=
  (Component.inv_of_reachable (C := component) h0 h).2 (p, n) hp

/-- The history never forgets: once connection ID `n` has left from `l`, no step
    of this component changes or erases that record. -/
theorem dcidFrom_grow_only {s s' : State} {e : Event} {fx : List Effect} {n : Nat}
    {l : LocalAddr} (h : Step s e (.ok s' fx)) (hn : s.dcidFrom.get? n = some l) :
    s'.dcidFrom.get? n = some l := by
  cases h with
  | cidRebindKeep _ | cidFresh _ =>
    rename_i p m _
    show ((s.recordCidUse p m).dcidFrom).get? n = some l
    by_cases hnm : n = m
    · subst hnm
      rw [State.dcidFrom_recordCidUse_of_some s p n hn]; exact hn
    · rw [get?_dcidFrom_recordCidUse_ne hnm]; exact hn
  | _ => simpa using hn

/-- **(d)** §9.3.2, lines 3452 and 3460: "an endpoint MUST revert to using the
    last validated peer address when validation of a new peer address fails …
    If an endpoint has no state about the last validated peer address, it MUST
    close the connection silently by discarding all connection state." -/
theorem revert_or_close {s s' : State} {p : Path} {fx : List Effect} (hi : Inv s)
    (h : Step s (.validationFailed p) (.ok s' fx)) (hact : p = s.active)
    (hnv : s.isValidated p = false) :
    (s.lastValidated = some s'.active ∧ s.statusOf s'.active = .validated ∧
        fx = [.switchPath s'.active]) ∨
      (s'.discarded = true ∧ fx = [.discardState]) := by
  cases h with
  | failRevert h' =>
    obtain ⟨q, hq, _⟩ := failCase_revert h'
    refine Or.inl ⟨?_, ?_, ?_⟩
    · simp [hq]
    · simp only [State.active_revertTo, hq, Option.getD_some]
      exact hi.1 q hq
    · simp [hq]
  | failNoPath _ => exact Or.inr ⟨rfl, rfl⟩
  | failOther h' => exact absurd h' (failCase_active_ne hact hnv).1
  | failOtherWait h' => exact absurd h' (failCase_active_ne hact hnv).2
  | failOtherGiveUp h' => exact absurd h' (failCase_active_ne hact hnv).2

/-- **(e)** §9, line 3284: with `disable_active_migration` received from the
    peer, nothing at all may leave from a new local address toward the address
    the peer used during the handshake — probing packets included. -/
theorem disableMigration_blocks (s : State) (d : OutDatagram) (pkt : OutPacket)
    (hin : pkt ∈ d.packets)
    (h : s.peerDisableMigration = true) (hl : (pathOf d).loc ≠ s.handshakePath.loc)
    (hd : (pathOf d).peer = s.handshakePath.peer) (ha : s.preferredActedOn = false) :
    ¬ MaySendDatagram s d := by
  intro hm
  have : s.sendBanned (pathOf d) = true := by
    simp [State.sendBanned, h, hl, hd, ha]
  rw [(hm.2.1 pkt hin).2.1] at this
  exact Bool.noConfusion this

/-- **(e)**, the converse: the ban of §9, line 3284 applies exactly in that
    situation.  In particular it lifts once the endpoint "has acted on a
    preferred_address transport parameter from the peer" (§5.2.2, line 1977:
    "The disable_active_migration transport parameter does not prohibit
    connection migration after a client has acted on a preferred_address
    transport parameter"), and it never applies to a destination other than the
    one used during the handshake. -/
theorem sendBanned_iff (s : State) (p : Path) :
    s.sendBanned p = true ↔
      (s.peerDisableMigration = true ∧ p.loc ≠ s.handshakePath.loc ∧
        p.peer = s.handshakePath.peer ∧ s.preferredActedOn = false) := by
  simp [State.sendBanned, and_assoc]

theorem disableMigration_preferred_exception (s : State) (p : Path)
    (ha : s.preferredActedOn = true) : s.sendBanned p = false := by
  simp [State.sendBanned, ha]

theorem disableMigration_other_destination (s : State) (p : Path)
    (hd : p.peer ≠ s.handshakePath.peer) : s.sendBanned p = false := by
  simp [State.sendBanned, hd]

theorem disableMigration_same_local (s : State) (p : Path)
    (hl : p.loc = s.handshakePath.loc) : s.sendBanned p = false := by
  simp [State.sendBanned, hl]

/-- §9.3.2, line 3460: a connection that has discarded its state sends nothing
    more — no packet … -/
theorem discarded_sends_nothing (s : State) (pkt : OutPacket) (h : s.discarded = true) :
    ¬ MaySendPacket s pkt := by
  intro hm
  rw [hm] at h
  exact Bool.noConfusion h

/-- … and no datagram. -/
theorem discarded_sends_no_datagram (s : State) (d : OutDatagram) (h : s.discarded = true) :
    ¬ MaySendDatagram s d := by
  intro hm
  rw [hm.1] at h
  exact Bool.noConfusion h

/-- The reference implementation always follows §9's advice: the preferred
    outcome of `outcomes` is the `Recommended` one. -/
theorem step_recommended (s : State) (e : Event) : Recommended s e (component.step s e) := by
  cases e with
  | recvPacket p pn pr d =>
    intro h
    show (outcomes s (Event.recvPacket p pn pr d)).head _ = _
    simp only [outcomes, h]
    rfl
  | validationSucceeded p =>
    intro h
    show (outcomes s (Event.validationSucceeded p)).head _ = _
    simp only [outcomes, h]
    rfl
  | _ => trivial


/-! ## 9. Examples (scenarios from the text) -/

private def la0 : LocalAddr := ⟨0⟩
private def la1 : LocalAddr := ⟨1⟩
private def pa0 : PeerAddr := ⟨0⟩
private def pa1 : PeerAddr := ⟨1⟩
private def p00 : Path := ⟨la0, pa0⟩
private def p01 : Path := ⟨la0, pa1⟩
private def p10 : Path := ⟨la1, pa0⟩

/-- Two of the peer's connection IDs, with sequence numbers 0 and 1
    (§5.1.1, line 1698: the `preferred_address` connection ID has number 1). -/
private def c0 : CidBytes := [0, 0, 0, 0]
private def c1 : CidBytes := [1, 1, 1, 1]

/-- A datagram leaving on path `p` carrying connection ID `cid`
    (`Spec.OutDatagram.src`/`dest` are the path, `dcid` the connection ID). -/
private def dgOn (p : Path) (cid : Option CidBytes) (pkts : List OutPacket) : OutDatagram :=
  { size := 1200, packets := pkts, src := ⟨p.loc.id⟩, dest := p.peer, dcid := cid }

example : pathOf (dgOn p10 (some c0) []) = p10 := by decide

private def run (s : State) : List Event → State
  | [] => s
  | e :: es => run ((component.step s e).next s) es

/-- A server just past its handshake with the client at `pa0`, using the peer's
    connection ID number 0 on that path, and told about the peer's connection
    IDs 0 and 1 (WP4 owns them; `Event.learnPeerCid` mirrors them). -/
private def srv : State :=
  run { (init .server p00 0) with handshakeConfirmed := true }
    [.learnPeerCid 0 c0, .learnPeerCid 1 c1]

/-- A client in the same position. -/
private def cli : State :=
  run { (init .client p00 0) with handshakeConfirmed := true }
    [.learnPeerCid 0 c0, .learnPeerCid 1 c1]

example : srv.peerCids = [(0, c0), (1, c1)] := by decide
example : srv.seqOfCid c1 = some 1 := by decide
example : srv.seqOfCid [7, 7] = none := by decide

-- §9.3, line 3379: "Receiving a packet from a new peer address containing a
-- non-probing frame indicates that the peer has migrated to that address" —
-- the server starts validation, switches, and probes the path it left
-- (§9.3.3, line 3498).
example : (component.step srv (.recvPacket p01 5 false 0)).obs =
    .ok [.startValidation p01, .switchPath p01, .validatePrevious p00] := by decide
example : ((component.step srv (.recvPacket p01 5 false 0)).next srv).active = p01 := by decide
-- … and refusing the migration is permitted too ("if the recipient permits"),
-- but §9, line 3312 still requires the path validation.
example : component.accepts srv (.recvPacket p01 5 false 0)
    (.ok (srv.observe p01 5 false 0) [.startValidation p01]) = true := by decide

-- §9.3, line 3379 has no condition on the *local* address the packet arrives
-- at (M-3): a non-probing, highest-numbered packet from a new peer address is
-- an apparent migration wherever it lands …
example : recvCase srv ⟨la1, pa1⟩ 5 false = .migrate := by decide
-- … and what line 3382 then requires is that we send to the new *peer* address;
-- the local address we send from is our own choice (§9.2, line 3345), so it
-- does not move.
example : ((component.step srv (.recvPacket ⟨la1, pa1⟩ 5 false 0)).next srv).active = p01 := by
  decide
example : srv.destOf ⟨la1, pa1⟩ = p01 := by decide

-- §9.1, line 3331 / line 3340: a probing packet from the new address validates
-- nothing about the peer's intent — the sending path does not move.
example : ((component.step srv (.recvPacket p01 5 true 0)).next srv).active = p00 := by decide
example : component.accepts srv (.recvPacket p01 5 true 0)
    (.ok (srv.permit p01 5 true 0) (srv.permitFx p01)) = false := by decide

-- §9.3, line 3387: "An endpoint only changes the address to which it sends
-- packets in response to the highest-numbered non-probing packet."  A
-- reordered packet from the old address cannot pull the connection back.
private def srvAt5 : State := (component.step srv (.recvPacket p01 5 false 0)).next srv
example : ((component.step srvAt5 (.recvPacket p00 3 false 0)).next srvAt5).active = p01 := by decide
-- … but a *newer* one does (§9.3.3, line 3492).
example : ((component.step srvAt5 (.recvPacket p00 9 false 0)).next srvAt5).active = p00 := by decide

-- §9.3.2, line 3451: validation of the new peer address fails, so the endpoint
-- reverts to the last validated peer address — which is the handshake path.
example : (component.step srvAt5 (.validationFailed p01)).obs = .ok [.switchPath p00] := by decide
example : ((component.step srvAt5 (.validationFailed p01)).next srvAt5).active = p00 := by decide

-- §9.3.2, line 3460: with no state about a last validated peer address, the
-- connection is closed silently by discarding all connection state.
private def srvNoLast : State := { srvAt5 with lastValidated := none }
example : (component.step srvNoLast (.validationFailed p01)).obs = .ok [.discardState] := by decide
example : ((component.step srvNoLast (.validationFailed p01)).next srvNoLast).discarded = true := by
  decide

-- §9, line 3289: we sent disable_active_migration and the peer migrated anyway.
-- "MUST either drop the incoming packets on that path without generating a
-- stateless reset or proceed with path validation and allow the peer to
-- migrate" — exactly two outcomes, and no third.
private def srvNoMig : State := { srv with ourDisableMigration := true }
example : outcomes srvNoMig (.recvPacket p01 5 false 0) =
    [.drop, .ok (srvNoMig.permit p01 5 false 0) (srvNoMig.permitFx p01)] := by decide
example : component.accepts srvNoMig (.recvPacket p01 5 false 0)
    (.ok (srvNoMig.observe p01 5 false 0) [.startValidation p01]) = false := by decide

-- §9, line 3280: before the handshake is confirmed a migration request does
-- nothing at all …
private def srvEarly : State := init .server p00 0
example : component.step srvEarly (.requestMigrate p10) = .drop := by decide
-- … and the send side refuses a non-probing packet from a new local address.
example : component.maySendDatagram srvEarly (dgOn p10 (some c1) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide
example : component.maySendDatagram srv (dgOn p10 (some c1) [⟨.oneRtt, [.ping]⟩]) = true := by
  decide

-- §9, line 3284: the peer sent disable_active_migration.  Probing packets are
-- covered too ("including probing packets"), and the ban is lifted once we have
-- acted on the peer's preferred_address.
private def cliNoMig : State := { cli with peerDisableMigration := true }
example : component.maySendDatagram cliNoMig (dgOn p10 (some c1) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide
example : component.maySendDatagram cliNoMig
    (dgOn p10 (some c1) [⟨.oneRtt, [.pathChallenge ByteArray.empty]⟩]) = false := by decide
example : component.maySendDatagram { cliNoMig with preferredActedOn := true }
    (dgOn p10 (some c1) [⟨.oneRtt, [.ping]⟩]) = true := by decide
-- … and it never applied to a destination other than the handshake address.
example : component.maySendDatagram cliNoMig
    (dgOn ⟨la1, pa1⟩ (some c1) [⟨.oneRtt, [.ping]⟩]) = true := by decide

-- M-2: the rule judges the datagram's own `src`/`dest`/`dcid`, not a send
-- context held in the state.  The same state permits one datagram and refuses
-- another that differs only in where it says it is going.
example : component.maySendDatagram srv (dgOn p00 (some c0) [⟨.oneRtt, [.ping]⟩]) = true := by decide
example : component.maySendDatagram srv (dgOn p01 (some c1) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide

-- §9.5, line 3603: the same connection ID may not be used from two local
-- addresses …
example : component.step cli (.beginSendOn p10 0) = .drop := by decide
-- … and, since line 3603 forbids *reuse*, changing the connection ID used on
-- the handshake path does not release connection ID 0 for a second local
-- address (regression for review finding M-1).
private def moved : State := run cli [.beginSendOn p00 3]
example : moved.dcidOn = [(p00, 3)] := by decide          -- what is in use now
example : moved.dcidFrom = [(0, la0), (3, la0)] := by decide   -- what has ever been used
example : cidCase moved p10 0 = .localReuse := by decide
example : component.step moved (.beginSendOn p10 0) = .drop := by decide
example : outcomes moved (.beginSendOn p10 0) = [.drop] := by decide
example : component.maySendDatagram moved (dgOn p10 (some c0) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide
-- … while a fresh sequence number is fine.
example : ((component.step cli (.beginSendOn p10 1)).next cli).dcidOn =
    [(p00, 0), (p10, 1)] := by decide
example : component.maySendDatagram ((component.step cli (.beginSendOn p10 1)).next cli)
    (dgOn p10 (some c1) [⟨.oneRtt, [.ping]⟩]) = true := by decide

-- §9.5, line 3609's MAY is about the *remote* address only, so the same
-- connection ID from the same local address to a new remote address is still
-- reachable — see the counterexample section below — but from a *second local
-- address* it is refused whatever the peer did.
example : cidCase moved ⟨la1, pa1⟩ 0 = .localReuse := by decide

-- A connection ID this component has not been told about (NOTES 16) leaves the
-- §9.5 clause with nothing to evaluate; the path clauses still apply.
example : component.maySendDatagram moved (dgOn p10 (some [9, 9]) [⟨.oneRtt, [.ping]⟩]) = true := by
  decide
example : component.maySendDatagram srvEarly (dgOn p10 (some [9, 9]) [⟨.oneRtt, [.ping]⟩]) = false
    := by decide

-- §9, line 3325: "If a client receives packets from an unknown server address,
-- the client MUST discard these packets."
example : outcomes cli (.recvPacket ⟨la0, ⟨9⟩⟩ 5 false 0) = [.drop] := by decide

-- §9.6: the server's preferred address.  The client learns it, migrates only
-- after validating it (§9.6.2, line 3715), and uses connection ID number 1
-- (§5.1.1, line 1698).
private def cliPref : State := (component.step cli (.learnPreferredAddress pa1)).next cli
example : cliPref.preferredPeer = some pa1 := by decide
example : (component.step cliPref (.requestMigrate p01)).obs = .ok [.startValidation p01] := by decide
example : ((component.step cliPref (.requestMigrate p01)).next cliPref).active = p00 := by decide
example : ((component.step cliPref (.requestMigrate p01)).next cliPref).preferredActedOn = true := by
  decide
example : preferredAddressCidSeq = 1 := by decide
-- §9.6.1, line 3707: as soon as validation succeeds the client moves over.
private def cliProbing : State := (component.step cliPref (.requestMigrate p01)).next cliPref
example : ((component.step cliProbing (.validationSucceeded p01)).next cliProbing).active = p01 := by
  decide
-- §9.6.1, line 3710: if it fails, the client keeps using the original address
-- and may not send to the preferred one.
private def cliFailed : State := (component.step cliProbing (.validationFailed p01)).next cliProbing
example : cliFailed.active = p00 := by decide
example : component.maySendDatagram cliFailed (dgOn p01 (some c1) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide

-- §9, line 3323: "Servers do not send non-probing packets toward a client
-- address until they see a non-probing packet from that address."
example : component.maySendDatagram srv (dgOn p01 (some c1) [⟨.oneRtt, [.ping]⟩]) = false := by
  decide
example : component.maySendDatagram srv
    (dgOn p01 (some c1) [⟨.oneRtt, [.pathChallenge ByteArray.empty]⟩]) = true := by decide
example : component.maySendDatagram srvAt5 (dgOn p01 (some c1) [⟨.oneRtt, [.ping]⟩]) = true := by
  decide

-- A datagram may carry only packets that are themselves permitted (§12.2: the
-- packets coalesced in one datagram share its path and connection ID).
example : component.maySendDatagram srv (dgOn p01 (some c1)
    [⟨.oneRtt, [.pathChallenge ByteArray.empty]⟩, ⟨.oneRtt, [.ping]⟩]) = false := by decide

-- Set tracking, for the differential harness: seeing "nothing visible" after a
-- probing packet from a new address is impossible, because §9, line 3312
-- requires a path validation to start.
example : component.trackSet [srv] (.recvPacket p01 5 true 0) (Obs.ok []).matchesLoosely = [] := by
  decide

/-! ### The counterexample to the unrestricted form of (c)

The route below is *reachable from `cli` by permitted steps*
(`cliTwoPeers_reachable`), which the earlier hand-built witness was not
(review finding on theorem (c)).  It is the situation §9.5, line 3609 describes:
the server's packets start arriving from a new source address while addressing
the client with the same connection ID of the client's, so line 3611 lets the
client keep the connection ID it is using and send it to the new remote
address — while §9.3.3, line 3498 obliges it to go on probing the path it left,
which is a send with that same connection ID to the *old* remote address. -/

section Counterexample

/-- 1. A packet from the server on the handshake path, addressed to our
    connection ID number 4. -/
private def cliR1 : State := cli.observe p00 1 false 4
/-- 2. The `preferred_address` transport parameter (§9.6.1, line 3686). -/
private def cliR2 : State := { cliR1 with preferredPeer := some pa1 }
/-- 3. §9.6.2, line 3715: the client validates the preferred address before
    migrating to it, which is how it "acts on" the parameter. -/
private def cliR3 : State := cliR2.startProbe p01
/-- 4. A non-probing packet arrives from the preferred address, addressed to the
    same connection ID of ours: §9.3, line 3379's apparent migration. -/
private def cliR4 : State := cliR3.permit p01 2 false 4
/-- 5. §9.5, line 3611: the client keeps connection ID 0 on the new remote
    address. -/
private def cliTwoPeers : State := cliR4.useCid p01 0

private theorem r1 : Step cli (.recvPacket p00 1 false 4)
    (.ok cliR1 (cli.observeFx p00)) := Step.recvQuiet (by decide)
private theorem r2 : Step cliR1 (.learnPreferredAddress pa1) (.ok cliR2 []) :=
  Step.preferredLearn (by decide)
private theorem r3 : Step cliR2 (.requestMigrate p01) (.ok cliR3 [.startValidation p01]) :=
  Step.migValidateFirst (by decide)
private theorem r4 : Step cliR3 (.recvPacket p01 2 false 4)
    (.ok cliR4 (cliR3.permitFx p01)) := Step.recvMigrate (by decide)
private theorem r5 : Step cliR4 (.beginSendOn p01 0) (.ok cliTwoPeers []) :=
  Step.cidRebindKeep (by decide)

theorem cliTwoPeers_reachable : component.Reachable cli cliTwoPeers :=
  ((((Component.Reachable.refl.step r1).step r2).step r3).step r4).step r5

-- The steps of the route, read back.
example : recvCase cli p00 1 false = .quiet := by decide
example : cliR2.preferredPeer = some pa1 := by decide
example : migCase cliR2 p01 = .validateFirst := by decide
example : cliR3.preferredActedOn = true := by decide
example : recvCase cliR3 p01 2 false = .migrate := by decide
-- §9.3.3, line 3498: the model itself demands that the previous path go on
-- being probed, which is what keeps connection ID 0 in use toward `pa0`.
example : cliR3.permitFx p01 = [.startValidation p01, .switchPath p01, .validatePrevious p00] := by
  decide
example : cidCase cliR4 p01 0 = .rebind := by decide
-- … and the MAY is a MAY: refusing and taking a fresh connection ID instead is
-- equally conforming.
example : outcomes cliR4 (.beginSendOn p01 0) = [.ok (cliR4.useCid p01 0) [], .drop] := by decide

-- The counterexample proper: one connection ID sequence number in use on two
-- distinct paths at once, and both sends permitted.
example : cliTwoPeers.dcidOn = [(p00, 0), (p01, 0)] := by decide
example : p00 ≠ p01 := by decide
example : component.maySendDatagram cliTwoPeers (dgOn p01 (some c0) [⟨.oneRtt, [.ping]⟩]) = true := by
  decide
example : component.maySendDatagram cliTwoPeers
    (dgOn p00 (some c0) [⟨.oneRtt, [.pathChallenge ByteArray.empty]⟩]) = true := by decide
-- What survives is the local-address half of the rule (`dcid_one_local_address`).
example : p00.loc = p01.loc := by decide
example : cliTwoPeers.dcidFrom = [(0, la0)] := by decide
-- … and the history records both destinations connection ID 0 has gone to.
example : cliTwoPeers.dcidTo = [(0, [pa0, pa1])] := by decide

end Counterexample

end Quic.Spec.Migration
