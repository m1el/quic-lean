import QuicModel.Spec.Endpoint.Merge

/-!
  WP12 "Endpoint", part 1h: one wrapper per merged component.

  `stepX s e` is "hand event `e` to component X, keep every outcome X permits,
  tag its effects, write its state back".  Each comes with the two facts the
  composition needs: the list is never empty (so `outcomes_ne` lifts), and
  every `ok` in it satisfies `Endpoint.Inv` (so `step_inv` lifts).

  These are the only places the endpoint writes a component's state.  That is
  what makes `Endpoint.step_inv` a proof rather than a re-derivation: the
  component invariants hold because each component's own `step_inv` is applied
  to its projection, and the cross-component ones because the wrapper is the
  only writer.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ### Trivial steps -/

/-- Nothing happens. -/
def keep (s : State) : List Out := [.ok s []]

theorem keep_ne (s : State) : keep s ≠ [] := by simp [keep]

theorem keep_inv {s : State} (hi : Inv s) : InvOk (keep s) := InvOk.ok hi

/-- Give a path its `PathValidation` handle if it has none (Migration NOTES 1). -/
def register (p : Migration.Path) (s : State) : List Out := [.ok (s.register p) []]

theorem register_ne (p : Migration.Path) (s : State) : register p s ≠ [] := by simp [register]

theorem register_inv {s : State} (hi : Inv s) (p : Migration.Path) :
    InvOk (register p s) := InvOk.ok (inv_register hi p)

/-! ### One wrapper per component -/

def stepHs (s : State) (e : Handshake.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with hs := x }) Effect.hs (Handshake.outcomes s.hs e)

theorem stepHs_ne (s : State) (e : Handshake.Event) : stepHs s e ≠ [] :=
  liftList_ne (Handshake.outcomes_ne _ _)

theorem stepHs_inv {s : State} (hi : Inv s) (e : Handshake.Event) : InvOk (stepHs s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Handshake.outcomes_iff _ _ _).mp ho
  exact inv_setHs hi (Handshake.step_inv _ _ _ _ hi.hs hstep) (handshake_role_const hstep)

def stepSt (s : State) (e : StreamTable.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with st := x }) Effect.st (StreamTable.outcomes s.st e)

theorem stepSt_ne (s : State) (e : StreamTable.Event) : stepSt s e ≠ [] :=
  liftList_ne (StreamTable.outcomes_ne _ _)

theorem stepSt_inv {s : State} (hi : Inv s) (e : StreamTable.Event) : InvOk (stepSt s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (StreamTable.outcomes_iff _ _ _).mp ho
  exact inv_setSt hi (StreamTable.step_inv _ _ _ _ hi.st hstep) (streamTable_role_const hstep)

def stepFr (s : State) (e : FrameRules.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with fr := x }) Effect.fr (FrameRules.outcomes s.fr e)

theorem stepFr_ne (s : State) (e : FrameRules.Event) : stepFr s e ≠ [] :=
  liftList_ne (FrameRules.outcomes_ne _ _)

theorem stepFr_inv {s : State} (hi : Inv s) (e : FrameRules.Event) : InvOk (stepFr s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (FrameRules.outcomes_iff _ _ _).mp ho
  exact inv_setFr hi (frameRules_role_const hstep)

def stepAck (s : State) (sp : PnSpace) (e : Ack.Event) : List Out :=
  liftList (fun x => syncConfirmed (s.setAck sp x)) (Effect.ack sp) (Ack.outcomes (s.ack sp) e)

theorem stepAck_ne (s : State) (sp : PnSpace) (e : Ack.Event) : stepAck s sp e ≠ [] :=
  liftList_ne (Ack.outcomes_ne _ _)

theorem stepAck_inv {s : State} (hi : Inv s) (sp : PnSpace) (e : Ack.Event) :
    InvOk (stepAck s sp e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Ack.outcomes_iff _ _ _).mp ho
  exact inv_setAck hi sp (Ack.step_inv _ _ _ _ (hi.ackOf sp) hstep)
    ((ack_space_const hstep).trans (hi.spaceOf sp))

def stepCidLocal (s : State) (e : ConnIds.Local.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with cidLocal := x }) Effect.cidLocal
    (ConnIds.Local.outcomes s.cidLocal e)

theorem stepCidLocal_ne (s : State) (e : ConnIds.Local.Event) : stepCidLocal s e ≠ [] :=
  liftList_ne (ConnIds.Local.outcomes_ne _ _)

theorem stepCidLocal_inv {s : State} (hi : Inv s) (e : ConnIds.Local.Event) :
    InvOk (stepCidLocal s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (ConnIds.Local.outcomes_iff _ _ _).mp ho
  exact inv_setCidLocal hi (ConnIds.Local.step_inv _ _ _ _ hi.cidL hstep)

def stepCidRemote (s : State) (e : ConnIds.Remote.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with cidRemote := x }) Effect.cidRemote
    (ConnIds.Remote.outcomes s.cidRemote e)

theorem stepCidRemote_ne (s : State) (e : ConnIds.Remote.Event) : stepCidRemote s e ≠ [] :=
  liftList_ne (ConnIds.Remote.outcomes_ne _ _)

theorem stepCidRemote_inv {s : State} (hi : Inv s) (e : ConnIds.Remote.Event) :
    InvOk (stepCidRemote s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (ConnIds.Remote.outcomes_iff _ _ _).mp ho
  exact inv_setCidRemote hi (ConnIds.Remote.step_inv _ _ _ _ hi.cidR hstep)

def stepAv (s : State) (e : AddressValidation.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with av := x }) Effect.av
    (AddressValidation.outcomes s.av e)

theorem stepAv_ne (s : State) (e : AddressValidation.Event) : stepAv s e ≠ [] :=
  liftList_ne (AddressValidation.outcomes_ne _ _)

theorem stepAv_inv {s : State} (hi : Inv s) (e : AddressValidation.Event) :
    InvOk (stepAv s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (AddressValidation.outcomes_iff _ _ _).mp ho
  exact inv_setAv hi (AddressValidation.step_inv _ _ _ _ hi.av hstep)
    (addressValidation_role_const hstep)

def stepPv (s : State) (e : PathValidation.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with pv := x }) Effect.pv
    (PathValidation.outcomes s.pv e)

theorem stepPv_ne (s : State) (e : PathValidation.Event) : stepPv s e ≠ [] :=
  liftList_ne (PathValidation.outcomes_ne _ _)

theorem stepPv_inv {s : State} (hi : Inv s) (e : PathValidation.Event) :
    InvOk (stepPv s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (PathValidation.outcomes_iff _ _ _).mp ho
  exact inv_setPv hi (PathValidation.step_inv _ _ _ _ hi.pv hstep)

def stepMig (s : State) (e : Migration.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with mig := x }) Effect.mig
    (Migration.outcomes s.mig e)

theorem stepMig_ne (s : State) (e : Migration.Event) : stepMig s e ≠ [] :=
  liftList_ne (Migration.outcomes_ne _ _)

theorem stepMig_inv {s : State} (hi : Inv s) (e : Migration.Event) : InvOk (stepMig s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Migration.outcomes_iff _ _ _).mp ho
  exact inv_setMig hi (Migration.step_inv _ _ _ _ hi.mig hstep) (migration_role_const hstep)

def stepTerm (s : State) (e : Termination.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with term := x }) Effect.term
    (Termination.outcomes s.term e)

theorem stepTerm_ne (s : State) (e : Termination.Event) : stepTerm s e ≠ [] :=
  liftList_ne (Termination.outcomes_ne _ _)

theorem stepTerm_inv {s : State} (hi : Inv s) (e : Termination.Event) :
    InvOk (stepTerm s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Termination.outcomes_iff _ _ _).mp ho
  exact inv_setTerm hi (Termination.step_inv _ _ _ _ hi.term hstep)

def stepVnServer (s : State) (e : VersionNeg.Server.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with vnServer := x }) Effect.vnServer
    (VersionNeg.Server.outcomes s.vnServer e)

theorem stepVnServer_ne (s : State) (e : VersionNeg.Server.Event) : stepVnServer s e ≠ [] :=
  liftList_ne (VersionNeg.Server.outcomes_ne _ _)

theorem stepVnServer_inv {s : State} (hi : Inv s) (e : VersionNeg.Server.Event) :
    InvOk (stepVnServer s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (VersionNeg.Server.outcomes_iff _ _ _).mp ho
  exact inv_setVnServer hi (VersionNeg.Server.step_inv _ _ _ _ hi.vnS hstep)

def stepVnClient (s : State) (e : VersionNeg.Client.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with vnClient := x }) Effect.vnClient
    (VersionNeg.Client.outcomes s.vnClient e)

theorem stepVnClient_ne (s : State) (e : VersionNeg.Client.Event) : stepVnClient s e ≠ [] :=
  liftList_ne (VersionNeg.Client.outcomes_ne _ _)

theorem stepVnClient_inv {s : State} (hi : Inv s) (e : VersionNeg.Client.Event) :
    InvOk (stepVnClient s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (VersionNeg.Client.outcomes_iff _ _ _).mp ho
  exact inv_setVnClient hi (VersionNeg.Client.step_inv _ _ _ _ hi.vnC hstep)

def stepDsz (s : State) (e : DatagramSize.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with dsz := x }) Effect.dsz
    (DatagramSize.outcomes s.dsz e)

theorem stepDsz_ne (s : State) (e : DatagramSize.Event) : stepDsz s e ≠ [] :=
  liftList_ne (DatagramSize.outcomes_ne _ _)

theorem stepDsz_inv {s : State} (hi : Inv s) (e : DatagramSize.Event) :
    InvOk (stepDsz s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (DatagramSize.outcomes_iff _ _ _).mp ho
  exact inv_setDsz hi (DatagramSize.step_inv _ _ _ _ hi.dsz hstep) (datagramSize_role_const hstep)

def stepRtx (s : State) (e : Retransmission.Event) : List Out :=
  liftList (fun x => syncConfirmed { s with rtx := x }) Effect.rtx
    (Retransmission.outcomes s.rtx e)

theorem stepRtx_ne (s : State) (e : Retransmission.Event) : stepRtx s e ≠ [] :=
  liftList_ne (Retransmission.outcomes_ne _ _)

theorem stepRtx_inv {s : State} (hi : Inv s) (e : Retransmission.Event) :
    InvOk (stepRtx s e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Retransmission.outcomes_iff _ _ _).mp ho
  exact inv_setRtx hi (Retransmission.step_inv _ _ _ _ hi.rtx hstep)

def stepEcn (s : State) (sp : PnSpace) (e : Ecn.Event) : List Out :=
  liftList (fun x => syncConfirmed (s.setEcn sp x)) (Effect.ecn sp) (Ecn.outcomes (s.ecn sp) e)

theorem stepEcn_ne (s : State) (sp : PnSpace) (e : Ecn.Event) : stepEcn s sp e ≠ [] :=
  liftList_ne (Ecn.outcomes_ne _ _)

theorem stepEcn_inv {s : State} (hi : Inv s) (sp : PnSpace) (e : Ecn.Event) :
    InvOk (stepEcn s sp e) := by
  intro s' fx hm
  obtain ⟨o, ho, he⟩ := mem_liftList hm
  obtain ⟨x, gx, rfl, rfl⟩ := liftOutcome_eq_ok he
  have hstep := (Ecn.outcomes_iff _ _ _).mp ho
  exact inv_setEcn hi sp (Ecn.step_inv _ _ _ _ (hi.ecnOf sp) hstep)
    ((ecn_space_const hstep).trans (hi.ecnSpaceOf sp))

/-! ### Adding an alternative at the top level

§5.2.2 line 1936's CONNECTION_REFUSED, §11.1 line 4485's "MAY discard an invalid
Initial even where this specification otherwise mandates a connection error",
and §5.2.2 line 1946's "servers MUST drop under all other circumstances" are
rights of the *endpoint*, not of any component.  They are added here as extra
alternatives, and `addAlt` is the only way a permitted outcome ever enters the
list without a component having produced it. -/

/-- Append an outcome that no component produced.  The added outcome is always
    an `.error` or a `.drop`, so `InvOk` is unaffected. -/
def addAlt (l : List Out) (o : Out) : List Out := l ++ [o]

theorem addAlt_ne {l : List Out} (h : l ≠ []) (o : Out) : addAlt l o ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [addAlt]

theorem addAlt_inv_error {l : List Out} (h : InvOk l) (c : TransportError) :
    InvOk (addAlt l (.error c)) := InvOk.append h (InvOk.error c)

theorem addAlt_inv_drop {l : List Out} (h : InvOk l) :
    InvOk (addAlt l .drop) := InvOk.append h InvOk.drop

/-- Only error and drop alternatives may be added this way. -/
def isNonOk : Out → Bool
  | .ok .. => false
  | _ => true

/-- Several such alternatives at once. -/
def addAlts (l : List Out) (os : List Out) : List Out := l ++ os.filter isNonOk

theorem addAlts_ne {l : List Out} (h : l ≠ []) (os : List Out) : addAlts l os ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [addAlts]

theorem addAlts_inv {l : List Out} (h : InvOk l) (os : List Out) : InvOk (addAlts l os) := by
  refine InvOk.append h ?_
  intro s' fx hm
  obtain ⟨-, hb⟩ := List.mem_filter.mp hm
  simp [isNonOk] at hb

end Quic.Spec.Endpoint
