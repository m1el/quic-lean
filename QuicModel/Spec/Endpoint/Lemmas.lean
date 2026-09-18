import QuicModel.Spec.Handshake
import QuicModel.Spec.StreamTable
import QuicModel.Spec.Migration
import QuicModel.Spec.Termination
import QuicModel.Spec.ConnIds
import QuicModel.Spec.DatagramSize
import QuicModel.Spec.VersionNegotiation
import QuicModel.Spec.Ack
import QuicModel.Spec.Ecn

/-!
  WP12 "Endpoint", part 0: the facts about *other* components that composition
  needs and that no package stated, because none of them needed it on its own.

  Every one of them is of the same shape: "a step of this component never
  changes the field that identifies the endpoint".  They are what makes the
  cross-component clauses of `Endpoint.Inv` (roles agree; each `Ack` instance
  stays in its packet number space) preserved by `Endpoint.step_inv`.

  Nothing here edits another package: these are theorems *about* the components'
  `Step` relations, proved from their constructors.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## Roles are constant -/

theorem handshake_role_const {s s' : Handshake.State} {e : Handshake.Event}
    {fx : List Handshake.Effect} (h : Handshake.Step s e (.ok s' fx)) : s'.role = s.role := by
  cases h with
  | keys =>
    rename_i dir l
    obtain ⟨r, w, he⟩ := Handshake.provideKey_eq s dir l
    rw [he]
  | params hp => cases hp <;> rfl
  | header hh => cases hh <;> rfl
  | crypto hh => cases hh <;> rfl
  | _ => rfl

theorem streamTable_role_const {s s' : StreamTable.State} {e : StreamTable.Event}
    {fx : List StreamTable.Effect} (h : StreamTable.Step s e (.ok s' fx)) :
    s'.role = s.role := by
  cases h <;> rfl

theorem addressValidation_role_const {s s' : AddressValidation.State}
    {e : AddressValidation.Event} {fx : List AddressValidation.Effect}
    (h : AddressValidation.Step s e (.ok s' fx)) : s'.role = s.role := by
  cases h <;> rfl

/-- The three state helpers of §9 that are written with an `if`, so that they do
    not reduce by `rfl`.  Every branch of each of them is a record update that
    leaves `role` alone. -/
theorem migration_role_markFailed (s : Migration.State) (p : Migration.Path) :
    (s.markFailed p).role = s.role := by
  unfold Migration.State.markFailed; split <;> rfl

theorem migration_role_observe (s : Migration.State) (p : Migration.Path)
    (pn : Nat) (pr : Bool) (d : Nat) : (s.observe p pn pr d).role = s.role := by
  unfold Migration.State.observe; split <;> rfl

theorem migration_role_permit (s : Migration.State) (p : Migration.Path)
    (pn : Nat) (pr : Bool) (d : Nat) : (s.permit p pn pr d).role = s.role := by
  unfold Migration.State.permit; split <;> rfl

theorem migration_role_const {s s' : Migration.State} {e : Migration.Event}
    {fx : List Migration.Effect} (h : Migration.Step s e (.ok s' fx)) : s'.role = s.role := by
  cases h <;> first
    | rfl
    | exact migration_role_markFailed _ _
    | exact migration_role_observe _ _ _ _ _
    | exact migration_role_permit _ _ _ _ _

theorem datagramSize_role_const {s s' : DatagramSize.State} {e : DatagramSize.Event}
    {fx : List DatagramSize.Effect} (h : DatagramSize.Step s e (.ok s' fx)) :
    s'.role = s.role := by
  cases h <;> rfl

theorem frameRules_role_const {s s' : FrameRules.State} {e : FrameRules.Event}
    {fx : List FrameRules.Effect} (h : FrameRules.Step s e (.ok s' fx)) : s'.role = s.role :=
  FrameRules.role_const h

/-! ## Each `Ack` instance stays in its packet number space -/

theorem ack_space_const {s s' : Ack.State} {e : Ack.Event} {fx : List Ack.Effect}
    (h : Ack.Step s e (.ok s' fx)) : s'.space = s.space := by
  cases h with
  | ackSent => exact Ack.State.afterAckSent_space ..
  | _ => rfl

/-- Each `Ecn` instance stays in its packet number space (§13.4.1, line 5514). -/
theorem ecn_space_const {s s' : Ecn.State} {e : Ecn.Event} {fx : List Ecn.Effect}
    (h : Ecn.Step s e (.ok s' fx)) : s'.space = s.space := by
  cases h <;>
    first
      | rfl
      | (unfold Ecn.State.recordRecv; split <;> rfl)
      | (unfold Ecn.State.fail; split <;> rfl)
      | (simp only [Ecn.State.recordRecv, Ecn.State.fail]; repeat' split
         all_goals rfl)

/-! ## Handshake confirmation only ever turns on

Not needed by `step_inv` (the endpoint re-imposes the bit rather than tracking
it; see `Endpoint.syncConfirmed`), but it is what makes that re-imposition a
faithful reading of `Termination.Step.handshakeConfirmed`, which only ever sets
the bit. -/

theorem handshake_confirmed_mono {s s' : Handshake.State} {e : Handshake.Event}
    {fx : List Handshake.Effect} (h : Handshake.Step s e (.ok s' fx))
    (hc : s.confirmed = true) : s'.confirmed = true := by
  cases h with
  | keys =>
    rename_i dir l
    obtain ⟨r, w, he⟩ := Handshake.provideKey_eq s dir l
    rw [he]; exact hc
  | params hp => cases hp <;> exact hc
  | header hh => cases hh <;> exact hc
  | crypto hh => cases hh <;> exact hc
  | _ => first | rfl | exact hc

end Quic.Spec.Endpoint
