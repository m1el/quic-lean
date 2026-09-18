import QuicModel.Spec.Endpoint.Basic

/-!
  WP12 "Endpoint", part 1g: **the merge rule**, once, as a handful of
  combinators, and the proof that each of them preserves `Endpoint.Inv`.

  The rule (PLAN §4b–§4d):

  * one component's permitted outcomes are lifted to the endpoint by tagging
    its effects and writing its state back (`liftList`);
  * two steps in sequence compose as the **product** of their alternative lists
    (`bindAll`), so nothing a component permits is lost;
  * an `.error` from any component is a permitted outcome of the whole, and the
    effects produced before it are *dropped* from that outcome (`withFx`):
    ngtcp2 fires callbacks and then fails, and only the error code is compared
    (PLAN §4a);
  * `.error` and `.drop` are terminal for the rest of the sequence they occur
    in;
  * connection-level refusals are *added* at the top level as extra
    alternatives (`Endpoint/Pipeline.lean`), never removed by a component whose
    `accepts` is `false` — `AddressValidation` NOTES 5.

  Each component's state is written back through `syncConfirmed`, which
  re-imposes WP11's "handshake confirmed" bit on WP6 and WP10.  That is the one
  piece of state three components hold a copy of; `Endpoint.InvConfirmed` is
  what it maintains.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ### Keeping the three copies of "handshake confirmed" equal -/

/-- WP11 owns the bit (`Handshake.State.confirmed`); WP6 needs it for §10.2.3
    line 4056 and WP10 for §9 line 3280.  Writing it back after every step is a
    no-op except at the moment WP11 sets it, because
    `Endpoint.handshake_confirmed_mono` says WP11 never clears it and neither
    `Termination.Step` nor `Migration.Step` changes it except through the
    `handshakeConfirmed` events, which this composition never fires. -/
def syncConfirmed (s : State) : State :=
  { s with term := { s.term with handshakeConfirmed := s.hs.confirmed },
           mig := { s.mig with handshakeConfirmed := s.hs.confirmed } }

@[simp] theorem syncConfirmed_hs (s : State) : (syncConfirmed s).hs = s.hs := rfl
@[simp] theorem syncConfirmed_role (s : State) : (syncConfirmed s).role = s.role := rfl

/-! ### Lifting one component's outcomes -/

/-- Tag one component's effects and write its state back. -/
def liftOutcome {σ ε : Type} (put : σ → State) (tag : ε → Effect) :
    Outcome σ ε → Out
  | .ok x fx => .ok (put x) (fx.map tag)
  | .error c => .error c
  | .drop => .drop

def liftList {σ ε : Type} (put : σ → State) (tag : ε → Effect)
    (l : List (Outcome σ ε)) : List Out := l.map (liftOutcome put tag)

theorem liftList_ne {σ ε : Type} {put : σ → State} {tag : ε → Effect}
    {l : List (Outcome σ ε)} (h : l ≠ []) : liftList put tag l ≠ [] := by
  simpa [liftList] using h

theorem liftOutcome_eq_ok {σ ε : Type} {put : σ → State} {tag : ε → Effect}
    {o : Outcome σ ε} {s' : State} {fx : List Effect}
    (h : liftOutcome put tag o = .ok s' fx) :
    ∃ x gx, o = .ok x gx ∧ s' = put x := by
  cases o with
  | ok x gx =>
    simp only [liftOutcome, Outcome.ok.injEq] at h
    exact ⟨x, gx, rfl, h.1.symm⟩
  | error c => simp [liftOutcome] at h
  | drop => simp [liftOutcome] at h

theorem mem_liftList {σ ε : Type} {put : σ → State} {tag : ε → Effect}
    {l : List (Outcome σ ε)} {o : Out} (h : o ∈ liftList put tag l) :
    ∃ o', o' ∈ l ∧ liftOutcome put tag o' = o := by
  simpa [liftList, eq_comm] using List.mem_map.mp h

/-! ### Sequencing

`withFx` is where "effects that precede an error are dropped from the error
outcome" is decided: an error outcome keeps nothing but its code. -/

def withFx (fx : List Effect) : Out → Out
  | .ok s' fx' => .ok s' (fx ++ fx')
  | .error c => .error c
  | .drop => .drop

/-- Continue from one outcome.  `.error` and `.drop` are terminal. -/
def bindOut (o : Out) (f : State → List Out) : List Out :=
  match o with
  | .ok s fx => (f s).map (withFx fx)
  | .error c => [.error c]
  | .drop => [.drop]

/-- The product of two alternative lists: every continuation of every outcome. -/
def bindAll (l : List Out) (f : State → List Out) : List Out :=
  l.flatMap (fun o => bindOut o f)

theorem bindOut_ne {o : Out} {f : State → List Out} (hf : ∀ s, f s ≠ []) :
    bindOut o f ≠ [] := by
  cases o with
  | ok s fx => simpa [bindOut] using hf s
  | error c => simp [bindOut]
  | drop => simp [bindOut]

theorem bindAll_ne {l : List Out} {f : State → List Out} (hl : l ≠ [])
    (hf : ∀ s, f s ≠ []) : bindAll l f ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t =>
    simp only [bindAll, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
    intro h
    exact absurd h (bindOut_ne hf)

/-! ### `Inv` through the combinators -/

/-- Every `ok` outcome in this list satisfies the endpoint invariant. -/
def InvOk (l : List Out) : Prop := ∀ s' fx, (Outcome.ok s' fx) ∈ l → Inv s'

theorem InvOk.nil : InvOk [] := by intro _ _ h; simp at h

theorem InvOk.error (c : TransportError) : InvOk [Outcome.error c] := by
  intro _ _ h; simp at h

theorem InvOk.drop : InvOk [(Outcome.drop : Out)] := by intro _ _ h; simp at h

theorem InvOk.ok {s : State} {fx : List Effect} (h : Inv s) : InvOk [Outcome.ok s fx] := by
  intro s' _ hm
  simp only [List.mem_singleton, Outcome.ok.injEq] at hm
  exact hm.1 ▸ h

theorem InvOk.append {l₁ l₂ : List Out} (h₁ : InvOk l₁) (h₂ : InvOk l₂) :
    InvOk (l₁ ++ l₂) := by
  intro s' fx hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h₁ _ _ hm
  · exact h₂ _ _ hm

theorem InvOk.cons {o : Out} {l : List Out} (h₁ : InvOk [o]) (h₂ : InvOk l) :
    InvOk (o :: l) := by
  intro s' fx hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact h₁ _ _ (List.mem_singleton.mpr hm)
  · exact h₂ _ _ hm

theorem invOk_bindOut {o : Out} {f : State → List Out} (ho : InvOk [o])
    (hf : ∀ s, Inv s → InvOk (f s)) : InvOk (bindOut o f) := by
  cases o with
  | ok s fx =>
    have hs : Inv s := ho s fx (List.mem_singleton.mpr rfl)
    intro s' fx' hm
    simp only [bindOut, List.mem_map] at hm
    obtain ⟨o', ho', he⟩ := hm
    cases o' with
    | ok x gx =>
      simp only [withFx, Outcome.ok.injEq] at he
      exact he.1 ▸ hf s hs _ _ ho'
    | error c => simp [withFx] at he
    | drop => simp [withFx] at he
  | error c => intro _ _ hm; simp [bindOut] at hm
  | drop => intro _ _ hm; simp [bindOut] at hm

theorem invOk_bindAll {l : List Out} {f : State → List Out} (hl : InvOk l)
    (hf : ∀ s, Inv s → InvOk (f s)) : InvOk (bindAll l f) := by
  intro s' fx hm
  simp only [bindAll, List.mem_flatMap] at hm
  obtain ⟨o, ho, hmem⟩ := hm
  refine invOk_bindOut (o := o) ?_ hf s' fx hmem
  intro a b hab
  simp only [List.mem_singleton] at hab
  exact hl a b (hab ▸ ho)

/-! ### The setters, and that each preserves `Inv`

Each writes one component's state back through `syncConfirmed`.  Where a
component's own `Inv` mentions its role (`StreamTable`), the hypothesis that
the role did not change comes from `Endpoint/Lemmas.lean`. -/

theorem inv_setHs {s : State} {x : Handshake.State} (hi : Inv s)
    (hx : Handshake.Inv x) (hr : x.role = s.hs.role) :
    Inv (syncConfirmed { s with hs := x }) :=
  ⟨hx, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩,
   ⟨hr.trans hi.role.1, hi.role.2.1, hi.role.2.2.1, hi.role.2.2.2.1, hi.role.2.2.2.2.1,
    hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

theorem inv_setSt {s : State} {x : StreamTable.State} (hi : Inv s)
    (hx : StreamTable.Inv x) (hr : x.role = s.st.role) :
    Inv (syncConfirmed { s with st := x }) :=
  ⟨hi.hs, hx, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩,
   ⟨hi.role.1, hr.trans hi.role.2.1, hi.role.2.2.1, hi.role.2.2.2.1, hi.role.2.2.2.2.1,
    hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

theorem inv_setFr {s : State} {x : FrameRules.State} (hi : Inv s)
    (hr : x.role = s.fr.role) : Inv (syncConfirmed { s with fr := x }) :=
  ⟨hi.hs, hi.st, trivial, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩,
   ⟨hi.role.1, hi.role.2.1, hr.trans hi.role.2.2.1, hi.role.2.2.2.1, hi.role.2.2.2.2.1,
    hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

theorem inv_setAck {s : State} {x : Ack.State} (hi : Inv s) (sp : PnSpace)
    (hx : Ack.Inv x) (hsp : x.space = sp) :
    Inv (syncConfirmed (s.setAck sp x)) := by
  cases sp <;>
    exact ⟨hi.hs, hi.st, hi.fr, by first | exact hx | exact hi.ackI,
      by first | exact hx | exact hi.ackH, by first | exact hx | exact hi.ackA,
      hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig, hi.term, hi.vnS, hi.vnC, hi.dsz,
      ⟨rfl, rfl⟩, hi.role,
      ⟨by first | exact hsp | exact hi.spaces.1, by first | exact hsp | exact hi.spaces.2.1,
       by first | exact hsp | exact hi.spaces.2.2⟩,
      hi.paths⟩

theorem inv_setCidLocal {s : State} {x : ConnIds.Local.State} (hi : Inv s)
    (hx : ConnIds.Local.Inv x) : Inv (syncConfirmed { s with cidLocal := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hx, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setCidRemote {s : State} {x : ConnIds.Remote.State} (hi : Inv s)
    (hx : ConnIds.Remote.Inv x) : Inv (syncConfirmed { s with cidRemote := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hx, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setAv {s : State} {x : AddressValidation.State} (hi : Inv s)
    (hx : AddressValidation.Inv x) (hr : x.role = s.av.role) :
    Inv (syncConfirmed { s with av := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hx, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩,
   ⟨hi.role.1, hi.role.2.1, hi.role.2.2.1, hr.trans hi.role.2.2.2.1, hi.role.2.2.2.2.1,
    hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

theorem inv_setPv {s : State} {x : PathValidation.State} (hi : Inv s)
    (hx : PathValidation.Inv x) : Inv (syncConfirmed { s with pv := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hx, hi.mig,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setMig {s : State} {x : Migration.State} (hi : Inv s)
    (hx : Migration.Inv x) (hr : x.role = s.mig.role) :
    Inv (syncConfirmed { s with mig := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hx,
   hi.term, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩,
   ⟨hi.role.1, hi.role.2.1, hi.role.2.2.1, hi.role.2.2.2.1, hr.trans hi.role.2.2.2.2.1,
    hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

theorem inv_setTerm {s : State} {x : Termination.State} (hi : Inv s)
    (hx : Termination.Inv x) : Inv (syncConfirmed { s with term := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hx, hi.vnS, hi.vnC, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setVnServer {s : State} {x : VersionNeg.Server.State} (hi : Inv s)
    (hx : VersionNeg.Server.Inv x) : Inv (syncConfirmed { s with vnServer := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hx, hi.vnC, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setVnClient {s : State} {x : VersionNeg.Client.State} (hi : Inv s)
    (hx : VersionNeg.Client.Inv x) : Inv (syncConfirmed { s with vnClient := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hx, hi.dsz, ⟨rfl, rfl⟩, hi.role, hi.spaces, hi.paths⟩

theorem inv_setDsz {s : State} {x : DatagramSize.State} (hi : Inv s)
    (hx : DatagramSize.Inv x) (hr : x.role = s.dsz.role) :
    Inv (syncConfirmed { s with dsz := x }) :=
  ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv, hi.mig,
   hi.term, hi.vnS, hi.vnC, hx, ⟨rfl, rfl⟩,
   ⟨hi.role.1, hi.role.2.1, hi.role.2.2.1, hi.role.2.2.2.1, hi.role.2.2.2.2.1,
    hr.trans hi.role.2.2.2.2.2⟩,
   hi.spaces, hi.paths⟩

/-! ### The path registry -/

/-- Adding a key with a fresh value keeps the bound and the injectivity. -/
theorem invPaths_insert {ids : Map Migration.Path Nat} {n : Nat} {p : Migration.Path}
    (hb : ∀ q i, ids.get? q = some i → i < n)
    (hinj : ∀ q r i, ids.get? q = some i → ids.get? r = some i → q = r) :
    (∀ q i, (ids.set p n).get? q = some i → i < n + 1) ∧
      (∀ q r i, (ids.set p n).get? q = some i → (ids.set p n).get? r = some i → q = r) := by
  constructor
  · intro q i hq
    by_cases hqp : q = p
    · subst hqp
      rw [Map.get?_set_self] at hq
      simp only [Option.some.injEq] at hq
      omega
    · rw [Map.get?_set_of_ne _ _ hqp] at hq
      have := hb q i hq
      omega
  · intro q r i hq hr
    by_cases hqp : q = p
    · subst hqp
      rw [Map.get?_set_self] at hq
      simp only [Option.some.injEq] at hq
      by_cases hrp : r = q
      · exact hrp.symm
      · rw [Map.get?_set_of_ne _ _ hrp] at hr
        have := hb r i hr
        omega
    · rw [Map.get?_set_of_ne _ _ hqp] at hq
      by_cases hrp : r = p
      · subst hrp
        rw [Map.get?_set_self] at hr
        simp only [Option.some.injEq] at hr
        have := hb q i hq
        omega
      · rw [Map.get?_set_of_ne _ _ hrp] at hr
        exact hinj q r i hq hr

theorem inv_register {s : State} (hi : Inv s) (p : Migration.Path) :
    Inv (s.register p) := by
  obtain ⟨hb, hinj⟩ := hi.paths
  unfold State.register
  split
  · exact hi
  · exact ⟨hi.hs, hi.st, hi.fr, hi.ackI, hi.ackH, hi.ackA, hi.cidL, hi.cidR, hi.av, hi.pv,
      hi.mig, hi.term, hi.vnS, hi.vnC, hi.dsz, hi.confirmed, hi.role, hi.spaces,
      invPaths_insert hb hinj⟩

end Quic.Spec.Endpoint
