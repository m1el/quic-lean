import QuicModel.Spec.TransportParams.Order
import QuicModel.Spec.TransportParams.Validity

/-
  WP1 — Transport parameters (§7.4, §7.4.1, §7.4.2, §18).

  The component: one endpoint receiving its peer's encoded transport parameters
  out of the TLS handshake, deciding whether to accept them or to close the
  connection with TRANSPORT_PARAMETER_ERROR.

  Supporting files, in the order they are used:
    * `TransportParams/Wire.lean`     §18 identifiers, record, defaults, codec
    * `TransportParams/Validity.lean` §7.4 / §18.2 value rules, §7.4.1 0-RTT
    * `TransportParams/Order.lean`    interpretation is order independent

  File order follows `Spec/Template.lean`.
-/
namespace Quic.Spec.TransportParams

/-! ## 1. State, events, effects -/

structure State where
  /-- Our own role.  The parameters we receive are our peer's. -/
  role : Role
  /-- The peer's parameters, once they have been received and validated.
      §7.4: "Once the handshake completes, the transport parameters declared by
      the peer are available." -/
  peer : Option TransportParams
  deriving DecidableEq

/-- The role of the endpoint whose parameters we are checking. -/
def State.sender (s : State) : Role := s.role.peer

inductive Event where
  /-- The TLS stack hands over the peer's `quic_transport_parameters`
      extension.  §18: "QUIC encodes transport parameters into a sequence of
      bytes, which is then included in the cryptographic handshake." -/
  | recvParams (encoded : ByteArray)
  deriving DecidableEq

inductive Effect where
  /-- The peer's parameters now govern the connection. -/
  | paramsApplied (tp : TransportParams)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ### Decoding and checking one extension

Three steps, each of which the text makes a separate rule: decode the sequence
(§18), ignore unknown identifiers and interpret the rest (§7.4.2, §18.2), then
check the values against the sender's role (§7.4, §18.2, §4.6). -/

/-- Check an interpreted record against §7.4 / §18.2.  `none` is
    "TRANSPORT_PARAMETER_ERROR". -/
def checkValid (sender : Role) : Option TransportParams → Option TransportParams
  | some tp => if validB sender tp then some tp else none
  | none => none

/-- Interpret and check, taking the **last** copy of a repeated parameter. -/
def validate (sender : Role) (raw : Raw) : Option TransportParams :=
  checkValid sender (interpret raw)

/-- Interpret and check, taking the **first** copy of a repeated parameter
    (§7.4, line 2540 leaves the choice open — NOTES 2).  Equal to `validate`
    unless a known parameter repeats. -/
def validateFirst (sender : Role) (raw : Raw) : Option TransportParams :=
  checkValid sender (interpretFirst raw)

/-- §7.4, line 2539: "An endpoint MUST NOT send a parameter more than once in a
    given transport parameters extension."  Only known parameters are counted:
    an unknown identifier is dropped before anything looks at it (§7.4.2), so
    "the parameter" it would duplicate does not exist for this endpoint. -/
def duplicated (raw : Raw) : Bool := !decide (knownIds raw).Nodup

theorem checkValid_valid {sender : Role} {o : Option TransportParams} {tp : TransportParams}
    (h : checkValid sender o = some tp) : Valid sender tp := by
  simp only [checkValid] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (validB_iff _ _).mp ‹_›
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem validate_valid {sender : Role} {raw : Raw} {tp : TransportParams}
    (h : validate sender raw = some tp) : Valid sender tp := checkValid_valid h

theorem validateFirst_valid {sender : Role} {raw : Raw} {tp : TransportParams}
    (h : validateFirst sender raw = some tp) : Valid sender tp := checkValid_valid h

/-- With no repeated known parameter the two readings coincide, so the extra
    outcome added below appears only where §7.4 is silent. -/
theorem validateFirst_eq_validate {sender : Role} {raw : Raw}
    (hnd : duplicated raw = false) : validateFirst sender raw = validate sender raw := by
  have h : (knownIds raw).Nodup := by
    simpa [duplicated] using hnd
  simp only [validateFirst, validate, interpretFirst_eq_interpret h]

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §18, Figures 20 and 21: the extension is a sequence of
      (identifier, length, value) tuples.  Bytes that are not such a sequence —
      a truncated tuple, or a Length that runs past the end — carry no valid
      parameter, so §7.4, line 2535 applies: "An endpoint MUST treat receipt of
      a transport parameter with an invalid value as a connection error of type
      TRANSPORT_PARAMETER_ERROR." -/
  | malformed {s b err} (h : decodeRaw b = .error err) :
      Step s (.recvParams b) (.error .transportParameterError)
  /-- §7.4, line 2535: same sentence, for a sequence that decodes but whose
      values break one of the rules collected in `Valid` — §18.2's ranges and
      role restrictions and §4.6's 2^60 stream limit. -/
  | invalid {s b raw} (h : decodeRaw b = .ok raw) (hv : validate s.sender raw = none) :
      Step s (.recvParams b) (.error .transportParameterError)
  /-- §7.4, line 2540: "An endpoint SHOULD treat receipt of duplicate transport
      parameters as a connection error of type TRANSPORT_PARAMETER_ERROR."
      A SHOULD, so this is an alternative to `accept`/`acceptFirst` for the same
      input and not a replacement for them.  It is the *recommended* one
      (`Recommended`, `step_recommended`). -/
  | duplicate {s b raw tp} (h : decodeRaw b = .ok raw)
      (hv : validate s.sender raw = some tp) (hd : duplicated raw = true) :
      Step s (.recvParams b) (.error .transportParameterError)
  /-- §7.4, line 2528: "Once the handshake completes, the transport parameters
      declared by the peer are available.  Each endpoint validates the values
      provided by its peer."

      With a repeated parameter this is the *last copy wins* reading; §7.4 does
      not say which copy applies (NOTES 2). -/
  | accept {s b raw tp} (h : decodeRaw b = .ok raw) (hv : validate s.sender raw = some tp) :
      Step s (.recvParams b) (.ok { s with peer := some tp } [.paramsApplied tp])
  /-- Same sentence, the *first copy wins* reading of a repeated parameter —
      what an "insert if absent" decoder produces.  §7.4, line 2540 is a SHOULD,
      so an endpoint that does not treat the duplicate as an error must pick a
      copy, and the text names neither; both choices are therefore permitted
      (NOTES 2).  Offered only when the last-copy reading is itself acceptable,
      so that no record the strict reading rejects gets in through this door. -/
  | acceptFirst {s b raw tp tp₁} (h : decodeRaw b = .ok raw)
      (hv : validate s.sender raw = some tp) (hd : duplicated raw = true)
      (hv₁ : validateFirst s.sender raw = some tp₁) :
      Step s (.recvParams b) (.ok { s with peer := some tp₁ } [.paramsApplied tp₁])

/-! ## 3. Executable form -/

/-- Preferred first: the error §7.4 line 2540 recommends, then the last-copy
    record, then the first-copy record (which is the same record, and so a
    harmless repeat in the list, unless the parameter really repeats). -/
def outcomes (s : State) : Event → List Out
  | .recvParams b =>
    match decodeRaw b with
    | .error _ => [.error .transportParameterError]
    | .ok raw =>
      match validate s.sender raw with
      | none => [.error .transportParameterError]
      | some tp =>
        if duplicated raw then
          match validateFirst s.sender raw with
          | none =>
            [.error .transportParameterError, .ok { s with peer := some tp } [.paramsApplied tp]]
          | some tp₁ =>
            [.error .transportParameterError, .ok { s with peer := some tp } [.paramsApplied tp],
              .ok { s with peer := some tp₁ } [.paramsApplied tp₁]]
        else [.ok { s with peer := some tp } [.paramsApplied tp]]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvParams b =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .malformed ‹_›
      · split at h
        · simp only [List.mem_singleton] at h; subst h; exact .invalid ‹_› ‹_›
        · split at h
          · split at h
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h <;> subst h
              · exact .duplicate ‹_› ‹_› ‹_›
              · exact .accept ‹_› ‹_›
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h | h <;> subst h
              · exact .duplicate ‹_› ‹_› ‹_›
              · exact .accept ‹_› ‹_›
              · exact .acceptFirst ‹_› ‹_› ‹_› ‹_›
          · simp only [List.mem_singleton] at h; subst h; exact .accept ‹_› ‹_›
  · intro h
    cases h with
    | malformed hd => simp [outcomes, hd]
    | invalid hd hv => simp [outcomes, hd, hv]
    | duplicate hd hv hdup =>
      simp only [outcomes, hd, hv, hdup, ↓reduceIte]
      split <;> simp
    | accept hd hv =>
      simp only [outcomes, hd, hv]
      split
      · split <;> simp
      · simp
    | acceptFirst hd hv hdup hv₁ =>
      simp [outcomes, hd, hv, hdup, hv₁]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- Whatever we have accepted from the peer satisfies §7.4 and §18.2. -/
def Inv (s : State) : Prop := ∀ tp, s.peer = some tp → Valid s.sender tp

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (_hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | accept hd hv =>
    intro tp' htp
    simp only [State.sender] at hv ⊢
    simp only [Option.some.injEq] at htp
    subst htp
    exact validate_valid hv
  | acceptFirst hd hv hdup hv₁ =>
    intro tp' htp
    simp only [State.sender] at hv₁ ⊢
    simp only [Option.some.injEq] at htp
    subst htp
    exact validateFirst_valid hv₁

/-! ## 6. Send side

Transport parameters travel in the TLS handshake, not in frames (§7.4: "QUIC
includes the encoded transport parameters in the cryptographic handshake"), so
this component governs no frame at all and `MaySend` is `True` everywhere.  The
parameters do constrain what may be sent — flow control limits, stream limits,
`disable_active_migration`, `max_udp_payload_size` — but those constraints are
the business of the components that own those frames (WP2, WP3, WP9, WP10);
here the fields are only exposed. -/

def MaySend (_ : State) (_ : Frame) : Prop := True

def maySend (_ : State) (_ : Frame) : Bool := true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-! ### Recommended (the SHOULDs of the range)

Three sentences in the assigned range use SHOULD: §7.4 line 2540 (duplicates),
§7.4.1 line 2638 (0-RTT limits non-zero) and §18.2 line 7040 (max_ack_delay
covers alarm slack).  The first picks between outcomes this component models
and is `Recommended` below; the other two constrain the parameters an endpoint
*sends*, and are `RecommendedParams`.  All three are advice: nothing in `Step`
or `MaySend` is conditioned on them. -/

/-- The two SHOULDs about the parameters an endpoint puts in its own extension.

    `zeroRtt` says the endpoint means the peer to be able to use 0-RTT with
    these values; `plannedAckDelay` is the acknowledgement delay it actually
    intends to apply and `alarmSlack` how late its alarms fire.  The last two
    are properties of the implementation's clock, not of the connection, so
    they are arguments rather than state (NOTES 12). -/
def RecommendedParams (zeroRtt : Bool) (plannedAckDelay alarmSlack : Nat)
    (tp : TransportParams) : Prop :=
  -- §7.4.1, line 2638: "The applicable subset of transport parameters that
  -- permit sending of application data SHOULD be set to non-zero values for
  -- 0-RTT.  This includes initial_max_data and either initial_max_streams_bidi
  -- and initial_max_stream_data_bidi_remote, or initial_max_streams_uni and
  -- initial_max_stream_data_uni."
  (zeroRtt = true →
      0 < tp.initialMaxData ∧
      ((0 < tp.initialMaxStreamsBidi ∧ 0 < tp.initialMaxStreamDataBidiRemote) ∨
       (0 < tp.initialMaxStreamsUni ∧ 0 < tp.initialMaxStreamDataUni))) ∧
  -- §18.2, line 7040: "This value SHOULD include the receiver's expected delays
  -- in alarms firing.  For example, if a receiver sets a timer for 5ms and
  -- alarms commonly fire up to 1ms late, then it should send a max_ack_delay of
  -- 6ms."
  plannedAckDelay + alarmSlack ≤ tp.maxAckDelay

def recommendedParams (zeroRtt : Bool) (plannedAckDelay alarmSlack : Nat)
    (tp : TransportParams) : Bool :=
  (!zeroRtt ||
    (decide (0 < tp.initialMaxData) &&
      ((decide (0 < tp.initialMaxStreamsBidi) &&
          decide (0 < tp.initialMaxStreamDataBidiRemote)) ||
       (decide (0 < tp.initialMaxStreamsUni) &&
          decide (0 < tp.initialMaxStreamDataUni))))) &&
  decide (plannedAckDelay + alarmSlack ≤ tp.maxAckDelay)

theorem recommendedParams_iff (zeroRtt : Bool) (plannedAckDelay alarmSlack : Nat)
    (tp : TransportParams) :
    recommendedParams zeroRtt plannedAckDelay alarmSlack tp = true ↔
      RecommendedParams zeroRtt plannedAckDelay alarmSlack tp := by
  cases zeroRtt <;> simp [recommendedParams, RecommendedParams, and_assoc]

instance (zeroRtt : Bool) (plannedAckDelay alarmSlack : Nat) (tp : TransportParams) :
    Decidable (RecommendedParams zeroRtt plannedAckDelay alarmSlack tp) :=
  decidable_of_iff _ (recommendedParams_iff zeroRtt plannedAckDelay alarmSlack tp)

/-- §7.4, line 2540: "An endpoint SHOULD treat receipt of duplicate transport
    parameters as a connection error of type TRANSPORT_PARAMETER_ERROR."

    The only SHOULD in range that picks among the outcomes of `Step`: when a
    known parameter repeats, the recommended outcome is the error.  Advice only
    — `Step.accept` and `Step.acceptFirst` remain permitted; `step_recommended`
    shows the reference implementation takes the advice. -/
def Recommended (_s : State) (e : Event) (o : Out) : Prop :=
  match e with
  | .recvParams b =>
    match decodeRaw b with
    | .ok raw => duplicated raw = true → o = .error .transportParameterError
    | .error _ => True

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

/-! ## 8. Named theorems

`step` is the head of `outcomes`, so these two bridges do all the unfolding. -/

theorem head?_outcomes (s : State) (e : Event) :
    (outcomes s e).head? = some (component.step s e) :=
  List.head?_eq_some_head (outcomes_ne s e)

theorem step_eq_of_outcomes {s : State} {e : Event} {a : Out} {t : List Out}
    (h : outcomes s e = a :: t) : component.step s e = a := by
  have h1 := head?_outcomes s e
  rw [h, List.head?_cons] at h1
  exact (Option.some.inj h1).symm

theorem step_congr {s : State} {e₁ e₂ : Event} (h : outcomes s e₁ = outcomes s e₂) :
    component.step s e₁ = component.step s e₂ :=
  Option.some.inj (by rw [← head?_outcomes, ← head?_outcomes, h])

/-- Once duplicates are present the preferred outcome is the error, whatever
    the parameters say — this is what makes the reference implementation
    order independent, and what `step_recommended` needs. -/
theorem step_of_duplicated {s : State} {b : ByteArray} {raw : Raw}
    (hd : decodeRaw b = .ok raw) (hdup : duplicated raw = true) :
    component.step s (.recvParams b) = .error .transportParameterError := by
  cases hv : validate s.sender raw with
  | none =>
    have ho : outcomes s (.recvParams b) = [.error .transportParameterError] := by
      simp only [outcomes, hd, hv]
    exact step_eq_of_outcomes ho
  | some tp =>
    cases hv₁ : validateFirst s.sender raw with
    | none =>
      have ho : outcomes s (.recvParams b) =
          [.error .transportParameterError,
            .ok { s with peer := some tp } [.paramsApplied tp]] := by
        simp only [outcomes, hd, hv, hdup, ↓reduceIte, hv₁]
      exact step_eq_of_outcomes ho
    | some tp₁ =>
      have ho : outcomes s (.recvParams b) =
          [.error .transportParameterError,
            .ok { s with peer := some tp } [.paramsApplied tp],
            .ok { s with peer := some tp₁ } [.paramsApplied tp₁]] := by
        simp only [outcomes, hd, hv, hdup, ↓reduceIte, hv₁]
      exact step_eq_of_outcomes ho

/-- The reference implementation takes the advice of §7.4, line 2540. -/
theorem step_recommended (s : State) (e : Event) : Recommended s e (component.step s e) := by
  cases e with
  | recvParams b =>
    simp only [Recommended]
    split
    · next raw hraw => exact fun hdup => step_of_duplicated hraw hdup
    · trivial

/-- **(b)** Anything accepted satisfies the validity predicate, and the
    application is told exactly what was accepted. -/
theorem step_ok_valid {s : State} {e : Event} {s' : State} {fx : List Effect}
    (h : Step s e (.ok s' fx)) :
    ∃ tp, s'.peer = some tp ∧ Valid s.sender tp ∧ fx = [.paramsApplied tp] := by
  cases h with
  | accept hd hv => exact ⟨_, rfl, validate_valid hv, rfl⟩
  | acceptFirst hd hv hdup hv₁ => exact ⟨_, rfl, validateFirst_valid hv₁, rfl⟩

/-- Accepting never changes our own role, so `Inv` is about a fixed sender. -/
theorem step_role {s : State} {e : Event} {s' : State} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s'.role = s.role := by
  cases h with
  | accept _ _ => rfl
  | acceptFirst _ _ _ _ => rfl

theorem duplicated_toRaw (tp : TransportParams) : duplicated (toRaw tp) = false := by
  simp only [duplicated, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
  simpa [knownIds, toRaw] using nodup_toEntries tp

theorem outcomes_encodeParams (role : Role) (tp : TransportParams) (hwf : tp.WF)
    (hv : Valid role.peer tp) (peer₀ : Option TransportParams) :
    outcomes ⟨role, peer₀⟩ (.recvParams (encodeParams tp))
      = [.ok ⟨role, some tp⟩ [.paramsApplied tp]] := by
  have hdec : decodeRaw (encodeParams tp) = .ok (toRaw tp) :=
    decodeRaw_encodeRaw _ (rawWF_toRaw tp hwf)
  have hval : validate role.peer (toRaw tp) = some tp := by
    simp only [validate, checkValid, interpret_toRaw tp hwf, (validB_iff _ _).mpr hv,
      ↓reduceIte]
  simp only [outcomes, State.sender, hdec, hval, duplicated_toRaw tp, Bool.false_eq_true,
    ↓reduceIte]

/-- **(a)** Round trip, at the level of the component: a representable, valid
    parameter record is encoded, decoded and accepted unchanged. -/
theorem step_encodeParams (role : Role) (tp : TransportParams) (hwf : tp.WF)
    (hv : Valid role.peer tp) (peer₀ : Option TransportParams) :
    component.step ⟨role, peer₀⟩ (.recvParams (encodeParams tp))
      = .ok ⟨role, some tp⟩ [.paramsApplied tp] :=
  step_eq_of_outcomes (outcomes_encodeParams role tp hwf hv peer₀)

theorem duplicated_perm {l₁ l₂ : Raw} (h : l₁.Perm l₂) : duplicated l₁ = duplicated l₂ := by
  have : (knownIds l₁).Perm (knownIds l₂) := (knownEntries_perm h).map Prod.fst
  simp only [duplicated, this.nodup_iff]

/-- With no repeated known parameter, the *whole* list of permitted outcomes is
    order independent — not just the preferred one.  (With a repeat it is not:
    the last-copy and first-copy records swap places, which is exactly the
    ambiguity of NOTES 2.) -/
theorem outcomes_perm (s : State) {raw₁ raw₂ : Raw} (hp : raw₁.Perm raw₂)
    (hwf : RawWF raw₁) (hnd : (knownIds raw₁).Nodup) :
    outcomes s (.recvParams (encodeRaw raw₁)) = outcomes s (.recvParams (encodeRaw raw₂)) := by
  have hwf₂ : RawWF raw₂ := fun e he => hwf e (hp.mem_iff.mpr he)
  have h₁ : decodeRaw (encodeRaw raw₁) = .ok raw₁ := decodeRaw_encodeRaw _ hwf
  have h₂ : decodeRaw (encodeRaw raw₂) = .ok raw₂ := decodeRaw_encodeRaw _ hwf₂
  have hdup₁ : duplicated raw₁ = false := by simp [duplicated, hnd]
  have hdup₂ : duplicated raw₂ = false := by rw [← duplicated_perm hp]; exact hdup₁
  have hint : interpret raw₁ = interpret raw₂ := interpret_perm hp hnd
  simp only [outcomes, h₁, h₂, validate, hint, hdup₁, hdup₂, Bool.false_eq_true,
    ↓reduceIte]

/-- **(c)** Validation does not depend on the order the parameters appear in:
    the reference implementation's outcome is the same for any permutation.
    Unchanged by the first-copy alternative of `Step.acceptFirst`, because with
    a repeated identifier the *preferred* outcome is the error either way
    (`step_of_duplicated`), and with no repeat the two readings coincide
    (`interpretFirst_eq_interpret`), so the whole outcome list agrees
    (`outcomes_perm`).

    The accepted *record* is still order dependent when a parameter repeats:
    both the last-copy and the first-copy record are permitted, and a
    permutation exchanges them — see the counterexample in section 9. -/
theorem step_perm (s : State) {raw₁ raw₂ : Raw} (hp : raw₁.Perm raw₂) (hwf : RawWF raw₁) :
    component.step s (.recvParams (encodeRaw raw₁))
      = component.step s (.recvParams (encodeRaw raw₂)) := by
  by_cases hnd : (knownIds raw₁).Nodup
  · exact step_congr (outcomes_perm s hp hwf hnd)
  · have hwf₂ : RawWF raw₂ := fun e he => hwf e (hp.mem_iff.mpr he)
    have h₁ : decodeRaw (encodeRaw raw₁) = .ok raw₁ := decodeRaw_encodeRaw _ hwf
    have h₂ : decodeRaw (encodeRaw raw₂) = .ok raw₂ := decodeRaw_encodeRaw _ hwf₂
    have hdup₁ : duplicated raw₁ = true := by simp [duplicated, hnd]
    have hdup₂ : duplicated raw₂ = true := by rw [← duplicated_perm hp]; exact hdup₁
    rw [step_of_duplicated h₁ hdup₁, step_of_duplicated h₂ hdup₂]

/-! ## 9. Examples (scenarios from the text) -/

/-- A short-hand for an encoded extension. -/
private def ext (l : List (Nat × List UInt8)) : ByteArray :=
  encodeRaw (l.map fun e => (e.1, bytes e.2))

private def cli : State := ⟨.client, none⟩   -- we are the client; the sender is the server
private def srv : State := ⟨.server, none⟩   -- we are the server; the sender is the client

-- §18.2: "Transport parameters have a default value of 0 if the transport
-- parameter is absent unless otherwise stated."  An empty extension is the
-- defaults.
example : component.step srv (.recvParams (ext [])) = .ok ⟨.server, some defaults⟩
    [.paramsApplied defaults] := by decide

-- §18.1: identifier 27 = 31*0 + 27 is reserved "to exercise the requirement
-- that unknown transport parameters be ignored"; 58 = 31*1 + 27 likewise.
example : component.step srv (.recvParams (ext [(27, [0xde, 0xad]), (58, [])]))
    = .ok ⟨.server, some defaults⟩ [.paramsApplied defaults] := by decide

-- §18.2: "The value of the active_connection_id_limit parameter MUST be at
-- least 2.  An endpoint that receives a value less than 2 MUST close the
-- connection with an error of type TRANSPORT_PARAMETER_ERROR."
example : component.step cli (.recvParams (ext [(0x0e, [0x01])]))
    = .error .transportParameterError := by decide
example : component.step cli (.recvParams (ext [(0x0e, [0x04])]))
    = .ok ⟨.client, some { defaults with activeConnectionIdLimit := 4 }⟩
        [.paramsApplied { defaults with activeConnectionIdLimit := 4 }] := by decide

-- §18.2: "A client MUST NOT include any server-only transport parameter …
-- A server MUST treat receipt of any of these transport parameters as a
-- connection error of type TRANSPORT_PARAMETER_ERROR."  The same bytes are
-- fine coming from a server.
example : component.step srv (.recvParams (ext [(0x00, [0xc1])]))
    = .error .transportParameterError := by decide
example : component.step cli (.recvParams (ext [(0x00, [0xc1])]))
    = .ok ⟨.client, some { defaults with originalDestinationConnectionId := some (bytes [0xc1]) }⟩
        [.paramsApplied { defaults with originalDestinationConnectionId := some (bytes [0xc1]) }] := by
  decide

-- §18.2: "Values above 20 are invalid" (ack_delay_exponent).
example : component.step cli (.recvParams (ext [(0x0a, [20])])) ≠ .error .transportParameterError := by
  decide
example : component.step cli (.recvParams (ext [(0x0a, [21])])) = .error .transportParameterError := by
  decide

-- §18.2: "Values of 2^14 or greater are invalid" (max_ack_delay); 0x7f 0xff is
-- the two-byte varint for 2^14 - 1 and 0x80 0x00 0x40 0x00 is 2^14.
example : component.step cli (.recvParams (ext [(0x0b, [0x7f, 0xff])]))
    ≠ .error .transportParameterError := by decide
example : component.step cli (.recvParams (ext [(0x0b, [0x80, 0x00, 0x40, 0x00])]))
    = .error .transportParameterError := by decide

-- §18.2: "Values below 1200 are invalid" (max_udp_payload_size).
example : component.step cli (.recvParams (ext [(0x03, [0x44, 0xaf])]))
    = .error .transportParameterError := by decide      -- 1199
example : component.step cli (.recvParams (ext [(0x03, [0x44, 0xb0])]))
    ≠ .error .transportParameterError := by decide      -- 1200

-- §18: a Length that runs past the end of the extension.
example : component.step cli (.recvParams ⟨#[0x01, 0x08, 0x00]⟩)
    = .error .transportParameterError := by decide

-- §18.2: stateless_reset_token "is a sequence of 16 bytes"; a 15-byte one is
-- an invalid value.
example : component.step cli (.recvParams (ext [(0x02, List.replicate 15 0)]))
    = .error .transportParameterError := by decide

-- §18.2: active_connection_id_limit below 2 has no accepting outcome, even for
-- an endpoint that issues zero-length connection IDs (§18.2, line 7125 is
-- unconditional; NOTES 10).
example : component.outcomes cli (.recvParams (ext [(0x0e, [0x01])]))
    = [.error .transportParameterError] := by decide

-- §7.4, line 2540: duplicates.  The SHOULD is the preferred outcome …
example : component.step cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    = .error .transportParameterError := by decide
-- … which is what `step_recommended` says in general.
example : Recommended cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (component.step cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))) :=
  step_recommended _ _
-- Ignoring the SHOULD, the last copy may win …
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 20 }⟩
      [.paramsApplied { defaults with initialMaxData := 20 }]) = true := by decide
-- … and so may the first (W1-1: the text names neither).
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 10 }⟩
      [.paramsApplied { defaults with initialMaxData := 10 }]) = true := by decide
-- Exactly those three, error first — a copy that is in neither position is not
-- permitted.
example : component.outcomes cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    = [.error .transportParameterError,
       .ok ⟨.client, some { defaults with initialMaxData := 20 }⟩
         [.paramsApplied { defaults with initialMaxData := 20 }],
       .ok ⟨.client, some { defaults with initialMaxData := 10 }⟩
         [.paramsApplied { defaults with initialMaxData := 10 }]] := by decide
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 30 }⟩
      [.paramsApplied { defaults with initialMaxData := 30 }]) = false := by decide
-- An implementation whose observations do not fix its state is followed through
-- both readings at once.
example : component.trackSet [cli] (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (fun o => match o with | .ok _ => true | _ => false)
    = [⟨.client, some { defaults with initialMaxData := 20 }⟩,
       ⟨.client, some { defaults with initialMaxData := 10 }⟩] := by decide
-- The first-copy reading never admits a record the last-copy reading rejects:
-- with the first copy below §18.2's minimum only the last-copy record is offered
example : component.outcomes cli (.recvParams (ext [(0x0e, [0x01]), (0x0e, [0x04])]))
    = [.error .transportParameterError,
       .ok ⟨.client, some { defaults with activeConnectionIdLimit := 4 }⟩
         [.paramsApplied { defaults with activeConnectionIdLimit := 4 }]] := by decide
-- … and with the last copy below it, the error is the only outcome.
example : component.outcomes cli (.recvParams (ext [(0x0e, [0x04]), (0x0e, [0x01])]))
    = [.error .transportParameterError] := by decide
-- With no repeat there is one outcome, as before.
private def twoParams : TransportParams :=
  { defaults with initialMaxData := 10, initialMaxStreamDataBidiLocal := 20 }
example : component.outcomes cli (.recvParams (ext [(0x04, [0x0a]), (0x05, [0x14])]))
    = [.ok ⟨.client, some twoParams⟩ [.paramsApplied twoParams]] := by decide
-- A repeated *reserved* identifier is not a duplicate (NOTES 1).
example : component.outcomes srv (.recvParams (ext [(27, [0x01]), (27, [0x02])]))
    = [.ok ⟨.server, some defaults⟩ [.paramsApplied defaults]] := by decide

-- Order independence at the level of the whole outcome list, when nothing
-- repeats (`outcomes_perm`).
example : component.outcomes cli (.recvParams (ext [(0x04, [0x0a]), (0x05, [0x14])]))
    = component.outcomes cli (.recvParams (ext [(0x05, [0x14]), (0x04, [0x0a])])) := by decide
-- With a repeat the two accepting outcomes swap places, so the list is only
-- equal up to permutation — but the preferred outcome (the error) does not move.
example : component.outcomes cli (.recvParams (ext [(0x04, [0x14]), (0x04, [0x0a])]))
    = [.error .transportParameterError,
       .ok ⟨.client, some { defaults with initialMaxData := 10 }⟩
         [.paramsApplied { defaults with initialMaxData := 10 }],
       .ok ⟨.client, some { defaults with initialMaxData := 20 }⟩
         [.paramsApplied { defaults with initialMaxData := 20 }]] := by decide

-- Order independence, and the counterexample that makes duplicates an error:
-- with no repeat, swapping two parameters changes nothing …
example : interpret [(0x04, bytes [0x0a]), (0x05, bytes [0x14])]
        = interpret [(0x05, bytes [0x14]), (0x04, bytes [0x0a])] := by decide
-- … with a repeat, the record that would be accepted depends on the order.
example : interpret [(0x04, bytes [0x0a]), (0x04, bytes [0x14])]
        ≠ interpret [(0x04, bytes [0x14]), (0x04, bytes [0x0a])] := by decide

-- §4.6: "If a max_streams transport parameter … is received with a value
-- greater than 2^60 … the connection MUST be closed immediately with a
-- connection error of type TRANSPORT_PARAMETER_ERROR."
example : component.step cli
    (.recvParams (ext [(0x08, [0xd0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01])]))
    = .error .transportParameterError := by decide

-- Following an implementation we cannot see inside (§7.4 duplicates again).
example : component.track cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.error .transportParameterError) = some cli := rfl

-- §7.4.1: "a server that accepts 0-RTT data MUST NOT set values for the
-- following parameters that are smaller than the remembered value".
example : zeroRttCompatible { defaults with initialMaxData := 100 }
    { defaults with initialMaxData := 50 } = false := by decide
example : zeroRttCompatible { defaults with initialMaxData := 100 }
    { defaults with initialMaxData := 100 } = true := by decide
-- The parameters a client must not carry over are back at their defaults.
example :
    remembered { defaults with maxAckDelay := 7,
                               statelessResetToken := some (bytes []),
                               initialMaxData := 99 }
      = { defaults with initialMaxData := 99 } := by decide
-- §7.4.1 MAY: a server that also remembers max_udp_payload_size rejects a
-- reduction that the plain test allows.
example : zeroRttCompatibleStrict { defaults with maxUdpPayloadSize := 1500 }
    { defaults with maxUdpPayloadSize := 1300 } = false := by decide
example : zeroRttCompatible { defaults with maxUdpPayloadSize := 1500 }
    { defaults with maxUdpPayloadSize := 1300 } = true := by decide

-- §7.3, Figure 8: a handshake with a Retry.  The server reports
-- original_destination_connection_id = S1, retry_source_connection_id = S2 and
-- initial_source_connection_id = S3; a client accepts all three.  (Checking
-- them against the connection IDs actually seen is WP11's job.)
private def figure8 : TransportParams :=
  { defaults with originalDestinationConnectionId := some (bytes [0x51]),
                  initialSourceConnectionId := some (bytes [0x53]),
                  retrySourceConnectionId := some (bytes [0x52]) }

example : interpret [(0x00, bytes [0x51]), (0x0f, bytes [0x53]), (0x10, bytes [0x52])]
    = some figure8 := by decide
example : Valid .server figure8 := by decide
example : ¬ Valid .client figure8 := by decide

-- §7.4: this component governs no frame.
example : component.maySend cli (.maxData 5) = true := by decide

-- §7.4.1, line 2638: the §18.2 defaults leave 0-RTT enabled but unusable …
example : recommendedParams true 5 1 defaults = false := by decide
-- … while a set that permits bidirectional application data takes the advice.
example : recommendedParams true 5 1
    { defaults with initialMaxData := 10000, initialMaxStreamsBidi := 3,
                    initialMaxStreamDataBidiRemote := 4000 } = true := by decide
-- §18.2, line 7042's own example: "if a receiver sets a timer for 5ms and alarms
-- commonly fire up to 1ms late, then it should send a max_ack_delay of 6ms".
example : recommendedParams false 5 1 { defaults with maxAckDelay := 6 } = true := by decide
example : recommendedParams false 5 1 { defaults with maxAckDelay := 5 } = false := by decide
-- Both are advice: a record that ignores them is still `Valid`, so `Step`
-- accepts it.
example : Valid .server { defaults with maxAckDelay := 5 } := by decide
example : component.step cli (.recvParams (ext [(0x0b, [5])]))
    = .ok ⟨.client, some { defaults with maxAckDelay := 5 }⟩
        [.paramsApplied { defaults with maxAckDelay := 5 }] := by decide

/-! ## 10. Coverage and notes

Assigned text: lines 2506–2695 (§7.4, §7.4.1, §7.4.2) and 6875–7154 (§18).

Citations name the line on which the quoted sentence's first word appears, and
every one of them was checked mechanically before the final commit
(`out/check_citations.py`).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §7.4 (2528) | "Once the handshake completes, the transport parameters declared by the peer are available.  Each endpoint validates the values provided by its peer." | `Step.accept` / `Step.acceptFirst` |
| §7.4 (2535) | "An endpoint MUST treat receipt of a transport parameter with an invalid value as a connection error of type TRANSPORT_PARAMETER_ERROR." | `Step.invalid`, `Step.malformed`, `Valid` |
| §7.4 (2539) | "An endpoint MUST NOT send a parameter more than once in a given transport parameters extension." | `duplicated`; a send-side obligation of the peer, so it appears here only as the receive rule below |
| §7.4 (2540) | "An endpoint SHOULD treat receipt of duplicate transport parameters as a connection error of type TRANSPORT_PARAMETER_ERROR." | SHOULD → `Recommended`, `step_recommended`; `Step.duplicate` is the preferred outcome, `Step.accept` (last copy) and `Step.acceptFirst` (first copy) stay permitted — NOTES 2 |
| §7.4 (2544) | "Endpoints use transport parameters to authenticate the negotiation of connection IDs during the handshake" | out of scope: WP11 Handshake; the three CID fields are exposed |
| §7.4 (2547) | "Application Layer Protocol Negotiation (ALPN; see [ALPN]) allows clients to offer multiple application protocols" | not normative for the transport |
| §7.4.1 (2588) | "The definition of a new transport parameter (Section 7.4.2) MUST specify whether storing the transport parameter for 0-RTT is mandatory, optional, or prohibited." | out of scope: a rule about future specifications, not about an endpoint |
| §7.4.1 (2590) | "A client need not store a transport parameter it cannot process." | permissive; `knownEntries` already drops unknown identifiers |
| §7.4.1 (2593) | "A client MUST NOT use remembered values for the following parameters" (seven named) | `remembered`, `remembered_resets` |
| §7.4.1 (2600) | "A client that attempts to send 0-RTT data MUST remember all other transport parameters used by the server that it is able to process." | `remembered` keeps every other field |
| §7.4.1 (2607) | "If 0-RTT data is accepted by the server, the server MUST NOT reduce any limits" (then the seven bullets) | `ZeroRttCompatible` / `zeroRttCompatible` — NOTES 11 |
| §7.4.1 (2638) | "The applicable subset of transport parameters that permit sending of application data SHOULD be set to non-zero values for 0-RTT." | SHOULD → `RecommendedParams`, first clause |
| §7.4.1 (2645) | "A server MAY store and recover the previously sent values of the max_idle_timeout, max_udp_payload_size, and disable_active_migration parameters and reject 0-RTT if it selects smaller values." | `zeroRttCompatibleStrict`, the permitted alternative to `zeroRttCompatible` |
| §7.4.1 (2653) | "A server MUST reject 0-RTT data if the restored values for transport parameters cannot be supported." | out of scope: WP11 owns the accept/reject decision; the test is `zeroRttCompatible` |
| §7.4.1 (2656) | "When sending frames in 0-RTT packets, a client MUST only use remembered transport parameters" | out of scope: WP2/WP9 enforce limits per packet, WP11 owns 0-RTT |
| §7.4.1 (2663) | "A server MAY treat use of updated transport parameters in 0-RTT as a connection error of type PROTOCOL_VIOLATION." | out of scope: WP11; a permission, so no outcome here is lost by omitting it |
| §7.4.2 (2670) | "An endpoint MUST ignore transport parameters that it does not support." | `knownEntries`, `ParamId.ofCode?_reserved` |
| §18 (6895) | "Each transport parameter is encoded as an (identifier, length, value) tuple, as shown in Figure 21" | `paramEntry`, `decodeRaw` / `encodeRaw` |
| §18 (6906) | "The Transport Parameter Length field contains the length of the Transport Parameter Value field in bytes." | `paramEntry` (`P.take len`) |
| §18.1 (6914) | "Transport parameters with an identifier of the form "31 * N + 27" for integer values of N are reserved" | `ParamId.IsReserved`, `ParamId.ofCode?_reserved` |
| §18.2 (6924) | "Those transport parameters that are identified as integers use a variable-length integer encoding" | `varintValue?` |
| §18.2 (6926) | "Transport parameters have a default value of 0 if the transport parameter is absent unless otherwise stated." | the field defaults of `TransportParams` |
| §18.2 (6932) | "original_destination_connection_id (0x00):  The value of the Destination Connection ID field from the first Initial packet sent by the client" | field; §7.3 checking is WP11 |
| §18.2 (6934) | "This transport parameter is only sent by a server." (odcid) | `Valid`, first conjunct |
| §18.2 (6937) | "max_idle_timeout (0x01):  The max idle timeout is a value in milliseconds that is encoded as an integer" | field |
| §18.2 (6939) | "Idle timeout is disabled when both endpoints omit this transport parameter or specify a value of 0." | out of scope: WP6 Termination owns the timer; the field is exposed |
| §18.2 (6950) | "This parameter is a sequence of 16 bytes." (stateless_reset_token) | `setParam` (length 16) |
| §18.2 (6951) | "This transport parameter MUST NOT be sent by a client, but MAY be sent by a server." | `Valid`, first conjunct (the MUST NOT); the MAY is the absence of any further constraint on a server |
| §18.2 (6952) | "A server that does not send this transport parameter cannot use stateless reset (Section 10.3) for the connection ID negotiated during the handshake." | out of scope: WP6 Termination |
| §18.2 (6957) | "max_udp_payload_size (0x03):  The maximum UDP payload size parameter is an integer value that limits the size of UDP payloads that the endpoint is willing to receive." | field |
| §18.2 (6963) | "The default for this parameter is the maximum permitted UDP payload of 65527." | the field default |
| §18.2 (6964) | "Values below 1200 are invalid." | `Valid`, second conjunct |
| §18.2 (6966) | "This limit does act as an additional constraint on datagram size in the same way as the path MTU" | out of scope: WP7 DatagramSize (`RecommendedDatagram`) |
| §18.2 (6972) | "initial_max_data (0x04)" | field; its effect is WP2/WP9 |
| §18.2 (6978) | "initial_max_stream_data_bidi_local (0x05)" | field; WP2/WP9 |
| §18.2 (6988) | "initial_max_stream_data_bidi_remote (0x06)" | field; WP2/WP9 |
| §18.2 (7005) | "initial_max_stream_data_uni (0x07)" | field; WP2/WP9 |
| §18.2 (7014) | "initial_max_streams_bidi (0x08)" | field; WP9, and §4.6's 2^60 bound in `Valid` |
| §18.2 (7023) | "initial_max_streams_uni (0x09)" | field; WP9, and §4.6's 2^60 bound in `Valid` |
| §18.2 (7032) | "ack_delay_exponent (0x0a)" | field; the decoding of ACK Delay is WP3 |
| §18.2 (7034) | "If this value is absent, a default value of 3 is assumed" | the field default |
| §18.2 (7036) | "Values above 20 are invalid." | `Valid`, third conjunct |
| §18.2 (7038) | "max_ack_delay (0x0b)" | field; the ACK timer is WP3 |
| §18.2 (7040) | "This value SHOULD include the receiver's expected delays in alarms firing." | SHOULD → `RecommendedParams`, second clause — NOTES 12 |
| §18.2 (7044) | "If this value is absent, a default of 25 milliseconds is assumed." | the field default |
| §18.2 (7045) | "Values of 2^14 or greater are invalid." | `Valid`, fourth conjunct |
| §18.2 (7047) | "disable_active_migration (0x0c)" | field |
| §18.2 (7050) | "An endpoint that receives this transport parameter MUST NOT use a new local address when sending to the address that the peer used during the handshake." | out of scope: WP10 Migration; the flag is exposed |
| §18.2 (7062) | "This parameter is a zero-length value." | `setParam` (size 0) — NOTES 7 |
| §18.2 (7065) | "preferred_address (0x0d):  The server's preferred address is used to effect a change in server address at the end of the handshake" | out of scope: acting on it is WP10 Migration |
| §18.2 (7067) | "This transport parameter is only sent by a server." (preferred_address) | `Valid`, first conjunct |
| §18.2 (7068) | "Servers MAY choose to only send a preferred address of one address family by sending an all-zero address and port" | permissive; the codec accepts any 4- and 16-byte address |
| §18.2 (7090) | "The Connection ID and Stateless Reset Token fields of a preferred address are identical in syntax and semantics to the corresponding fields of a NEW_CONNECTION_ID frame" | the 1…20 bound in `Valid` — NOTES 4 |
| §18.2 (7092) | "A server that chooses a zero-length connection ID MUST NOT provide a preferred address." | `Valid`, last conjunct — NOTES 5 |
| §18.2 (7094) | "Similarly, a server MUST NOT include a zero-length connection ID in this transport parameter." | `Valid`, second-to-last conjunct |
| §18.2 (7095) | "A client MUST treat violation of these requirements as a connection error of type TRANSPORT_PARAMETER_ERROR." | `Step.invalid` |
| §18.2 (7099) | Figure 22, Preferred Address format | `preferredAddressP` / `encodePreferredAddress` |
| §18.2 (7119) | "active_connection_id_limit (0x0e):  The active connection ID limit is an integer value specifying the maximum number of connection IDs from the peer that an endpoint is willing to store." | field; enforcing the limit is WP4 ConnIds |
| §18.2 (7124) | "The value of the active_connection_id_limit parameter MUST be at least 2." | `Valid`, fifth conjunct |
| §18.2 (7125) | "An endpoint that receives a value less than 2 MUST close the connection with an error of type TRANSPORT_PARAMETER_ERROR." | `Step.invalid` via `Valid` |
| §18.2 (7127) | "If this transport parameter is absent, a default of 2 is assumed." | the field default |
| §18.2 (7128) | "If an endpoint issues a zero-length connection ID, it will never send a NEW_CONNECTION_ID frame and therefore ignores the active_connection_id_limit value received from its peer." | decided here: the MUST of line 7125 is unconditional and wins, so the value is still checked; only the *use* of the limit (never issuing a NEW_CONNECTION_ID) is WP4's — NOTES 10 |
| §18.2 (7133) | "initial_source_connection_id (0x0f)" | field; §7.3 checking is WP11 |
| §18.2 (7137) | "retry_source_connection_id (0x10)" | field; §7.3 checking is WP11 |
| §18.2 (7139) | "This transport parameter is only sent by a server." (retry_source_connection_id) | `Valid`, first conjunct |
| §18.2 (7141) | "If present, transport parameters that set initial per-stream flow control limits … are equivalent to sending a MAX_STREAM_DATA frame" | out of scope: WP2/WP9 |
| §18.2 (7145) | "If the transport parameter is absent, streams of that type start with a flow control limit of 0." | the field defaults |
| §18.2 (7149) | "A client MUST NOT include any server-only transport parameter" | `Valid`, first conjunct |
| §18.2 (7151) | "A server MUST treat receipt of any of these transport parameters as a connection error of type TRANSPORT_PARAMETER_ERROR." | `Step.invalid` via `Valid` |
| §4.6 (1537) | "If a max_streams transport parameter or a MAX_STREAMS frame is received with a value greater than 2^60" → TRANSPORT_PARAMETER_ERROR | `Valid` (cited here because §18.2 defers the limit to §4.6) |

Every SHOULD in the assigned range (there are three: 2540, 2638, 7040) is a
clause of `Recommended` or `RecommendedParams`; none is left as advice-only.

NOTES — ambiguities and the reading encoded

1. **Duplicates of an *unknown* identifier.**  §7.4 says duplicates SHOULD be an
   error; §7.4.2 says unknown parameters MUST be ignored.  Taken together they
   conflict for a repeated unknown identifier — in particular for two entries
   with the same reserved `31*N+27` identifier, which §18.1 says exist precisely
   to be ignored.  Reading encoded: `duplicated` counts only *known*
   identifiers, so ignoring wins.
2. **Which copy of a duplicated parameter applies.**  §7.4, line 2540 is a
   SHOULD, so an endpoint may accept an extension with a repeated parameter;
   the text then says nothing about which copy takes effect.  Reading encoded:
   *both* obvious decoders conform.  `interpret` folds left to right (the last
   copy wins) and `interpretFirst` skips an identifier it has already applied
   (the first copy wins, which is what an "insert if absent" decoder produces);
   `outcomes` offers the error first, then the last-copy record, then the
   first-copy record, and `Step` has `accept` and `acceptFirst` for the latter
   two.  Three consequences worth knowing:
   * **Only first and last are enumerated.**  For k copies of one parameter a
     decoder could in principle keep any one of them, and for several repeated
     parameters it could choose independently per parameter — 2^n… combinations
     that no real decoder produces and that would make `outcomes` unbounded.
     First and last are the two folds an implementation actually writes, so
     those are the two enumerated.  An implementation that keeps a middle copy
     is not accepted by `accepts`; that is a deliberate, recorded incompleteness
     rather than an oversight.
   * **A later copy is still parsed.**  §7.4, line 2535 makes *receipt* of a
     parameter with an invalid value an error, so `applyEntriesFirst` still runs
     the value parser over a copy it does not apply; only the field update is
     suppressed.
   * **The first-copy reading never widens what is accepted.**  `acceptFirst`
     carries `validate … = some tp` as well, so the alternative is offered only
     where the last-copy record is itself valid.  With
     `[(0x0e, 1), (0x0e, 4)]` the first copy is below §18.2's minimum and only
     the last-copy record is offered; with the copies the other way round the
     error is the only outcome.
   `interpretFirst_eq_interpret` shows the two readings coincide whenever no
   known parameter repeats, so nothing outside §7.4's silence is affected, and
   the *preferred* outcome (`step`) is the error in every duplicate case
   (`step_of_duplicated`), which is what keeps `step_perm` true.
3. **Non-minimal varints inside a parameter value.**  §16 says "Values do not
   need to be encoded on the minimum number of bytes necessary, with the sole
   exception of the Frame Type field", so an 8-byte encoding of 0 in a
   `max_idle_timeout` is accepted.  What is *not* accepted is a value field that
   is longer or shorter than the varint inside it: `varintValue?` insists the
   varint fills the field exactly.  The text does not spell this out; the
   reading is that a trailing byte makes the value invalid.
4. **Connection ID lengths in the three CID parameters.**  §18.2 puts no length
   bound on original_destination_connection_id, initial_source_connection_id or
   retry_source_connection_id, and §7.3 explicitly allows a zero-length value.
   Reading encoded: no bound is imposed here.  (§17.2's 20-byte limit applies to
   long headers; whether these values match the headers seen is WP11's check.)
   The Connection ID *inside* preferred_address is different: §18.2, line 7090
   says it is "identical in syntax and semantics to the corresponding fields of
   a NEW_CONNECTION_ID frame", so 1…20 is enforced.
5. **"A server that chooses a zero-length connection ID MUST NOT provide a
   preferred address"** (§18.2, line 7092).  Decided from the parameters alone
   by reading "the connection ID the server chose" as its
   initial_source_connection_id (§7.3: "The value that the endpoint included in
   the Source Connection ID field of the first Initial packet it sends").  If
   that parameter is absent the rule is vacuous here; its absence is itself an
   error, but that is WP11's rule.
6. **Error code for a malformed sequence.**  §18 gives no code for bytes that
   are not a well-formed (ID, Length, Value) sequence.  Reading encoded:
   TRANSPORT_PARAMETER_ERROR, by §7.4's "invalid value" sentence (line 2535).
   ngtcp2 also reports TRANSPORT_PARAMETER_ERROR here.
7. **`disable_active_migration` with a non-empty value.**  §18.2, line 7062:
   "This parameter is a zero-length value."  Reading encoded: a non-empty value
   is an invalid value, hence TRANSPORT_PARAMETER_ERROR, rather than being
   ignored.
8. **Receiving a second set of parameters.**  The model simply replaces `peer`.
   Whether that can happen at all is a TLS question (WP11).
9. **`zeroRttCompatibleStrict` and `disable_active_migration`.**  §7.4.1 speaks
   of "smaller values" for a parameter that is a flag.  Reading encoded: turning
   the flag on when it was previously off counts as a reduction.
10. **`active_connection_id_limit` below 2 and zero-length connection IDs.**
    §18.2, lines 7124–7131 say three things in a row: the value MUST be at least
    2; an endpoint that receives less than 2 MUST close the connection; and "if
    an endpoint issues a zero-length connection ID, it will never send a
    NEW_CONNECTION_ID frame and therefore ignores the
    active_connection_id_limit value received from its peer."  Reading encoded:
    the closing MUST at line 7125 is unconditional and wins, so `Valid` rejects
    a value below 2 for every endpoint.  The last sentence is about what the
    limit is *used for* — issuing connection IDs, which a zero-length-CID
    endpoint never does — and is a statement of fact, not an exemption from a
    MUST expressed as a receipt check; "ignores the value" is also weaker than
    "need not validate it".  The consequence is deliberate and visible: for
    `active_connection_id_limit = 1` the only permitted outcome is the error,
    for a zero-length-CID endpoint too.  The decision is taken *here*, not in
    WP4: WP4 owns the use of the limit once it has been accepted.
11. **The breadth of §7.4.1's 0-RTT clause.**  Line 2607 reads "the server MUST
    NOT reduce any limits **or alter any values that might be violated by the
    client with its 0-RTT data**", and then "**In particular**, …" with a
    seven-item list.  The leading clause is broader than the list.  Reading
    encoded: the list exhausts it — `ZeroRttCompatible` has exactly the seven
    bullets of lines 2613–2625.  A value that is not one of the seven and that
    0-RTT data could violate would have to be named to be checkable, and the
    only candidates the text itself offers are the three of line 2645, which
    `zeroRttCompatibleStrict` covers as the permitted stricter test.
12. **The two SHOULDs about what an endpoint sends.**  §7.4.1 line 2638 and
    §18.2 line 7040 both constrain the parameter record an endpoint puts in its
    own extension, not what it does with the record it receives, so they are
    `RecommendedParams` rather than clauses of `Recommended`.  Line 7040 ("this
    value SHOULD include the receiver's expected delays in alarms firing") is
    only checkable against two quantities the connection state does not carry —
    the acknowledgement delay the endpoint intends to apply and how late its
    alarms fire — so they are arguments of the predicate; the text's own example
    (a 5 ms timer, 1 ms of slack, max_ack_delay 6 ms) is one of the examples in
    section 9.  Line 2638 is read as binding only an endpoint that means the
    peer to be able to use 0-RTT, which is the `zeroRtt` argument.
13. **Citation convention.**  A cited line is the line on which the quoted
    sentence's *first word* appears, even when that word is the last on the
    line: §18.2 line 7092 ends "… (Section 19.15).  A server", so the
    zero-length-CID rule is cited at 7092 rather than 7093.
-/

end Quic.Spec.TransportParams
