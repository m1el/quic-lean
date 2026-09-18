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

/-- **(c)** Validation does not depend on the order the parameters appear in:
    the reference implementation's outcome is the same for any permutation.
    With no repeated identifier the whole outcome list agrees
    (`interpret_perm`); with a repeated identifier it is the error either way
    (`step_of_duplicated`).  The accepted *record* is order dependent when a
    parameter repeats — see the counterexample in section 9. -/
theorem step_perm (s : State) {raw₁ raw₂ : Raw} (hp : raw₁.Perm raw₂) (hwf : RawWF raw₁) :
    component.step s (.recvParams (encodeRaw raw₁))
      = component.step s (.recvParams (encodeRaw raw₂)) := by
  have hwf₂ : RawWF raw₂ := fun e he => hwf e (hp.mem_iff.mpr he)
  have h₁ : decodeRaw (encodeRaw raw₁) = .ok raw₁ := decodeRaw_encodeRaw _ hwf
  have h₂ : decodeRaw (encodeRaw raw₂) = .ok raw₂ := decodeRaw_encodeRaw _ hwf₂
  by_cases hnd : (knownIds raw₁).Nodup
  · have hdup₁ : duplicated raw₁ = false := by simp [duplicated, hnd]
    have hdup₂ : duplicated raw₂ = false := by rw [← duplicated_perm hp]; exact hdup₁
    have hint : interpret raw₁ = interpret raw₂ := interpret_perm hp hnd
    refine step_congr ?_
    simp only [outcomes, h₁, h₂, validate, hint, hdup₁, hdup₂, Bool.false_eq_true,
      ↓reduceIte]
  · have hdup₁ : duplicated raw₁ = true := by simp [duplicated, hnd]
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

-- §7.4: duplicates.  The SHOULD is the preferred outcome …
example : component.step cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    = .error .transportParameterError := by decide
-- … but ignoring the SHOULD and taking the last copy is also permitted.
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 20 }⟩
      [.paramsApplied { defaults with initialMaxData := 20 }]) = true := by decide

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

/-! ## 10. Coverage and notes

Assigned text: lines 2506–2695 (§7.4, §7.4.1, §7.4.2) and 6875–7154 (§18).

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §7.4 (2536) | receipt of a parameter with an invalid value MUST be TRANSPORT_PARAMETER_ERROR | `Step.invalid`, `Valid` |
| §7.4 (2539) | an endpoint MUST NOT send a parameter more than once | `duplicated`; send side is the peer's obligation, so it appears only as the receive rule below |
| §7.4 (2540) | receipt of duplicates SHOULD be TRANSPORT_PARAMETER_ERROR | `Step.duplicate` (preferred) with `Step.accept` still permitted |
| §7.4 (2545) | transport parameters authenticate connection ID negotiation | out of scope: WP11 Handshake; the three CID fields are exposed |
| §7.4 (2548) | ALPN: a client's parameters apply to all protocols it offers | not normative for the transport |
| §7.4.1 (2566) | a new parameter's definition MUST say whether storing it for 0-RTT is mandatory/optional/prohibited | out of scope: a rule about future specifications, not about an endpoint |
| §7.4.1 (2574) | a client MUST NOT use remembered values for seven named parameters | `remembered`, `remembered_resets` |
| §7.4.1 (2580) | a client that attempts 0-RTT MUST remember all other parameters it can process | `remembered` keeps every other field |
| §7.4.1 (2584) | a server accepting 0-RTT MUST NOT set seven listed parameters smaller than remembered | `ZeroRttCompatible` / `zeroRttCompatible` |
| §7.4.1 (2606) | the subset permitting application data SHOULD be non-zero | advice only; not modelled (SHOULD that recommends) |
| §7.4.1 (2612) | a server MAY also remember max_idle_timeout, max_udp_payload_size, disable_active_migration | `zeroRttCompatibleStrict`, the permitted alternative |
| §7.4.1 (2620) | a server MUST reject 0-RTT if restored values cannot be supported | out of scope: WP11 owns the accept/reject decision; the test is `zeroRttCompatible` |
| §7.4.1 (2623) | a client MUST only use remembered parameters in 0-RTT packets; a server MAY treat use of updated ones as PROTOCOL_VIOLATION | out of scope: WP2/WP9 enforce limits per packet, WP11 owns 0-RTT |
| §7.4.2 (2664) | an endpoint MUST ignore transport parameters it does not support | `knownEntries`, `ParamId.ofCode?_reserved` |
| §18 (6893) | the extension is a sequence of (ID, Length, Value) tuples | `decodeRaw` / `encodeRaw` |
| §18.1 (6912) | identifiers 31*N+27 are reserved | `ParamId.IsReserved`, `ParamId.ofCode?_reserved` |
| §18.2 (6926) | integer parameters use the varint encoding; absent parameters default to 0 | `varintValue?`, the field defaults of `TransportParams` |
| §18.2 (6940) | original_destination_connection_id is only sent by a server | `Valid`, first conjunct |
| §18.2 (6944) | max_idle_timeout; disabled when both omit it or send 0 | field; the timer itself is WP6 Termination |
| §18.2 (6959) | stateless_reset_token is 16 bytes, MUST NOT be sent by a client, MAY be sent by a server | `setParam` (length) and `Valid` (role) |
| §18.2 (6962) | a server that omits stateless_reset_token cannot stateless-reset the negotiated CID | out of scope: WP6 Termination |
| §18.2 (6952) | max_udp_payload_size default 65527, values below 1200 invalid | default field, `Valid` |
| §18.2 (6971–7016) | initial_max_data, the three per-stream limits, the two stream limits | fields; their effect is WP2/WP9 |
| §18.2 (7018) | ack_delay_exponent default 3, values above 20 invalid | default field, `Valid` |
| §18.2 (7024) | max_ack_delay default 25 ms, values ≥ 2^14 invalid | default field, `Valid` |
| §18.2 (7026) | max_ack_delay SHOULD include expected alarm delays | advice to the sender; not modelled (SHOULD that recommends) |
| §7.4.1 (2571) | a client need not store a parameter it cannot process | permissive; `knownEntries` already drops unknown ones |
| §18.2 (7040) | disable_active_migration is a zero-length value; the receiver MUST NOT use a new local address | `setParam` (length); the migration ban is WP10 |
| §18.2 (7051) | preferred_address is only sent by a server | `Valid`, first conjunct |
| §18.2 (7054) | a server MAY send an all-zero address and port for one family | permissive; the codec accepts any 4- and 16-byte address |
| §18.2 (7062) | Figure 22 layout | `preferredAddressP` / `encodePreferredAddress` |
| §18.2 (7093) | a server choosing a zero-length CID MUST NOT provide a preferred address | `Valid`, last conjunct |
| §18.2 (7094) | a server MUST NOT include a zero-length CID in preferred_address; a client MUST treat violation as TRANSPORT_PARAMETER_ERROR | `Valid`, second-to-last conjunct |
| §18.2 (7096) | acting on a preferred address | out of scope: WP10 Migration |
| §18.2 (7124) | active_connection_id_limit MUST be at least 2; below 2 MUST be TRANSPORT_PARAMETER_ERROR; default 2 | `Valid`, default field |
| §18.2 (7131) | an endpoint that issues a zero-length CID ignores the peer's active_connection_id_limit | out of scope: WP4 ConnIds |
| §18.2 (7134) | initial_source_connection_id | field; §7.3 checking is WP11 |
| §18.2 (7138) | retry_source_connection_id is only sent by a server | `Valid`, first conjunct |
| §18.2 (7141) | absent per-stream limits mean a limit of 0 | the field defaults |
| §18.2 (7145) | a client MUST NOT include any server-only parameter; a server MUST treat receipt as TRANSPORT_PARAMETER_ERROR | `Valid`, first conjunct |
| §4.6 (1537) | a max_streams transport parameter above 2^60 MUST be TRANSPORT_PARAMETER_ERROR | `Valid` (cited here because §18.2 defers the limit to §4.6) |

NOTES — ambiguities and the reading encoded

1. **Duplicates of an *unknown* identifier.**  §7.4 says duplicates SHOULD be an
   error; §7.4.2 says unknown parameters MUST be ignored.  Taken together they
   conflict for a repeated unknown identifier — in particular for two entries
   with the same reserved `31*N+27` identifier, which §18.1 says exist precisely
   to be ignored.  Reading encoded: `duplicated` counts only *known*
   identifiers, so ignoring wins.
2. **What an endpoint that ignores the duplicate SHOULD does.**  The text does
   not say which copy applies.  Reading encoded: the last copy, because
   `applyEntries` walks the sequence in order; this is the only alternative
   enumerated beside the error.  It is a choice, not something the text states —
   an implementation that takes the first copy is rejected by `accepts` even
   though the text arguably permits it.  The *preferred* outcome (`step`) is the
   error, so the reference implementation is unaffected.
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
   The Connection ID *inside* preferred_address is different: §18.2 says it is
   "identical in syntax and semantics to the corresponding fields of a
   NEW_CONNECTION_ID frame", so 1…20 is enforced.
5. **"A server that chooses a zero-length connection ID MUST NOT provide a
   preferred address."**  Decided from the parameters alone by reading "the
   connection ID the server chose" as its initial_source_connection_id (§7.3:
   "The value that the endpoint included in the Source Connection ID field of
   the first Initial packet it sends").  If that parameter is absent the rule is
   vacuous here; its absence is itself an error, but that is WP11's rule.
6. **Error code for a malformed sequence.**  §18 gives no code for bytes that
   are not a well-formed (ID, Length, Value) sequence.  Reading encoded:
   TRANSPORT_PARAMETER_ERROR, by §7.4's "invalid value" sentence.  ngtcp2 also
   reports TRANSPORT_PARAMETER_ERROR here.
7. **`disable_active_migration` with a non-empty value.**  §18.2: "This
   parameter is a zero-length value."  Reading encoded: a non-empty value is an
   invalid value, hence TRANSPORT_PARAMETER_ERROR, rather than being ignored.
8. **Receiving a second set of parameters.**  The model simply replaces `peer`.
   Whether that can happen at all is a TLS question (WP11).
9. **`zeroRttCompatibleStrict` and `disable_active_migration`.**  §7.4.1 speaks
   of "smaller values" for a parameter that is a flag.  Reading encoded: turning
   the flag on when it was previously off counts as a reduction.
-/

end Quic.Spec.TransportParams
