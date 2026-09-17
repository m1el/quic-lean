import QuicModel.Spec.TransportParams.Wire

/-
  The rules a *received* set of transport parameters must satisfy (§7.4, §18.2,
  §4.6), and the 0-RTT rules of §7.4.1.

  Everything here is a property of the decoded record plus the role of the
  endpoint that sent it; the events and error codes are in
  `QuicModel/Spec/TransportParams.lean`.
-/
namespace Quic.Spec.TransportParams

/-! ## Validity of a received parameter set

`sender` is the role of the endpoint whose parameters these are — the peer of
the endpoint doing the checking. -/

/-- §7.4, line 2536: "An endpoint MUST treat receipt of a transport parameter
    with an invalid value as a connection error of type
    TRANSPORT_PARAMETER_ERROR."  This is what "invalid value" means, parameter
    by parameter. -/
def Valid (sender : Role) (tp : TransportParams) : Prop :=
  -- §18.2, line 7145: "A client MUST NOT include any server-only transport
  -- parameter: original_destination_connection_id, preferred_address,
  -- retry_source_connection_id, or stateless_reset_token.  A server MUST treat
  -- receipt of any of these transport parameters as a connection error of type
  -- TRANSPORT_PARAMETER_ERROR."
  (sender = .client →
      tp.originalDestinationConnectionId = none ∧ tp.preferredAddress = none ∧
      tp.retrySourceConnectionId = none ∧ tp.statelessResetToken = none) ∧
  -- §18.2, line 6952: "Values below 1200 are invalid."
  1200 ≤ tp.maxUdpPayloadSize ∧
  -- §18.2, line 7018: "Values above 20 are invalid."
  tp.ackDelayExponent ≤ 20 ∧
  -- §18.2, line 7028: "Values of 2^14 or greater are invalid."
  tp.maxAckDelay < 2 ^ 14 ∧
  -- §18.2, line 7124: "The value of the active_connection_id_limit parameter
  -- MUST be at least 2.  An endpoint that receives a value less than 2 MUST
  -- close the connection with an error of type TRANSPORT_PARAMETER_ERROR."
  2 ≤ tp.activeConnectionIdLimit ∧
  -- §4.6, line 1537: "If a max_streams transport parameter … is received with a
  -- value greater than 2^60 … the connection MUST be closed immediately with a
  -- connection error of type TRANSPORT_PARAMETER_ERROR."
  tp.initialMaxStreamsBidi ≤ 2 ^ 60 ∧
  tp.initialMaxStreamsUni ≤ 2 ^ 60 ∧
  -- §18.2, line 7094: "a server MUST NOT include a zero-length connection ID in
  -- this transport parameter"; the Connection ID field is "identical in syntax
  -- and semantics to the corresponding field of a NEW_CONNECTION_ID frame",
  -- which bounds it by 20.  "A client MUST treat violation of these
  -- requirements as a connection error of type TRANSPORT_PARAMETER_ERROR."
  (∀ pa, tp.preferredAddress = some pa → 1 ≤ pa.cid.size ∧ pa.cid.size ≤ 20) ∧
  -- §18.2, line 7093: "A server that chooses a zero-length connection ID MUST
  -- NOT provide a preferred address."  The connection ID the server chose is
  -- the one it reports in initial_source_connection_id (§7.3).
  (∀ pa, tp.preferredAddress = some pa →
      ∀ c, tp.initialSourceConnectionId = some c → c.size ≠ 0)

def validB (sender : Role) (tp : TransportParams) : Bool :=
  (match sender with
   | .client =>
     tp.originalDestinationConnectionId.isNone && tp.preferredAddress.isNone &&
     tp.retrySourceConnectionId.isNone && tp.statelessResetToken.isNone
   | .server => true) &&
  decide (1200 ≤ tp.maxUdpPayloadSize) &&
  decide (tp.ackDelayExponent ≤ 20) &&
  decide (tp.maxAckDelay < 2 ^ 14) &&
  decide (2 ≤ tp.activeConnectionIdLimit) &&
  decide (tp.initialMaxStreamsBidi ≤ 2 ^ 60) &&
  decide (tp.initialMaxStreamsUni ≤ 2 ^ 60) &&
  (match tp.preferredAddress with
   | none => true
   | some pa =>
     decide (1 ≤ pa.cid.size) && decide (pa.cid.size ≤ 20) &&
     (match tp.initialSourceConnectionId with
      | none => true
      | some c => decide (c.size ≠ 0)))

theorem validB_iff (sender : Role) (tp : TransportParams) :
    validB sender tp = true ↔ Valid sender tp := by
  cases sender <;>
    cases hpa : tp.preferredAddress <;>
    cases hsc : tp.initialSourceConnectionId <;>
    simp [validB, Valid, hpa, hsc, and_assoc]

instance (sender : Role) (tp : TransportParams) : Decidable (Valid sender tp) :=
  decidable_of_iff _ (validB_iff sender tp)

/-- The §18.2 defaults are valid for either role: no default value is out of
    range, and the four server-only parameters are absent. -/
theorem valid_defaults (sender : Role) : Valid sender defaults := by
  rw [← validB_iff]; cases sender <;> rfl

/-! ## 0-RTT (§7.4.1) -/

/-- §7.4.1, line 2574: "A client MUST NOT use remembered values for the
    following parameters: ack_delay_exponent, max_ack_delay,
    initial_source_connection_id, original_destination_connection_id,
    preferred_address, retry_source_connection_id, and stateless_reset_token.
    The client MUST use the server's new values in the handshake instead; if the
    server does not provide new values, the default value is used."

    "A client that attempts to send 0-RTT data MUST remember all other transport
    parameters used by the server that it is able to process." -/
def remembered (tp : TransportParams) : TransportParams :=
  { tp with
    ackDelayExponent := defaults.ackDelayExponent
    maxAckDelay := defaults.maxAckDelay
    initialSourceConnectionId := none
    originalDestinationConnectionId := none
    preferredAddress := none
    retrySourceConnectionId := none
    statelessResetToken := none }

/-- §7.4.1, line 2584: "If 0-RTT data is accepted by the server, the server MUST
    NOT reduce any limits or alter any values that might be violated by the
    client with its 0-RTT data.  In particular, a server that accepts 0-RTT data
    MUST NOT set values for the following parameters (Section 18.2) that are
    smaller than the remembered value of the parameters." -/
def ZeroRttCompatible (old new : TransportParams) : Prop :=
  old.activeConnectionIdLimit ≤ new.activeConnectionIdLimit ∧
  old.initialMaxData ≤ new.initialMaxData ∧
  old.initialMaxStreamDataBidiLocal ≤ new.initialMaxStreamDataBidiLocal ∧
  old.initialMaxStreamDataBidiRemote ≤ new.initialMaxStreamDataBidiRemote ∧
  old.initialMaxStreamDataUni ≤ new.initialMaxStreamDataUni ∧
  old.initialMaxStreamsBidi ≤ new.initialMaxStreamsBidi ∧
  old.initialMaxStreamsUni ≤ new.initialMaxStreamsUni

/-- The decidable form asked for by §7.4.1. -/
def zeroRttCompatible (old new : TransportParams) : Bool :=
  decide (old.activeConnectionIdLimit ≤ new.activeConnectionIdLimit) &&
  decide (old.initialMaxData ≤ new.initialMaxData) &&
  decide (old.initialMaxStreamDataBidiLocal ≤ new.initialMaxStreamDataBidiLocal) &&
  decide (old.initialMaxStreamDataBidiRemote ≤ new.initialMaxStreamDataBidiRemote) &&
  decide (old.initialMaxStreamDataUni ≤ new.initialMaxStreamDataUni) &&
  decide (old.initialMaxStreamsBidi ≤ new.initialMaxStreamsBidi) &&
  decide (old.initialMaxStreamsUni ≤ new.initialMaxStreamsUni)

theorem zeroRttCompatible_iff (old new : TransportParams) :
    zeroRttCompatible old new = true ↔ ZeroRttCompatible old new := by
  simp [zeroRttCompatible, ZeroRttCompatible, and_assoc]

instance (old new : TransportParams) : Decidable (ZeroRttCompatible old new) :=
  decidable_of_iff _ (zeroRttCompatible_iff old new)

/-- §7.4.1, line 2612: "A server MAY store and recover the previously sent
    values of the max_idle_timeout, max_udp_payload_size, and
    disable_active_migration parameters and reject 0-RTT if it selects smaller
    values."  A server that takes that option uses this stricter test; both are
    permitted, which is why they are separate predicates. -/
def zeroRttCompatibleStrict (old new : TransportParams) : Bool :=
  zeroRttCompatible old new &&
  decide (old.maxIdleTimeout ≤ new.maxIdleTimeout) &&
  decide (old.maxUdpPayloadSize ≤ new.maxUdpPayloadSize) &&
  (old.disableActiveMigration || !new.disableActiveMigration)

theorem zeroRttCompatible_of_strict {old new : TransportParams}
    (h : zeroRttCompatibleStrict old new = true) : zeroRttCompatible old new = true := by
  simp only [zeroRttCompatibleStrict, Bool.and_eq_true] at h
  exact h.1.1.1

theorem zeroRttCompatible_refl (tp : TransportParams) : ZeroRttCompatible tp tp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.le_refl _

theorem zeroRttCompatible_trans {a b c : TransportParams}
    (h₁ : ZeroRttCompatible a b) (h₂ : ZeroRttCompatible b c) : ZeroRttCompatible a c := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := h₁
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := h₂
  exact ⟨Nat.le_trans p1 q1, Nat.le_trans p2 q2, Nat.le_trans p3 q3, Nat.le_trans p4 q4,
    Nat.le_trans p5 q5, Nat.le_trans p6 q6, Nat.le_trans p7 q7⟩

/-- The seven parameters a client may not carry over really are back at their
    §18.2 defaults in what it remembers. -/
theorem remembered_resets (tp : TransportParams) :
    (remembered tp).ackDelayExponent = defaults.ackDelayExponent ∧
    (remembered tp).maxAckDelay = defaults.maxAckDelay ∧
    (remembered tp).initialSourceConnectionId = defaults.initialSourceConnectionId ∧
    (remembered tp).originalDestinationConnectionId
      = defaults.originalDestinationConnectionId ∧
    (remembered tp).preferredAddress = defaults.preferredAddress ∧
    (remembered tp).retrySourceConnectionId = defaults.retrySourceConnectionId ∧
    (remembered tp).statelessResetToken = defaults.statelessResetToken :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Everything a 0-RTT limit check looks at survives being remembered, so
    checking against `remembered tp` is the same as checking against `tp`. -/
theorem zeroRttCompatible_remembered (tp new : TransportParams) :
    ZeroRttCompatible (remembered tp) new ↔ ZeroRttCompatible tp new := Iff.rfl

end Quic.Spec.TransportParams
