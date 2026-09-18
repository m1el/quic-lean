import QuicModel.Spec.Handshake.Component

/-!
  WP11 "Handshake" — the transport side of the cryptographic handshake.

  Assigned text: §7 and §7.1–§7.3 (lines 2157–2505), §7.5 (2696–2723),
  §17.2.2 and §17.2.2.1 (6300–6409), §17.2.3 and §17.2.4 (6410–6556),
  §19.6 (7509–7564), §19.20 (8193–8211).

  * `Handshake/Crypto.lean`    — the CRYPTO stream of one level (§19.6, §7.5)
  * `Handshake/Basic.lean`     — state, events, `Step`, `outcomes` (§1–3)
  * `Handshake/Component.lean` — `outcomes_iff`, `Inv`, send side, the component
  * this file                  — the named theorems, examples and coverage table

  §7.4 transport parameters are WP1's; this file composes with them.
-/
namespace Quic.Spec.Handshake

open Quic.Spec.ConnIds (Cid)

/-! ## 8. Named theorems -/

/-! ### (a) Complete and confirmed -/

/-- **(a)** The handshake is never confirmed before it is complete.  §19.20,
    line 8207: "Servers MUST NOT send a HANDSHAKE_DONE frame before completing
    the handshake", and at the client confirmation *is* that frame. -/
theorem confirmed_complete {s : State} (hi : Inv s) (h : s.confirmed = true) :
    s.complete = true := hi.1 h

/-- **(a)** `complete` never goes back to false. -/
theorem complete_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hc : s.complete = true) : s'.complete = true := by
  cases h
  case keys dir lv => obtain ⟨r, w, he⟩ := provideKey_eq s dir lv; rw [he]; exact hc
  case header hh => cases hh <;> exact hc
  case crypto hh => cases hh <;> exact hc
  case params hp => cases hp <;> exact hc
  case completeServer => rfl
  case completeClient => rfl
  all_goals exact hc

/-- **(a)** `confirmed` never goes back to false. -/
theorem confirmed_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (hc : s.confirmed = true) : s'.confirmed = true := by
  cases h
  case keys dir lv => obtain ⟨r, w, he⟩ := provideKey_eq s dir lv; rw [he]; exact hc
  case header hh => cases hh <;> exact hc
  case crypto hh => cases hh <;> exact hc
  case params hp => cases hp <;> exact hc
  case completeServer => rfl
  case doneClient => rfl
  all_goals exact hc

theorem reachable_complete {s₀ s : State} (h0 : s₀.complete = true)
    (h : component.Reachable s₀ s) : s.complete = true :=
  Component.reachable_induction (C := component) (motive := fun t => t.complete = true) h0
    (fun _ hs ih => complete_mono hs ih) h

theorem reachable_confirmed {s₀ s : State} (h0 : s₀.confirmed = true)
    (h : component.Reachable s₀ s) : s.confirmed = true :=
  Component.reachable_induction (C := component) (motive := fun t => t.confirmed = true) h0
    (fun _ hs ih => confirmed_mono hs ih) h

/-- A server's handshake is confirmed exactly when it completes (RFC 9001
    §4.1.2, referred to at line 3281); the client needs HANDSHAKE_DONE. -/
theorem server_confirms_on_complete {s : State} (hr : s.role = .server) (hc : s.complete = false) :
    component.step s .tlsComplete =
      .ok { s with complete := true, confirmed := true } [.handshakeComplete, .handshakeConfirmed] := by
  have : outcomes s .tlsComplete =
      [.ok { s with complete := true, confirmed := true }
         [.handshakeComplete, .handshakeConfirmed]] := by simp [outcomes, hc, hr]
  simp only [Component.step, this, List.head_cons]

/-! ### (b) CRYPTO data reaches TLS in order and without gaps -/

@[simp] theorem stream_setStream_self (s : State) (l : CryptoLevel) (c : Crypto) :
    (s.setStream l c).stream l = c := by rw [stream_setStream]; simp

/-- **(b)** The delivered prefix of every CRYPTO stream only grows. -/
theorem delivered_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (l : CryptoLevel) :
    (s.stream l).delivered ≤ (s'.stream l).delivered := by
  have setLe : ∀ (lv : CryptoLevel) (c : Crypto), (s.stream lv).delivered ≤ c.delivered →
      (s.stream l).delivered ≤ ((s.setStream lv c).stream l).delivered := by
    intro lv c hc
    rw [stream_setStream]
    split
    · rename_i he; subst he; exact hc
    · exact Nat.le_refl _
  cases h
  case keys dir lv => obtain ⟨r, w, he⟩ := provideKey_eq s dir lv; rw [he]; exact Nat.le_refl _
  case send => exact setLe _ _ (Nat.le_refl _)
  case sentCrypto => exact setLe _ _ (Nat.le_refl _)
  case header hh => cases hh <;> exact Nat.le_refl _
  case params hp => cases hp <;> exact Nat.le_refl _
  case crypto hh =>
    cases hh
    case alreadyDiscarding => exact Nat.le_refl _
    case accept => exact setLe _ _ (Crypto.delivered_le_recv _ _ _)
    case expand => exact setLe _ _ (Crypto.delivered_le_recv _ _ _)
    case overflowDiscard => exact setLe _ _ (Nat.le_refl _)
  all_goals exact Nat.le_refl _

theorem reachable_delivered_mono {s₀ s : State} (h : component.Reachable s₀ s) (l : CryptoLevel) :
    (s₀.stream l).delivered ≤ (s.stream l).delivered :=
  Component.reachable_induction (C := component)
    (motive := fun t => (s₀.stream l).delivered ≤ (t.stream l).delivered) (Nat.le_refl _)
    (fun _ hs ih => Nat.le_trans ih (delivered_mono hs l)) h

/-- **(b)** Data handed to TLS is contiguous: an effect starts exactly where the
    last one stopped and ends exactly at the new delivered prefix, and it is
    never empty.  §7, line 2167: "QUIC provides reliable, ordered delivery of
    the cryptographic handshake data." -/
theorem deliverCrypto_contiguous {s s' : State} {l : CryptoLevel} {o n : Nat} {fx : List Effect}
    {lv : CryptoLevel} {off len : Nat}
    (h : Step s (.recvCrypto l o n) (.ok s' fx)) (hm : Effect.deliverCrypto lv off len ∈ fx) :
    lv = l ∧ off = (s.stream l).delivered ∧ off + len = (s'.stream l).delivered ∧ 0 < len := by
  cases h with
  | crypto hh =>
    cases hh with
    | alreadyDiscarding => simp at hm
    | overflowDiscard => simp at hm
    | accept =>
      simp only [deliverFx] at hm
      split at hm
      · rename_i hlt
        simp only [List.mem_singleton, Effect.deliverCrypto.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        exact ⟨rfl, rfl, by rw [stream_setStream_self]; omega, by omega⟩
      · simp at hm
    | expand =>
      simp only [deliverFx] at hm
      split at hm
      · rename_i hlt
        simp only [List.mem_singleton, Effect.deliverCrypto.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        exact ⟨rfl, rfl, by rw [stream_setStream_self]; omega, by omega⟩
      · simp at hm

/-- **(b)** Every byte handed to TLS was received: it was either already
    buffered or lies in the CRYPTO frame being processed.  Nothing is invented,
    and nothing is skipped (the range is contiguous by the theorem above). -/
theorem deliverCrypto_received {s s' : State} {l : CryptoLevel} {o n : Nat} {fx : List Effect}
    {lv : CryptoLevel} {off len m : Nat} (hi : Inv s)
    (h : Step s (.recvCrypto l o n) (.ok s' fx)) (hm : Effect.deliverCrypto lv off len ∈ fx)
    (h1 : off ≤ m) (h2 : m < off + len) :
    Ack.Ranges.mem (s.stream l).buf m = true ∨ (o ≤ m ∧ m < o + n) := by
  obtain ⟨_, hoff, hend, _⟩ := deliverCrypto_contiguous h hm
  refine Crypto.recv_delivers_received (hi.2.2 l) (by omega) ?_
  cases h with
  | crypto hh =>
    cases hh with
    | alreadyDiscarding => simp at hm
    | overflowDiscard => simp at hm
    | accept => rw [stream_setStream_self] at hend; omega
    | expand => rw [stream_setStream_self] at hend; omega

/-! ### (c) Discarded keys stay discarded -/

theorem provideKey_read_discarded {s : State} {d : KeyDir} {lv l : Level}
    (hd : s.read.get l = .discarded) : (s.provideKey d lv).read.get l = .discarded := by
  cases d
  · by_cases h : s.read.get lv = .discarded
    · simpa [State.provideKey, h] using hd
    · simp only [State.provideKey, h, ↓reduceIte, Keys.get_set]
      split
      · rename_i he; subst he; exact absurd hd h
      · exact hd
  · by_cases h : s.write.get lv = .discarded
    · simpa [State.provideKey, h] using hd
    · simpa [State.provideKey, h] using hd

theorem provideKey_write_discarded {s : State} {d : KeyDir} {lv l : Level}
    (hd : s.write.get l = .discarded) : (s.provideKey d lv).write.get l = .discarded := by
  cases d
  · by_cases h : s.read.get lv = .discarded
    · simpa [State.provideKey, h] using hd
    · simpa [State.provideKey, h] using hd
  · by_cases h : s.write.get lv = .discarded
    · simpa [State.provideKey, h] using hd
    · simp only [State.provideKey, h, ↓reduceIte, Keys.get_set]
      split
      · rename_i he; subst he; exact absurd hd h
      · exact hd

theorem discardKeys_read_discarded {s : State} {lv l : Level} (hd : s.read.get l = .discarded) :
    (s.discardKeys lv).read.get l = .discarded := by
  simp only [State.discardKeys, Keys.get_set]; split
  · rfl
  · exact hd

theorem discardKeys_write_discarded {s : State} {lv l : Level} (hd : s.write.get l = .discarded) :
    (s.discardKeys lv).write.get l = .discarded := by
  simp only [State.discardKeys, Keys.get_set]; split
  · rfl
  · exact hd

/-- **(c)** A key, once discarded, never comes back — in either direction and at
    every level.  §17.2.2.1, line 6403: "Initial packet protection keys are
    discarded"; nothing in the text restores them. -/
theorem read_discarded_stable {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) {l : Level} (hd : s.read.get l = .discarded) :
    s'.read.get l = .discarded := by
  cases h
  case keys dir lv => exact provideKey_read_discarded hd
  case discard => exact discardKeys_read_discarded hd
  case zeroRttRejected => exact discardKeys_read_discarded (lv := Level.zeroRtt) hd
  case sentHandshake => exact discardKeys_read_discarded hd
  case header hh =>
    cases hh
    case srvHandshakeDiscard => exact discardKeys_read_discarded hd
    all_goals exact hd
  case crypto hh => cases hh <;> exact hd
  case params hp => cases hp <;> exact hd
  all_goals exact hd

theorem write_discarded_stable {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) {l : Level} (hd : s.write.get l = .discarded) :
    s'.write.get l = .discarded := by
  cases h
  case keys dir lv => exact provideKey_write_discarded hd
  case discard => exact discardKeys_write_discarded hd
  case zeroRttRejected => exact discardKeys_write_discarded (lv := Level.zeroRtt) hd
  case sentHandshake => exact discardKeys_write_discarded hd
  case header hh =>
    cases hh
    case srvHandshakeDiscard => exact discardKeys_write_discarded hd
    all_goals exact hd
  case crypto hh => cases hh <;> exact hd
  case params hp => cases hp <;> exact hd
  all_goals exact hd

theorem reachable_read_discarded {s₀ s : State} {l : Level} (h0 : s₀.read.get l = .discarded)
    (h : component.Reachable s₀ s) : s.read.get l = .discarded :=
  Component.reachable_induction (C := component) (motive := fun t => t.read.get l = .discarded) h0
    (fun _ hs ih => read_discarded_stable hs ih) h

theorem outcomes_initial_discarded (s : State) (d c : Cid)
    (hd : s.read.get .initial = .discarded) :
    outcomes s (.recvHeader .initial d c) = [.drop] := by
  simp [outcomes, headerOutcomes, State.readKeyFor, levelOf, hd]

/-- **(c)** Once the Initial keys are discarded, every Initial packet is
    dropped, and nothing else is permitted.  §17.2.2.1, line 6398: an endpoint
    "stops both sending and processing Initial packets". -/
theorem initial_discarded_drop {s : State} {d c : Cid} {o : Outcome State Effect}
    (hd : s.read.get .initial = .discarded) (h : Step s (.recvHeader .initial d c) o) :
    o = .drop := by
  have hm := (outcomes_iff s _ o).mpr h
  rw [outcomes_initial_discarded s d c hd] at hm
  simpa using hm

/-- **(c)** The same, for every state reachable from one that has discarded
    them. -/
theorem reachable_initial_discarded_drop {s₀ s : State} {d c : Cid} {o : Outcome State Effect}
    (h0 : s₀.read.get .initial = .discarded) (hr : component.Reachable s₀ s)
    (h : Step s (.recvHeader .initial d c) o) : o = .drop :=
  initial_discarded_drop (reachable_read_discarded h0 hr) h

/-- §17.2.2.1, line 6398: "A client stops both sending and processing Initial
    packets when it sends its first Handshake packet." -/
theorem client_discards_on_first_handshake {s : State} (hr : s.role = .client)
    (hd : s.write.get .initial ≠ .discarded) :
    component.step s (.sentPacket .handshake) =
      .ok (s.discardKeys .initial) [.keysDiscarded .initial] := by
  have : outcomes s (.sentPacket .handshake) =
      [.ok (s.discardKeys .initial) [.keysDiscarded .initial]] := by simp [outcomes, hr, hd]
  simp only [Component.step, this, List.head_cons]

/-- §17.2.2.1, line 6399: "A server stops sending and processing Initial packets
    when it receives its first Handshake packet." -/
theorem server_discards_on_first_handshake {s : State} (hr : s.role = .server)
    (hk : s.read.get .handshake = .present) (hd : s.read.get .initial ≠ .discarded)
    (d c : Cid) :
    component.step s (.recvHeader .handshake d c) =
      .ok (s.discardKeys .initial) [.keysDiscarded .initial] := by
  have : outcomes s (.recvHeader .handshake d c) =
      [.ok (s.discardKeys .initial) [.keysDiscarded .initial]] := by
    simp [outcomes, headerOutcomes, State.readKeyFor, levelOf, hk, cidOutcomes, hr, hd]
  simp only [Component.step, this, List.head_cons]

/-! ### (d) The client changes its Destination Connection ID at most once per
connection attempt -/

/-- §7.2, line 2368: "a client might have to change the connection ID it sets in
    the Destination Connection ID field twice during connection establishment:
    once in response to a Retry, and once in response to an Initial packet from
    the server" — and line 2376: "in response to only the first received Initial
    or Retry packet". -/
def bit : Bool → Nat
  | true => 1
  | false => 0

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

def DcidBound (s : State) : Prop := s.dcidChanges ≤ bit s.retrySeen + bit s.sawPeerInitial

theorem step_dcidBound {s s' : State} {e : Event} {fx : List Effect}
    (hb : DcidBound s) (h : Step s e (.ok s' fx)) : DcidBound s' := by
  cases h
  case keys dir lv => obtain ⟨r, w, he⟩ := provideKey_eq s dir lv; rw [he]; exact hb
  case params hp => cases hp <;> exact hb
  case crypto hh => cases hh <;> exact hb
  case sentRetry =>
    simp only [DcidBound, bit] at hb ⊢
    have := bit_le_one s.retrySeen
    simp only [bit] at this
    omega
  case header hh =>
    cases hh
    case cliInitialFirst hk hr hs =>
      simp only [DcidBound, State.adoptScid, hs, bit] at hb ⊢
      omega
    case srvInitialFirst hk hr hs =>
      simp only [DcidBound, State.adoptScid, hs, bit] at hb ⊢
      omega
    case cliRetryFirst hk hr hs ht =>
      simp only [DcidBound, State.adoptRetryScid, hs, ht, bit] at hb ⊢
      omega
    all_goals exact hb
  all_goals exact hb

/-- **(d)** From a fresh connection attempt (no change made yet), the number of
    Destination Connection ID changes is at most one, plus one more exactly when
    a Retry intervened. -/
theorem dcidChanges_bound {s₀ s : State} (h0 : s₀.dcidChanges = 0)
    (h : component.Reachable s₀ s) : DcidBound s := by
  refine Component.reachable_induction (C := component) (motive := DcidBound) ?_
    (fun _ hs ih => step_dcidBound ih hs) h
  simp only [DcidBound, h0]
  exact Nat.zero_le _

/-- **(d)** Never more than twice, and never more than once without a Retry. -/
theorem dcidChanges_le_two {s₀ s : State} (h0 : s₀.dcidChanges = 0)
    (h : component.Reachable s₀ s) : s.dcidChanges ≤ 2 := by
  have hb := dcidChanges_bound h0 h
  simp only [DcidBound] at hb
  have h1 := bit_le_one s.retrySeen
  have h2 := bit_le_one s.sawPeerInitial
  omega

theorem dcidChanges_le_one_of_no_retry {s₀ s : State} (h0 : s₀.dcidChanges = 0)
    (h : component.Reachable s₀ s) (hr : s.retrySeen = false) : s.dcidChanges ≤ 1 := by
  have hb := dcidChanges_bound h0 h
  simp only [DcidBound] at hb
  have h1 : bit s.retrySeen = 0 := by rw [hr]; rfl
  have h2 := bit_le_one s.sawPeerInitial
  omega

/-! ### (e) §7.3 authenticating connection IDs -/

/-- §18.2, line 7149 (WP1's `Valid`): a client may send neither
    `original_destination_connection_id` nor `retry_source_connection_id`, so at
    a server the two Retry bullets of §7.3 are vacuous. -/
theorem server_peer_cids_absent {s : State} (hr : s.role = .server) {tp : Params}
    (hv : TransportParams.Valid s.role.peer tp) :
    tp.originalDestinationConnectionId = none ∧ tp.retrySourceConnectionId = none := by
  have : s.role.peer = .client := by rw [hr]; rfl
  obtain ⟨h1, _⟩ := hv
  obtain ⟨ho, _, hrs, _⟩ := h1 this
  exact ⟨ho, hrs⟩

/-- **(e)** §7.3 in full: the peer's parameters are accepted exactly in the
    configurations the text lists, for each of client/server and Retry/no-Retry.

    For a client the peer is the server (Figure 7 and Figure 8): it must report
    the Source Connection ID of its first Initial in
    `initial_source_connection_id` ("S3"), the Destination Connection ID of the
    client's first Initial in `original_destination_connection_id` ("S1"), and
    `retry_source_connection_id` ("S2") if and only if it sent a Retry — which
    is the one equation `optCid … = s.retryScid`, `none` on both sides when
    there was none.

    For a server the peer is the client, which reports only
    `initial_source_connection_id` ("C1"); the other two are absent by WP1's
    `Valid` (`server_peer_cids_absent`). -/
theorem cids_ok_iff (s : State) (tp : Params) :
    (missingCid s tp = false ∧ cidMismatch s tp = false) ↔
      (match s.role with
       | .client =>
         tp.initialSourceConnectionId.isSome = true ∧
         tp.initialSourceConnectionId = optCid s.peerScid ∧
         tp.originalDestinationConnectionId.isSome = true ∧
         tp.originalDestinationConnectionId = optCid s.originalDcid ∧
         tp.retrySourceConnectionId = optCid s.retryScid
       | .server =>
         tp.initialSourceConnectionId.isSome = true ∧
         tp.initialSourceConnectionId = optCid s.peerScid) := by
  cases hr : s.role <;>
    cases hi : tp.initialSourceConnectionId <;>
    cases ho : tp.originalDestinationConnectionId <;>
    cases hq : tp.retrySourceConnectionId <;>
    simp [missingCid, cidMismatch, optCid, hr, hi, ho, hq]

/-! **(e)** the same, spelled out over the four Retry × role cases the text
distinguishes.  §7.3, line 2436: "absence of the retry_source_connection_id
transport parameter from the server after receiving a Retry packet"; line 2439:
"presence of the retry_source_connection_id transport parameter when no Retry
packet was received". -/

/-- Client, no Retry (Figure 7, line 2449): the server must report its own
    Source Connection ID and the client's original Destination Connection ID,
    and MUST NOT report a `retry_source_connection_id`. -/
theorem cids_ok_client_noRetry {s : State} (hr : s.role = .client) (hq : s.retryScid = none)
    (tp : Params) :
    (missingCid s tp = false ∧ cidMismatch s tp = false) ↔
      (tp.initialSourceConnectionId = optCid s.peerScid ∧ s.peerScid.isSome = true ∧
       tp.originalDestinationConnectionId = optCid s.originalDcid ∧
       s.originalDcid.isSome = true ∧ tp.retrySourceConnectionId = none) := by
  rw [cids_ok_iff]
  cases hp : s.peerScid <;> cases hd : s.originalDcid <;>
    cases hi : tp.initialSourceConnectionId <;> cases ho : tp.originalDestinationConnectionId <;>
    simp [hr, hq, optCid, and_comm, and_left_comm]

/-- Client, after a Retry (Figure 8, line 2479): additionally the server must
    report the Retry packet's Source Connection ID. -/
theorem cids_ok_client_retry {s : State} {r : Cid} (hr : s.role = .client)
    (hq : s.retryScid = some r) (tp : Params) :
    (missingCid s tp = false ∧ cidMismatch s tp = false) ↔
      (tp.initialSourceConnectionId = optCid s.peerScid ∧ s.peerScid.isSome = true ∧
       tp.originalDestinationConnectionId = optCid s.originalDcid ∧
       s.originalDcid.isSome = true ∧ tp.retrySourceConnectionId = some (bytes r)) := by
  rw [cids_ok_iff]
  cases hp : s.peerScid <;> cases hd : s.originalDcid <;>
    cases hi : tp.initialSourceConnectionId <;> cases ho : tp.originalDestinationConnectionId <;>
    simp [hr, hq, optCid, and_comm, and_left_comm]

/-- Server, with or without a Retry: the client reports only
    `initial_source_connection_id` (line 2493: "In both cases (Figure 7 and
    Figure 8), the client sets the value of the initial_source_connection_id
    transport parameter to "C1""), and §18.2, line 7149 already forbids it the
    other two. -/
theorem cids_ok_server {s : State} (hr : s.role = .server) (tp : Params) :
    (missingCid s tp = false ∧ cidMismatch s tp = false) ↔
      (tp.initialSourceConnectionId = optCid s.peerScid ∧ s.peerScid.isSome = true) := by
  rw [cids_ok_iff]
  cases hp : s.peerScid <;> cases hi : tp.initialSourceConnectionId <;>
    simp [hr, optCid, and_comm]

/-- §7.3, line 2428: absence of a required parameter is TRANSPORT_PARAMETER_ERROR
    and nothing else. -/
theorem authOutcomes_missing (s : State) (tps : TransportParams.State) {tp : Params}
    (hp : tps.peer = some tp) (hm : missingCid s tp = true) :
    authOutcomes s tps = [.error .transportParameterError] := by
  simp [authOutcomes, hp, hm]

/-- §7.3, line 2433: a mismatch (or a misplaced `retry_source_connection_id`) is
    TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION, and nothing else. -/
theorem authOutcomes_mismatch (s : State) (tps : TransportParams.State) {tp : Params}
    (hp : tps.peer = some tp) (hm : missingCid s tp = false) (hc : cidMismatch s tp = true) :
    authOutcomes s tps = [.error .transportParameterError, .error .protocolViolation] := by
  simp [authOutcomes, hp, hm, hc]

/-- **(e)** "Peer parameters accepted" happens exactly in the configurations of
    `cids_ok_iff`. -/
theorem authOutcomes_accept_iff (s : State) (tps : TransportParams.State) {tp : Params}
    (hp : tps.peer = some tp) :
    authOutcomes s tps = [.ok { s with peerParams := some tp } [.peerParams tp]] ↔
      (missingCid s tp = false ∧ cidMismatch s tp = false) := by
  constructor
  · intro h
    by_cases hm : missingCid s tp = true
    · rw [authOutcomes_missing s tps hp hm] at h; simp at h
    · simp only [Bool.not_eq_true] at hm
      by_cases hc : cidMismatch s tp = true
      · rw [authOutcomes_mismatch s tps hp hm hc] at h; simp at h
      · exact ⟨hm, by simpa using hc⟩
  · rintro ⟨hm, hc⟩; simp [authOutcomes, hp, hm, hc]

/-! ### (f) HANDSHAKE_DONE -/

/-- **(f)** §19.20, line 8207: "A HANDSHAKE_DONE frame can only be sent by the
    server.  Servers MUST NOT send a HANDSHAKE_DONE frame before completing the
    handshake."  Nothing else may send it, ever. -/
theorem maySend_handshakeDone_iff (s : State) :
    maySend s .handshakeDone = true ↔ (s.role = .server ∧ s.complete = true) := by
  simp [maySend]

theorem client_never_sends_handshakeDone {s : State} (hr : s.role = .client) :
    maySend s .handshakeDone = false := by simp [maySend, hr]

/-- §19.20, line 8195: the client's handshake is confirmed by the frame. -/
theorem client_confirms_on_done {s : State} (hr : s.role = .client) (hc : s.complete = true) :
    component.step s .recvHandshakeDone = .ok { s with confirmed := true } [.handshakeConfirmed] := by
  have : outcomes s .recvHandshakeDone = [.ok { s with confirmed := true } [.handshakeConfirmed]] := by
    simp [outcomes, hr, hc]
  simp only [Component.step, this, List.head_cons]

/-! ### Packet-level send rules -/

/-- §17.2.2.1: nothing may be sent at a level whose write keys are gone. -/
theorem no_packet_without_keys {s : State} {p : OutPacket} {l : Level}
    (hl : levelOf p.ptype = some l) (hk : s.write.get l ≠ .present) :
    maySendPacket s p = false := by
  simp only [maySendPacket, hl, Bool.and_eq_false_imp, Bool.and_eq_true, beq_iff_eq]
  intro h
  exact absurd h.1 hk

/-- §17.2.3, line 6415 and line 6476: 0-RTT packets are the client's, and only
    until it starts processing 1-RTT packets from the server. -/
theorem zeroRtt_client_only {s : State} {p : OutPacket} (hp : p.ptype = .zeroRtt)
    (h : maySendPacket s p = true) : s.role = .client ∧ s.processed1Rtt = false := by
  have := (maySendPacket_iff s p).mp h
  exact this.2.1 hp

/-- §19.6: a CRYPTO frame never runs past what TLS handed over at that level,
    and never past 2^62-1; an exact repeat of a frame sent earlier is still
    permitted (§12.4, line 4936: "All frames are idempotent").  §17.2.2, line
    6378: while nothing has been sent at that level, it begins at offset 0. -/
theorem crypto_within_handed {s : State} {p : OutPacket} {l : CryptoLevel} {off : Nat}
    {data : ByteArray} (hl : cryptoLevelOf p.ptype = some l) (hf : Frame.crypto off data ∈ p.frames)
    (h : maySendPacket s p = true) :
    off + data.size ≤ (s.stream l).handed ∧ off + data.size ≤ maxCryptoOffset ∧
      s.write.get l.level ≠ .discarded ∧ ((s.stream l).sentNext = 0 → off = 0) := by
  have hok := ((maySendPacket_iff s p).mp h).2.2 l hl _ hf
  simp only [cryptoFrameOk, maySendCryptoAt, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, Bool.or_eq_true,
    bne_iff_ne, beq_iff_eq] at hok
  refine ⟨hok.1.1.1, hok.1.1.2, hok.1.2, fun hs => ?_⟩
  rcases hok.2 with h0 | h0
  · exact absurd hs h0
  · exact h0

/-- **(g)** §17.2.2, line 6378: "The first CRYPTO frame sent always begins at an
    offset of 0."  Stated on its own, for either role and every level. -/
theorem first_crypto_at_zero {s : State} {p : OutPacket} {l : CryptoLevel} {off : Nat}
    {data : ByteArray} (hl : cryptoLevelOf p.ptype = some l) (hf : Frame.crypto off data ∈ p.frames)
    (h : maySendPacket s p = true) (hs : (s.stream l).sentNext = 0) : off = 0 :=
  (crypto_within_handed hl hf h).2.2.2 hs

/-! ### §7.2 on the send side

`SendHeader` (in `Handshake/Component.lean`) is now the definition the
component's `MaySendDatagram` field is built from, over `Spec.OutDatagram`'s
`dcid`/`scid`; these are the two MUSTs of the client's first flight, stated on
the field itself. -/

/-- **(h)** §7.2, line 2340: "This Destination Connection ID MUST be at least 8
    bytes in length", and line 2341: "Until a packet is received from the
    server, the client MUST use the same Destination Connection ID value on all
    packets in this connection" — for every long-header packet of a datagram a
    client may send in its first flight.  Line 2357 gives the third conjunct:
    the Source Connection ID is the one the client chose. -/
theorem maySendDatagram_firstFlight {s : State} {d : OutDatagram} {dcid scid : Cid}
    {p : OutPacket} (hf : s.firstFlight = true) (hd : d.dcid = some dcid)
    (hs : d.scid = some scid) (h : MaySendDatagram s d) (hp : p ∈ d.packets)
    (hlong : p.ptype = .initial ∨ p.ptype = .zeroRtt ∨ p.ptype = .handshake) :
    scid = s.localScid ∧ s.dcidSent = some dcid ∧ 8 ≤ dcid.length := by
  simp only [MaySendDatagram, MaySendDatagramOn, hd, hs] at h
  have hh := h p hp
  have hdc : DcidAllowed s none dcid ∧ scid = s.localScid ∧ (s.firstFlight = true → 8 ≤ dcid.length) := by
    rcases hlong with hpt | hpt | hpt <;>
      · rw [hpt] at hh
        exact ⟨hh.2.1, hh.1, hh.2.2⟩
  refine ⟨hdc.2.1, ?_, hdc.2.2 hf⟩
  rcases hdc.1 with h1 | h1
  · exact h1
  · exact absurd hf (by rw [h1.1]; simp)

/-- §7.2, line 2380: "Any further changes to the Destination Connection ID are
    only permitted if the values are taken from NEW_CONNECTION_ID frames."  Once
    the first flight is over the rule is exactly that, so with WP4's set supplied
    a datagram may carry either the adopted connection ID or one the peer
    issued, and nothing else. -/
theorem sendHeader_after_firstFlight {s : State} {pt : PacketType} {dcid scid : Cid}
    {cids : List Cid} (hf : s.firstFlight = false)
    (hlong : pt = .initial ∨ pt = .zeroRtt ∨ pt = .handshake) :
    SendHeader s pt dcid scid (some cids) ↔
      (scid = s.localScid ∧ (s.dcidSent = some dcid ∨ dcid ∈ cids)) := by
  rcases hlong with rfl | rfl | rfl <;>
    simp [SendHeader, DcidAllowed, hf]

/-! ## 9. Examples (scenarios from the text) -/

section Examples

private def C1 : Cid := [0xc1]
private def S1 : Cid := [0x51]
private def S2 : Cid := [0x52]
private def S3 : Cid := [0x53]
/-- A connection ID the server issued later, in a NEW_CONNECTION_ID frame. -/
private def S4 : Cid := [0x54]
/-- An eight-byte first Destination Connection ID (§7.2, line 2340). -/
private def S1big : Cid := List.replicate 8 0x51

/-- Figure 7: the client sends `Initial: DCID=S1, SCID=C1`. -/
private def cli0 : State := initClient C1 S1
/-- The server before it has heard anything. -/
private def srv0 : State := initServer S3

-- §7.2, line 2340: the client's first Destination Connection ID must be at
-- least 8 bytes; S1 is one byte, so this is a bad header …
example : sendHeader cli0 .initial S1 C1 = false := by decide
-- … whereas the same client with an 8-byte value may send it.
private def cli0big : State := initClient C1 S1big
example : sendHeader cli0big .initial S1big C1 = true := by decide
-- §7.2, line 2341: until a packet is received from the server the client uses
-- the same value; another 8-byte value is not permitted …
example : sendHeader cli0big .initial (List.replicate 8 0x99) C1 = false := by decide
-- … and the Source Connection ID is the one the client chose (line 2357).
example : sendHeader cli0big .initial S1big S2 = false := by decide

-- The same rules as the component's `MaySendDatagram` field, which is what
-- WP12 and the harness drive (K-1).  One datagram of long-header packets:
private def dgram (pts : List PacketType) (dcid scid : Cid) : OutDatagram :=
  { size := 1200, packets := pts.map (fun pt => ⟨pt, [.ping]⟩),
    dcid := some dcid, scid := some scid }
example : component.maySendDatagram cli0 (dgram [.initial] S1 C1) = false := by decide
example : component.maySendDatagram cli0big (dgram [.initial, .zeroRtt] S1big C1)
    = true := by decide
-- §7.2, line 2361: a 0-RTT packet of the first flight uses the same pair.
example : component.maySendDatagram cli0big (dgram [.zeroRtt] (List.replicate 8 0x99) C1)
    = false := by decide
-- `Core`: `none` means "the rule being checked does not look at them", so a
-- datagram that carries no connection IDs is not judged on them.
example : component.maySendDatagram cli0 { size := 1200, packets := [⟨.initial, [.ping]⟩] }
    = true := by decide

-- Line 2380 does not reopen the first flight: a client that has heard nothing
-- from the server may use no other value, whatever the peer has issued.
example : maySendDatagramOn (some [S4]) cli0big (dgram [.initial] S4 C1) = false := by decide

-- Figure 7: `<- Initial: DCID=C1, SCID=S3`.  The client adopts S3.
private def cli1 : State := cli0.adoptScid S3
example : component.step cli0 (.recvHeader .initial C1 S3) = .ok cli1 [.dcidChanged S3] := by decide
example : cli1.dcidSent = some S3 ∧ cli1.dcidChanges = 1 := by decide

-- §7.2, line 2380, and K-3: after the first flight the Destination Connection
-- ID may also be one the peer issued in a NEW_CONNECTION_ID frame, so with the
-- set unknown the rule accepts S4 …
example : sendHeader cli1 .handshake S4 C1 = true := by decide
example : component.maySendDatagram cli1 (dgram [.handshake] S4 C1) = true := by decide
-- … with the set supplied and empty it does not …
example : maySendDatagramOn (some []) cli1 (dgram [.handshake] S4 C1) = false := by decide
-- … and with S4 among the connection IDs the server issued, it does again.
example : maySendDatagramOn (some [S4]) cli1 (dgram [.handshake] S4 C1) = true := by decide
-- The adopted connection ID is always permitted (line 2333).
example : maySendDatagramOn (some []) cli1 (dgram [.handshake] S3 C1) = true := by decide
-- Short headers carry no Source Connection ID and no §7.2 rule of this file.
example : component.maySendDatagram cli1 (dgram [.oneRtt] S4 C1) = true := by decide

-- §7.2, line 2371: "Once a client has received a valid Initial packet from the
-- server, it MUST discard any subsequent packet it receives on that connection
-- with a different Source Connection ID."
example : component.step cli1 (.recvHeader .initial C1 S2) = .drop := by decide
example : component.accepts cli1 (.recvHeader .initial C1 S2) (.ok cli1 []) = false := by decide
-- The same Source Connection ID again is fine (§17.2.2, line 6365: "A server
-- MAY send multiple Initial packets").
example : component.step cli1 (.recvHeader .initial C1 S3) = .ok cli1 [] := by decide

-- Figure 8: a Retry intervenes.  `<- Retry: DCID=C1, SCID=S2`, then
-- `Initial: DCID=S2, SCID=C1 ->`, then `<- Initial: DCID=C1, SCID=S3`.
private def cliR1 : State := cli0.adoptRetryScid S2
private def cliR2 : State := cliR1.adoptScid S3
example : component.step cli0 (.recvHeader .retry C1 S2) = .ok cliR1 [.dcidChanged S2] := by decide
example : component.step cliR1 (.recvHeader .initial C1 S3) = .ok cliR2 [.dcidChanged S3] := by decide
-- Two changes, which is what line 2368 permits with a Retry, and no more:
example : cliR2.dcidChanges = 2 ∧ cliR2.retryScid = some S2 := by decide
-- §17.2.5.2, line 6621 / §7.2, line 2376: a second Retry is discarded.
example : component.step cliR1 (.recvHeader .retry C1 S1) = .drop := by decide
example : component.step cliR2 (.recvHeader .retry C1 S1) = .drop := by decide

-- Figure 7 at the server: `Initial: DCID=S1, SCID=C1 ->`.
private def srv1 : State := { (srv0.adoptScid C1) with originalDcid := some S1 }
example : component.step srv0 (.recvHeader .initial S1 C1) = .ok srv1 [.dcidChanged C1] := by decide
-- §7.2, line 2381: a subsequent Initial with a different Source Connection ID
-- MUST be discarded.
example : component.step srv1 (.recvHeader .initial S1 S2) = .drop := by decide

-- §7.3, Figure 7: the server reports original_destination_connection_id = S1
-- and initial_source_connection_id = S3, and no retry_source_connection_id.
private def fig7Params : Params :=
  { TransportParams.defaults with
      originalDestinationConnectionId := some (bytes S1),
      initialSourceConnectionId := some (bytes S3) }
example : authOutcomes cli1 ⟨.client, some fig7Params⟩
    = [.ok { cli1 with peerParams := some fig7Params } [.peerParams fig7Params]] := by decide
-- The same parameters after a Retry are wrong: retry_source_connection_id is
-- missing (§7.3, line 2436), so both error codes are permitted and nothing else.
example : authOutcomes cliR2 ⟨.client, some fig7Params⟩
    = [.error .transportParameterError, .error .protocolViolation] := by decide

-- §7.3, Figure 8: with the Retry reported, the same handshake is accepted.
private def fig8Params : Params :=
  { fig7Params with retrySourceConnectionId := some (bytes S2) }
example : authOutcomes cliR2 ⟨.client, some fig8Params⟩
    = [.ok { cliR2 with peerParams := some fig8Params } [.peerParams fig8Params]] := by decide
-- … and §7.3, line 2439: reporting a Retry that did not happen is an error.
example : authOutcomes cli1 ⟨.client, some fig8Params⟩
    = [.error .transportParameterError, .error .protocolViolation] := by decide
-- §7.3, line 2428: a missing initial_source_connection_id is
-- TRANSPORT_PARAMETER_ERROR, with no second alternative.
example : authOutcomes cli1 ⟨.client, some { fig7Params with initialSourceConnectionId := none }⟩
    = [.error .transportParameterError] := by decide
-- At the server the client reports only initial_source_connection_id = C1.
private def cliParams : Params :=
  { TransportParams.defaults with initialSourceConnectionId := some (bytes C1) }
private def badParams : Params :=
  { TransportParams.defaults with initialSourceConnectionId := some (bytes S2) }
example : authOutcomes srv1 ⟨.server, some cliParams⟩
    = [.ok { srv1 with peerParams := some cliParams } [.peerParams cliParams]] := by decide
-- A client that reports the wrong value is rejected (§7.3, line 2442).
example : authOutcomes srv1 ⟨.server, some badParams⟩
    = [.error .transportParameterError, .error .protocolViolation] := by decide

-- §17.2.2.1: the client discards its Initial keys when it sends its first
-- Handshake packet, and then drops Initial packets (Figure 5's second flight).
private def cliH : State := cli1.discardKeys .initial
example : component.step cli1 (.sentPacket .handshake) = .ok cliH [.keysDiscarded .initial] := by
  decide
example : component.step cliH (.recvHeader .initial C1 S3) = .drop := by decide
example : component.accepts cliH (.recvCrypto .initial 0 10) .drop = true := by decide
-- A server does the same when it first receives a Handshake packet.
example : component.step { srv1 with read := { srv1.read with handshake := .present } }
      (.recvHeader .handshake C1 C1)
    = .ok ({ srv1 with read := { srv1.read with handshake := .present } }.discardKeys .initial)
        [.keysDiscarded .initial] := by decide

-- §5.2.1, line 1895 / §12.2, line 4622: a packet whose keys are not yet
-- available may be buffered or dropped — both, and only those two.
example : component.accepts cli0 (.recvHeader .handshake C1 S3) (.ok cli0 []) = true := by decide
example : component.accepts cli0 (.recvHeader .handshake C1 S3) .drop = true := by decide

-- §7, line 2167 and §7.5: CRYPTO data is delivered in order.  Bytes [10,20)
-- arrive first and are buffered; [0,10) then completes the prefix and all 20
-- bytes go to TLS at once.
private def cliB : State := (cli0.setStream .initial ((cli0.stream .initial).recv 10 10))
example : component.step cli0 (.recvCrypto .initial 10 10) = .ok cliB [] := by decide
example : bufferedBytes (cliB.stream .initial).buf = 10 := by decide
example : component.step cliB (.recvCrypto .initial 0 10)
    = .ok (cliB.setStream .initial ((cliB.stream .initial).recv 0 10))
        [.deliverCrypto .initial 0 20] := by decide
example : ((cliB.stream .initial).recv 0 10).delivered = 20 := by decide

-- §7.5, line 2703: an endpoint MUST be able to buffer at least 4096 bytes of
-- out-of-order data, which is what `Inv` demands of `bufLimit` …
example : Inv (initClient C1 S1) := by
  refine ⟨by simp [initClient], by simp [initClient], fun l => ?_⟩
  cases l <;> exact Crypto.WF_default
-- … and line 2713: past the limit, an endpoint that does not expand its buffer
-- MUST close with CRYPTO_BUFFER_EXCEEDED — but expanding is also permitted.
-- (A limit of 8 stands in for 4096 here so that `decide` stays small; nothing
-- in the rules depends on the value.)
private def cliSmall : State := { initClient C1 S1 with bufLimit := 8 }
example : component.accepts cliSmall (.recvCrypto .initial 1 8)
    (.ok (cliSmall.setStream .initial ((cliSmall.stream .initial).recv 1 8)) []) = true := by
  decide
example : component.accepts cliSmall (.recvCrypto .initial 1 9)
    (.error .cryptoBufferExceeded) = true := by decide
example : component.accepts cliSmall (.recvCrypto .initial 1 9)
    (.ok (cliSmall.setStream .initial ((cliSmall.stream .initial).recv 1 9)) []) = true := by
  decide
-- Nothing else is permitted there.
example : component.accepts cliSmall (.recvCrypto .initial 1 9) .drop = false := by decide
-- §7.5, line 2716: once the handshake is complete the same overflow may be
-- discarded from here on, or closed with CRYPTO_BUFFER_EXCEEDED — and, by line
-- 2707, still simply buffered (NOTE 15).  All three, and nothing else.
private def cliSmallDone : State := { cliSmall with complete := true }
example : component.outcomes cliSmallDone (.recvCrypto .initial 1 9) =
    [.ok (cliSmallDone.setStream .initial
            { cliSmallDone.stream .initial with discarding := true })
         [.cryptoDiscarding .initial],
     .ok (cliSmallDone.setStream .initial ((cliSmallDone.stream .initial).recv 1 9)) [],
     .error .cryptoBufferExceeded] := by decide
-- and once it is discarding, a later frame is acknowledged and ignored, never
-- dropped (line 2719: "Packets containing discarded CRYPTO frames MUST be
-- acknowledged") — but the same sentence's close is still on the table, because
-- it is granted per frame (NOTE 18).
private def cliDiscarding : State :=
  cliSmallDone.setStream .initial { cliSmallDone.stream .initial with discarding := true }
example : component.outcomes cliDiscarding (.recvCrypto .initial 1 9) =
    [.ok cliDiscarding [], .error .cryptoBufferExceeded] := by decide
example : component.accepts cliDiscarding (.recvCrypto .initial 1 9) .drop = false := by decide

-- §19.6, line 7545: offset + length above 2^62-1 is FRAME_ENCODING_ERROR or
-- CRYPTO_BUFFER_EXCEEDED, and nothing else.
example : component.outcomes cli0 (.recvCrypto .initial (2 ^ 62 - 1) 1)
    = [.error .frameEncodingError, .error .cryptoBufferExceeded] := by decide
example : component.accepts cli0 (.recvCrypto .initial (2 ^ 62 - 2) 1)
    (.error .frameEncodingError) = false := by decide

-- NOTE 10 / K-2: why the `recvHeader` contract is a hard requirement on the
-- endpoint.  With the read keys present, a server Initial *mandates* the change
-- of Destination Connection ID: leaving the state alone is not permitted, and
-- neither is dropping the packet (§7.2, line 2332 and line 2371).  A
-- `recvHeader` fired before protection was removed would therefore let one
-- forged packet dictate the client's connection ID.
example : cli0.read.get .initial = .present := by decide
example : component.outcomes cli0 (.recvHeader .initial C1 S3)
    = [.ok (cli0.adoptScid S3) [.dcidChanged S3]] := by decide
example : component.accepts cli0 (.recvHeader .initial C1 S3) (.ok cli0 []) = false := by decide
example : component.accepts cli0 (.recvHeader .initial C1 S3) .drop = false := by decide

-- §19.20 / K-4: a client that receives HANDSHAKE_DONE before its own handshake
-- completes.  The text gives the receiver no rule, so both ignoring it and
-- closing the connection are permitted, and nothing else is.
example : cli1.complete = false := by decide
example : component.outcomes cli1 .recvHandshakeDone
    = [.ok cli1 [], .error .protocolViolation] := by decide
example : component.step cli1 .recvHandshakeDone = .ok cli1 [] := by decide
example : component.accepts cli1 .recvHandshakeDone .drop = false := by decide

-- §19.20: only a server whose handshake is complete may send HANDSHAKE_DONE.
example : component.maySend srv1 .handshakeDone = false := by decide
example : component.maySend { srv1 with complete := true } .handshakeDone = true := by decide
example : component.maySend { cli1 with complete := true } .handshakeDone = false := by decide

-- §17.2.3, line 6476: a client may send 0-RTT packets until it processes a
-- 1-RTT packet from the server.
private def cli0rtt : State :=
  { cli1 with write := { cli1.write with zeroRtt := .present } }
example : component.maySendPacket cli0rtt ⟨.zeroRtt, [.ping]⟩ = true := by decide
example : component.maySendPacket
    ((cli0rtt.sawOneRtt)) ⟨.zeroRtt, [.ping]⟩ = false := by decide
-- A server never sends them.
example : component.maySendPacket
    { srv1 with write := { srv1.write with zeroRtt := .present } } ⟨.zeroRtt, [.ping]⟩
    = false := by decide

-- §19.6: a CRYPTO frame may only carry bytes TLS handed over, and the same
-- frame may be re-sent afterwards (§12.4, line 4936).
private def cliTls : State :=
  cli0.setStream .initial { cli0.stream .initial with handed := 100 }
example : component.maySendPacket cliTls ⟨.initial, [.crypto 0 (bytes (List.replicate 10 0))]⟩
    = true := by decide
example : component.maySendPacket cliTls ⟨.initial, [.crypto 95 (bytes (List.replicate 10 0))]⟩
    = false := by decide
-- After the Initial keys are gone, no Initial packet may be sent at all
-- (§17.2.2.1, line 6398).
example : component.maySendPacket (cliTls.discardKeys .initial) ⟨.initial, [.ping]⟩ = false := by
  decide
-- §17.2.2, line 6378: "The first CRYPTO frame sent always begins at an offset
-- of 0" — so with nothing sent yet, offset 50 is refused …
example : component.maySendPacket cliTls ⟨.initial, [.crypto 50 (bytes (List.replicate 10 0))]⟩
    = false := by decide
-- … and once the first frame has gone out, a continuation at 10 is fine (a
-- ClientHello spanning packets, or line 6389's HelloRetryRequest continuation).
private def cliSent : State :=
  (component.step cliTls (.sentCrypto .initial 0 10)).next cliTls
example : (cliSent.stream .initial).sentNext = 10 := by decide
example : component.maySendPacket cliSent ⟨.initial, [.crypto 10 (bytes (List.replicate 10 0))]⟩
    = true := by decide
-- The mark only moves forward, so a retransmission of the first frame after a
-- later one has been sent is still permitted (§13.3).
example : component.maySendPacket cliSent ⟨.initial, [.crypto 0 (bytes (List.replicate 10 0))]⟩
    = true := by decide

-- §12.4, line 4936: the same frame is still sendable once TLS has handed over
-- more, which is what a retransmission after loss needs (§13.3).
private def cliTls2 : State :=
  cli0.setStream .initial { cli0.stream .initial with handed := 400 }
example : component.maySendPacket cliTls2 ⟨.initial, [.crypto 0 (bytes (List.replicate 10 0))]⟩
    = true := by decide
-- §19.6, line 7512: CRYPTO "can be sent in all packet types except 0-RTT", and a
-- 1-RTT CRYPTO frame is measured against the 1-RTT stream, not the Initial one.
private def cliOneRtt : State :=
  { (cliTls.setStream .oneRtt { cliTls.stream .oneRtt with handed := 7 }) with
      write := { cliTls.write with oneRtt := .present } }
example : component.maySendPacket cliOneRtt ⟨.oneRtt, [.crypto 0 (bytes (List.replicate 7 0))]⟩
    = true := by decide
example : component.maySendPacket cliOneRtt ⟨.oneRtt, [.crypto 0 (bytes (List.replicate 8 0))]⟩
    = false := by decide
-- §17.2.3, line 6476 is the exact rule, and it is not handshake completion: a
-- complete client may still send 0-RTT until it processes a 1-RTT packet from
-- the server (NOTE 9).
private def cli0rttDone : State := { cli0rtt with complete := true }
example : component.maySendPacket cli0rttDone ⟨.zeroRtt, [.ping]⟩ = true := by decide
example : component.maySendPacket cli0rttDone.sawOneRtt ⟨.zeroRtt, [.ping]⟩ = false := by decide

-- §20.1: a TLS alert becomes CRYPTO_ERROR 0x100 + alert, and nothing else.
example : component.outcomes cli0 (.tlsAlert 0x2f) = [.error (.cryptoError 0x2f)] := by decide
example : (TransportError.cryptoError 0x2f).code = 0x12f := by decide

-- Following an implementation we cannot see inside: the harness sees only that
-- something was dropped.
example : component.track cli1 (.recvHeader .initial C1 S2) .drop = some cli1 := by decide
-- NOTE 16: `Effect.cryptoDiscarding` is what keeps the two §7.5 `ok` outcomes
-- apart, so an endpoint that starts discarding can be followed exactly …
example : component.track cliSmallDone (.recvCrypto .initial 1 9)
      (.ok [.cryptoDiscarding .initial])
    = some (cliSmallDone.setStream .initial
              { cliSmallDone.stream .initial with discarding := true }) := by decide
-- … and a harness that sees only "processed, nothing visible" is left with the
-- one candidate that buffered the frame anyway.
example : (component.trackSet [cliSmallDone] (.recvCrypto .initial 1 9)
      (Obs.ok []).matchesLoosely).length = 1 := by decide
-- A "processed with no visible effect" observation on a packet whose keys are
-- missing leaves two candidate states — here they coincide.
example : component.trackSet [cli0] (.recvHeader .handshake C1 S3) (Obs.ok []).matchesLoosely
    = [cli0] := by decide

/-! ### §7.1, Figure 5 (line 2257): the 1-RTT handshake at the client

`Initial[0]: CRYPTO[CH] ->`, `<- Initial[0]: CRYPTO[SH]`,
`<- Handshake[0]: CRYPTO[EE, CERT, CV, FIN]`, `Handshake[0]: CRYPTO[FIN] ->`,
`<- 1-RTT[1]: HANDSHAKE_DONE`.  Only the events this component sees are
replayed; the packet numbers and the ACKs are WP3's.  The byte counts are tiny
so that `decide` stays small — nothing in the rules depends on them. -/

/-- Run a list of events through the reference implementation. -/
private def run (s : State) : List Event → State
  | [] => s
  | e :: es => run ((component.step s e).next s) es

private def fig5 : List Event :=
  [ .tlsSend .initial 3,                -- TLS hands over the ClientHello
    .sentPacket .initial,                -- Initial[0]: CRYPTO[CH] ->
    .recvHeader .initial C1 S3,          -- <- Initial[0]: CRYPTO[SH]
    .recvCrypto .initial 0 3,
    .tlsKeys .read .handshake, .tlsKeys .write .handshake,
    .recvHeader .handshake C1 S3,        -- <- Handshake[0]: CRYPTO[EE, CERT, CV, FIN]
    .recvCrypto .handshake 0 5,
    .tlsSend .handshake 4,
    .sentPacket .handshake,              -- Handshake[0]: CRYPTO[FIN] ->
    .tlsComplete,
    .tlsKeys .read .oneRtt, .tlsKeys .write .oneRtt,
    .recvHeader .oneRtt C1 [],           -- <- 1-RTT[1]: HANDSHAKE_DONE
    .recvHandshakeDone ]

private def fig5End : State := run cli0 fig5

-- The client adopted the server's connection ID once and once only (§7.2),
-- gave TLS every CRYPTO byte in order (§7), discarded its Initial keys when
-- it sent its first Handshake packet (§17.2.2.1) and is now confirmed (§19.20).
example : fig5End.dcidSent = some S3 ∧ fig5End.dcidChanges = 1 := by decide
example : (fig5End.stream .initial).delivered = 3 := by decide
example : (fig5End.stream .handshake).delivered = 5 := by decide
example : fig5End.write.get .initial = .discarded ∧ fig5End.read.get .initial = .discarded := by
  decide
example : fig5End.complete = true ∧ fig5End.confirmed = true := by decide
-- An Initial packet arriving after that is dropped, and stays dropped.
example : component.step fig5End (.recvHeader .initial C1 S3) = .drop := by decide
-- The client still may not send HANDSHAKE_DONE itself (§19.20, line 8207).
example : component.maySend fig5End .handshakeDone = false := by decide

end Examples

/-! ## 10. Coverage and notes

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §7 (2167) | "QUIC provides reliable, ordered delivery of the cryptographic handshake data" | `Crypto.recv`, `Effect.deliverCrypto`, `deliverCrypto_contiguous` |
| §7 (2169) | "The cryptographic handshake MUST provide the following properties" (authenticated key exchange, transport parameters, ALPN) | out of scope: RFC 9001 and TLS; `Event.tls*` is the interface those properties are assumed of |
| §7 (2200) | CRYPTO offsets "start from zero in each packet number space" | `Streams`, one `Crypto` per `CryptoLevel`, each starting at 0 |
| §7 (2204) | Figure 4, the simplified handshake | examples |
| §7 (2225) | "Endpoints can use packets sent during the handshake to test for Explicit Congestion Notification (ECN) support" | out of scope: ECN is WP14 Reliability's (§13.4); nothing here constrains which packets carry ECN counts |
| §7 (2231) | "Endpoints MUST explicitly negotiate an application protocol" | out of scope: ALPN is inside TLS |
| §7.1 (2264) | "Multiple QUIC packets -- even of different packet types -- can be coalesced into a single UDP datagram", and the server's first flight | out of scope: coalescing is WP12's (`Spec.OutDatagram.packets`); this component sees one packet at a time through `Event.recvHeader` |
| §7.1 (2257, 2289) | Figures 5 and 6, the 1-RTT and 0-RTT flows | examples: `fig5` replays Figure 5 event by event at the client; Figure 6 differs only in 0-RTT, covered by the `MaySendPacket` examples |
| §7.2 (2322) | the long header's two connection IDs | `Event.recvHeader`, `SendHeader` |
| §7.2 (2332) | "After processing the first Initial packet, each endpoint sets the Destination Connection ID field in subsequent packets it sends to the value of the Source Connection ID field that it received" | `State.adoptScid`, `HdrStep.cliInitialFirst`, `HdrStep.srvInitialFirst`.  "After processing" is the contract on `Event.recvHeader`, not a guard in `HdrStep`; NOTE 10 |
| §7.2 (2337) | the client's first DCID is unpredictable and "MUST be at least 8 bytes in length" | `SendHeader` (length); unpredictability is not a property of a trace.  **`SendHeader` is a free-standing predicate, not a field of `component`**, so a harness driving the `Component` record alone does not check it (NOTE 6) |
| §7.2 (2341) | "Until a packet is received from the server, the client MUST use the same Destination Connection ID value on all packets" | `SendHeader` (`s.dcidSent = some dcid`, which only `adoptScid`/`adoptRetryScid` change).  **`SendHeader` is a free-standing predicate, not a field of `component`**, so a harness driving the `Component` record alone does not check it (NOTE 6) |
| §7.2 (2345) | the first DCID determines the Initial keys, which change after a Retry | out of scope: RFC 9001 §5.2 |
| §7.2 (2357) | "The client populates the Source Connection ID field with a value of its choosing" | `State.localScid`, `SendHeader`.  **`SendHeader` is a free-standing predicate, not a field of `component`**, so a harness driving the `Component` record alone does not check it (NOTE 6) |
| §7.2 (2361) | "The first flight of 0-RTT packets use the same Destination Connection ID and Source Connection ID values as the client's first Initial packet" | `SendHeader` covers `.zeroRtt` with the same `dcidSent`/`localScid`.  **`SendHeader` is a free-standing predicate, not a field of `component`**, so a harness driving the `Component` record alone does not check it (NOTE 6) |
| §7.2 (2365) | "Upon first receiving an Initial or Retry packet from the server, the client uses the Source Connection ID supplied by the server as the Destination Connection ID"; "twice during connection establishment" | `HdrStep.cliInitialFirst`, `HdrStep.cliRetryFirst`, `dcidChanges_bound` |
| §7.2 (2371) | "Once a client has received a valid Initial packet from the server, it MUST discard any subsequent packet it receives on that connection with a different Source Connection ID" | `HdrStep.cliInitialOther`, `HdrStep.cliHandshakeOther` |
| §7.2 (2376) | "A client MUST change the Destination Connection ID … in response to only the first received Initial or Retry packet" | `HdrStep.cliRetryLate`, `dcidChanges_le_two`, `dcidChanges_le_one_of_no_retry` |
| §7.2 (2378) | "A server MUST set the Destination Connection ID it uses for sending packets based on the first received Initial packet" | `HdrStep.srvInitialFirst` |
| §7.2 (2380) | "Any further changes … are only permitted if the values are taken from NEW_CONNECTION_ID frames" | out of scope: WP4 ConnIds owns NEW_CONNECTION_ID; `SendHeader` covers only long-header packets, see NOTE 6 |
| §7.2 (2381) | "if subsequent Initial packets include a different Source Connection ID, they MUST be discarded" | `HdrStep.srvInitialOther`, `HdrStep.cliInitialOther` |
| §7.2 (2387) | the DCID can change over the connection's life (migration) | out of scope: WP10 Migration |
| §7.3 (2421) | "Endpoints MUST validate that received transport parameters match received Connection ID values" | `cidMismatch`, `ParamStep`, `cids_ok_iff` |
| §7.3 (2399) | "Each endpoint includes the value of the Source Connection ID field from the first Initial packet it sent in the initial_source_connection_id transport parameter" | `State.localScid`; the receive-side check is `cidMismatch` |
| §7.3 (2402) | a server includes the first Initial's DCID in original_destination_connection_id, "before sending the Retry packet" if there was one | `HdrStep.srvInitialFirst` records `originalDcid` once and never again, and `cidMismatch` checks the *peer* against it.  The mandate on the parameters **we** emit is not encoded: this component never models an outgoing parameter set (the bytes are opaque and WP1 owns the encoding).  NOTE 20 |
| §7.3 (2414) | "If it sends a Retry packet, a server also includes the Source Connection ID field from the Retry packet in retry_source_connection_id" | `Step.sentRetry` records `retryScid`; as with line 2402, only the receive-side check is encoded.  NOTE 20 |
| §7.3 (2418) | "The values provided by a peer … MUST match the values that an endpoint used in the Destination and Source Connection ID fields of Initial packets that it sent (and received, for servers)" | `cidMismatch`, `cids_ok_iff` |
| §7.3 (2428) | absence of initial_source_connection_id from either endpoint, or of original_destination_connection_id from the server: TRANSPORT_PARAMETER_ERROR | `missingCid`, `ParamStep.missing`, `authOutcomes_missing` |
| §7.3 (2433–2444) | the three "TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION" bullets | `cidMismatch`, `ParamStep.mismatchTpe`/`mismatchPv`, `authOutcomes_mismatch`; the three bullets split out by role and Retry in `cids_ok_client_noRetry`, `cids_ok_client_retry`, `cids_ok_server` |
| §7.3 (2446) | "If a zero-length connection ID is selected, the corresponding transport parameter is included with a zero-length value" | `optCid`: `some []` is a legal value and compares equal to a zero-length `Cid` |
| §7.3 (2449, 2479) | Figures 7 and 8 | examples; `cids_ok_client_noRetry` is Figure 7 and `cids_ok_client_retry` Figure 8 |
| §7.5 (2703) | "Implementations MUST support buffering at least 4096 bytes of data received in out-of-order CRYPTO frames" | `Inv` (`4096 ≤ s.bufLimit`) — **assumed of a conforming endpoint, not checked by any outcome**: `bufLimit` is a parameter of the state, so this MUST is a side condition on the states WP12 may build, and `step_inv` only preserves it.  The `cliSmall` examples deliberately use `bufLimit := 8`, a state for which `Inv` is false, so that `decide` stays small |
| §7.5 (2704) | "Endpoints MAY choose to allow more data to be buffered" | `State.bufLimit` is a parameter |
| §7.5 (2707) | "An endpoint's buffer size does not need to remain constant during the life of the connection" | `CryptoStep.expand`, which stays available after the handshake completes for exactly this reason (NOTE 15).  No event changes `bufLimit` itself: growing the buffer shows up as the frame being accepted, not as a new limit |
| §7.5 (2711) | "it can expand its buffer temporarily to complete the handshake" | `CryptoStep.expand` |
| §7.5 (2713) | "If an endpoint does not expand its buffer, it MUST close the connection with a CRYPTO_BUFFER_EXCEEDED error code" | `CryptoStep.overflowClose` |
| §7.5 (2716) | once complete, "it MAY discard that CRYPTO frame and all CRYPTO frames received in the future, or it MAY close the connection" | `CryptoStep.overflowDiscard`, `Crypto.discarding`, `CryptoStep.alreadyDiscarding` |
| §7.5 (2719) | "Packets containing discarded CRYPTO frames MUST be acknowledged" | those outcomes are `.ok`, never `.drop` |
| §17.2.2 (6341) | "Initial packets sent by the server MUST set the Token Length field to zero; clients that receive an Initial packet with a non-zero Token Length field MUST either discard the packet or generate a connection error of type PROTOCOL_VIOLATION" | out of scope: WP5 AddressValidation owns tokens |
| §17.2.2 (6351) | Initial packets are protected with connection- and version-specific keys | out of scope: RFC 9001 |
| §17.2.2 (6358) | "The client and server use the Initial packet type for any packet that contains an initial cryptographic handshake message.  This includes all cases where a new packet containing the initial cryptographic message needs to be created, such as the packets sent after receiving a Retry packet" | partly `cryptoLevelOf`/`levelOf`, which bind the Initial CRYPTO stream to the Initial packet type so a ClientHello can only travel there.  Which *message* TLS re-offers after a Retry is opaque (`Event.tlsSend` carries a length, not a message), so "a new packet containing the initial cryptographic message" is not checkable here; §17.2.5.3 line 6671 ("A client MUST use the same cryptographic handshake message") is WP5's |
| §17.2.2 (6364) | "A server sends its first Initial packet in response to a client Initial." | not encoded: a per-step predicate cannot require that something *happens* (PLAN §4b, "trace-level obligations").  `HdrStep.srvInitialFirst` is the step that records the client Initial; the obligation to answer it belongs to WP12's timed traces |
| §17.2.2 (6365) | "A server MAY send multiple Initial packets" | `HdrStep.cliInitialSame` |
| §17.2.2 (6369) | the Initial payload holds CRYPTO, ACK, PING, PADDING and CONNECTION_CLOSE 0x1c; other frames are "discard the packet as spurious or treat it as a connection error" | out of scope: WP3 FrameRules Table 3 |
| §17.2.2 (6376) | "The first packet sent by a client always includes a CRYPTO frame that contains the start or all of the first cryptographic handshake message.  The first CRYPTO frame sent always begins at an offset of 0" | second sentence: `cryptoFrameOk` (offset 0 while `sentNext = 0`), `Event.sentCrypto`, `first_crypto_at_zero`.  First sentence: **not encoded** — it constrains the client's very first packet, and the component has no "have we sent anything at all" state; requiring a CRYPTO frame in every first-flight Initial would wrongly reject the second packet of a ClientHello that spans packets.  WP12, which fires `sentPacket`, is where it belongs |
| §17.2.2 (6389) | a HelloRetryRequest makes the client send more Initials continuing at the matching offset | `Crypto.handed` and `Crypto.sentNext` are per level and only grow, so a continuation at a non-zero offset is permitted once the first frame has gone out (`cryptoFrameOk`); the TLS reason for it is opaque |
| §17.2.2.1 (6398) | "A client stops both sending and processing Initial packets when it sends its first Handshake packet" | `Step.sentHandshake`, `client_discards_on_first_handshake`, `initial_discarded_drop`, `no_packet_without_keys` |
| §17.2.2.1 (6399) | "A server stops sending and processing Initial packets when it receives its first Handshake packet" | `HdrStep.srvHandshakeDiscard`, `server_discards_on_first_handshake` |
| §17.2.2.1 (6403) | Initial keys are discarded along with loss recovery and congestion control state | keys: `State.discardKeys`; recovery state: out of scope (RFC 9002) |
| §17.2.2.1 (6407) | "Any data in CRYPTO frames is discarded - and no longer retransmitted - when Initial keys are discarded" | `CryptoStep.levelGone` (receive), `maySendCryptoAt` (send) |
| §17.2.3 (6415) | a 0-RTT packet carries early data "from the client to the server … prior to handshake completion" | `MaySendPacket` (client only), `HdrStep.cliZeroRtt`.  The "prior to handshake completion" half is description, not a rule: the rule that ends 0-RTT sending is line 6476, and `MaySendPacket` encodes that one, not completion.  NOTE 9 |
| §17.2.3 (6417) | "the server can accept or reject this early data" | `Event.tlsZeroRtt`, `Step.zeroRttAccepted`/`zeroRttRejected` |
| §17.2.3 (6463) | "Packet numbers for 0-RTT protected packets use the same space as 1-RTT protected packets." | out of scope: WP3 Ack owns packet number spaces (`PacketType.space` in `Core` already maps both to `.appData`) |
| §17.2.3 (6467) | "A client SHOULD attempt to resend data in 0-RTT packets after it sends a new Initial packet." | advice, not checkable here: the data in a 0-RTT packet is application data, which this component neither carries nor remembers, so nothing in its state can say whether a re-sent 0-RTT packet repeats what a Retry discarded.  `State.retrySeen` records the Retry; the retransmission itself is WP14 Reliability's and the application's |
| §17.2.3 (6469) | "New packet numbers MUST be used for any new packets that are sent" | out of scope: packet numbers are WP3 Ack's (`PnSpace`); this component's events carry no packet number |
| §17.2.3 (6473) | "A client only receives acknowledgments for its 0-RTT packets once the handshake is complete" | out of scope: WP3 Ack |
| §17.2.3 (6476) | "A client MUST NOT send 0-RTT packets once it starts processing 1-RTT packets from the server" | `State.processed1Rtt`, `HdrStep.cliOneRtt`, `MaySendPacket`, `zeroRtt_client_only` |
| §17.2.3 (6477) | "This means that 0-RTT packets cannot contain any response to frames from 1-RTT packets.  For instance, a client cannot send an ACK frame in a 0-RTT packet" | out of scope: WP3 FrameRules (`forbiddenIn0Rtt`, Table 3) forbids ACK in 0-RTT; this is a consequence of line 6476, which is encoded here |
| §17.2.3 (6480) | "An acknowledgment for a 1-RTT packet MUST be carried in a 1-RTT packet" | out of scope: WP3 Ack (`appData_ack_in_oneRtt`) |
| §17.2.3 (6483) | "A server SHOULD treat a violation of remembered limits (Section 7.4.1) as a connection error of an appropriate type" | advice, not checkable here: the remembered limits are WP1's (`TransportParams.zeroRttCompatible`) and a violation of them is a stream or connection flow-control event in WP2/WP9.  This component models no limit and no stream data, so it has no outcome the clause could constrain |
| §17.2.4 (6527) | "Once a client has received a Handshake packet from a server, it uses Handshake packets to send subsequent cryptographic handshake messages" | `MaySendPacket` (Handshake write keys), `HdrStep.cliHandshakeOk` |
| §17.2.4 (6531) | the Handshake header's connection IDs are as §7.2 | `SendHeader`, `HdrStep.cliHandshakeOther` |
| §17.2.4 (6536) | "Handshake packets have their own packet number space" | out of scope: WP3 Ack (`PnSpace`) |
| §17.2.4 (6540) | the payload holds CRYPTO, PING, PADDING, ACK and CONNECTION_CLOSE 0x1c; "Endpoints MUST treat receipt of Handshake packets with other frames as a connection error of type PROTOCOL_VIOLATION" | out of scope: WP3 FrameRules |
| §17.2.4 (6546) | "data in CRYPTO frames for Handshake packets is discarded … when Handshake protection keys are discarded" | `CryptoStep.levelGone`, `maySendCryptoAt`, driven by `Event.tlsDiscardKeys` |
| §19.6 (7512) | CRYPTO "can be sent in all packet types except 0-RTT" | `CryptoLevel` has no 0-RTT constructor; the frame-in-packet rule is WP3's |
| §19.6 (7513) | "The CRYPTO frame offers the cryptographic protocol an in-order stream of bytes" | `Crypto.recv`, `Effect.deliverCrypto` |
| §19.6 (7514) | CRYPTO frames "are not flow controlled" | no flow-control state here; §7.5's buffer limit is the only bound |
| §19.6 (7541) | "each encryption level is treated as a separate CRYPTO stream of data" | `Streams` |
| §19.6 (7545) | "The largest offset delivered on a stream … cannot exceed 2^62-1.  Receipt of a frame that exceeds this limit MUST be treated as a connection error of type FRAME_ENCODING_ERROR or CRYPTO_BUFFER_EXCEEDED" | `CryptoStep.tooLargeEncoding`/`tooLargeBuffer`, `maxCryptoOffset` |
| §19.6 (7552) | "The stream does not have an explicit end, so CRYPTO frames do not have a FIN bit" | `Crypto` has no final size |
| §19.20 (8195) | "The server uses a HANDSHAKE_DONE frame (type=0x1e) to signal confirmation of the handshake to the client" | `Step.doneClient`, `client_confirms_on_done` |
| §19.20 (8207) | "A HANDSHAKE_DONE frame can only be sent by the server.  Servers MUST NOT send a HANDSHAKE_DONE frame before completing the handshake" | `MaySend`, `maySend_handshakeDone_iff` |
| §19.20 (8208) | "A server MUST treat receipt of a HANDSHAKE_DONE frame as a connection error of type PROTOCOL_VIOLATION" | out of scope here: WP3 FrameRules `senderOf`/`mustReject`; `Step.doneServer` is deliberately silent |
| §10.2.3 (4056) and §9 (3281) | "the handshake is confirmed, as defined in section 4.1.2 of [QUIC-TLS]" | `State.confirmed`, `Step.completeServer`, `Step.doneClient`, `confirmed_complete` |
| §5.2.1 (1895) / §12.2 (4622) | a packet whose keys are unavailable MAY be dropped or buffered | `HdrStep.keysAbsentBuffer`/`keysAbsentDrop` |
| §17.2.5.2 (6621) | "A client MUST accept and process at most one Retry packet …  it MUST discard any subsequent Retry packets" | WP5 owns it; `HdrStep.cliRetryLate` agrees (both give `.drop`) |
| §17.2.5.3 (6652) | "The client copies the Source Connection ID field from the Retry packet to the Destination Connection ID field" | `HdrStep.cliRetryFirst` (and WP5's `retryAccept` for the token side) |
| §17.2.5.3 (6694) | "The connection IDs used on Initial and Retry packets … are copied to the transport parameters and validated as described in Section 7.3" | `ParamStep`, `cids_ok_iff` |

NOTES — ambiguities in the text and the readings encoded

1. **How many times a client may change its Destination Connection ID.**  Line
   2368 says a client "might have to change the connection ID … twice during
   connection establishment: once in response to a Retry, and once in response
   to an Initial packet from the server", while line 2376 says it "MUST change
   the Destination Connection ID it uses for sending packets in response to only
   the first received Initial or Retry packet".  Read literally the two
   sentences conflict.  Reading encoded: "the first received Initial or Retry"
   is per *connection attempt*, and a Retry starts a new attempt, so a change is
   permitted once in response to the first Retry and once in response to the
   first Initial from the server — at most twice, and at most once without a
   Retry.  That is `dcidChanges_bound` and its two corollaries.  A Retry
   arriving after the server's first Initial changes nothing (`cliRetryLate`),
   which agrees with §17.2.5.2 line 6621.

2. **Where §7.5's limit is measured.**  The text says "unable to buffer all data
   in a CRYPTO frame" without saying whether in-order data counts.  Reading
   encoded: the frame is first merged into the range set and the deliverable
   prefix handed to TLS, and only what is *left buffered* is compared with
   `bufLimit`.  An in-order frame of any size is therefore always accepted,
   which is what "buffering … data received in out-of-order CRYPTO frames"
   (line 2703) says the limit is about.

3. **Which §7.5 alternative is preferred.**  All of them are permitted
   (`outcomes` lists all of them), so `accepts` takes any; only the reference
   implementation `step` has to choose.  It prefers expanding during the
   handshake (line 2711 recommends it — "it can expand its buffer temporarily to
   complete the handshake") and discarding afterwards (line 2716 lists
   discarding first).  If ngtcp2 prefers the error, that is still inside `Step`.

4. **A CRYPTO frame below the delivered prefix.**  Retransmissions repeat data
   already given to TLS.  `Crypto.recv` merges them into the range set and
   `flush` drops whatever lies entirely below `delivered`, so they are a no-op
   and are neither re-delivered nor counted against the buffer.  The text does
   not spell this out; it follows from "reliable, ordered delivery".

5. **CRYPTO bytes are not modelled.**  An event carries an offset and a length,
   never the bytes, so the model cannot detect a peer that sends *different*
   bytes for the same offset.  The text does not make that a transport error
   either (it is TLS's problem), so nothing is lost; a `Ranges`-based state
   would have to become a byte map to see it.

6. **§7.2's send-side rules are not in `MaySendPacket`.**  `Spec.OutPacket` is
   `(ptype, frames)`, with no connection ID fields, so `SendHeader` is a
   free-standing predicate.  **Requested `Core` change:** give `OutPacket`
   optional `dcid`/`scid` fields (long headers have both, short headers only a
   DCID, and Version Negotiation neither), after which `SendHeader` folds into
   `MaySendPacket` and WP4/WP10 can state their connection ID choice rules
   there too.

7. **A HANDSHAKE_DONE frame reaching a client whose handshake is not yet
   complete.**  §19.20 forbids the *server* from sending it then, and a client
   that is not complete has no 1-RTT read keys, so the situation cannot arise on
   a conforming path.  The text gives the receiver no rule, so `Step.doneEarly`
   makes it a no-op rather than an error; this is what keeps `confirmed →
   complete` (`Inv`) true.  Treating it as PROTOCOL_VIOLATION would be stricter
   than the text.

8. **A server receiving HANDSHAKE_DONE.**  §19.20 line 8208 makes it
   PROTOCOL_VIOLATION, but that rule is WP3's (`FrameRules.senderOf` /
   `mustReject`), so `Step.doneServer` deliberately says nothing (`.ok s []`)
   rather than duplicating it.  An endpoint's behaviour is the conjunction of
   the components, so the error still stands.

9. **0-RTT rejection.**  The transport draft says only that the server "can
   accept or reject this early data" (line 6417).  Reading encoded: rejection
   discards the 0-RTT keys (RFC 9001 §4.9.3), after which `MaySendPacket`
   forbids 0-RTT packets through the ordinary key rule rather than through a
   separate prohibition.  §17.2.3's own stopping condition — "once it starts
   processing 1-RTT packets from the server" — is encoded literally and
   separately, because it is the sentence the draft actually states.

10. **"Successfully processes", and what `Event.recvHeader` means.**  Line 6399
    says a server stops processing Initial packets when it "receives" its first
    Handshake packet; RFC 9001 §4.9.1 says "successfully processes".  Reading
    "receives" literally would let an attacker's undecryptable packet kill the
    Initial keys, and §7.2's own rules are worded the careful way — line 2332
    "After processing the first Initial packet", line 2371 "a valid Initial
    packet", line 6476 "once it starts processing".

    Reading encoded: `Event.recvHeader` *is* the successful case.  It is fired
    only for a packet whose protection has been removed, which is a contract on
    WP12, written on the constructor.  Two consequences follow, and both are
    deliberate:

    * a packet at a level whose keys we do not have never becomes a
      `recvHeader` with those keys present, so `HdrStep.keysAbsentBuffer` /
      `keysAbsentDrop` cover it and nothing is discarded or adopted;
    * given the event, every §7.2 state change is *mandatory* — the branches of
      `cidOutcomes` are singletons.  That is right for a packet that has been
      authenticated, and it is why there is no "header seen, AEAD failed"
      outcome here: that is not an event of this component.

    A reviewer reading `HdrStep` without the contract will read
    `srvHandshakeDiscard`, `cliInitialFirst` and `cliOneRtt` as mandating a
    state change on a forged packet.  They do not, but only because of the
    contract, so WP12 must honour it: fire `recvHeader` after removing
    protection, never before.  If WP12 cannot arrange that, the fix is a second
    event (`recvUndecryptable`) rather than adding `.drop` to these arms, which
    would lose the MUSTs of lines 2371 and 2381.

11. **CRYPTO at a discarded level.**  A frame can only arrive in a packet, and a
    packet at a discarded level is dropped, so `CryptoStep.levelGone` is
    unreachable through a whole datagram.  It is kept because the frame-level
    event is what WP12 dispatches, and `.drop` is the outcome that matches
    "any data in CRYPTO frames is discarded".

12. **Keys are per level, not per key phase.**  Key update (RFC 9001 §6) is out
    of scope, so `KeyState` has no phase.  `Event.tlsDiscardKeys` is the hook
    RFC 9001 §4.9's other discards (Handshake keys at confirmation, 0-RTT keys
    at rejection) come through; the transport draft states only the Initial
    case, which this component drives itself.

13. **`sentPacket` and `sentRetry` are our own actions, not received frames.**
    They are events rather than `MaySend` rules because they move the state
    (§17.2.2.1's discard, §7.3's `retry_source_connection_id`).  WP12 fires them
    after a packet has actually been sent; they are never errors.

14. **`Event.recvHeader` for a 1-RTT packet.**  Short headers carry no Source
    Connection ID; the `scid` argument is ignored for `.oneRtt`, and §7.2's
    "different Source Connection ID" discard is applied only to the long-header
    types the sentence is about.

15. **Buffering past the limit after the handshake completes** (a change to an
    earlier reading of this file).  §7.5, line 2716 offers an endpoint that "is
    unable to buffer all data in a CRYPTO frame" two ways out, and this file
    used to offer only those two — discard forever, or CRYPTO_BUFFER_EXCEEDED.
    That made a MAY the *only* outcome.  Line 2707 says "An endpoint's buffer
    size does not need to remain constant during the life of the connection", so
    an endpoint that enlarges its buffer is not the endpoint line 2716 is about,
    and simply accepting the frame is permitted at every point in the
    connection.  `CryptoStep.expand` therefore lost its `s.complete = false`
    hypothesis and `outcomes` lists three alternatives past the limit once the
    handshake is complete.  `bufLimit` is the size the endpoint has *committed*
    to (the invariant keeps it at line 2703's 4096 or more); growing it is not
    an event of this component, so expanding shows up as the frame being
    accepted rather than as a change to `bufLimit`.

16. **The two `.ok` outcomes past a completed handshake's buffer limit are
    told apart by an effect.**  §7.5's "discard that CRYPTO frame and all CRYPTO
    frames received in the future" and NOTE 15's "buffer it anyway" both leave
    the connection open with nothing delivered, so without an effect they would
    share the observation `ok []` while leaving the endpoint in different states
    — the case PLAN §1 says to resolve with a distinguishing effect.
    `Effect.cryptoDiscarding` is that effect.  Like `keysDiscarded` and
    `peerParams` it is a model-level signal, not something the ngtcp2 API
    reports, so a harness that cannot see it uses `trackSet` and carries both
    candidate states.

17. **`Crypto.discarding` is per encryption level, not per endpoint.**  §7.5
    line 2716 speaks of "an endpoint" that is unable to buffer, and the model
    latches the decision on the level whose frame overflowed.  After the
    handshake completes only the 1-RTT stream can still receive CRYPTO, so no
    reachable trace tells the two readings apart; the per-level form is chosen
    because `bufLimit` is compared against one stream's buffer, which is where
    §7.5's "data received in out-of-order CRYPTO frames" lives.

18. **The §7.5 close is granted per frame.**  Line 2716 offers the discard and
    the CRYPTO_BUFFER_EXCEEDED close in one sentence, per CRYPTO frame the
    endpoint cannot buffer.  Electing the discard on one frame does not forfeit
    the close on the next, so `CryptoStep.discardingClose` keeps the error
    available while `discarding` is set.  An earlier version of this file
    offered only `.ok s []` there, which made a MAY the only outcome.

19. **A client receiving a 0-RTT packet.**  `HdrStep.cliZeroRtt` is guarded on
    the client holding 0-RTT *read* keys, which nothing in this component or in
    RFC 9001 ever gives it, so the arm is dead.  Its `.drop` is a convention for
    a state the text does not describe; nothing is read out of the text there,
    and `outcomes_ne` is the only reason it exists.

20. **§7.3 is encoded on the receive side only.**  Lines 2399, 2402 and 2414 are
    "each endpoint includes X in transport parameter Y" mandates about the
    parameters an endpoint *emits*; lines 2418–2444 are the checks it performs
    on the parameters it *receives*.  Only the second half is here.  The reason
    is that `Event.tlsPeerParams` carries opaque bytes and the encoding is WP1's:
    this component never constructs a parameter set, so it has nothing to
    constrain.  What it does instead is record `localScid`, `originalDcid` and
    `retryScid` faithfully, which is exactly what a send-side check would need.
    **Requested follow-up:** WP1 (or WP12) should add a `MaySend`-style
    predicate over an outgoing `TransportParams` asserting
    `initial_source_connection_id = localScid`,
    `original_destination_connection_id = originalDcid` and
    `retry_source_connection_id = retryScid`, reading those three fields from
    this component's state.  Without it an endpoint that reports the wrong
    connection IDs is caught only by its peer.

21. **No SHOULD in the assigned range becomes a `Recommended` clause.**  §7,
    §7.1–§7.3, §7.5, §17.2.2, §17.2.3, §17.2.4, §19.6 and §19.20 contain exactly
    two SHOULDs, both in §17.2.3 (lines 6467 and 6483).  Neither constrains an
    outcome or a frame this component models — one is about re-sending
    application data, the other about limits this component does not hold — so
    the coverage table carries them as `advice, not checkable here` with the
    reason, and there is no `Recommended` predicate here.
-/

end Quic.Spec.Handshake
