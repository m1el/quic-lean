import QuicModel.Spec.Endpoint.Dispatch

/-!
  WP12 "Endpoint", parts 2–3: **the receive pipeline** and the other four event
  families, as one total function from a state and an event to the list of
  permitted outcomes.

  The datagram pipeline, in order, with the sentence each stage enforces:

  1. the path is registered (so `PathValidation` has a handle for it) and the
     bytes are counted — §8.1, line 2776: "servers MUST count all of the payload
     bytes received in datagrams that are uniquely attributed to a single
     connection … This includes datagrams that contain packets that are
     successfully processed and datagrams that contain packets that are all
     discarded";
  2. `Termination`'s phase gate — §10.2.2, line 4023 (draining sends nothing)
     and §10.2.1, line 3965 (closing answers with CONNECTION_CLOSE).  Only the
     `active` phase goes on to parse;
  3. §14's size rules (`DatagramSize`), which is where §14.1 line 5727's "a
     server MUST discard an Initial packet … smaller than 1200 bytes" and
     §11.1 line 4485's MAY-discard live;
  4. version handling — `VersionNeg.Server` for a server, `VersionNeg.Client`
     for a client;
  5. for each coalesced packet: `Quic.decodePacket`, then `Handshake`'s key and
     connection-ID rules (fired **only** after successful unprotection —
     `Handshake` NOTE 10), then §9's receive rules (`Migration`), then §12.3's
     duplicate check (`Ack`), then frame by frame §12.4/§12.5 (`FrameRules`) and
     dispatch to the component that owns the frame's semantics;
  6. after the datagram: §10.1 line 3841's idle-timer restart, which the text
     conditions on the packet having been "received and processed successfully".

  §12.2, line 4622: "if the packet cannot be processed, an endpoint MUST discard
  the remainder of the datagram" — an undecryptable packet ends the loop and
  leaves `Effect.skippedRest` behind.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## 2a. Two more combinators

`gate` is the receive-pipeline's reading of a component's `.drop`: it discards
*this packet*, not the datagram, so the coalesced packets after it are still
processed.  The state it continues with is the one the gate started from, which
is exactly what `.drop` means ("nothing changes"), so `gate` is not a weakening
of any component. -/

def gateOut (s : State) (k : State → List Out) : Out → List Out
  | .ok s' fx => (k s').map (withFx fx)
  | .error c => [.error c]
  | .drop => [.ok s []]

def gate (s : State) (l : List Out) (k : State → List Out) : List Out :=
  l.flatMap (gateOut s k)

theorem gateOut_ne {s : State} {k : State → List Out} (hk : ∀ s, k s ≠ []) (o : Out) :
    gateOut s k o ≠ [] := by
  cases o with
  | ok s' fx => simpa [gateOut] using hk s'
  | error c => simp [gateOut]
  | drop => simp [gateOut]

theorem gate_ne {s : State} {l : List Out} {k : State → List Out} (hl : l ≠ [])
    (hk : ∀ s, k s ≠ []) : gate s l k ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t =>
    simp only [gate, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
    intro h
    exact absurd h (gateOut_ne hk a)

theorem gate_inv {s : State} {l : List Out} {k : State → List Out} (hs : Inv s)
    (hl : InvOk l) (hk : ∀ s, Inv s → InvOk (k s)) : InvOk (gate s l k) := by
  intro s' fx hm
  simp only [gate, List.mem_flatMap] at hm
  obtain ⟨o, ho, hmem⟩ := hm
  simp only [gateOut] at hmem
  cases o with
  | ok s0 fx0 =>
    have h0 : Inv s0 := hl _ _ ho
    simp only [List.mem_map] at hmem
    obtain ⟨o', ho', he⟩ := hmem
    cases o' with
    | ok x gx =>
      simp only [withFx, Outcome.ok.injEq] at he
      exact he.1 ▸ hk s0 h0 _ _ ho'
    | error c => simp [withFx] at he
    | drop => simp [withFx] at he
  | error c => simp at hmem
  | drop =>
    simp only [List.mem_singleton, Outcome.ok.injEq] at hmem
    exact hmem.1 ▸ hs

/-! ## 2b. Reading a packet header -/

def hdrPtype : Header → PacketType
  | .versionNegotiation .. => .versionNegotiation
  | .long .initial .. => .initial
  | .long .zeroRtt .. => .zeroRtt
  | .long .handshake .. => .handshake
  | .long .retry .. => .retry
  | .short .. => .oneRtt

def hdrDcid : Header → ByteArray
  | .versionNegotiation d _ => d
  | .long _ _ _ d _ _ _ => d
  | .short _ d => d

def hdrScid : Header → ByteArray
  | .versionNegotiation _ c => c
  | .long _ _ _ _ c _ _ => c
  | .short _ _ => .empty

/-- §12.3: the packet number the decoder should expect next in this space. -/
def expectedPnOf (s : State) (pt : PacketType) : Nat :=
  match pt.space with
  | none => 0
  | some sp => match (s.ack sp).largest with
    | none => 0
    | some m => m + 1

/-- Parse the packet at `pos`, using the packet number the space expects. -/
def parseOne (prot : Protection) (s : State) (buf : ByteArray) (pos : Nat) :
    Except PacketErr (Packet × Nat) :=
  match Quic.decodeHeader buf s.shortDcidLen pos with
  | .error e => .error (.header e)
  | .ok (hd, _) =>
    Quic.decodePacket prot buf s.shortDcidLen (expectedPnOf s (hdrPtype hd)) s.greaseQuicBit pos

/-- The sequence number of the connection ID of ours a packet was addressed to
    (§19.16, line 8050).  `0` — the handshake connection ID — when the value is
    not one we have issued, which is the conservative reading. -/
def dcidSeqOf (s : State) (d : ByteArray) : Nat :=
  match s.cidLocal.issued.find? (fun e => decide (e.cid = d.toList)) with
  | some e => e.seq
  | none => 0

/-! ## 2c. What a packet that cannot be parsed means

§5.2, line 1878: "Invalid packets that lack strong integrity protection, such as
Initial, Retry, or Version Negotiation, MAY be discarded."  §12.2, line 4622:
"if the packet cannot be processed, an endpoint MUST discard the remainder of
the datagram."  §17.2, line 6183 / §17.3.1: a clear fixed bit MUST be discarded.
§17.2 reserved bits and §12.4 line 4740's empty payload are PROTOCOL_VIOLATION;
a frame that will not parse is FRAME_ENCODING_ERROR (§12.4, line 4933). -/

def packetErrOutcomes (s : State) (isInitial : Bool) : PacketErr → List Out
  -- these leave the rest of the datagram unread (§12.2, line 4622)
  | .header _ | .lengthExceedsDatagram | .tooShortForSample | .decryptFailed
  | .fixedBitClear | .badVersionList | .badRetry => [.ok s [.skippedRest]]
  -- §17.2, line 6191 / §17.3.1, line 6297: reserved bits set.  §11.1, line 4485
  -- adds the MAY-discard for an Initial packet.
  | .reservedBits =>
    if isInitial then [.error .protocolViolation, .drop] else [.error .protocolViolation]
  | .emptyPayload =>
    if isInitial then [.error .protocolViolation, .drop] else [.error .protocolViolation]
  | .frame _ =>
    if isInitial then [.error .frameEncodingError, .drop] else [.error .frameEncodingError]

theorem packetErrOutcomes_ne (s : State) (b : Bool) (e : PacketErr) :
    packetErrOutcomes s b e ≠ [] := by
  cases e <;> simp only [packetErrOutcomes] <;> repeat' split
  all_goals simp

theorem packetErrOutcomes_inv {s : State} (hs : Inv s) (b : Bool) (e : PacketErr) :
    InvOk (packetErrOutcomes s b e) := by
  cases e <;> simp only [packetErrOutcomes] <;>
    first
      | exact InvOk.ok hs
      | (split <;>
          first
            | exact InvOk.append (InvOk.error _) InvOk.drop
            | exact InvOk.error _)

/-! ## 2d. Dispatching one frame to the component that owns it -/

/-- The encryption level a CRYPTO frame in this packet type belongs to
    (§19.6, line 7541: "each encryption level is treated as a separate CRYPTO
    stream of data"). -/
def cryptoLevelOf (pt : PacketType) : Option Handshake.CryptoLevel := Handshake.cryptoLevelOf pt

/-- §19.19: the reason a received CONNECTION_CLOSE carries. -/
def closeReasonOfFrame : Frame → Option Termination.CloseReason
  | .connectionClose err (some ft) _ => some (.transport (errorOfCode err) ft)
  | .connectionClose err none _ => some (.application err)
  | _ => none
where
  /-- §20.1: the transport error code, as the `TransportError` the model uses.
      Codes outside §20.1's table become `INTERNAL_ERROR`, which §11 line 4434
      makes an always-usable stand-in. -/
  errorOfCode : Nat → TransportError
    | 0x0 => .noError | 0x1 => .internalError | 0x2 => .connectionRefused
    | 0x3 => .flowControlError | 0x4 => .streamLimitError | 0x5 => .streamStateError
    | 0x6 => .finalSizeError | 0x7 => .frameEncodingError
    | 0x8 => .transportParameterError | 0x9 => .connectionIdLimitError
    | 0xa => .protocolViolation | 0xb => .invalidToken | 0xc => .applicationError
    | 0xd => .cryptoBufferExceeded | 0xe => .keyUpdateError | 0xf => .aeadLimitReached
    | 0x10 => .noViablePath
    | n => if 0x100 ≤ n ∧ n ≤ 0x1ff then .cryptoError (n - 0x100).toUInt8 else .internalError

/-- `PathValidation`'s effects, fed to the components that §8.2.3 line 3220 and
    §9 say must hear about them (`PathValidation` NOTES 10, `Migration` NOTES 1). -/
def pvEffects (mp : Migration.Path) : List PathValidation.Effect → State → List Out
  | [], s => keep s
  | .sendChallenge _ d :: rest, s =>
    bindAll [.ok s [Effect.sendPending (.pathChallenge d)]] (pvEffects mp rest)
  | .queueResponse _ d :: rest, s =>
    bindAll [.ok s [Effect.sendPending (.pathResponse d)]] (pvEffects mp rest)
  | .pathValidated q :: rest, s =>
    let m := (s.pathOfId q.id).getD mp
    bindAll (bindAll (stepMig s (.validationSucceeded m))
      (fun s1 => stepAv s1 (.pathValidated m.peer))) (pvEffects mp rest)
  | .pathFailed q :: rest, s =>
    let m := (s.pathOfId q.id).getD mp
    bindAll (stepMig s (.validationFailed m)) (pvEffects mp rest)

theorem pvEffects_ne (mp : Migration.Path) (fx : List PathValidation.Effect) (s : State) :
    pvEffects mp fx s ≠ [] := by
  induction fx generalizing s with
  | nil => simp [pvEffects, keep]
  | cons a t ih =>
    cases a with
    | sendChallenge p d =>
      exact bindAll_ne (by simp) (fun _ => ih _)
    | queueResponse p d =>
      exact bindAll_ne (by simp) (fun _ => ih _)
    | pathValidated q =>
      exact bindAll_ne (bindAll_ne (stepMig_ne _ _) (fun _ => stepAv_ne _ _)) (fun _ => ih _)
    | pathFailed q =>
      exact bindAll_ne (stepMig_ne _ _) (fun _ => ih _)

theorem pvEffects_inv {s : State} (hs : Inv s) (mp : Migration.Path)
    (fx : List PathValidation.Effect) : InvOk (pvEffects mp fx s) := by
  induction fx generalizing s with
  | nil => exact keep_inv hs
  | cons a t ih =>
    cases a with
    | sendChallenge p d => exact invOk_bindAll (InvOk.ok hs) (fun _ h => ih h)
    | queueResponse p d => exact invOk_bindAll (InvOk.ok hs) (fun _ h => ih h)
    | pathValidated q =>
      exact invOk_bindAll
        (invOk_bindAll (stepMig_inv hs _) (fun _ h => stepAv_inv h _)) (fun _ h => ih h)
    | pathFailed q => exact invOk_bindAll (stepMig_inv hs _) (fun _ h => ih h)

/-- A `PathValidation` step whose consequences for §9 and §8.1 are dispatched. -/
def pvThenOut (s : State) (mp : Migration.Path) :
    Outcome PathValidation.State PathValidation.Effect → List Out
  | .ok x fx =>
    (pvEffects mp fx (syncConfirmed { s with pv := x })).map (withFx (fx.map Effect.pv))
  | .error c => [.error c]
  | .drop => [.drop]

def stepPvThen (s : State) (mp : Migration.Path) (e : PathValidation.Event) : List Out :=
  (PathValidation.outcomes s.pv e).flatMap (pvThenOut s mp)

theorem pvThenOut_ne (s : State) (mp : Migration.Path)
    (o : Outcome PathValidation.State PathValidation.Effect) : pvThenOut s mp o ≠ [] := by
  cases o with
  | ok x fx => simpa [pvThenOut] using pvEffects_ne mp fx (syncConfirmed { s with pv := x })
  | error c => simp [pvThenOut]
  | drop => simp [pvThenOut]

theorem stepPvThen_ne (s : State) (mp : Migration.Path) (e : PathValidation.Event) :
    stepPvThen s mp e ≠ [] := by
  cases hh : PathValidation.outcomes s.pv e with
  | nil => exact absurd hh (PathValidation.outcomes_ne _ _)
  | cons a t =>
    simp only [stepPvThen, hh, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
    intro h
    exact absurd h (pvThenOut_ne s mp a)

theorem stepPvThen_inv {s : State} (hs : Inv s) (mp : Migration.Path)
    (e : PathValidation.Event) : InvOk (stepPvThen s mp e) := by
  intro s' fx hm
  simp only [stepPvThen, List.mem_flatMap] at hm
  obtain ⟨o, ho, hmem⟩ := hm
  simp only [pvThenOut] at hmem
  cases o with
  | ok x gx =>
    have hx : Inv (syncConfirmed { s with pv := x }) :=
      inv_setPv hs (PathValidation.step_inv _ _ _ _ hs.pv ((PathValidation.outcomes_iff _ _ _).mp ho))
    simp only [List.mem_map] at hmem
    obtain ⟨o', ho', he⟩ := hmem
    cases o' with
    | ok y hy =>
      simp only [withFx, Outcome.ok.injEq] at he
      exact he.1 ▸ pvEffects_inv hx mp gx _ _ ho'
    | error c => simp [withFx] at he
    | drop => simp [withFx] at he
  | error c => simp at hmem
  | drop => simp at hmem

/-- Frame by frame: the component that owns this frame's semantics.
    `FrameRules` has already decided that the frame is legal in this packet
    type (§12.4, line 4901); what is left is what the frame *means*. -/
def dispatchFrame (now : Time) (mp : Migration.Path) (pt : PacketType) (dcidSeq : Nat)
    (av : Bool) (f : Frame) (s : State) : List Out :=
  match f with
  | .padding _ | .ping => keep s
  | .ack largest _ first ranges _ =>
    match pt.space with
    | some sp => stepAck s sp (.recvAck largest first ranges.toList)
    | none => keep s
  | .resetStream id code fs => stepSt s (.stream ⟨id⟩ (.recv (.recvResetStream code fs)))
  | .stopSending id code => stepSt s (.stream ⟨id⟩ (.send (.recvStopSending code)))
  | .crypto off data =>
    match cryptoLevelOf pt with
    | some l => stepHs s (.recvCrypto l off data.size)
    | none => keep s
  | .newToken token => gate s (stepAv s (.recvNewToken token)) keep
  | .stream id off fin data => stepSt s (.stream ⟨id⟩ (.recv (.recvStream off data.size fin)))
  | .maxData v => stepSt s (.recvMaxData v)
  | .maxStreamData id v => stepSt s (.stream ⟨id⟩ (.send (.recvMaxStreamData v)))
  | .maxStreams dir v => stepSt s (.recvMaxStreams dir v)
  | .dataBlocked v => stepSt s (.recvDataBlocked v)
  | .streamDataBlocked id v => stepSt s (.stream ⟨id⟩ (.recv (.recvStreamDataBlocked v)))
  | .streamsBlocked dir v => stepSt s (.recvStreamsBlocked dir v)
  | .newConnectionId seq rpt cid token =>
    stepCidRemote s (.recvNewCid seq rpt cid.toList token.toList)
  | .retireConnectionId seq => stepCidLocal s (.recvRetireCid seq (some dcidSeq))
  | .pathChallenge d => stepPvThen s mp (.recvChallenge (s.pathOf mp) d)
  | .pathResponse d => stepPvThen s mp (.recvResponse (s.pathOf mp) d)
  | .connectionClose err ft reason =>
    match closeReasonOfFrame (.connectionClose err ft reason) with
    | some r => stepTerm s (.recvClose now s.pto r av)
    | none => keep s
  | .handshakeDone => stepHs s .recvHandshakeDone
  -- RFC 9221 §5: a DATAGRAM frame is delivered to the application and changes
  -- no transport state.  Out of the draft's scope, so nothing is modelled.
  | .datagram _ _ => keep s

theorem dispatchFrame_ne (now : Time) (mp : Migration.Path) (pt : PacketType) (d : Nat)
    (av : Bool) (f : Frame) (s : State) : dispatchFrame now mp pt d av f s ≠ [] := by
  cases f <;> simp only [dispatchFrame] <;>
    first
      | exact keep_ne _
      | exact stepSt_ne _ _
      | exact stepAck_ne _ _ _
      | exact stepHs_ne _ _
      | exact stepCidRemote_ne _ _
      | exact stepCidLocal_ne _ _
      | exact stepPvThen_ne _ _ _
      | exact gate_ne (stepAv_ne _ _) keep_ne
      | (split <;>
          first
            | exact keep_ne _
            | exact stepAck_ne _ _ _
            | exact stepHs_ne _ _
            | exact stepTerm_ne _ _)

theorem dispatchFrame_inv {s : State} (hs : Inv s) (now : Time) (mp : Migration.Path)
    (pt : PacketType) (d : Nat) (av : Bool) (f : Frame) :
    InvOk (dispatchFrame now mp pt d av f s) := by
  cases f <;> simp only [dispatchFrame] <;>
    first
      | exact keep_inv hs
      | exact stepSt_inv hs _
      | exact stepAck_inv hs _ _
      | exact stepHs_inv hs _
      | exact stepCidRemote_inv hs _
      | exact stepCidLocal_inv hs _
      | exact stepPvThen_inv hs _ _
      | exact gate_inv hs (stepAv_inv hs _) (fun _ h => keep_inv h)
      | (split <;>
          first
            | exact keep_inv hs
            | exact stepAck_inv hs _ _
            | exact stepHs_inv hs _
            | exact stepTerm_inv hs _)

/-! ## 2e. One packet's frames -/

def processFrames (now : Time) (mp : Migration.Path) (pt : PacketType) (dcidSeq : Nat)
    (av : Bool) : List Frame → State → List Out
  | [], s => keep s
  | f :: rest, s =>
    bindAll (bindAll (stepFr s (.recvFrame pt f)) (dispatchFrame now mp pt dcidSeq av f))
      (processFrames now mp pt dcidSeq av rest)

theorem processFrames_ne (now : Time) (mp : Migration.Path) (pt : PacketType) (d : Nat)
    (av : Bool) (fs : List Frame) (s : State) : processFrames now mp pt d av fs s ≠ [] := by
  induction fs generalizing s with
  | nil => exact keep_ne _
  | cons f t ih =>
    exact bindAll_ne (bindAll_ne (stepFr_ne _ _) (fun _ => dispatchFrame_ne _ _ _ _ _ _ _))
      (fun _ => ih _)

theorem processFrames_inv {s : State} (hs : Inv s) (now : Time) (mp : Migration.Path)
    (pt : PacketType) (d : Nat) (av : Bool) (fs : List Frame) :
    InvOk (processFrames now mp pt d av fs s) := by
  induction fs generalizing s with
  | nil => exact keep_inv hs
  | cons f t ih =>
    exact invOk_bindAll
      (invOk_bindAll (stepFr_inv hs _) (fun _ h => dispatchFrame_inv h _ _ _ _ _ _))
      (fun _ h => ih h)

/-! ## 2f. One packet -/

/-- §8.1, line 2757 and line 2765: what processing a packet of this type tells
    `AddressValidation` about the peer's address. -/
def avAfterPacket (pt : PacketType) (a : Addr) (s : State) : List Out :=
  match s.role, pt with
  | _, .handshake => stepAv s (.handshakeProcessed a)
  | .client, .initial => gate s (stepAv s (.serverInitialProcessed a)) keep
  | _, _ => keep s

theorem avAfterPacket_ne (pt : PacketType) (a : Addr) (s : State) :
    avAfterPacket pt a s ≠ [] := by
  cases hr : s.role <;> cases pt <;> simp only [avAfterPacket, hr] <;>
    first | exact keep_ne _ | exact stepAv_ne _ _ | exact gate_ne (stepAv_ne _ _) keep_ne

theorem avAfterPacket_inv {s : State} (hs : Inv s) (pt : PacketType) (a : Addr) :
    InvOk (avAfterPacket pt a s) := by
  cases hr : s.role <;> cases pt <;> simp only [avAfterPacket, hr] <;>
    first
      | exact keep_inv hs
      | exact stepAv_inv hs _
      | exact gate_inv hs (stepAv_inv hs _) (fun _ h => keep_inv h)

/-- §6.2, line 2100: "any other packet" a client has "received and successfully
    processed" — the fact that arms the Version Negotiation discard. -/
def vnAfterPacket (ver : Option Nat) (s : State) : List Out :=
  match s.role with
  | .client => gate s (stepVnClient s (.recvOther ver true)) keep
  | .server => keep s

theorem vnAfterPacket_ne (ver : Option Nat) (s : State) : vnAfterPacket ver s ≠ [] := by
  cases hr : s.role <;> simp only [vnAfterPacket, hr] <;>
    first | exact keep_ne _ | exact gate_ne (stepVnClient_ne _ _) keep_ne

theorem vnAfterPacket_inv {s : State} (hs : Inv s) (ver : Option Nat) :
    InvOk (vnAfterPacket ver s) := by
  cases hr : s.role <;> simp only [vnAfterPacket, hr] <;>
    first
      | exact keep_inv hs
      | exact gate_inv hs (stepVnClient_inv hs _) (fun _ h => keep_inv h)

/-- §17.2.5: a Retry packet.  Whether its integrity tag validates is
    [QUIC-TLS] §5.8 and opaque here; `Quic.decodePacket` has already checked the
    packet's shape, and the token and Source Connection ID rules are WP5's. -/
def retryPacket (token scid dcid : ByteArray) (s : State) : List Out :=
  gate s (stepAv s (.recvRetry token scid true))
    (fun s1 => gate s1 (stepHs s1 (.recvHeader .retry dcid.toList scid.toList)) keep)

theorem retryPacket_ne (t c d : ByteArray) (s : State) : retryPacket t c d s ≠ [] :=
  gate_ne (stepAv_ne _ _) (fun _ => gate_ne (stepHs_ne _ _) keep_ne)

theorem retryPacket_inv {s : State} (hs : Inv s) (t c d : ByteArray) :
    InvOk (retryPacket t c d s) :=
  gate_inv hs (stepAv_inv hs _)
    (fun _ h => gate_inv h (stepHs_inv h _) (fun _ h' => keep_inv h'))

/-- §17.2.1: a Version Negotiation packet.  §6.1, line 2066: a server never
    answers one, and §5.2.2 line 1946 makes it a drop. -/
def vnPacket (dcid scid : ByteArray) (vs : List Nat) (s : State) : List Out :=
  match s.role with
  | .client => stepVnClient s (.recvVersionNegotiation dcid scid vs)
  | .server => [.drop]

theorem vnPacket_ne (d c : ByteArray) (vs : List Nat) (s : State) : vnPacket d c vs s ≠ [] := by
  cases hr : s.role <;> simp only [vnPacket, hr] <;>
    first | exact stepVnClient_ne _ _ | simp

theorem vnPacket_inv {s : State} (hs : Inv s) (d c : ByteArray) (vs : List Nat) :
    InvOk (vnPacket d c vs s) := by
  cases hr : s.role <;> simp only [vnPacket, hr] <;>
    first | exact stepVnClient_inv hs _ | exact InvOk.drop

/-- The body of one 1-RTT / 0-RTT / Initial / Handshake packet, in the order of
    the pipeline: `Handshake`'s key and connection-ID rules, §9's receive rules,
    §12.3's duplicate check, then the frames. -/
def processPayload (now : Time) (mp : Migration.Path) (av : Bool) (ver : Option Nat)
    (pt : PacketType) (dcid scid : ByteArray) (pn : Nat) (fs : List Frame) (s : State) :
    List Out :=
  if fs.isEmpty then stepFr s (.recvPacketFrames pt []) else
  gate s (stepHs s (.recvHeader pt dcid.toList scid.toList)) (fun s1 =>
    gate s1 (stepMig s1 (.recvPacket mp pn (FrameRules.packetProbing fs) (dcidSeqOf s1 dcid)))
      (fun s2 =>
        match pt.space with
        | none => keep s2
        | some sp =>
          gate s2 (stepAck s2 sp (.recvPacket pn now (FrameRules.packetAckEliciting fs)))
            (fun s3 =>
              bindAll (processFrames now mp pt (dcidSeqOf s3 dcid) av fs s3) (fun s4 =>
                bindAll (avAfterPacket pt mp.peer s4) (vnAfterPacket ver)))))

theorem processPayload_ne (now : Time) (mp : Migration.Path) (av : Bool) (ver : Option Nat)
    (pt : PacketType) (dcid scid : ByteArray) (pn : Nat) (fs : List Frame) (s : State) :
    processPayload now mp av ver pt dcid scid pn fs s ≠ [] := by
  simp only [processPayload]
  split
  · exact stepFr_ne _ _
  · refine gate_ne (stepHs_ne _ _) (fun _ => gate_ne (stepMig_ne _ _) (fun _ => ?_))
    split
    · exact keep_ne _
    · exact gate_ne (stepAck_ne _ _ _) (fun _ =>
        bindAll_ne (processFrames_ne _ _ _ _ _ _ _)
          (fun _ => bindAll_ne (avAfterPacket_ne _ _ _) (fun _ => vnAfterPacket_ne _ _)))

theorem processPayload_inv {s : State} (hs : Inv s) (now : Time) (mp : Migration.Path)
    (av : Bool) (ver : Option Nat) (pt : PacketType) (dcid scid : ByteArray) (pn : Nat)
    (fs : List Frame) : InvOk (processPayload now mp av ver pt dcid scid pn fs s) := by
  simp only [processPayload]
  split
  · exact stepFr_inv hs _
  · refine gate_inv hs (stepHs_inv hs _) (fun s1 h1 =>
      gate_inv h1 (stepMig_inv h1 _) (fun s2 h2 => ?_))
    split
    · exact keep_inv h2
    · exact gate_inv h2 (stepAck_inv h2 _ _) (fun s3 h3 =>
        invOk_bindAll (processFrames_inv h3 _ _ _ _ _ _)
          (fun s4 h4 => invOk_bindAll (avAfterPacket_inv h4 _ _)
            (fun _ h5 => vnAfterPacket_inv h5 _)))

/-- One decoded packet of a datagram. -/
def processPacket (now : Time) (mp : Migration.Path) (av : Bool) (ver : Option Nat)
    (pkt : Packet) (s : State) : List Out :=
  match pkt.body with
  | .versions vs => vnPacket (hdrDcid pkt.header) (hdrScid pkt.header) vs.toList s
  | .retry token _ => retryPacket token (hdrScid pkt.header) (hdrDcid pkt.header) s
  | .payload pn _ _ frames =>
    processPayload now mp av ver (hdrPtype pkt.header) (hdrDcid pkt.header)
      (hdrScid pkt.header) pn (frames.toList.map (·.1)) s

theorem processPacket_ne (now : Time) (mp : Migration.Path) (av : Bool) (ver : Option Nat)
    (pkt : Packet) (s : State) : processPacket now mp av ver pkt s ≠ [] := by
  cases hb : pkt.body <;> simp only [processPacket, hb]
  · exact vnPacket_ne _ _ _ _
  · exact retryPacket_ne _ _ _ _
  · exact processPayload_ne _ _ _ _ _ _ _ _ _ _

theorem processPacket_inv {s : State} (hs : Inv s) (now : Time) (mp : Migration.Path)
    (av : Bool) (ver : Option Nat) (pkt : Packet) :
    InvOk (processPacket now mp av ver pkt s) := by
  cases hb : pkt.body <;> simp only [processPacket, hb]
  · exact vnPacket_inv hs _ _ _
  · exact retryPacket_inv hs _ _ _
  · exact processPayload_inv hs _ _ _ _ _ _ _ _ _

/-! ## 2g. The coalesced packets of one datagram

§12.2, line 4614: "A sender can coalesce multiple QUIC packets … into one UDP
datagram."  Line 4622: "if the packet cannot be processed, an endpoint MUST
discard the remainder of the datagram." -/

/-- Does the packet at `pos` look like an Initial?  §11.1, line 4485's
    MAY-discard is only for those. -/
def initialAt (s : State) (buf : ByteArray) (pos : Nat) : Bool :=
  match Quic.decodeHeader buf s.shortDcidLen pos with
  | .ok (hd, _) => hdrPtype hd == .initial
  | .error _ => false

def recvPackets (prot : Protection) (now : Time) (mp : Migration.Path) (av : Bool)
    (ver : Option Nat) (buf : ByteArray) : Nat → Nat → State → List Out
  | 0, _, s => keep s
  | fuel + 1, pos, s =>
    if buf.size ≤ pos then keep s
    else
      match parseOne prot s buf pos with
      | .error e => packetErrOutcomes s (initialAt s buf pos) e
      | .ok (pkt, next) =>
        if next ≤ pos then keep s
        else bindAll (processPacket now mp av ver pkt s)
               (recvPackets prot now mp av ver buf fuel next)

theorem recvPackets_ne (prot : Protection) (now : Time) (mp : Migration.Path) (av : Bool)
    (ver : Option Nat) (buf : ByteArray) (fuel pos : Nat) (s : State) :
    recvPackets prot now mp av ver buf fuel pos s ≠ [] := by
  induction fuel generalizing pos s with
  | zero => exact keep_ne _
  | succ n ih =>
    simp only [recvPackets]
    split
    · exact keep_ne _
    · split
      · exact packetErrOutcomes_ne _ _ _
      · split
        · exact keep_ne _
        · exact bindAll_ne (processPacket_ne _ _ _ _ _ _) (fun _ => ih _ _)

theorem recvPackets_inv (prot : Protection) (now : Time) (mp : Migration.Path) (av : Bool)
    (ver : Option Nat) (buf : ByteArray) (fuel pos : Nat) {s : State} (hs : Inv s) :
    InvOk (recvPackets prot now mp av ver buf fuel pos s) := by
  induction fuel generalizing pos s with
  | zero => exact keep_inv hs
  | succ n ih =>
    simp only [recvPackets]
    split
    · exact keep_inv hs
    · split
      · exact packetErrOutcomes_inv hs _ _
      · split
        · exact keep_inv hs
        · exact invOk_bindAll (processPacket_inv hs _ _ _ _ _) (fun _ h => ih _ h)

/-! ## 2h. Version handling, per role -/

/-- §5.2.2 and §6.1, for a server.  `eventOfDatagram = none` is a datagram that
    is not even an RFC 8999 packet, which §5.2.2 line 1946 ("Servers MUST drop
    incoming packets under all other circumstances") disposes of without any
    state being consulted (`VersionNeg` coverage, line 1946). -/
def vnServerOut (s : State) (k : State → List Out) :
    Outcome VersionNeg.Server.State VersionNeg.Server.Effect → List Out
  | .ok x fx =>
    if fx.any VersionNeg.Server.Effect.isSendVn then
      [.ok (syncConfirmed { s with vnServer := x }) (fx.map Effect.vnServer)]
    else (k (syncConfirmed { s with vnServer := x })).map (withFx (fx.map Effect.vnServer))
  | .error c => [.error c]
  | .drop => [.drop]

def vnServerGate (buf : ByteArray) (k : State → List Out) (s : State) : List Out :=
  match VersionNeg.Server.eventOfDatagram s.vnServer buf with
  | none => [.drop]
  | some e => (VersionNeg.Server.outcomes s.vnServer e).flatMap (vnServerOut s k)

theorem vnServerOut_ne {k : State → List Out} (hk : ∀ s, k s ≠ []) (s : State)
    (o : Outcome VersionNeg.Server.State VersionNeg.Server.Effect) :
    vnServerOut s k o ≠ [] := by
  cases o with
  | ok x fx =>
    simp only [vnServerOut]
    split
    · simp
    · simpa using hk (syncConfirmed { s with vnServer := x })
  | error c => simp [vnServerOut]
  | drop => simp [vnServerOut]

theorem vnServerGate_ne {k : State → List Out} (hk : ∀ s, k s ≠ []) (buf : ByteArray)
    (s : State) : vnServerGate buf k s ≠ [] := by
  simp only [vnServerGate]
  split
  · simp
  · rename_i e _
    cases hh : VersionNeg.Server.outcomes s.vnServer e with
    | nil => exact absurd hh (VersionNeg.Server.outcomes_ne _ _)
    | cons a t =>
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro h
      exact absurd h (vnServerOut_ne hk s a)

theorem vnServerGate_inv {s : State} (hs : Inv s) {k : State → List Out}
    (hk : ∀ s, Inv s → InvOk (k s)) (buf : ByteArray) : InvOk (vnServerGate buf k s) := by
  simp only [vnServerGate]
  split
  · exact InvOk.drop
  · rename_i e _
    intro s' fx hm
    simp only [List.mem_flatMap] at hm
    obtain ⟨o, ho, hmem⟩ := hm
    simp only [vnServerOut] at hmem
    cases o with
    | ok x gx =>
      have hx : Inv (syncConfirmed { s with vnServer := x }) :=
        inv_setVnServer hs
          (VersionNeg.Server.step_inv _ _ _ _ hs.vnS ((VersionNeg.Server.outcomes_iff _ _ _).mp ho))
      simp only at hmem
      split at hmem
      · simp only [List.mem_singleton, Outcome.ok.injEq] at hmem
        exact hmem.1 ▸ hx
      · simp only [List.mem_map] at hmem
        obtain ⟨o', ho', he⟩ := hmem
        cases o' with
        | ok y hy =>
          simp only [withFx, Outcome.ok.injEq] at he
          exact he.1 ▸ hk _ hx _ _ ho'
        | error c => simp [withFx] at he
        | drop => simp [withFx] at he
    | error c => simp at hmem
    | drop => simp at hmem

/-- The version field of a datagram, as RFC 8999 sees it: `none` for a short
    header, which has none (§5.2.2, line 1926). -/
def versionOfDatagram (s : State) (buf : ByteArray) : Option (Option Nat) :=
  match Quic.versionCid buf s.shortDcidLen with
  | .error _ => none
  | .ok (vc, _) => some (if VersionNeg.Server.isLongHeader buf then some vc.version else none)

/-- §5.2.1 and §6.2, for a client.  Two of `VersionNeg.Client`'s rules are
    applied here as gates rather than as steps, because they must fire *before*
    the packet is processed: line 1889's "packets that do not match an existing
    connection are discarded" once the attempt is abandoned, and line 1898's
    "if a client receives a packet that uses a different version than it
    initially selected, it MUST discard that packet".  Line 2100's
    `processedAny` is set afterwards, by `vnAfterPacket`, because the sentence
    counts packets that were "received and successfully processed". -/
def vnClientGate (buf : ByteArray) (k : Option Nat → State → List Out) (s : State) : List Out :=
  if s.vnClient.abandoned then [.drop]
  else match versionOfDatagram s buf with
  | none => [.drop]
  | some ver =>
    if VersionNeg.Client.versionMatches s.vnClient ver = false then [.drop]
    else k ver s

theorem vnClientGate_ne {k : Option Nat → State → List Out} (hk : ∀ v s, k v s ≠ [])
    (buf : ByteArray) (s : State) : vnClientGate buf k s ≠ [] := by
  simp only [vnClientGate]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · exact hk _ _

theorem vnClientGate_inv {s : State} (hs : Inv s) {k : Option Nat → State → List Out}
    (hk : ∀ v s, Inv s → InvOk (k v s)) (buf : ByteArray) : InvOk (vnClientGate buf k s) := by
  simp only [vnClientGate]
  split
  · exact InvOk.drop
  · split
    · exact InvOk.drop
    · split
      · exact InvOk.drop
      · exact hk _ _ hs

/-! ## 2i. §14's size rules -/

/-- Does the datagram start with an Initial packet?  §14.1's rule is about the
    datagram that *carries* one. -/
def carriesInitial (s : State) (buf : ByteArray) : Bool :=
  match Quic.decodeHeader buf s.shortDcidLen with
  | .ok (hd, _) => hdrPtype hd == .initial
  | .error _ => false

def dszGate (buf : ByteArray) (k : State → List Out) (s : State) : List Out :=
  if carriesInitial s buf then bindAll (stepDsz s (.recvInitial buf.size)) k
  else bindAll (stepDsz s (.recvDatagram buf.size)) k

theorem dszGate_ne {k : State → List Out} (hk : ∀ s, k s ≠ []) (buf : ByteArray) (s : State) :
    dszGate buf k s ≠ [] := by
  simp only [dszGate]
  split <;> exact bindAll_ne (stepDsz_ne _ _) hk

theorem dszGate_inv {s : State} (hs : Inv s) {k : State → List Out}
    (hk : ∀ s, Inv s → InvOk (k s)) (buf : ByteArray) : InvOk (dszGate buf k s) := by
  simp only [dszGate]
  split <;> exact invOk_bindAll (stepDsz_inv hs _) hk

/-! ## 2j. The whole datagram -/

/-- Is the peer address this datagram came from one the anti-amplification limit
    no longer binds?  §10.2.1, line 4008's "packets received from an unvalidated
    address" is `AddressValidation`'s judgement, as `Termination` says. -/
def addrValidated (s : State) (a : Addr) : Bool := !s.av.limitedB a

/-- §19.19: the CONNECTION_CLOSE a datagram carries, if the closing endpoint
    still has the keys to see it.  Used only by the phase gate (§10.2.2,
    line 4044, "MAY enter the draining state from the closing state if it
    receives a CONNECTION_CLOSE frame"). -/
def closeReasonOfDatagram (prot : Protection) (s : State) (buf : ByteArray) :
    Option Termination.CloseReason :=
  match parseOne prot s buf 0 with
  | .ok (pkt, _) =>
    match pkt.body with
    | .payload _ _ _ frames =>
      (frames.toList.map (·.1)).findSome? closeReasonOfFrame
    | _ => none
  | .error _ => none

/-- Version handling, per role (§5.2.1, §5.2.2, §6.1, §6.2). -/
def routeVersion (prot : Protection) (now : Time) (mp : Migration.Path) (av : Bool)
    (buf : ByteArray) (s : State) : List Out :=
  match s.role with
  | .server =>
    vnServerGate buf (fun s2 => recvPackets prot now mp av none buf buf.size 0 s2) s
  | .client =>
    vnClientGate buf (fun ver s2 => recvPackets prot now mp av ver buf buf.size 0 s2) s

theorem routeVersion_ne (prot : Protection) (now : Time) (mp : Migration.Path) (av : Bool)
    (buf : ByteArray) (s : State) : routeVersion prot now mp av buf s ≠ [] := by
  cases hr : s.role <;> simp only [routeVersion, hr]
  · exact vnClientGate_ne (fun _ _ => recvPackets_ne _ _ _ _ _ _ _ _ _) buf s
  · exact vnServerGate_ne (fun _ => recvPackets_ne _ _ _ _ _ _ _ _ _) buf s

theorem routeVersion_inv {s : State} (hs : Inv s) (prot : Protection) (now : Time)
    (mp : Migration.Path) (av : Bool) (buf : ByteArray) :
    InvOk (routeVersion prot now mp av buf s) := by
  cases hr : s.role <;> simp only [routeVersion, hr]
  · exact vnClientGate_inv hs (fun _ _ h => recvPackets_inv _ _ _ _ _ _ _ _ h) buf
  · exact vnServerGate_inv hs (fun _ h => recvPackets_inv _ _ _ _ _ _ _ _ h) buf

/-- Parts 3–5 of the pipeline, for the `active` phase. -/
def routeDatagram (prot : Protection) (now : Time) (src : Addr) (mp : Migration.Path)
    (buf : ByteArray) (s : State) : List Out :=
  dszGate buf (routeVersion prot now mp (addrValidated s src) buf) s

theorem routeDatagram_ne (prot : Protection) (now : Time) (src : Addr) (mp : Migration.Path)
    (buf : ByteArray) (s : State) : routeDatagram prot now src mp buf s ≠ [] :=
  dszGate_ne (fun _ => routeVersion_ne _ _ _ _ _ _) buf s

theorem routeDatagram_inv {s : State} (hs : Inv s) (prot : Protection) (now : Time)
    (src : Addr) (mp : Migration.Path) (buf : ByteArray) :
    InvOk (routeDatagram prot now src mp buf s) :=
  dszGate_inv hs (fun _ h => routeVersion_inv h _ _ _ _ _) buf

/-- §10.1, line 3841: "An endpoint restarts its idle timer when a packet from its
    peer is received and processed successfully." -/
def afterDatagram (now : Time) (av : Bool) (s : State) : List Out :=
  stepTerm s (.recvPacket now s.pto av)

/-- The phases that process nothing (`draining`, `closed`) and the one that
    answers with a CONNECTION_CLOSE (`closing`) — §10.2.1, line 3965; §10.2.2,
    line 4023; §10.2, line 3953.  §10.2.2 line 4044's "MAY enter the draining
    state from the closing state if it receives a CONNECTION_CLOSE frame" needs
    to know whether the datagram carries one, which is why the payload is looked
    at even though no frame is dispatched. -/
def closedPhase (prot : Protection) (now : Time) (av : Bool) (buf : ByteArray)
    (s : State) : List Out :=
  match closeReasonOfDatagram prot s buf with
  | some r => stepTerm s (.recvClose now s.pto r av)
  | none => stepTerm s (.recvPacket now s.pto av)

theorem closedPhase_ne (prot : Protection) (now : Time) (av : Bool) (buf : ByteArray)
    (s : State) : closedPhase prot now av buf s ≠ [] := by
  simp only [closedPhase]; split <;> exact stepTerm_ne _ _

theorem closedPhase_inv {s : State} (hs : Inv s) (prot : Protection) (now : Time)
    (av : Bool) (buf : ByteArray) : InvOk (closedPhase prot now av buf s) := by
  simp only [closedPhase]; split <;> exact stepTerm_inv hs _

/-- Part 2 of the pipeline: `Termination`'s phase gate. -/
def phaseGate (prot : Protection) (now : Time) (src : Addr) (mp : Migration.Path)
    (buf : ByteArray) (s : State) : List Out :=
  match s.term.phase with
  | .active =>
    bindAll (routeDatagram prot now src mp buf s) (afterDatagram now (addrValidated s src))
  | _ => closedPhase prot now (addrValidated s src) buf s

theorem phaseGate_ne (prot : Protection) (now : Time) (src : Addr) (mp : Migration.Path)
    (buf : ByteArray) (s : State) : phaseGate prot now src mp buf s ≠ [] := by
  simp only [phaseGate]
  split
  · exact bindAll_ne (routeDatagram_ne _ _ _ _ _ _) (fun _ => stepTerm_ne _ _)
  · exact closedPhase_ne _ _ _ _ _

theorem phaseGate_inv {s : State} (hs : Inv s) (prot : Protection) (now : Time) (src : Addr)
    (mp : Migration.Path) (buf : ByteArray) : InvOk (phaseGate prot now src mp buf s) := by
  simp only [phaseGate]
  split
  · exact invOk_bindAll (routeDatagram_inv hs _ _ _ _ _) (fun _ h => stepTerm_inv h _)
  · exact closedPhase_inv hs _ _ _ _

/-- The whole receive pipeline. -/
def recvDatagram (prot : Protection) (s : State) (src dest : Addr) (buf : ByteArray)
    (now : Time) : List Out :=
  bindAll (register ⟨⟨dest.id⟩, src⟩ s) (fun s0 =>
    bindAll (stepAv s0 (.datagramRecv src buf.size false))
      (phaseGate prot now src ⟨⟨dest.id⟩, src⟩ buf))

theorem recvDatagram_ne (prot : Protection) (s : State) (src dest : Addr) (buf : ByteArray)
    (now : Time) : recvDatagram prot s src dest buf now ≠ [] :=
  bindAll_ne (register_ne _ _) (fun _ =>
    bindAll_ne (stepAv_ne _ _) (fun _ => phaseGate_ne _ _ _ _ _ _))

theorem recvDatagram_inv {s : State} (hs : Inv s) (prot : Protection) (src dest : Addr)
    (buf : ByteArray) (now : Time) : InvOk (recvDatagram prot s src dest buf now) :=
  invOk_bindAll (register_inv hs _) (fun _ h0 =>
    invOk_bindAll (stepAv_inv h0 _) (fun _ h1 => phaseGate_inv h1 _ _ _ _ _))

end Quic.Spec.Endpoint
