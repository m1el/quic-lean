import QuicModel.Spec.Endpoint.Theorems
import QuicModel.Dump

/-!
  WP12 "Endpoint", part 8b: **what WP13 calls**.

  The style is `QuicModel/Dump.lean`'s: `@[export quic_endpoint_…]` on a plain
  `def` whose arguments are scalars, `ByteArray`s or boxed Lean values.

  Everything here fixes the harness's packet protection to
  `Quic.Protection.stub 16`, the stub `harness/conn_trace.c` and
  `harness/pkt_diff.c` install (payload in the clear, tag = 16 bytes of 0xA5,
  header-protection mask = the first five bytes of the sample).  The general
  endpoint is `Endpoint.component prot` for any `prot`; only the exports are
  specialised.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-- The packet protection `harness/conn_trace.c` installs. -/
def harnessProtection : Protection := Protection.stub 16

/-! ## The effect rendering

`harness/conn_trace.c` prints one `CB <name> <k=v>…` line per application
callback ngtcp2 fired; those are the model's effects.  `cbName` is the mapping,
and `none` means "do not compare this".  For most of them that is because
ngtcp2 does not surface them at all: `keysDiscarded`, `peerParams`,
`cryptoDiscarding`, `dcidChanged`, `addressValidated`, `handshakeProceeds`,
`queueRetire`, `switchPath`, `deliver`, `sendPending`, `skippedRest`,
`packetProcessed` and the
`Termination` send effects are model-level signals, or things that appear in the
trace as `OUT`/`ERR` records rather than as `CB` lines.

Three are `none` for a second reason, and it is not the same one: the `Stream`
*request* effects `stopSendingRequested`, `resetRequested` and `resetAcked` do
have ngtcp2 counterparts (`stream_stop_sending` is printed by
`harness/conn_trace.c`), but ngtcp2 fires them when the frame is **written**,
whereas the model produces them when the *application* asks — one event earlier,
and the model has no effect-producing step at the later moment.  Equating them
would compare two different points of the trace, so they stay `none` and WP13
must ignore ngtcp2's `stream_stop_sending` line.  See `TRIAGE.md` `WP13-2`.

WP13 must *ignore* everything `cbName` maps to `none`, not treat it as a
mismatch; the full table is in §4b of `QuicModel/Spec/Endpoint.lean`. -/

def streamEffectName : Stream.Effect → Option String
  | .recv (.dataAvailable _) => some "recv_stream_data"
  | .recv (.allDataReceived _) => some "stream_close"
  | .recv (.streamReset _ _) => some "stream_reset"
  | .recv (.stopSendingRequested _) => none
  | .send (.creditAvailable _) => some "extend_max_stream_data"
  | .send (.peerStopSending _) => some "recv_stop_sending"
  | .send (.allDataAcked) => some "acked_stream_data_offset"
  | .send (.resetRequested _) => none
  | .send (.resetAcked) => none

def Effect.cbName : Effect → Option String
  | .st (.stream _ e) => streamEffectName e
  | .st (.streamOpened _) => some "stream_open"
  -- §2.1, line 718's implicitly opened streams are not an application event:
  -- ngtcp2 announces only the stream a frame names, quiche none at all.
  | .st (.streamsOpenedBelow ..) => none
  -- … and ngtcp2 announces one of those the first time a frame names it.
  | .st (.streamFirstUsed _) => some "stream_open"
  | .st (.dataCreditAvailable _) => some "extend_max_data"
  | .st (.streamsAvailable .bidi _) => some "extend_max_local_streams_bidi"
  | .st (.streamsAvailable .uni _) => some "extend_max_local_streams_uni"
  | .hs .handshakeComplete => some "handshake_completed"
  | .hs .handshakeConfirmed => some "handshake_confirmed"
  | .hs (.deliverCrypto ..) => some "recv_crypto_data"
  | .av (.storeToken _) => some "recv_new_token"
  | .av (.useToken _) => some "recv_retry"
  | .pv (.pathValidated _) => some "path_validation"
  | .pv (.pathFailed _) => some "path_validation"
  | .cidRemote (.stopUsing ..) => some "dcid_status"
  | .cidLocal (.sendNewCid ..) => some "get_new_connection_id"
  -- `cidRetiredByPeer` is NOT mapped: ngtcp2 fires `remove_connection_id` when
  -- it later removes the ID, not on receipt of RETIRE_CONNECTION_ID; comparing
  -- it rejected the candidates that had correctly applied the retirement
  -- (TRIAGE WP13-13).  Same class as `stream_close` (WP13-1).
  | .vnClient .abandon => some "recv_version_negotiation"
  | .vnClient (.attemptVersion _) => some "version_negotiation"
  | .ecn _ .ecnValidationFailed => some "path_validation"
  | _ => none

private def lvlName : Handshake.CryptoLevel → String
  | .initial => "initial" | .handshake => "handshake" | .oneRtt => "1rtt"

private def dirName : StreamDir → String
  | .bidi => "bidi" | .uni => "uni"

private def spaceName : PnSpace → String
  | .initial => "initial" | .handshake => "handshake" | .appData => "app"

/-- The full rendering, for a trace the reader can read.  The `CB` line of
    `conn_trace.c` is `cbName` plus these arguments. -/
def Effect.render : Effect → String
  | .st (.stream id (.recv (.dataAvailable n))) =>
    s!"recv_stream_data id={id.val} upTo={n}"
  | .st (.stream id (.recv (.allDataReceived fs))) =>
    s!"stream_close id={id.val} final_size={fs}"
  | .st (.stream id (.recv (.streamReset c fs))) =>
    s!"stream_reset id={id.val} final_size={fs} app_error_code={c}"
  | .st (.stream id (.recv (.stopSendingRequested c))) =>
    s!"stop_sending_requested id={id.val} app_error_code={c}"
  | .st (.stream id (.send (.creditAvailable m))) =>
    s!"extend_max_stream_data id={id.val} max_data={m}"
  | .st (.stream id (.send (.peerStopSending c))) =>
    s!"recv_stop_sending id={id.val} app_error_code={c}"
  | .st (.stream id (.send .allDataAcked)) => s!"acked_stream_data_offset id={id.val}"
  | .st (.stream id (.send (.resetRequested c))) =>
    s!"reset_requested id={id.val} app_error_code={c}"
  | .st (.stream id (.send .resetAcked)) => s!"reset_acked id={id.val}"
  | .st (.streamOpened id) => s!"stream_open id={id.val}"
  | .st (.streamsOpenedBelow first n) => s!"streams_opened_below first={first.val} count={n}"
  | .st (.streamFirstUsed id) => s!"stream_first_used id={id.val}"
  | .st (.dataCreditAvailable m) => s!"extend_max_data max_data={m}"
  | .st (.streamsAvailable d m) => s!"extend_max_local_streams_{dirName d} max_streams={m}"
  | .hs .handshakeComplete => "handshake_completed"
  | .hs .handshakeConfirmed => "handshake_confirmed"
  | .hs (.deliverCrypto l off len) => s!"recv_crypto_data level={lvlName l} off={off} len={len}"
  | .hs (.keysDiscarded _) => "keys_discarded"
  | .hs (.cryptoDiscarding l) => s!"crypto_discarding level={lvlName l}"
  | .hs (.peerParams _) => "peer_transport_parameters"
  | .hs (.dcidChanged _) => "dcid_changed"
  | .fr (.deliver f) => s!"deliver {f.dump}"
  | .ack sp _ => s!"processed space={spaceName sp}"
  | .cidLocal (.sendNewCid seq rpt _ _) => s!"get_new_connection_id seq={seq} rpt={rpt}"
  | .cidLocal (.cidRetiredByPeer seq) => s!"remove_connection_id seq={seq}"
  | .cidRemote (.stopUsing seq _) => s!"dcid_status type=deactivate seq={seq}"
  | .cidRemote (.queueRetire seq) => s!"queue_retire seq={seq}"
  | .av (.addressValidated a) => s!"address_validated addr={a.id}"
  | .av (.sendRetry a) => s!"send_retry addr={a.id}"
  | .av (.handshakeProceeds a) => s!"handshake_proceeds addr={a.id}"
  | .av (.useToken t) => s!"recv_retry token={hex t}"
  | .av (.useDcid c) => s!"use_dcid cid={hex c}"
  | .av (.storeToken t) => s!"recv_new_token token={hex t}"
  | .pv (.sendChallenge p _) => s!"begin_path_validation path={p.id}"
  | .pv (.queueResponse p _) => s!"queue_path_response path={p.id}"
  | .pv (.pathValidated p) => s!"path_validation path={p.id} res=success"
  | .pv (.pathFailed p) => s!"path_validation path={p.id} res=failure"
  | .mig (.startValidation _) => "mig_start_validation"
  | .mig (.switchPath _) => "mig_switch_path"
  | .mig (.validatePrevious _) => "mig_validate_previous"
  | .mig (.abandonValidation _) => "mig_abandon_validation"
  | .mig .discardState => "mig_discard_state"
  | .term (.sendClose _) => "send_connection_close"
  | .term .sendFarewellClose => "send_farewell_close"
  | .term .sendStatelessReset => "send_stateless_reset"
  | .term .discardState => "discard_state"
  | .vnServer .deliver => "vn_deliver"
  | .vnServer (.sendVersionNegotiation _) => "send_version_negotiation"
  | .vnClient .deliver => "vn_deliver"
  | .vnClient .abandon => "recv_version_negotiation"
  | .vnClient (.attemptVersion v) => s!"version_negotiation version={v}"
  | .dsz .deliver => "dsz_deliver"
  | .dsz .ceaseSending => "cease_sending"
  | .rtx (.repair _) => "repair"
  | .rtx (.ceaseSending _) => "cease_repair"
  | .rtx .congestionControlAction => "congestion_control_action"
  | .ecn sp .ecnValidationFailed => s!"ecn_validation_failed space={spaceName sp}"
  | .ecn sp .disableEcn => s!"disable_ecn space={spaceName sp}"
  | .ecn sp .ecnValidated => s!"ecn_validated space={spaceName sp}"
  | .sendPending f => s!"send_pending {f.dump}"
  | .skippedRest => "skipped_rest"
  | .packetProcessed => "packet_processed"

/-- Did this step make new bytes of stream `id` available to the application? -/
def deliversData (fx : List Effect) (id : StreamId) : Bool :=
  fx.any fun e =>
    match e with
    | .st (.stream i (.recv (.dataAvailable _))) => i == id
    | _ => false

/-- How one effect shows in an implementation's read interface.

    The model keeps two facts apart: new bytes are available
    (`Stream.Recv.Effect.dataAvailable`) and the final size has been reached
    (`allDataReceived`).  An implementation's read interface reports both
    through one channel — a read result that carries a FIN flag — so reaching
    the final size in a step that delivers *no* new bytes (an empty STREAM frame
    with FIN, or a FIN that closes a gap-free stream) is still a read: zero
    bytes, fin set.  ngtcp2 and quiche both report it (`DIFFERENCES.md` B6).
    That read is the completion, not data: no `dataAvailable` is invented, so
    nothing is delivered twice, and `stream_close` is still listed so the
    completion is not erased for an implementation that has such a callback. -/
def Effect.cbNames (fx : List Effect) : Effect → List String
  | .st (.stream id (.recv (.allDataReceived _))) =>
    if deliversData fx id then ["stream_close"] else ["recv_stream_data", "stream_close"]
  | e => e.cbName.toList

/-- The callback names one outcome's effects would show as `CB` lines, in order
    and with the ones ngtcp2 does not surface removed. -/
def observedCbs (fx : List Effect) : List String := fx.flatMap (Effect.cbNames fx)

/-! ## Building an initial state -/

/-- The connection `harness/conn_trace.c` sets up: both sides advertise the same
    parameters, both connection IDs are 8 bytes, the path is fixed. -/
def harnessConfig (isServer : Bool) (localCid peerCid : ByteArray)
    (maxData maxStreamData maxStreamsBidi maxStreamsUni maxIdle maxAckDelay
      cidLimit pto : Nat) : Config where
  role := if isServer then .server else .client
  ours :=
    { maxData, maxStreamDataBidiLocal := maxStreamData,
      maxStreamDataBidiRemote := maxStreamData, maxStreamDataUni := maxStreamData,
      maxStreamsBidi, maxStreamsUni }
  theirs :=
    { maxData, maxStreamDataBidiLocal := maxStreamData,
      maxStreamDataBidiRemote := maxStreamData, maxStreamDataUni := maxStreamData,
      maxStreamsBidi, maxStreamsUni }
  localCid := localCid.toList
  localToken := List.replicate 16 0
  peerCid := peerCid.toList
  peerToken := List.replicate 16 0
  origDcid := peerCid.toList
  localCidLimit := cidLimit
  peerCidLimit := cidLimit
  localMaxIdle := maxIdle
  peerMaxIdle := maxIdle
  maxAckDelay := maxAckDelay
  shortDcidLen := localCid.size
  pto := pto
  localAddr := ⟨0⟩
  peerAddr := ⟨1⟩
  prot := harnessProtection

@[export quic_endpoint_init]
def initC (isServer : UInt8) (localCid peerCid : ByteArray)
    (maxData maxStreamData maxStreamsBidi maxStreamsUni maxIdle maxAckDelay
      cidLimit pto : UInt64) : State :=
  init (harnessConfig (isServer != 0) localCid peerCid maxData.toNat maxStreamData.toNat
    maxStreamsBidi.toNat maxStreamsUni.toNat maxIdle.toNat maxAckDelay.toNat
    cidLimit.toNat pto.toNat)

/-! ## Driving the endpoint -/

@[export quic_endpoint_recv_datagram]
def recvDatagramC (s : State) (src dest : UInt64) (buf : ByteArray) (now : UInt64) : List Out :=
  outcomes harnessProtection s (.datagram ⟨src.toNat⟩ ⟨dest.toNat⟩ buf now.toNat)

@[export quic_endpoint_app_event]
def appEventC (s : State) (a : AppAction) (now : UInt64) : List Out :=
  outcomes harnessProtection s (.app a now.toNat)

@[export quic_endpoint_tls_event]
def tlsEventC (s : State) (e : TlsEvent) : List Out :=
  outcomes harnessProtection s (.tls e)

@[export quic_endpoint_tick]
def tickC (s : State) (now : UInt64) : List Out :=
  outcomes harnessProtection s (.timer now.toNat)

@[export quic_endpoint_local_event]
def localEventC (s : State) (a : LocalAction) (now : UInt64) : List Out :=
  outcomes harnessProtection s (.local a now.toNat)

/-- The preferred outcome — the reference implementation. -/
@[export quic_endpoint_step]
def stepC (s : State) (e : Event) : Out := step harnessProtection s e

/-- Is an outcome permitted? -/
@[export quic_endpoint_accepts]
def acceptsC (s : State) (e : Event) (o : Out) : UInt8 :=
  if accepts harnessProtection s e o then 1 else 0

/-! ## Reading an outcome -/

/-- `0xffffffff` when the outcome is not an error; §20.1's code otherwise. -/
@[export quic_endpoint_outcome_error]
def outcomeErrorC : Out → UInt64
  | .error c => c.code.toUInt64
  | _ => 0xffffffff

@[export quic_endpoint_outcome_is_drop]
def outcomeIsDropC : Out → UInt8
  | .drop => 1
  | _ => 0

@[export quic_endpoint_outcome_state]
def outcomeStateC (s : State) (o : Out) : State := o.next s

@[export quic_endpoint_outcome_cbs]
def outcomeCbsC : Out → List String
  | .ok _ fx => observedCbs fx
  | _ => []

@[export quic_endpoint_outcome_render]
def outcomeRenderC : Out → String
  | .ok _ fx => "OK [" ++ "; ".intercalate (fx.map Effect.render) ++ "]"
  | .error c => s!"ERR {c.code}"
  | .drop => "DROP"

/-! ## Following an implementation we cannot see inside

`Core` says why this is a *set*: ngtcp2 returns 0 both for a packet it processed
without visible effect and for one it discarded, so `.ok s []` and `.drop` look
alike (PLAN §4a).  A violation is the set becoming empty. -/

/-- The literal form the assignment asks for: `Obs.matchesSpec` against the
    observation the harness made. -/
@[export quic_endpoint_track_set]
def trackSetC (ss : List State) (e : Event) (seen : Obs Effect) : List State :=
  (component harnessProtection).trackSet ss e seen.matchesSpec

/-- The practical form: the harness cannot build an `Obs Effect`, but it can
    report "did it fail, with which code, and which `CB` lines did it print".
    Effects ngtcp2 does not surface are dropped by `observedCbs` before the
    comparison, and §11 line 4434's generic-code allowance is applied exactly as
    `Obs.matchesSpec` does. -/
def tracePattern (isError : Bool) (code : Nat) (cbs : List String) : Obs Effect → Bool
  | .error c => isError && (decide (c.code = code) || c.isGeneric)
  | .ok fx => !isError && observedCbs fx == cbs
  | .drop => !isError && cbs.isEmpty

@[export quic_endpoint_track_trace]
def trackTraceC (ss : List State) (e : Event) (isError : UInt8) (code : UInt64)
    (cbs : List String) : List State :=
  (component harnessProtection).trackSet ss e (tracePattern (isError != 0) code.toNat cbs)

/-! ## The send side

Every packet ngtcp2 writes must satisfy `maySendDatagram`; the absence of a
packet proves nothing (PLAN §4a, "send side is one-directional"). -/

/-- Construct a number entry without exposing Lean's Nat/Prod ABI to C. -/
@[export quic_endpoint_send_number]
def sendNumberC (space : UInt8) (pn : UInt64) : PnSpace × Nat :=
  (if space == 0 then .initial else if space == 1 then .handshake else .appData, pn.toNat)

@[export quic_endpoint_may_send_numbers]
def maySendNumbersC (s : State) (ns : List (PnSpace × Nat)) : UInt8 :=
  if maySendNumbers s ns then 1 else 0

@[export quic_endpoint_may_send_datagram]
def maySendDatagramC (s : State) (src dest : UInt64) (size : UInt64) (isPmtuProbe : UInt8)
    (isEcnMarked : UInt8) (dcid scid : ByteArray) (packets : List OutPacket) : UInt8 :=
  if maySendDatagram s
      { size := size.toNat, packets, dest := ⟨dest.toNat⟩, isPmtuProbe := isPmtuProbe != 0,
        isEcnMarked := isEcnMarked != 0, src := ⟨src.toNat⟩, dcid := some dcid.toList,
        scid := some scid.toList } then 1 else 0

/-- The refusing conjuncts of `maySendDatagram`, comma-separated (empty when it
    would return 1).  Diagnostic only (TRIAGE WP13-17). -/
@[export quic_endpoint_may_send_datagram_why]
def maySendDatagramWhyC (s : State) (src dest : UInt64) (size : UInt64) (isPmtuProbe : UInt8)
    (isEcnMarked : UInt8) (dcid scid : ByteArray) (packets : List OutPacket) : String :=
  ",".intercalate (maySendDatagramWhy s
    { size := size.toNat, packets, dest := ⟨dest.toNat⟩, isPmtuProbe := isPmtuProbe != 0,
      isEcnMarked := isEcnMarked != 0, src := ⟨src.toNat⟩, dcid := some dcid.toList,
      scid := some scid.toList })

@[export quic_endpoint_may_send_packet]
def maySendPacketC (s : State) (p : OutPacket) : UInt8 := if maySendPacket s p then 1 else 0

@[export quic_endpoint_may_send_frame]
def maySendFrameC (s : State) (f : Frame) : UInt8 := if maySend s f then 1 else 0

/-- §10.3 / §10.3.3: a Stateless Reset is not made of QUIC packets, so it has
    its own predicate (`Termination` part 6.3). -/
@[export quic_endpoint_may_send_stateless_reset]
def maySendStatelessResetC (preventsLooping : UInt8) (triggerSize resetSize : UInt64) : UInt8 :=
  if maySendStatelessReset (preventsLooping != 0) triggerSize.toNat resetSize.toNat then 1 else 0

/-! ## Trace-level obligations -/

@[export quic_endpoint_obligations]
def obligationsC (s : State) (now tolerance : UInt64) : UInt8 :=
  if obligations s now.toNat tolerance.toNat then 1 else 0

@[export quic_endpoint_resets_owed]
def resetsOwedC (s : State) : List UInt64 := (resetsOwed s).map (fun i => i.val.toUInt64)

/-- §13.3, line 5445: how many pieces of information are still owed a
    retransmission.  `0` at the end of a conforming run. -/
@[export quic_endpoint_repair_owed]
def repairOwedC (s : State) : UInt64 := (repairOwed s).length.toUInt64

/-- §13.4.1, line 5504: ECN counts received and not yet reported. -/
@[export quic_endpoint_ecn_feedback_owed]
def ecnFeedbackOwedC (s : State) : UInt8 := if ecnFeedbackOwed s then 1 else 0

/-- §13.4.2.2, line 5626: may the endpoint still set the ECT codepoint? -/
@[export quic_endpoint_may_mark_ecn]
def mayMarkEcnC (s : State) (marked : UInt8) : UInt8 :=
  if Ecn.mayMarkEcn s.ecnInitial (marked != 0) && Ecn.mayMarkEcn s.ecnHandshake (marked != 0) &&
      Ecn.mayMarkEcn s.ecnAppData (marked != 0) then 1 else 0

/-! ## Reading the state, for triage -/

@[export quic_endpoint_phase]
def phaseC (s : State) : UInt8 :=
  match s.term.phase with
  | .active => 0 | .closing => 1 | .draining => 2 | .closed => 3

@[export quic_endpoint_state_render]
def stateRenderC (s : State) : String :=
  s!"phase={phaseC s} confirmed={s.hs.confirmed} recvTotal={s.st.recvTotal} " ++
  s!"sentTotal={s.st.sentTotal} opened={s.st.opened.byClient.bidi}/{s.st.opened.byServer.bidi} " ++
  s!"activeCidsLocal={s.cidLocal.activeCount} activeCidsRemote={s.cidRemote.activeCount}"

end Quic.Spec.Endpoint
