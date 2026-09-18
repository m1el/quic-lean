import QuicModel.Spec.Endpoint.Exports

/-!
  WP13 "DiffHarness": the C glue.

  `QuicModel/Spec/Endpoint/Exports.lean` exports the twenty-seven entry points
  that *drive* the endpoint, but three of their argument types are Lean
  inductives — `Event`, `AppAction`, `LocalAction`, `TlsEvent`, `Frame`,
  `OutPacket` — and building one of those from C means allocating a constructor
  with the right tag and field order by hand.  That is exactly the kind of
  duplication that goes stale the first time a constructor is inserted, so this
  file builds them instead: one `@[export]`ed function per constructor the
  harness needs, taking scalars and `ByteArray`s only, in the style of
  `QuicModel/Dump.lean`.

  **No specification content lives here.**  Every function is either a
  constructor application or a call to a function `Spec` already defines
  (`Quic.decodeFrames`, `FrameRules.packetAckEliciting`, `Frame.dump`).  The
  file is outside `QuicModel/Spec/` for that reason.

  Argument conventions, the same as `Exports.lean`'s:

  * booleans and small enumerations arrive as `UInt8`, numbers as `UInt64`;
  * `dir`: 0 = bidi, 1 = uni;
  * `ptype`: 0 initial, 1 0-RTT, 2 handshake, 3 1-RTT, 4 retry, 5 VN;
  * `space`: 0 initial, 1 handshake, 2 app data;
  * `level` (`Handshake.Level`): 0 initial, 1 0-RTT, 2 handshake, 3 1-RTT;
  * `crypto level` (`Handshake.CryptoLevel`): 0 initial, 1 handshake, 2 1-RTT;
  * addresses are the `Spec.Addr.id` the harness assigns (0 = us, 1 = the peer),
    matching `harnessConfig`'s `localAddr := ⟨0⟩`, `peerAddr := ⟨1⟩`.
-/
namespace Quic.Harness

open Quic Quic.Spec Quic.Spec.Endpoint

/-! ## Small enumerations -/

def dirOf (u : UInt8) : StreamDir := if u == 0 then .bidi else .uni

def ptypeOf (u : UInt8) : PacketType :=
  match u with
  | 0 => .initial
  | 1 => .zeroRtt
  | 2 => .handshake
  | 3 => .oneRtt
  | 4 => .retry
  | _ => .versionNegotiation

def spaceOf (u : UInt8) : PnSpace :=
  match u with
  | 0 => .initial
  | 1 => .handshake
  | _ => .appData

def levelOf (u : UInt8) : Handshake.Level :=
  match u with
  | 0 => .initial
  | 1 => .zeroRtt
  | 2 => .handshake
  | _ => .oneRtt

def cryptoLevelOfU8 (u : UInt8) : Handshake.CryptoLevel :=
  match u with
  | 0 => .initial
  | 1 => .handshake
  | _ => .oneRtt

/-! ## `Event`: the five families of `Endpoint.Event` -/

@[export quic_h_ev_datagram]
def evDatagram (src dest : UInt64) (buf : ByteArray) (now : UInt64) : Event :=
  .datagram ⟨src.toNat⟩ ⟨dest.toNat⟩ buf now.toNat

@[export quic_h_ev_app]
def evApp (a : AppAction) (now : UInt64) : Event := .app a now.toNat

@[export quic_h_ev_tls]
def evTls (e : TlsEvent) : Event := .tls e

@[export quic_h_ev_timer]
def evTimer (now : UInt64) : Event := .timer now.toNat

@[export quic_h_ev_local]
def evLocal (a : LocalAction) (now : UInt64) : Event := .local a now.toNat

/-! ## `TlsEvent` (= `Handshake.Event`)

Only the four the harness needs to put the model where `conn_trace.c` puts
ngtcp2: `conn_trace.c` installs the Handshake and 1-RTT keys by hand and sets
`NGTCP2_CONN_FLAG_HANDSHAKE_COMPLETED`, which is `tlsKeys` four times and
`tlsComplete` once. -/

@[export quic_h_tls_keys]
def tlsKeys (isWrite level : UInt8) : TlsEvent :=
  .tlsKeys (if isWrite == 0 then .read else .write) (levelOf level)

@[export quic_h_tls_complete]
def tlsComplete (_dummy : UInt8) : TlsEvent := .tlsComplete

@[export quic_h_tls_send]
def tlsSend (level : UInt8) (len : UInt64) : TlsEvent :=
  .tlsSend (cryptoLevelOfU8 level) len.toNat

@[export quic_h_tls_recv_handshake_done]
def tlsRecvHandshakeDone (_dummy : UInt8) : TlsEvent := .recvHandshakeDone

/-! ## `AppAction` -/

@[export quic_h_app_open_stream]
def appOpenStream (dir : UInt8) : AppAction := .openStream (dirOf dir)

@[export quic_h_app_write]
def appWrite (id len : UInt64) : AppAction := .write ⟨id.toNat⟩ len.toNat

@[export quic_h_app_fin]
def appFin (id : UInt64) : AppAction := .fin ⟨id.toNat⟩

@[export quic_h_app_reset]
def appReset (id code : UInt64) : AppAction := .reset ⟨id.toNat⟩ code.toNat

@[export quic_h_app_stop_sending]
def appStopSending (id code : UInt64) : AppAction := .stopSending ⟨id.toNat⟩ code.toNat

@[export quic_h_app_read]
def appRead (id len : UInt64) : AppAction := .read ⟨id.toNat⟩ len.toNat

@[export quic_h_app_extend_max_stream_data]
def appExtendMaxStreamData (id v : UInt64) : AppAction :=
  .extendMaxStreamData ⟨id.toNat⟩ v.toNat

@[export quic_h_app_extend_max_data]
def appExtendMaxData (v : UInt64) : AppAction := .extendMaxData v.toNat

@[export quic_h_app_extend_max_streams]
def appExtendMaxStreams (dir : UInt8) (v : UInt64) : AppAction :=
  .extendMaxStreams (dirOf dir) v.toNat

@[export quic_h_app_close]
def appClose (code : UInt64) : AppAction := .close code.toNat

/-! ## `LocalAction`: what the harness has to synthesise for the send side -/

@[export quic_h_local_sent_packet]
def localSentPacket (ptype : UInt8) (pn : UInt64) (ackEliciting : UInt8) : LocalAction :=
  .sentPacket (ptypeOf ptype) pn.toNat (ackEliciting != 0)

@[export quic_h_local_sent_frame_in]
def localSentFrameIn (ptype : UInt8) (src dest : UInt64) (f : Frame) : LocalAction :=
  .sentFrameIn (ptypeOf ptype) ⟨⟨src.toNat⟩, ⟨dest.toNat⟩⟩ f

@[export quic_h_local_sent_packet_frames]
def localSentPacketFrames (space : UInt8) (pn : UInt64) (fs : List Frame) : LocalAction :=
  .sentPacketFrames (spaceOf space) pn.toNat fs

@[export quic_h_local_sent_datagram]
def localSentDatagram (dest n : UInt64) : LocalAction := .sentDatagram ⟨dest.toNat⟩ n.toNat

@[export quic_h_local_local_error]
def localLocalError (code frameType : UInt64) : LocalAction :=
  .localError (errorOfCode code.toNat) frameType.toNat
where
  /-- §20.1's table, as `Endpoint.closeReasonOfFrame` reads it. -/
  errorOfCode : Nat → TransportError
    | 0x0 => .noError | 0x1 => .internalError | 0x2 => .connectionRefused
    | 0x3 => .flowControlError | 0x4 => .streamLimitError | 0x5 => .streamStateError
    | 0x6 => .finalSizeError | 0x7 => .frameEncodingError
    | 0x8 => .transportParameterError | 0x9 => .connectionIdLimitError
    | 0xa => .protocolViolation | 0xb => .invalidToken | 0xc => .applicationError
    | 0xd => .cryptoBufferExceeded | 0xe => .keyUpdateError | 0xf => .aeadLimitReached
    | 0x10 => .noViablePath
    | n => if 0x100 ≤ n ∧ n ≤ 0x1ff then .cryptoError (n - 0x100).toUInt8 else .internalError

@[export quic_h_local_issue_cid]
def localIssueCid (cid token : ByteArray) (rpt : UInt64) : LocalAction :=
  .issueCid cid.toList token.toList rpt.toNat

@[export quic_h_local_retire_cid]
def localRetireCid (seq : UInt64) : LocalAction := .retireCid seq.toNat

/-! ### What a frame on the wire says the endpoint already decided

ngtcp2 issues and retires connection IDs inside the writer; the only trace of
the decision is the frame that announces it (§19.15, §19.16).  `ConnIds.Local`
and `ConnIds.Remote` want the decision as an event before they will let the
frame be sent, so the harness reads it back off the wire.  The NEW_CONNECTION_ID
frames of one datagram are replayed in increasing sequence number, because
`ConnIds.Local.Event.issueCid` numbers them itself and ngtcp2 writes them in
decreasing order. -/

private def insertBySeq (x : Nat × LocalAction) :
    List (Nat × LocalAction) → List (Nat × LocalAction)
  | [] => [x]
  | y :: t => if x.1 ≤ y.1 then x :: y :: t else y :: insertBySeq x t

private def sortBySeq : List (Nat × LocalAction) → List (Nat × LocalAction)
  | [] => []
  | x :: t => insertBySeq x (sortBySeq t)

@[export quic_h_presend_actions]
def presendActions (fs : List Frame) : List LocalAction :=
  (sortBySeq (fs.filterMap fun f =>
      match f with
      | .newConnectionId seq rpt cid token =>
        some (seq, LocalAction.issueCid cid.toList token.toList rpt)
      | _ => none)).map (·.2) ++
    fs.filterMap fun f =>
      match f with
      | .retireConnectionId seq => some (LocalAction.retireCid seq)
      | _ => none

@[export quic_h_actions_length]
def actionsLength (as : List LocalAction) : UInt64 := as.length.toUInt64

@[export quic_h_actions_get]
def actionsGet (as : List LocalAction) (i : UInt64) : LocalAction :=
  as.getD i.toNat (.retirementBacklog 0)

/-! ## Frames and packets

The harness never builds a `Frame` field by field: it hands over the bytes of a
packet payload and `Quic.decodeFrames` — the very function `harness/frame_diff.c`
is already differentially tested against — makes the list. -/

/-- The frames of a (decrypted) packet payload, in order.  A payload that stops
    parsing yields the frames before the error, which is what `conn_trace.c`'s
    `dump_frames_joined` shows too. -/
@[export quic_h_frames_of_bytes]
def framesOfBytes (buf : ByteArray) : List Frame := ((decodeFrames buf).1.map (·.1)).toList

@[export quic_h_frames_length]
def framesLength (fs : List Frame) : UInt64 := fs.length.toUInt64

@[export quic_h_frames_get]
def framesGet (fs : List Frame) (i : UInt64) : Frame := fs.getD i.toNat .ping

@[export quic_h_out_packet]
def outPacket (ptype : UInt8) (fs : List Frame) : OutPacket := ⟨ptypeOf ptype, fs⟩

/-- §13.2, line 5018: does a packet with these frames elicit an acknowledgment?
    `Endpoint.sentPacket` needs it and the trace does not carry it. -/
@[export quic_h_ack_eliciting]
def ackEliciting (fs : List Frame) : UInt8 := if FrameRules.packetAckEliciting fs then 1 else 0

/-! ## Rendering, for the mismatch reports -/

@[export quic_h_frame_dump]
def frameDump (f : Frame) : String := f.dump

@[export quic_h_frames_dump]
def framesDump (fs : List Frame) : String := "; ".intercalate (fs.map Frame.dump)

end Quic.Harness
