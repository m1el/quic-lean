import QuicModel.Packet
import QuicModel.Encode

/-
  Canonical text rendering of decoded frames, shared with `harness/frame_diff.c`.
  One line per frame: `NAME k=v ... n=<bytes consumed>`.

  `ngtcp2MaxAckRanges`: ngtcp2 parses every ACK range but only *stores* the first
  32 (`NGTCP2_MAX_ACK_RANGES`), so the comparison view truncates as well.  This is
  the single place where the dump deliberately shows less than the model knows.
-/
namespace Quic

def ngtcp2MaxAckRanges : Nat := 32

private def dirStr : StreamDir → String
  | .bidi => "bidi"
  | .uni => "uni"

def Frame.dump : Frame → String
  | .padding len => s!"PADDING len={len}"
  | .ping => "PING"
  | .ack largest delay first ranges ecn =>
    let kept := ranges.extract 0 ngtcp2MaxAckRanges
    let rs := ",".intercalate (kept.toList.map fun r => s!"{r.gap}:{r.len}")
    let e := match ecn with
      | none => ""
      | some e => s!" ecn={e.ect0},{e.ect1},{e.ce}"
    s!"ACK largest={largest} delay={delay} first={first} ranges=[{rs}]{e}"
  | .resetStream id err fs => s!"RESET_STREAM id={id} err={err} final={fs}"
  | .stopSending id err => s!"STOP_SENDING id={id} err={err}"
  | .crypto off data => s!"CRYPTO off={off} data={hex data}"
  | .newToken token => s!"NEW_TOKEN token={hex token}"
  | .stream id off fin data =>
    s!"STREAM id={id} off={off} fin={if fin then 1 else 0} data={hex data}"
  | .maxData v => s!"MAX_DATA v={v}"
  | .maxStreamData id v => s!"MAX_STREAM_DATA id={id} v={v}"
  | .maxStreams d v => s!"MAX_STREAMS dir={dirStr d} v={v}"
  | .dataBlocked v => s!"DATA_BLOCKED v={v}"
  | .streamDataBlocked id v => s!"STREAM_DATA_BLOCKED id={id} v={v}"
  | .streamsBlocked d v => s!"STREAMS_BLOCKED dir={dirStr d} v={v}"
  | .newConnectionId seq rpt cid token =>
    s!"NEW_CONNECTION_ID seq={seq} rpt={rpt} cid={hex cid} token={hex token}"
  | .retireConnectionId seq => s!"RETIRE_CONNECTION_ID seq={seq}"
  | .pathChallenge d => s!"PATH_CHALLENGE data={hex d}"
  | .pathResponse d => s!"PATH_RESPONSE data={hex d}"
  | .connectionClose err fty reason =>
    let t := match fty with
      | some t => s!"kind=transport err={err} ftype={t}"
      | none => s!"kind=app err={err} ftype=0"
    s!"CONNECTION_CLOSE {t} reason={hex reason}"
  | .handshakeDone => "HANDSHAKE_DONE"
  | .datagram hasLen data => s!"DATAGRAM len={if hasLen then 1 else 0} data={hex data}"

/-- Dump of a whole payload.  With `verbose`, errors name the rule that fired and
    frames that parse but violate an RFC value constraint get a `# check:` note;
    without it the text is exactly what the C harness prints. -/
def dumpFrames (buf : ByteArray) (verbose : Bool := false) : String :=
  let (frames, err) := decodeFrames buf
  let line (s : String) (fn : Frame × Nat) : String :=
    let s := s ++ fn.1.dump ++ s!" n={fn.2}\n"
    match verbose, fn.1.check with
    | true, some why => s ++ s!"# check: {why}\n"
    | _, _ => s
  frames.foldl line "" ++ match err with
    | none => "END\n"
    | some e => if verbose then s!"ERR {e}\n" else "ERR\n"

/-! ### Packets -/

private def longTypeStr : LongType → String
  | .initial => "INITIAL" | .zeroRtt => "0RTT" | .handshake => "HANDSHAKE" | .retry => "RETRY"

private def b01 (b : Bool) : Nat := if b then 1 else 0

def Header.dump : Header → String
  | .versionNegotiation dcid scid => s!"VN dcid={hex dcid} scid={hex scid}"
  | .long ty v fixed dcid scid token len =>
    s!"LONG type={longTypeStr ty} ver={v} fixed={b01 fixed} dcid={hex dcid} scid={hex scid} token={hex token} len={len}"
  | .short fixed dcid => s!"SHORT fixed={b01 fixed} dcid={hex dcid}"

def dumpHeader (buf : ByteArray) (shortDcidLen : Nat) : String :=
  let hd := match decodeHeader buf shortDcidLen with
    | .ok (h, n) => s!"{h.dump} hdlen={n}\n"
    | .error _ => "HD ERR\n"
  let vc := match versionCid buf shortDcidLen with
    | .ok (vc, r) =>
      let rc := if r == .deliver then "OK" else "VN"
      s!"VCID rc={rc} ver={vc.version} dcid={hex vc.dcid} scid={hex vc.scid}\n"
    | .error _ => "VCID ERR\n"
  hd ++ vc

def dumpPacket (buf : ByteArray) (shortDcidLen tagLen expectedPn : Nat)
    (greaseQuicBit : Bool := false) (verbose : Bool := false) : String :=
  match decodePacket (.stub tagLen) buf shortDcidLen expectedPn greaseQuicBit with
  | .error e => if verbose then s!"PKT ERR {e}\n" else "PKT ERR\n"
  | .ok (pkt, next) =>
    let body := match pkt.body with
      | .versions vs => s!"VERSIONS {vs.toList}\n"
      | .retry token tag => s!"RETRY token={hex token} tag={hex tag}\n"
      | .payload pn pnLen kp frames =>
        frames.foldl (fun s (f, n) => s ++ f.dump ++ s!" n={n}\n")
          s!"PN pn={pn} pnlen={pnLen} keyphase={b01 kp}\n"
    s!"{pkt.header.dump} hdlen={pkt.headerLen}\n" ++ body ++ s!"NEXT {next}\n"

@[export quic_model_dump_header]
def dumpHeaderC (buf : ByteArray) (shortDcidLen : UInt32) : String :=
  dumpHeader buf shortDcidLen.toNat

@[export quic_model_dump_packet]
def dumpPacketC (buf : ByteArray) (shortDcidLen tagLen : UInt32) (expectedPn : UInt64)
    (greaseQuicBit : UInt8) : String :=
  dumpPacket buf shortDcidLen.toNat tagLen.toNat expectedPn.toNat (greaseQuicBit != 0)

@[export quic_model_decode_pn]
def decodePacketNumberC (expected truncated : UInt64) (len : UInt8) : UInt64 :=
  (decodePacketNumber expected.toNat truncated.toNat len.toNat).toUInt64

/-! ### Encoder round trip, executable form -/

/-- Re-encode whatever `buf` decodes to; empty if `buf` is not a valid payload. -/
@[export quic_model_reencode]
def reencode (buf : ByteArray) : ByteArray :=
  match decodeFrames buf with
  | (fs, none) => encodeFrames (fs.map (·.1))
  | _ => .empty

/-- `decodeFrames (encodeFrames fs)` gives back exactly `fs`, for the frames
    found in `buf`.  1 = holds (or `buf` invalid), 0 = violated. -/
@[export quic_model_roundtrip_ok]
def roundTripOk (buf : ByteArray) : UInt8 :=
  match decodeFrames buf with
  | (fs, none) =>
    let fs := fs.map (·.1)
    match decodeFrames (encodeFrames fs) with
    | (fs', none) => if fs'.map (·.1) == fs then 1 else 0
    | _ => 0
  | _ => 1

/-- C entry point used by the differential harness. -/
@[export quic_model_dump_frames]
def dumpFramesC (buf : ByteArray) : String := dumpFrames buf

end Quic
