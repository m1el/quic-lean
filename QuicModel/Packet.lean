import QuicModel.Frame

/-
  QUIC packets (RFC 8999, RFC 9000 §17, RFC 9369 for v2 type codes), with packet
  protection abstracted behind `Protection` so that it can be stubbed.
-/
namespace Quic

def versionV1 : Nat := 0x00000001
def versionV2 : Nat := 0x6b3343cf
def isSupportedVersion (v : Nat) : Bool := v == versionV1 || v == versionV2

def maxCidLen : Nat := 20
def hpSampleLen : Nat := 16
def retryTagLen : Nat := 16

inductive LongType where | initial | zeroRtt | handshake | retry
  deriving Repr, DecidableEq

/-- Long packet type from the two type bits; v2 rotates the code points. -/
def longType (version bits : Nat) : LongType :=
  let bits := if version == versionV2 then (bits + 3) % 4 else bits
  match bits with
  | 0 => .initial | 1 => .zeroRtt | 2 => .handshake | _ => .retry

inductive Header where
  | versionNegotiation (dcid scid : ByteArray)
  /-- `length` is the Length field (packet number + payload); 0 for Retry. -/
  | long (ty : LongType) (version : Nat) (fixedBit : Bool)
      (dcid scid token : ByteArray) (length : Nat)
  | short (fixedBit : Bool) (dcid : ByteArray)

open P

private def cid : P ByteArray := do
  let n := (← u8).toNat
  if n > maxCidLen then throw (.badCidLen n)
  take n

/-- The header fields that follow first byte `b0`, up to but not including the
    packet number. -/
def headerBody (shortDcidLen : Nat) (b0 : Nat) : P Header := do
  let fixedBit := b0 &&& 0x40 ≠ 0
  if b0 &&& 0x80 == 0 then
    return .short fixedBit (← take shortDcidLen)
  let version ← uintBE 4
  let dcid ← cid
  let scid ← cid
  if version == 0 then
    return .versionNegotiation dcid scid
  if !isSupportedVersion version then
    throw (.badHeader "unsupported version")
  match longType version ((b0 >>> 4) &&& 3) with
  | .initial =>
    let token ← take (← varint)
    return .long .initial version fixedBit dcid scid token (← varint)
  | .retry => return .long .retry version fixedBit dcid scid .empty 0
  | ty => return .long ty version fixedBit dcid scid .empty (← varint)

/-- First byte (still header-protected in its low bits) and header.  This is
    the part that is readable without removing header protection, and it is
    what `ngtcp2_pkt_decode_hd_long` / `_short` compute. -/
def header (shortDcidLen : Nat) : P (UInt8 × Header) := do
  let b0 ← u8
  return (b0, ← headerBody shortDcidLen b0.toNat)

def decodeHeader (buf : ByteArray) (shortDcidLen : Nat) (pos : Nat := 0) :
    Except Err (Header × Nat) :=
  ((header shortDcidLen).run buf pos).map fun ((_, hd), n) => (hd, n)

/-! ### Routing a datagram before any connection exists (RFC 9000 §5.2, §6) -/

inductive Route where
  | deliver              -- look the DCID up / create a connection
  | sendVersionNegotiation
  deriving Repr, DecidableEq

structure VersionCid where
  version : Nat
  dcid : ByteArray
  scid : ByteArray

/-- The version-independent view of a datagram (RFC 8999) plus the server's
    routing decision.  Mirrors `ngtcp2_pkt_decode_version_cid`. -/
def versionCid (buf : ByteArray) (shortDcidLen : Nat) : Except Err (VersionCid × Route) :=
  let p : P (VersionCid × Route) := do
    let b0 := (← u8).toNat
    if b0 &&& 0x80 == 0 then
      return ({ version := 0, dcid := ← take shortDcidLen, scid := .empty }, .deliver)
    let version ← uintBE 4
    -- RFC 8999 allows CIDs up to 255 bytes here; only known versions cap at 20.
    let dcid ← take (← u8).toNat
    let scid ← take (← u8).toNat
    let vc := { version, dcid, scid : VersionCid }
    if version == 0 then return (vc, .deliver)
    if isSupportedVersion version then
      if dcid.size > maxCidLen ∨ scid.size > maxCidLen then
        throw (.badCidLen (max dcid.size scid.size))
      return (vc, .deliver)
    -- §5.2.2 / §6.1: only answer unknown versions if the datagram is big
    -- enough to have been a valid Initial in some version.
    if buf.size < 1200 then throw (.badHeader "unsupported version, small datagram")
    return (vc, .sendVersionNegotiation)
  (p.run buf).map (·.1)

/-! ### Packet numbers (RFC 9000 §17.1, Appendix A.3) -/

/-- Recover the full packet number from its `len`-byte truncation, given the
    next expected packet number (largest received + 1). -/
def decodePacketNumber (expected truncated len : Nat) : Nat :=
  let win := 2 ^ (8 * len)
  let hwin := win / 2
  let cand := expected - expected % win + truncated
  if cand + hwin ≤ expected ∧ cand + win < 2 ^ 62 then cand + win
  else if cand > expected + hwin ∧ cand ≥ win then cand - win
  else cand

/-! ### Packet protection, abstracted -/

/-- What the model needs from packet protection.  Real QUIC instantiates this
    with AEAD + a header-protection cipher; `Protection.stub` does not. -/
structure Protection where
  tagLen : Nat
  /-- 5-byte header-protection mask from a 16-byte ciphertext sample. -/
  hpMask : ByteArray → ByteArray
  /-- AEAD open: header bytes (AAD), packet number, ciphertext‖tag ↦ plaintext. -/
  aeadOpen : (aad : ByteArray) → (pn : Nat) → (ct : ByteArray) → Option ByteArray
  /-- §17.2.5.2 / [QUIC-TLS] §5.8: does the Retry Integrity Tag validate?  The
      arguments are the client's original Destination Connection ID (the Retry
      Pseudo-Packet is prefixed with it), the Retry packet without its tag, and
      the tag.  The algorithm stays abstract; the *outcome* has to reach the
      transport rules, because §17.2.5.2 makes it decide whether the packet is
      discarded. -/
  retryTagOk : (odcid : ByteArray) → (retry : ByteArray) → (tag : ByteArray) → Bool

/-- Stub protection shared with `harness/pkt_diff.c`: the payload is sent in the
    clear, the tag is `tagLen` bytes of 0xA5, and the header-protection mask is
    the first five bytes of the sample.  A Retry Integrity Tag follows the same
    convention: it validates when it is sixteen bytes of 0xA5.  Not secure; but it still exercises the
    sample offset, the masked header bits and the tag position. -/
def Protection.stub (tagLen : Nat := 16) : Protection where
  tagLen := tagLen
  hpMask sample := sample.extract 0 5
  aeadOpen _ _ ct :=
    if ct.size < tagLen then none else
    let tag := ct.extract (ct.size - tagLen) ct.size
    if tag.data.all (· == 0xa5) then some (ct.extract 0 (ct.size - tagLen)) else none
  retryTagOk _ _ tag := tag.size == retryTagLen && tag.data.all (· == 0xa5)

inductive PacketErr where
  | header (e : Err)
  | lengthExceedsDatagram
  | tooShortForSample
  | fixedBitClear               -- §17.2 / §17.3.1: MUST be discarded
  | reservedBits               -- PROTOCOL_VIOLATION
  | decryptFailed
  | emptyPayload               -- PROTOCOL_VIOLATION
  | frame (e : Err)            -- FRAME_ENCODING_ERROR
  | badVersionList
  | badRetry

def PacketErr.toString : PacketErr → String
  | .header e => s!"header: {e}"
  | .lengthExceedsDatagram => "length exceeds datagram"
  | .tooShortForSample => "too short for header-protection sample"
  | .fixedBitClear => "fixed bit clear"
  | .reservedBits => "reserved bits set"
  | .decryptFailed => "decrypt failed"
  | .emptyPayload => "empty payload"
  | .frame e => s!"frame: {e}"
  | .badVersionList => "bad version list"
  | .badRetry => "bad retry"

instance : ToString PacketErr := ⟨PacketErr.toString⟩

inductive Body where
  | versions (vs : Array Nat)
  | retry (token tag : ByteArray)
  | payload (pn pnLen : Nat) (keyPhase : Bool) (frames : Array (Frame × Nat))

structure Packet where
  header : Header
  headerLen : Nat
  body : Body

/-- `n` big-endian 32-bit versions. -/
private def versionList : Nat → Array Nat → P (Array Nat)
  | 0, acc => pure acc
  | n + 1, acc => do versionList n (acc.push (← uintBE 4))

/-- Remove header protection from the first byte and the packet number field.
    `pnField` is the four bytes at the packet number offset (the real field may
    be shorter).  Returns the first byte and the packet number bytes, unmasked. -/
def unmaskHeader (isLong : Bool) (b0 : UInt8) (pnField mask : ByteArray) : UInt8 × ByteArray :=
  let b0 := b0 ^^^ (byteAt mask 0 &&& (if isLong then 0x0f else 0x1f))
  let pnLen := (b0.toNat &&& 3) + 1
  let pn := (List.range pnLen).map fun i => byteAt pnField i ^^^ byteAt mask (i + 1)
  (b0, ⟨pn.toArray⟩)

/-- Decode the packet that starts at `pos` in a datagram; returns it together
    with the offset of the next coalesced packet.

    `greaseQuicBit`: the peer's `grease_quic_bit` transport parameter was
    received (RFC 9287), which lifts the draft's "fixed bit = 0 MUST be
    discarded" rule.  Version Negotiation is always exempt: its low seven bits
    are Unused. -/
def decodePacket (prot : Protection) (buf : ByteArray) (shortDcidLen expectedPn : Nat)
    (greaseQuicBit : Bool := false) (pos : Nat := 0) : Except PacketErr (Packet × Nat) := do
  let ((b0, hd), pnOff) ← ((header shortDcidLen).run buf pos).mapError .header
  let mk (body : Body) (next : Nat) : Packet × Nat :=
    ({ header := hd, headerLen := pnOff - pos, body }, next)
  let fixedOk := greaseQuicBit || match hd with
    | .long _ _ fixed .. => fixed
    | .short fixed _ => fixed
    | .versionNegotiation .. => true
  if !fixedOk then throw .fixedBitClear
  match hd with
  | .versionNegotiation .. =>
    let n := buf.size - pnOff
    if n == 0 ∨ n % 4 ≠ 0 then throw .badVersionList
    match (versionList (n / 4) #[]).run buf pnOff with
    | .ok (vs, _) => return mk (.versions vs) buf.size
    | .error _ => throw .badVersionList
  | .long .retry .. =>
    let n := buf.size - pnOff
    if n < 1 + retryTagLen then throw .badRetry
    let split := buf.size - retryTagLen
    return mk (.retry (buf.extract pnOff split) (buf.extract split buf.size)) buf.size
  | _ =>
    let (isLong, pktEnd) := match hd with
      | .long _ _ _ _ _ _ length => (true, pnOff + length)
      | _ => (false, buf.size)
    if pktEnd > buf.size then throw .lengthExceedsDatagram
    -- Header protection: the sample starts 4 bytes after the start of the
    -- packet number field, whatever the real packet number length is.
    if pnOff + 4 + hpSampleLen > pktEnd then throw .tooShortForSample
    let mask := prot.hpMask (buf.extract (pnOff + 4) (pnOff + 4 + hpSampleLen))
    let (b0, pnBytes) := unmaskHeader isLong b0 (buf.extract pnOff (pnOff + 4)) mask
    let pnLen := pnBytes.size
    let pn := decodePacketNumber expectedPn (beNat pnBytes) pnLen
    -- AAD is the header with protection removed.
    let aad := (ByteArray.empty.push b0) ++ buf.extract (pos + 1) pnOff ++ pnBytes
    let some plain := prot.aeadOpen aad pn (buf.extract (pnOff + pnLen) pktEnd)
      | throw .decryptFailed
    if b0.toNat &&& (if isLong then 0x0c else 0x18) ≠ 0 then throw .reservedBits
    if plain.size == 0 then throw .emptyPayload
    let (frames, err) := decodeFrames plain
    if let some e := err then throw (.frame e)
    return mk (.payload pn pnLen (!isLong && b0.toNat &&& 0x04 ≠ 0) frames) pktEnd

end Quic
