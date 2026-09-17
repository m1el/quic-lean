import QuicModel.Basic

/-
  QUIC frames (RFC 9000 §19, RFC 9221 DATAGRAM) and their wire decoder.

  `decodeFrame` is the *syntactic* layer: it accepts exactly the byte strings
  that have the shape of a frame.  Value constraints that the RFC also files
  under FRAME_ENCODING_ERROR (e.g. MAX_STREAMS > 2^60) live in `Frame.check`,
  because ngtcp2 defers those to the connection layer, not `ngtcp2_pkt.c`.
-/
namespace Quic

inductive StreamDir where | bidi | uni
  deriving Repr, DecidableEq

structure AckRange where
  gap : Nat
  len : Nat
  deriving Repr, DecidableEq

structure Ecn where
  ect0 : Nat
  ect1 : Nat
  ce : Nat
  deriving Repr, DecidableEq

inductive Frame where
  /-- A run of `len ≥ 1` PADDING bytes (ngtcp2 coalesces them; so do we). -/
  | padding (len : Nat)
  | ping
  | ack (largest delay first : Nat) (ranges : Array AckRange) (ecn : Option Ecn)
  | resetStream (id err finalSize : Nat)
  | stopSending (id err : Nat)
  | crypto (offset : Nat) (data : ByteArray)
  | newToken (token : ByteArray)
  | stream (id offset : Nat) (fin : Bool) (data : ByteArray)
  | maxData (v : Nat)
  | maxStreamData (id v : Nat)
  | maxStreams (dir : StreamDir) (v : Nat)
  | dataBlocked (v : Nat)
  | streamDataBlocked (id v : Nat)
  | streamsBlocked (dir : StreamDir) (v : Nat)
  | newConnectionId (seq retirePriorTo : Nat) (cid token : ByteArray)
  | retireConnectionId (seq : Nat)
  | pathChallenge (data : ByteArray)
  | pathResponse (data : ByteArray)
  /-- `frameType = none` is the application variant (0x1d). -/
  | connectionClose (err : Nat) (frameType : Option Nat) (reason : ByteArray)
  | handshakeDone
  | datagram (hasLen : Bool) (data : ByteArray)
  deriving DecidableEq

open P

/-- `count` ACK ranges, by structural recursion on the count. -/
def ackRangesAux : Nat → Array AckRange → P (Array AckRange)
  | 0, acc => pure acc
  | n + 1, acc => do
    let gap ← varint
    let len ← varint
    ackRangesAux n (acc.push { gap, len })

def ackRanges (count : Nat) : P (Array AckRange) := do
  -- Every range needs at least two bytes; reject absurd counts up front so the
  -- recursion depth is bounded by the input size, not by a 62-bit number.
  if count * 2 > (← remaining) then throw .truncated
  ackRangesAux count (Array.mkEmpty count)

/-- The fields of a frame of type `ty`, after the type has been consumed. -/
def frameOfType (ty : Nat) : P Frame := do
  match ty with
  | 0x00 => return .padding (1 + (← skipZeros))
  | 0x01 => return .ping
  | 0x02 | 0x03 =>
    let largest ← varint
    let delay ← varint
    let count ← varint
    let first ← varint
    let ranges ← ackRanges count
    let ecn ← if ty == 0x03 then do
        let ect0 ← varint
        let ect1 ← varint
        let ce ← varint
        pure (some { ect0, ect1, ce : Ecn })
      else pure none
    return .ack largest delay first ranges ecn
  | 0x04 => return .resetStream (← varint) (← varint) (← varint)
  | 0x05 => return .stopSending (← varint) (← varint)
  | 0x06 =>
    let off ← varint
    let len ← varint
    return .crypto off (← take len)
  | 0x07 =>
    let len ← varint
    return .newToken (← take len)
  | 0x10 => return .maxData (← varint)
  | 0x11 => return .maxStreamData (← varint) (← varint)
  | 0x12 => return .maxStreams .bidi (← varint)
  | 0x13 => return .maxStreams .uni (← varint)
  | 0x14 => return .dataBlocked (← varint)
  | 0x15 => return .streamDataBlocked (← varint) (← varint)
  | 0x16 => return .streamsBlocked .bidi (← varint)
  | 0x17 => return .streamsBlocked .uni (← varint)
  | 0x18 =>
    let seq ← varint
    let rpt ← varint
    let cil := (← u8).toNat
    if cil < 1 ∨ cil > 20 then throw (.badCidLen cil)
    let cid ← take cil
    let token ← take 16
    return .newConnectionId seq rpt cid token
  | 0x19 => return .retireConnectionId (← varint)
  | 0x1a => return .pathChallenge (← take 8)
  | 0x1b => return .pathResponse (← take 8)
  | 0x1c =>
    let err ← varint
    let fty ← varint
    let len ← varint
    return .connectionClose err (some fty) (← take len)
  | 0x1d =>
    let err ← varint
    let len ← varint
    return .connectionClose err none (← take len)
  | 0x1e => return .handshakeDone
  | 0x30 => return .datagram false (← rest)
  | 0x31 =>
    let len ← varint
    return .datagram true (← take len)
  | _ =>
    if 0x08 ≤ ty ∧ ty ≤ 0x0f then
      let id ← varint
      let off ← if ty &&& 0x04 ≠ 0 then varint else pure 0
      let data ← if ty &&& 0x02 ≠ 0 then do take (← varint) else rest
      return .stream id off (ty &&& 0x01 ≠ 0) data
    else
      throw (.unknownFrameType ty)

/-- A frame whose first byte `b0` has already been consumed. -/
def frameBody (b0 : UInt8) : P Frame := do
  let (ty, tyLen) ← varintTail b0
  if tyLen ≠ varintLen ty then throw (.nonMinimalFrameType ty)
  frameOfType ty

/-- Decode the frame that starts at `pos`.  The result type says the cursor
    moved strictly forward: a frame is at least its type byte. -/
def decodeFrame (buf : ByteArray) (pos : Nat := 0) : Except Err (Res1 pos Frame) :=
  if h : pos < buf.size then
    match frameBody buf[pos] buf (pos + 1) with
    | .error e => .error e
    | .ok ⟨r, hr⟩ => .ok ⟨r, Nat.lt_of_succ_le hr⟩
  else .error .truncated

/-- Decode a whole packet payload the way `fuzz/decode_frame.cc` drives the C
    decoder: frame after frame until the input is exhausted or one fails.
    Each frame is paired with the number of bytes it occupied.  Terminates
    because `decodeFrame` makes progress. -/
def decodeFrames (buf : ByteArray) (pos : Nat := 0) (acc : Array (Frame × Nat) := #[]) :
    Array (Frame × Nat) × Option Err :=
  if pos < buf.size then
    match decodeFrame buf pos with
    | .error e => (acc, some e)
    | .ok ⟨(f, pos'), _⟩ => decodeFrames buf pos' (acc.push (f, pos' - pos))
  else (acc, none)
termination_by buf.size - pos
decreasing_by omega

/-! ### Semantic checks the RFC attaches to individual frames -/

/-- §19.3.1: walk the ranges downwards from `smallest`; any computed packet
    number going negative is an error. -/
def checkAckRanges (smallest : Nat) : List AckRange → Option String
  | [] => none
  | r :: rs =>
    if smallest < r.gap + 2 then some "ACK: gap underflows packet number space"
    else if smallest - r.gap - 2 < r.len then
      some "ACK: range length underflows packet number space"
    else checkAckRanges (smallest - r.gap - 2 - r.len) rs

/-- RFC 9000 value constraints that are decidable from the frame alone.
    Returns a description of the first violated rule. -/
def Frame.check : Frame → Option String
  | .ack largest _ first ranges _ =>
    if first > largest then some "ACK: first range exceeds largest acknowledged"
    else checkAckRanges (largest - first) ranges.toList
  | .stream _ off _ data =>
    if off + data.size > maxVarint then some "STREAM: offset + length exceeds 2^62-1" else none
  | .crypto off data =>
    if off + data.size > maxVarint then some "CRYPTO: offset + length exceeds 2^62-1" else none
  | .newToken token =>
    if token.size == 0 then some "NEW_TOKEN: empty token" else none
  | .maxStreams _ v =>
    if v > 2 ^ 60 then some "MAX_STREAMS: exceeds 2^60" else none
  | .streamsBlocked _ v =>
    if v > 2 ^ 60 then some "STREAMS_BLOCKED: exceeds 2^60" else none
  | .newConnectionId seq rpt _ _ =>
    if rpt > seq then some "NEW_CONNECTION_ID: retire_prior_to > sequence number" else none
  | _ => none

end Quic
