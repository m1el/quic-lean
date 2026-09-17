/-
  Total byte-level parsers and QUIC variable-length integers (§16).

  Everything here is a total function: no `partial`, no `while`, no panicking
  index.  A parser's result type carries a proof that the cursor did not move
  backwards, so loops over parsers terminate by construction.
-/
namespace Quic

/-- Why decoding stopped.  ngtcp2 reports every one of these as
    `NGTCP2_ERR_FRAME_ENCODING` / `NGTCP2_ERR_INVALID_ARGUMENT`; the model keeps
    them apart so that a differential run can say *which* rule fired. -/
inductive Err where
  | truncated            -- ran out of input
  | unknownFrameType (ty : Nat)
  | nonMinimalFrameType (ty : Nat)   -- §12.4, MAY be PROTOCOL_VIOLATION
  | badCidLen (n : Nat)
  | badHeader (why : String)
  deriving Repr, DecidableEq

def Err.toString : Err → String
  | .truncated => "truncated"
  | .unknownFrameType ty => s!"unknown-frame-type {ty}"
  | .nonMinimalFrameType ty => s!"non-minimal-frame-type {ty}"
  | .badCidLen n => s!"bad-cid-len {n}"
  | .badHeader why => s!"bad-header {why}"

instance : ToString Err := ⟨Err.toString⟩

/-- Result of running a parser from `pos`: a value and the new cursor, which is
    never behind `pos`. -/
abbrev Res (pos : Nat) (α : Type) := { r : α × Nat // pos ≤ r.2 }

/-- Like `Res`, but the cursor moved strictly forward. -/
abbrev Res1 (pos : Nat) (α : Type) := { r : α × Nat // pos < r.2 }

/-- A parser reads from a fixed buffer at a cursor. -/
def P (α : Type) : Type := (buf : ByteArray) → (pos : Nat) → Except Err (Res pos α)

namespace P

@[inline] protected def pure (a : α) : P α :=
  fun _ pos => .ok ⟨(a, pos), Nat.le_refl _⟩

@[inline] protected def bind (p : P α) (f : α → P β) : P β := fun buf pos =>
  match p buf pos with
  | .error e => .error e
  | .ok ⟨(a, p1), h1⟩ =>
    match f a buf p1 with
    | .error e => .error e
    | .ok ⟨(b, p2), h2⟩ => .ok ⟨(b, p2), Nat.le_trans h1 h2⟩

instance : Monad P where
  pure := P.pure
  bind := P.bind

instance : MonadExceptOf Err P where
  throw e := fun _ _ => .error e
  tryCatch p handler := fun buf pos =>
    match p buf pos with
    | .error e => handler e buf pos
    | ok => ok

/-- Run a parser, forgetting the progress proof. -/
def run (p : P α) (buf : ByteArray) (pos : Nat := 0) : Except Err (α × Nat) :=
  (p buf pos).map (·.val)

def remaining : P Nat :=
  fun buf pos => .ok ⟨(buf.size - pos, pos), Nat.le_refl _⟩

def u8 : P UInt8 := fun buf pos =>
  if h : pos < buf.size then .ok ⟨(buf[pos], pos + 1), Nat.le_succ _⟩
  else .error .truncated

def take (n : Nat) : P ByteArray := fun buf pos =>
  if pos + n ≤ buf.size then .ok ⟨(buf.extract pos (pos + n), pos + n), Nat.le_add_right _ _⟩
  else .error .truncated

/-- Everything up to the end of the buffer. -/
def rest : P ByteArray := fun buf pos =>
  .ok ⟨(buf.extract pos buf.size, max pos buf.size), Nat.le_max_left _ _⟩

end P

/-- Big-endian value of `bs`, continuing from `init`. -/
def beNat (bs : ByteArray) (init : Nat := 0) : Nat :=
  bs.data.foldl (fun acc x => acc * 256 + x.toNat) init

/-- Total byte access: bytes past the end read as 0.  Only used where a
    preceding length check makes the default unreachable. -/
def byteAt (bs : ByteArray) (i : Nat) : UInt8 := bs.data.getD i 0

/-- Number of consecutive zero bytes starting at `pos`. -/
def zeroRun (buf : ByteArray) (pos : Nat) (acc : Nat := 0) : Nat :=
  if h : pos < buf.size then
    if buf[pos] = 0 then zeroRun buf (pos + 1) (acc + 1) else acc
  else acc
termination_by buf.size - pos

namespace P

/-- Skip a run of zero bytes; returns how many were skipped. -/
def skipZeros : P Nat := fun buf pos =>
  let n := zeroRun buf pos
  .ok ⟨(n, pos + n), Nat.le_add_right _ _⟩

/-- Big-endian unsigned integer of `n` bytes. -/
def uintBE (n : Nat) : P Nat := do
  return beNat (← take n)

/-- The rest of a varint whose first byte `b0` has already been consumed;
    returns `(value, encodedLength)`. -/
def varintTail (b0 : UInt8) : P (Nat × Nat) := do
  let len := 2 ^ (b0.toNat >>> 6)
  let tail ← take (len - 1)
  return (beNat tail (b0.toNat &&& 0x3f), len)

/-- Variable-length integer; returns `(value, encodedLength)`. -/
def varintL : P (Nat × Nat) := do
  varintTail (← u8)

def varint : P Nat := do
  return (← varintL).1

end P

/-- Shortest encoding length of a varint value. -/
def varintLen (v : Nat) : Nat :=
  if v < 64 then 1 else if v < 16384 then 2 else if v < 1073741824 then 4 else 8

def maxVarint : Nat := 2 ^ 62 - 1

/-- The low `n` bytes of `v`, big-endian. -/
def beBytes (v : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => beBytes (v / 256) n ++ [(v % 256).toUInt8]

/-- Encode a varint using exactly `len ∈ {1,2,4,8}` bytes. -/
def encodeVarintWith (v : Nat) (len : Nat) : ByteArray :=
  let tag : UInt8 := match len with | 1 => 0x00 | 2 => 0x40 | 4 => 0x80 | _ => 0xc0
  match beBytes v len with
  | [] => .empty
  | b :: bs => ⟨((b ||| tag) :: bs).toArray⟩

def encodeVarint (v : Nat) : ByteArray := encodeVarintWith v (varintLen v)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (b : ByteArray) : String :=
  b.data.foldl (fun s x => (s.push (hexDigit (x.toNat / 16))).push (hexDigit (x.toNat % 16))) ""

end Quic
