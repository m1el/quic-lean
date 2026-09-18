import QuicModel.Spec.Core
import QuicModel.RoundTrip

/-
  §18 Transport Parameter Encoding: the parameter identifiers, the
  `TransportParams` record with the defaults §18.2 gives, the wire codec, and
  the validity predicate that §7.4 / §18.2 attach to received values.

  The component that consumes all of this is `QuicModel/Spec/TransportParams.lean`.
-/
namespace Quic.Spec.TransportParams

/-! ## Parameter identifiers (§18.2) -/

/-- The seventeen transport parameters defined by §18.2.  Every other
    identifier — including the reserved `31 * N + 27` family of §18.1 — is
    unknown and MUST be ignored (§7.4.2). -/
inductive ParamId where
  | originalDestinationConnectionId   -- 0x00
  | maxIdleTimeout                    -- 0x01
  | statelessResetToken               -- 0x02
  | maxUdpPayloadSize                 -- 0x03
  | initialMaxData                    -- 0x04
  | initialMaxStreamDataBidiLocal     -- 0x05
  | initialMaxStreamDataBidiRemote    -- 0x06
  | initialMaxStreamDataUni           -- 0x07
  | initialMaxStreamsBidi             -- 0x08
  | initialMaxStreamsUni              -- 0x09
  | ackDelayExponent                  -- 0x0a
  | maxAckDelay                       -- 0x0b
  | disableActiveMigration            -- 0x0c
  | preferredAddress                  -- 0x0d
  | activeConnectionIdLimit           -- 0x0e
  | initialSourceConnectionId         -- 0x0f
  | retrySourceConnectionId           -- 0x10
  deriving DecidableEq, Repr

namespace ParamId

def code : ParamId → Nat
  | .originalDestinationConnectionId => 0x00
  | .maxIdleTimeout => 0x01
  | .statelessResetToken => 0x02
  | .maxUdpPayloadSize => 0x03
  | .initialMaxData => 0x04
  | .initialMaxStreamDataBidiLocal => 0x05
  | .initialMaxStreamDataBidiRemote => 0x06
  | .initialMaxStreamDataUni => 0x07
  | .initialMaxStreamsBidi => 0x08
  | .initialMaxStreamsUni => 0x09
  | .ackDelayExponent => 0x0a
  | .maxAckDelay => 0x0b
  | .disableActiveMigration => 0x0c
  | .preferredAddress => 0x0d
  | .activeConnectionIdLimit => 0x0e
  | .initialSourceConnectionId => 0x0f
  | .retrySourceConnectionId => 0x10

def ofCode? : Nat → Option ParamId
  | 0x00 => some .originalDestinationConnectionId
  | 0x01 => some .maxIdleTimeout
  | 0x02 => some .statelessResetToken
  | 0x03 => some .maxUdpPayloadSize
  | 0x04 => some .initialMaxData
  | 0x05 => some .initialMaxStreamDataBidiLocal
  | 0x06 => some .initialMaxStreamDataBidiRemote
  | 0x07 => some .initialMaxStreamDataUni
  | 0x08 => some .initialMaxStreamsBidi
  | 0x09 => some .initialMaxStreamsUni
  | 0x0a => some .ackDelayExponent
  | 0x0b => some .maxAckDelay
  | 0x0c => some .disableActiveMigration
  | 0x0d => some .preferredAddress
  | 0x0e => some .activeConnectionIdLimit
  | 0x0f => some .initialSourceConnectionId
  | 0x10 => some .retrySourceConnectionId
  | _ => none

@[simp] theorem ofCode?_code (p : ParamId) : ofCode? p.code = some p := by
  cases p <;> rfl

theorem code_of_ofCode? {n : Nat} {p : ParamId} (h : ofCode? n = some p) : p.code = n := by
  unfold ofCode? at h
  split at h <;> first
    | (injection h with h; subst h; rfl)
    | simp at h

/-- §18.2, line 7149: "A client MUST NOT include any server-only transport
    parameter: original_destination_connection_id, preferred_address,
    retry_source_connection_id, or stateless_reset_token." -/
def serverOnly : ParamId → Bool
  | .originalDestinationConnectionId | .preferredAddress
  | .retrySourceConnectionId | .statelessResetToken => true
  | _ => false

/-- §18.1, line 6914: "Transport parameters with an identifier of the form
    "31 * N + 27" for integer values of N are reserved to exercise the
    requirement that unknown transport parameters be ignored." -/
def IsReserved (n : Nat) : Prop := n % 31 = 27

instance (n : Nat) : Decidable (IsReserved n) := by unfold IsReserved; infer_instance

/-- Reserved identifiers really are unknown, so §7.4.2 applies to them. -/
theorem ofCode?_reserved {n : Nat} (h : IsReserved n) : ofCode? n = none := by
  have h17 : 17 ≤ n := by unfold IsReserved at h; omega
  match n, h17 with
  | _ + 17, _ => rfl

end ParamId

/-! ## The preferred address (§18.2, Figure 22) -/

/-- §18.2, line 7099, Figure 22: IPv4 Address (32), IPv4 Port (16),
    IPv6 Address (128), IPv6 Port (16), Connection ID Length (8),
    Connection ID (..), Stateless Reset Token (128). -/
structure PreferredAddress where
  ipv4 : ByteArray
  ipv4Port : Nat
  ipv6 : ByteArray
  ipv6Port : Nat
  cid : ByteArray
  token : ByteArray
  deriving DecidableEq

/-- What the wire format can represent. -/
def PreferredAddress.WF (pa : PreferredAddress) : Prop :=
  pa.ipv4.size = 4 ∧ pa.ipv4Port < 65536 ∧ pa.ipv6.size = 16 ∧ pa.ipv6Port < 65536 ∧
  pa.cid.size < 256 ∧ pa.token.size = 16

/-! ## The parameter record (§18.2)

§18.2, line 6926: "Transport parameters have a default value of 0 if the
transport parameter is absent unless otherwise stated." -/

structure TransportParams where
  /-- 0x00, server only; §7.3. -/
  originalDestinationConnectionId : Option ByteArray := none
  /-- 0x01, milliseconds; §18.2, line 6939: "Idle timeout is disabled when
      both endpoints omit this transport parameter or specify a value of 0." -/
  maxIdleTimeout : Nat := 0
  /-- 0x02, 16 bytes, server only. -/
  statelessResetToken : Option ByteArray := none
  /-- 0x03; §18.2, line 6963: "The default for this parameter is the maximum
      permitted UDP payload of 65527.  Values below 1200 are invalid." -/
  maxUdpPayloadSize : Nat := 65527
  /-- 0x04 -/
  initialMaxData : Nat := 0
  /-- 0x05 -/
  initialMaxStreamDataBidiLocal : Nat := 0
  /-- 0x06 -/
  initialMaxStreamDataBidiRemote : Nat := 0
  /-- 0x07 -/
  initialMaxStreamDataUni : Nat := 0
  /-- 0x08 -/
  initialMaxStreamsBidi : Nat := 0
  /-- 0x09 -/
  initialMaxStreamsUni : Nat := 0
  /-- 0x0a; §18.2, line 7034: "If this value is absent, a default value of 3
      is assumed (indicating a multiplier of 8).  Values above 20 are
      invalid." -/
  ackDelayExponent : Nat := 3
  /-- 0x0b, milliseconds; §18.2, line 7044: "If this value is absent, a
      default of 25 milliseconds is assumed.  Values of 2^14 or greater are
      invalid." -/
  maxAckDelay : Nat := 25
  /-- 0x0c; §18.2, line 7062: "This parameter is a zero-length value." —
      presence is the value. -/
  disableActiveMigration : Bool := false
  /-- 0x0d, server only. -/
  preferredAddress : Option PreferredAddress := none
  /-- 0x0e; §18.2, line 7127: "If this transport parameter is absent, a
      default of 2 is assumed." -/
  activeConnectionIdLimit : Nat := 2
  /-- 0x0f; §7.3. -/
  initialSourceConnectionId : Option ByteArray := none
  /-- 0x10, server only; §7.3. -/
  retrySourceConnectionId : Option ByteArray := none
  deriving DecidableEq

/-- Every parameter absent: the defaults of §18.2. -/
def defaults : TransportParams := {}

/-! ## Value-level codecs

Every parameter value is a self-contained byte string; `exactly` runs a parser
over it and insists that it consumed all of it.  A value that is too short or
has trailing bytes is malformed. -/

/-- Run `p` over exactly the bytes of `v`. -/
def exactly (p : P α) (v : ByteArray) : Option α :=
  match p.run v 0 with
  | .ok (a, pos) => if pos = v.size then some a else none
  | .error _ => none

theorem exactly_of_parses {α : Type} {p : P α} {enc : ByteArray} {a : α}
    (h : Parses p enc a) : exactly p enc = some a := by
  have h := h .empty .empty
  rw [ByteArray.empty_append, ByteArray.append_empty] at h
  have hz : ByteArray.empty.size = 0 := rfl
  rw [hz, Nat.zero_add] at h
  simp only [exactly, h, ↓reduceIte]

/-- §18.2, line 6924: "Those transport parameters that are identified as
    integers use a variable-length integer encoding; see Section 16." -/
def varintValue? (v : ByteArray) : Option Nat := exactly P.varint v

theorem varintValue?_encodeVarint {n : Nat} (h : n ≤ maxVarint) :
    varintValue? (encodeVarint n) = some n :=
  exactly_of_parses (parses_varint n h)

/-- §18.2, line 7099, Figure 22, as a parser. -/
def preferredAddressP : P PreferredAddress := do
  let ipv4 ← P.take 4
  let p4 ← P.uintBE 2
  let ipv6 ← P.take 16
  let p6 ← P.uintBE 2
  let cidLen ← P.u8
  let cid ← P.take cidLen.toNat
  let token ← P.take 16
  return { ipv4 := ipv4, ipv4Port := p4, ipv6 := ipv6, ipv6Port := p6,
           cid := cid, token := token }

def decodePreferredAddress (v : ByteArray) : Option PreferredAddress :=
  exactly preferredAddressP v

def encodePreferredAddress (pa : PreferredAddress) : ByteArray :=
  pa.ipv4 ++ (bytes (beBytes pa.ipv4Port 2) ++ (pa.ipv6 ++ (bytes (beBytes pa.ipv6Port 2) ++
    (bytes [pa.cid.size.toUInt8] ++ (pa.cid ++ pa.token)))))

theorem parses_uintBE2 {n : Nat} (h : n < 65536) :
    Parses (P.uintBE 2) (bytes (beBytes n 2)) n := by
  have hsz : (bytes (beBytes n 2)).size = 2 := by simp [beBytes]
  have ht := parses_take (bytes (beBytes n 2))
  rw [hsz] at ht
  have hval : beNat (bytes (beBytes n 2)) = n := by
    simp only [beBytes, beNat_bytes]
    simp
    omega
  have := Parses.map (fun b => beNat b) ht
  rw [hval] at this
  exact this

theorem parses_preferredAddress (pa : PreferredAddress) (h : pa.WF) :
    Parses preferredAddressP (encodePreferredAddress pa) pa := by
  obtain ⟨h4, hp4, h6, hp6, hc, ht⟩ := h
  have t4 := parses_take pa.ipv4; rw [h4] at t4
  have t6 := parses_take pa.ipv6; rw [h6] at t6
  have tt := parses_take pa.token; rw [ht] at tt
  have hcil : (pa.cid.size.toUInt8).toNat = pa.cid.size := by
    simp [Nat.toUInt8]; omega
  refine Parses.bind t4 (Parses.bind (parses_uintBE2 hp4) (Parses.bind t6
    (Parses.bind (parses_uintBE2 hp6) (Parses.bind (parses_u8 _) ?_))))
  simp only [hcil]
  exact Parses.bind (parses_take pa.cid) (Parses.map _ tt)

theorem decodePreferredAddress_encode (pa : PreferredAddress) (h : pa.WF) :
    decodePreferredAddress (encodePreferredAddress pa) = some pa :=
  exactly_of_parses (parses_preferredAddress pa h)

/-! ## The sequence of parameters (§18, Figures 20 and 21)

§18, line 6895: "Each transport parameter is encoded as an (identifier, length,
value) tuple, as shown in Figure 21"; line 6906: "The Transport Parameter
Length field contains the length of the Transport Parameter Value field in
bytes."

    Transport Parameter { ID (i), Length (i), Value (..) }

`Raw` is the list of `(identifier, value bytes)` pairs exactly as they appear
on the wire, before any of them is interpreted. -/

abbrev Raw := List (Nat × ByteArray)

def paramEntry : P (Nat × ByteArray) := do
  let id ← P.varint
  let len ← P.varint
  let v ← P.take len
  return (id, v)

/-- Decode a whole `Transport Parameters` sequence, with `fuel` an upper bound
    on the bytes left to read.  The recursion is structural in `fuel` so that
    the decoder reduces in the kernel (`decide` works on it).  The `pos < pos'`
    guard is dead code — `paramEntry` always consumes at least two bytes, see
    `paramEntry_progress` — and so is `fuel = 0` with bytes still to read, since
    every entry consumes at least one byte. -/
def decodeRawAux : Nat → ByteArray → Nat → Except Err Raw
  | 0, _, _ => .ok []
  | fuel + 1, buf, pos =>
    if pos < buf.size then
      match paramEntry.run buf pos with
      | .error e => .error e
      | .ok (kv, pos') =>
        if pos < pos' then (decodeRawAux fuel buf pos').map (kv :: ·)
        else .error .truncated
    else .ok []

def decodeRaw (buf : ByteArray) (pos : Nat := 0) : Except Err Raw :=
  decodeRawAux (buf.size - pos) buf pos

/-- The name the work package uses for `decodeRaw`. -/
abbrev decodeTransportParams (b : ByteArray) : Except Err Raw := decodeRaw b

def encodeRawEntry (e : Nat × ByteArray) : ByteArray :=
  encodeVarint e.1 ++ (encodeVarint e.2.size ++ e.2)

def encodeRaw : Raw → ByteArray
  | [] => .empty
  | e :: es => encodeRawEntry e ++ encodeRaw es

/-- What the wire format can represent: identifiers and lengths are varints. -/
def RawWF (raw : Raw) : Prop := ∀ e ∈ raw, e.1 ≤ maxVarint ∧ e.2.size ≤ maxVarint

/-! ### The entry parser makes progress -/

theorem P.run_le {α : Type} {p : P α} {buf : ByteArray} {pos : Nat} {a : α} {pos' : Nat}
    (h : p.run buf pos = .ok (a, pos')) : pos ≤ pos' := by
  simp only [P.run] at h
  cases hp : p buf pos with
  | error e => rw [hp] at h; simp only [Except.map] at h; exact absurd h (by simp)
  | ok r =>
    obtain ⟨⟨a', p'⟩, hle⟩ := r
    rw [hp] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    omega

theorem run_u8_eq {buf : ByteArray} {pos : Nat} {b : UInt8} {pos' : Nat}
    (h : P.u8.run buf pos = .ok (b, pos')) : pos' = pos + 1 := by
  simp only [P.run, P.u8] at h
  split at h
  · simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h; omega
  · exact absurd h (by simp [Except.map])

theorem varint_progress {buf : ByteArray} {pos v pos' : Nat}
    (h : P.varint.run buf pos = .ok (v, pos')) : pos < pos' := by
  simp only [P.varint, P.varintL, P.run_bind] at h
  cases h8 : P.u8.run buf pos with
  | error e => simp only [h8] at h; exact absurd h (by simp)
  | ok r =>
    obtain ⟨b, p1⟩ := r
    have hp1 : p1 = pos + 1 := run_u8_eq h8
    simp only [h8] at h
    cases ht : (P.varintTail b).run buf p1 with
    | error e => simp only [ht] at h; exact absurd h (by simp)
    | ok r2 =>
      obtain ⟨t, p2⟩ := r2
      simp only [ht, P.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
      have := P.run_le ht
      omega

theorem paramEntry_progress {buf : ByteArray} {pos : Nat} {kv : Nat × ByteArray} {pos' : Nat}
    (h : paramEntry.run buf pos = .ok (kv, pos')) : pos < pos' := by
  simp only [paramEntry, P.run_bind] at h
  cases h1 : P.varint.run buf pos with
  | error e => simp only [h1] at h; exact absurd h (by simp)
  | ok r1 =>
    obtain ⟨id, p1⟩ := r1
    have hlt := varint_progress h1
    simp only [h1] at h
    cases h2 : P.varint.run buf p1 with
    | error e => simp only [h2] at h; exact absurd h (by simp)
    | ok r2 =>
      obtain ⟨len, p2⟩ := r2
      have hle2 := P.run_le h2
      simp only [h2] at h
      cases h3 : (P.take len).run buf p2 with
      | error e => simp only [h3] at h; exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨v, p3⟩ := r3
        have hle3 := P.run_le h3
        simp only [h3, P.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        omega

/-! ### Round trip of the sequence -/

theorem parses_paramEntry {e : Nat × ByteArray} (h1 : e.1 ≤ maxVarint) (h2 : e.2.size ≤ maxVarint) :
    Parses paramEntry (encodeRawEntry e) e := by
  obtain ⟨id, v⟩ := e
  exact Parses.bind (parses_varint id h1)
    (Parses.bind (parses_varint v.size h2) (Parses.map (fun b => (id, b)) (parses_take v)))

theorem one_le_size_encodeRawEntry (e : Nat × ByteArray) : 1 ≤ (encodeRawEntry e).size := by
  have := one_le_size_encodeVarint e.1
  simp only [encodeRawEntry, ByteArray.size_append]
  omega

theorem size_encodeRaw_cons (e : Nat × ByteArray) (es : Raw) :
    (encodeRaw (e :: es)).size = (encodeRawEntry e).size + (encodeRaw es).size := by
  simp [encodeRaw, ByteArray.size_append]

theorem decodeRawAux_encodeRaw (raw : Raw) (h : RawWF raw) :
    ∀ (fuel : Nat) (pre : ByteArray), (encodeRaw raw).size ≤ fuel →
      decodeRawAux fuel (pre ++ encodeRaw raw) pre.size = .ok raw := by
  induction raw with
  | nil =>
    intro fuel pre _
    have hsz : (pre ++ encodeRaw ([] : Raw)).size = pre.size := by simp [encodeRaw]
    cases fuel with
    | zero => rfl
    | succ f => simp only [decodeRawAux, hsz, Nat.lt_irrefl, ↓reduceIte]
  | cons e es ih =>
    intro fuel pre hf
    have he := h e (by simp)
    have hes : RawWF es := fun x hx => h x (by simp [hx])
    have h1 : 1 ≤ (encodeRawEntry e).size := one_le_size_encodeRawEntry e
    have hsize := size_encodeRaw_cons e es
    cases fuel with
    | zero => exact absurd hf (by rw [hsize]; omega)
    | succ f =>
      have hbuf : pre ++ encodeRaw (e :: es) = pre ++ encodeRawEntry e ++ encodeRaw es := by
        simp [encodeRaw, ByteArray.append_assoc]
      have hpar := parses_paramEntry he.1 he.2 pre (encodeRaw es)
      have hlt : pre.size < (pre ++ encodeRaw (e :: es)).size := by
        rw [hbuf]; simp only [ByteArray.size_append]; omega
      rw [decodeRawAux]
      simp only [hlt, ↓reduceIte]
      rw [hbuf, hpar]
      have hprog : pre.size < pre.size + (encodeRawEntry e).size := by omega
      simp only [hprog, ↓reduceIte]
      have hih := ih hes f (pre ++ encodeRawEntry e) (by rw [hsize] at hf; omega)
      simp only [ByteArray.size_append, ByteArray.append_assoc] at hih ⊢
      rw [hih]
      rfl

theorem decodeRaw_encodeRaw_at (raw : Raw) (h : RawWF raw) (pre : ByteArray) :
    decodeRaw (pre ++ encodeRaw raw) pre.size = .ok raw := by
  unfold decodeRaw
  refine decodeRawAux_encodeRaw raw h _ pre ?_
  simp only [ByteArray.size_append]
  omega

/-- **Wire round trip.**  A representable sequence of transport parameters
    decodes back to itself. -/
theorem decodeRaw_encodeRaw (raw : Raw) (h : RawWF raw) : decodeRaw (encodeRaw raw) = .ok raw := by
  have := decodeRaw_encodeRaw_at raw h .empty
  rw [ByteArray.empty_append] at this
  have hz : ByteArray.empty.size = 0 := rfl
  rw [hz] at this
  exact this

/-! ## Interpreting the raw sequence (§18.2)

§7.4.2, line 2670: "An endpoint MUST ignore transport parameters that it does
not support."  `knownEntries` is where that happens: an entry whose identifier
is not one of the seventeen of §18.2 — including every reserved `31*N+27`
identifier of §18.1 — is dropped before anything else looks at it. -/

def knownEntries : Raw → List (ParamId × ByteArray)
  | [] => []
  | (id, v) :: l =>
    match ParamId.ofCode? id with
    | some p => (p, v) :: knownEntries l
    | none => knownEntries l

def knownIds (raw : Raw) : List ParamId := (knownEntries raw).map Prod.fst

@[simp] theorem knownEntries_append (l₁ l₂ : Raw) :
    knownEntries (l₁ ++ l₂) = knownEntries l₁ ++ knownEntries l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨id, v⟩ := a
    cases h : ParamId.ofCode? id <;> simp [knownEntries, h, ih]

/-- Interpret one parameter's value bytes.  `none` is a malformed value: a
    length that does not match the parameter's definition, or an integer field
    that is not exactly one variable-length integer. -/
def setParam (tp : TransportParams) : ParamId → ByteArray → Option TransportParams
  | .originalDestinationConnectionId, v =>
      some { tp with originalDestinationConnectionId := some v }
  | .maxIdleTimeout, v => (varintValue? v).map fun n => { tp with maxIdleTimeout := n }
  | .statelessResetToken, v =>
      if v.size = 16 then some { tp with statelessResetToken := some v } else none
  | .maxUdpPayloadSize, v => (varintValue? v).map fun n => { tp with maxUdpPayloadSize := n }
  | .initialMaxData, v => (varintValue? v).map fun n => { tp with initialMaxData := n }
  | .initialMaxStreamDataBidiLocal, v =>
      (varintValue? v).map fun n => { tp with initialMaxStreamDataBidiLocal := n }
  | .initialMaxStreamDataBidiRemote, v =>
      (varintValue? v).map fun n => { tp with initialMaxStreamDataBidiRemote := n }
  | .initialMaxStreamDataUni, v =>
      (varintValue? v).map fun n => { tp with initialMaxStreamDataUni := n }
  | .initialMaxStreamsBidi, v =>
      (varintValue? v).map fun n => { tp with initialMaxStreamsBidi := n }
  | .initialMaxStreamsUni, v =>
      (varintValue? v).map fun n => { tp with initialMaxStreamsUni := n }
  | .ackDelayExponent, v => (varintValue? v).map fun n => { tp with ackDelayExponent := n }
  | .maxAckDelay, v => (varintValue? v).map fun n => { tp with maxAckDelay := n }
  | .disableActiveMigration, v =>
      if v.size = 0 then some { tp with disableActiveMigration := true } else none
  | .preferredAddress, v =>
      (decodePreferredAddress v).map fun pa => { tp with preferredAddress := some pa }
  | .activeConnectionIdLimit, v =>
      (varintValue? v).map fun n => { tp with activeConnectionIdLimit := n }
  | .initialSourceConnectionId, v => some { tp with initialSourceConnectionId := some v }
  | .retrySourceConnectionId, v => some { tp with retrySourceConnectionId := some v }

/-- Apply known entries left to right, starting from the §18.2 defaults.
    A later copy of a parameter overwrites an earlier one — the *last copy
    wins*.  §7.4, line 2540 says duplicates SHOULD be an error; an endpoint
    that does not take that advice has to pick a copy, and the text does not
    say which, so `applyEntriesFirst` below is the other reading and the
    component permits both. -/
def applyEntries : List (ParamId × ByteArray) → TransportParams → Option TransportParams
  | [], tp => some tp
  | (p, v) :: l, tp => (setParam tp p v).bind (applyEntries l)

/-- The other reading of a repeated parameter: the *first copy wins*, which is
    what an "insert if absent" decoder produces.  `seen` collects the
    identifiers already applied.

    A later copy's value is still parsed, and a malformed one still makes the
    whole extension invalid: §7.4, line 2535 ("An endpoint MUST treat receipt
    of a transport parameter with an invalid value as a connection error of
    type TRANSPORT_PARAMETER_ERROR") is a MUST about *receipt*, and a copy that
    does not apply has still been received.  Only the field update is
    suppressed. -/
def applyEntriesFirst : List (ParamId × ByteArray) → List ParamId → TransportParams →
    Option TransportParams
  | [], _, tp => some tp
  | (p, v) :: l, seen, tp =>
    match setParam tp p v with
    | none => none
    | some tp' => applyEntriesFirst l (p :: seen) (if p ∈ seen then tp else tp')

/-- With no repeated identifier the two folds agree; they differ only on the
    duplicates §7.4 leaves unspecified. -/
theorem applyEntriesFirst_eq :
    ∀ (l : List (ParamId × ByteArray)) (seen : List ParamId) (tp : TransportParams),
      (l.map Prod.fst).Nodup → (∀ e ∈ l, e.1 ∉ seen) →
      applyEntriesFirst l seen tp = applyEntries l tp := by
  intro l
  induction l with
  | nil => intro _ _ _ _; rfl
  | cons a l ih =>
    obtain ⟨p, v⟩ := a
    intro seen tp hnd hs
    have hp : p ∉ seen := hs (p, v) (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hs' : ∀ e ∈ l, e.1 ∉ p :: seen := by
      intro e he
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => hnd.1 (List.mem_map.mpr ⟨e, he, h⟩), hs e (List.mem_cons_of_mem _ he)⟩
    cases hsp : setParam tp p v with
    | none =>
      have hL : applyEntriesFirst ((p, v) :: l) seen tp = none := by
        simp [applyEntriesFirst, hsp]
      have hR : applyEntries ((p, v) :: l) tp = none := by simp [applyEntries, hsp]
      rw [hL, hR]
    | some tp' =>
      have hL : applyEntriesFirst ((p, v) :: l) seen tp = applyEntriesFirst l (p :: seen) tp' := by
        simp [applyEntriesFirst, hsp, hp]
      have hR : applyEntries ((p, v) :: l) tp = applyEntries l tp' := by
        simp [applyEntries, hsp]
      rw [hL, hR]
      exact ih (p :: seen) tp' hnd.2 hs'

theorem applyEntries_append (l₁ l₂ : List (ParamId × ByteArray)) (tp : TransportParams) :
    applyEntries (l₁ ++ l₂) tp = (applyEntries l₁ tp).bind (applyEntries l₂) := by
  induction l₁ generalizing tp with
  | nil => simp [applyEntries]
  | cons a l ih =>
    obtain ⟨p, v⟩ := a
    cases h : setParam tp p v <;> simp [applyEntries, h, ih]

/-- The parameters a sequence of raw entries denotes, or `none` if any value is
    malformed.  A repeated known parameter takes its **last** copy. -/
def interpret (raw : Raw) : Option TransportParams := applyEntries (knownEntries raw) defaults

/-- The same, taking the **first** copy of a repeated known parameter. -/
def interpretFirst (raw : Raw) : Option TransportParams :=
  applyEntriesFirst (knownEntries raw) [] defaults

/-- The two readings of §7.4's unspecified duplicate handling coincide whenever
    no known parameter actually repeats. -/
theorem interpretFirst_eq_interpret {raw : Raw} (hnd : (knownIds raw).Nodup) :
    interpretFirst raw = interpret raw :=
  applyEntriesFirst_eq _ [] defaults hnd (by simp)

/-! ## Encoding a parameter record

Canonical choices: parameters appear in ascending identifier order, integers use
the shortest variable-length encoding, and a parameter whose value is an
`Option`/flag appears only when it is present.  Integer parameters are always
emitted, including at their default value — §18.2 permits that. -/

/-- A known parameter that is present only when its value is. -/
def optEntry (p : ParamId) : Option ByteArray → List (ParamId × ByteArray)
  | some v => [(p, v)]
  | none => []

/-- The parameters a record denotes, in ascending identifier order. -/
def toEntries (tp : TransportParams) : List (ParamId × ByteArray) :=
  optEntry .originalDestinationConnectionId tp.originalDestinationConnectionId ++
  ((.maxIdleTimeout, vi tp.maxIdleTimeout) ::
   optEntry .statelessResetToken tp.statelessResetToken ++
  ((.maxUdpPayloadSize, vi tp.maxUdpPayloadSize) ::
   (.initialMaxData, vi tp.initialMaxData) ::
   (.initialMaxStreamDataBidiLocal, vi tp.initialMaxStreamDataBidiLocal) ::
   (.initialMaxStreamDataBidiRemote, vi tp.initialMaxStreamDataBidiRemote) ::
   (.initialMaxStreamDataUni, vi tp.initialMaxStreamDataUni) ::
   (.initialMaxStreamsBidi, vi tp.initialMaxStreamsBidi) ::
   (.initialMaxStreamsUni, vi tp.initialMaxStreamsUni) ::
   (.ackDelayExponent, vi tp.ackDelayExponent) ::
   (.maxAckDelay, vi tp.maxAckDelay) ::
   (if tp.disableActiveMigration then [(ParamId.disableActiveMigration, .empty)] else []) ++
  ((match tp.preferredAddress with
    | some pa => [(ParamId.preferredAddress, encodePreferredAddress pa)]
    | none => []) ++
  ((.activeConnectionIdLimit, vi tp.activeConnectionIdLimit) ::
   optEntry .initialSourceConnectionId tp.initialSourceConnectionId ++
   optEntry .retrySourceConnectionId tp.retrySourceConnectionId))))

/-- Each parameter appears at most once in an encoded record. -/
theorem nodup_toEntries (tp : TransportParams) : ((toEntries tp).map Prod.fst).Nodup := by
  obtain ⟨odc, idle, srt, mups, imd, b5, b6, b7, s8, s9, ade, mad, dam, pa, acl, iscid, rscid⟩ := tp
  cases odc <;> cases srt <;> cases pa <;> cases iscid <;> cases rscid <;> cases dam <;>
    simp [toEntries, optEntry]

/-- Forget the parameter names: what actually goes on the wire. -/
def rawOf : List (ParamId × ByteArray) → Raw
  | [] => []
  | (p, v) :: l => (p.code, v) :: rawOf l

@[simp] theorem knownEntries_rawOf (l : List (ParamId × ByteArray)) : knownEntries (rawOf l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => obtain ⟨p, v⟩ := a; simp [rawOf, knownEntries, ih]

def toRaw (tp : TransportParams) : Raw := rawOf (toEntries tp)

def encodeParams (tp : TransportParams) : ByteArray := encodeRaw (toRaw tp)

/-- Parameter records the wire format can represent. -/
def TransportParams.WF (tp : TransportParams) : Prop :=
  tp.maxIdleTimeout ≤ maxVarint ∧ tp.maxUdpPayloadSize ≤ maxVarint ∧
  tp.initialMaxData ≤ maxVarint ∧ tp.initialMaxStreamDataBidiLocal ≤ maxVarint ∧
  tp.initialMaxStreamDataBidiRemote ≤ maxVarint ∧ tp.initialMaxStreamDataUni ≤ maxVarint ∧
  tp.initialMaxStreamsBidi ≤ maxVarint ∧ tp.initialMaxStreamsUni ≤ maxVarint ∧
  tp.ackDelayExponent ≤ maxVarint ∧ tp.maxAckDelay ≤ maxVarint ∧
  tp.activeConnectionIdLimit ≤ maxVarint ∧
  (∀ c, tp.originalDestinationConnectionId = some c → c.size ≤ maxVarint) ∧
  (∀ c, tp.initialSourceConnectionId = some c → c.size ≤ maxVarint) ∧
  (∀ c, tp.retrySourceConnectionId = some c → c.size ≤ maxVarint) ∧
  (∀ t, tp.statelessResetToken = some t → t.size = 16) ∧
  (∀ pa, tp.preferredAddress = some pa → pa.WF)

/-- The interpretation half of the round trip: encoding a record as parameters
    and reading them back gives the record. -/
theorem interpret_toRaw (tp : TransportParams) (hwf : tp.WF) : interpret (toRaw tp) = some tp := by
  rw [interpret, toRaw, knownEntries_rawOf]
  obtain ⟨odc, idle, srt, mups, imd, b5, b6, b7, s8, s9, ade, mad, dam, pa, acl, iscid, rscid⟩ := tp
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, ho, hi, hr, ht, hp⟩ := hwf
  cases odc <;> cases srt <;> cases pa <;> cases iscid <;> cases rscid <;> cases dam <;>
    simp_all [toEntries, optEntry, applyEntries, setParam, defaults,
      varintValue?_encodeVarint, decodePreferredAddress_encode]

/-! ### The encoding is representable -/

theorem thousand_le_maxVarint : 1000 ≤ maxVarint := by decide

theorem le_maxVarint_of_le {n : Nat} (h : n ≤ 1000) : n ≤ maxVarint :=
  Nat.le_trans h thousand_le_maxVarint

theorem size_vi_le (v : Nat) : (vi v).size ≤ maxVarint := by
  refine le_maxVarint_of_le ?_
  rw [size_encodeVarint]
  unfold varintLen
  repeat' split
  all_goals omega

theorem code_le_maxVarint (p : ParamId) : p.code ≤ maxVarint := by
  cases p <;> exact le_maxVarint_of_le (by decide)

theorem size_encodePreferredAddress (pa : PreferredAddress) :
    (encodePreferredAddress pa).size =
      pa.ipv4.size + 2 + (pa.ipv6.size + (2 + (1 + (pa.cid.size + pa.token.size)))) := by
  simp only [encodePreferredAddress, ByteArray.size_append, size_bytes, beBytes]
  simp
  omega

theorem rawWF_rawOf (l : List (ParamId × ByteArray)) (h : ∀ e ∈ l, e.2.size ≤ maxVarint) :
    RawWF (rawOf l) := by
  induction l with
  | nil => intro e he; simp [rawOf] at he
  | cons a l ih =>
    obtain ⟨p, v⟩ := a
    intro e he
    simp only [rawOf, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨code_le_maxVarint p, h (p, v) (by simp)⟩
    · exact ih (fun x hx => h x (by simp [hx])) e he

theorem size_encodePreferredAddress_le (pa : PreferredAddress) (h : pa.WF) :
    (encodePreferredAddress pa).size ≤ maxVarint := by
  obtain ⟨h4, -, h6, -, hc, ht⟩ := h
  rw [size_encodePreferredAddress, h4, h6, ht]
  exact le_maxVarint_of_le (by omega)

theorem rawWF_toRaw (tp : TransportParams) (hwf : tp.WF) : RawWF (toRaw tp) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ho, hi, hr, ht, hp⟩ := hwf
  have hpa : ∀ pa, tp.preferredAddress = some pa → (encodePreferredAddress pa).size ≤ maxVarint :=
    fun pa h => size_encodePreferredAddress_le pa (hp pa h)
  clear hp
  refine rawWF_rawOf _ ?_
  obtain ⟨odc, idle, srt, mups, imd, b5, b6, b7, s8, s9, ade, mad, dam, pa, acl, iscid, rscid⟩ := tp
  intro e he
  have hv := size_vi_le
  have hmv := thousand_le_maxVarint
  cases odc <;> cases srt <;> cases pa <;> cases iscid <;> cases rscid <;> cases dam <;>
    simp_all [toEntries, optEntry] <;>
    first
      | omega
      | (rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl | rfl | rfl | rfl <;> simp_all <;> omega)

/-! ## The receive-side codec -/

/-- §18: decode the extension's bytes, ignore unknown identifiers, interpret the
    rest.  `none` is "malformed": a truncated or over-long sequence, or a
    parameter value that does not match its definition. -/
def decodeParams (b : ByteArray) : Option TransportParams :=
  match decodeRaw b with
  | .ok raw => interpret raw
  | .error _ => none

/-- **Round trip (a).**  Every representable parameter record encodes to bytes
    that decode back to it. -/
theorem decodeParams_encodeParams (tp : TransportParams) (hwf : tp.WF) :
    decodeParams (encodeParams tp) = some tp := by
  simp only [decodeParams, encodeParams, decodeRaw_encodeRaw _ (rawWF_toRaw tp hwf),
    interpret_toRaw tp hwf]

end Quic.Spec.TransportParams
