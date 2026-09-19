import QuicModel.Api.Usage

/-!
  The C interface of the API-usage monitor, in the style of
  `Spec/Endpoint/Exports.lean`: `@[export quic_api_…]` on plain functions over
  scalars.  A call is `kind` plus the arguments the contract looks at; unused
  ones are ignored.  Violations come back as a bit mask, bit `i` being
  `Clause.all[i]`.
-/
namespace Quic.Api

/-- 0 `read_pkt`, 1 `writev_stream`, 2 `handle_expiry`,
    3 `extend_max_stream_offset`. -/
def callOf (kind : UInt8) (pathNull : UInt8) (path pi dest destlen ts : UInt64) : Call :=
  match kind with
  | 0 => .readPkt (pathNull != 0) ts.toNat
  | 1 => .writevStream ⟨path.toNat, pi.toNat, dest.toNat, destlen.toNat, ts.toNat⟩
  | 2 => .handleExpiry ts.toNat
  | _ => .extendMaxStreamOffset

/-- ngtcp2's return code as a `Ret`.  `more` is whether
    `NGTCP2_WRITE_STREAM_FLAG_MORE` was passed: `NGTCP2_ERR_STREAM_DATA_BLOCKED`
    (-208) leaves a packet pending only then (c:4493–4500).  -230 WRITE_MORE;
    -220 STREAM_NOT_FOUND, -219 STREAM_SHUT_WR and -201 INVALID_ARGUMENT return
    before the packet is touched; -223 CLOSING, -224 DRAINING. -/
def retOfCode (code : Int) (more : Bool) : Ret :=
  if code ≥ 0 then .done
  else if code = -230 then .pending
  else if code = -208 then (if more then .pending else .unchanged)
  else if code = -220 ∨ code = -219 ∨ code = -201 then .unchanged
  else if code = -223 ∨ code = -224 then .closed
  else .terminal

def maskOf (cs : List Clause) : UInt32 :=
  (Clause.all.zipIdx.filter (fun ci => cs.contains ci.1)).foldl
    (fun m ci => m ||| ((1 : UInt32) <<< ci.2.toUInt32)) 0

@[export quic_api_init]
def initC (_ : UInt8) : State := {}

@[export quic_api_check]
def checkC (s : State) (kind pathNull : UInt8) (path pi dest destlen ts : UInt64) : UInt32 :=
  maskOf (check s (callOf kind pathNull path pi dest destlen ts))

/-- `code` is the return value as a 64-bit two's complement. -/
@[export quic_api_post]
def postC (s : State) (kind pathNull : UInt8) (path pi dest destlen ts : UInt64) (code : UInt64)
    (more : UInt8) : State :=
  post s (callOf kind pathNull path pi dest destlen ts)
    (retOfCode (Int.ofNat code.toNat - (if code ≥ 0x8000000000000000 then 2 ^ 64 else 0))
      (more != 0))

@[export quic_api_enter_callback]
def enterCallbackC (s : State) : State := enterCallback s

@[export quic_api_exit_callback]
def exitCallbackC (s : State) : State := exitCallback s

@[export quic_api_is_pending]
def isPendingC (s : State) : UInt8 := if s.isPending then 1 else 0

@[export quic_api_clause_count]
def clauseCountC (_ : UInt8) : UInt8 := Clause.all.length.toUInt8

/-- `name [enforcement]` of clause `i`. -/
@[export quic_api_clause_name]
def clauseNameC (i : UInt8) : String :=
  match Clause.all[i.toNat]? with
  | some c => s!"{c.name} [{c.enforcement.name}]"
  | none => "?"

example : maskOf [.tsMonotonic, .pathNonNull] = 0b100001 := by decide
example : retOfCode (-230) false = .pending := by decide
example : retOfCode (-208) false = .unchanged ∧ retOfCode (-208) true = .pending := by decide
example : retOfCode (-238) false = .terminal := by decide

end Quic.Api
