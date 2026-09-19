/-!
  **The application's side of the ngtcp2 API, as a typestate contract.**

  `QuicModel/Spec` says what the *peer* and ngtcp2 owe each other (RFC 9000).
  This file says what the *application* owes ngtcp2: which calls are legal in
  which state, and how each return value moves that state.  It is a monitor:
  `check s c` lists the clauses a call breaks *before* it is made, and
  `post s c r` is the state after it returned `r`.

  Trial scope — four functions:

  * `ngtcp2_conn_read_pkt`
  * `ngtcp2_conn_writev_stream`
  * `ngtcp2_conn_handle_expiry`
  * `ngtcp2_conn_extend_max_stream_offset`

  Sources, cited per clause as the specification cites the draft: `h:N` is
  `lib/includes/ngtcp2/ngtcp2.h` line `N`, `c:N` is `lib/ngtcp2_conn.c` line
  `N`, both at ngtcp2 `v1.25.0-92-g3c23148e`.  The implementation's assumptions
  are the primary source and the header's prose the second: a clause is in the
  contract if *either* needs it, and `Clause.enforcement` records what the code
  does about it.  `API_CONTRACT.md` is the inventory this was written from.
-/
namespace Quic.Api

/-! ## 1. Clauses -/

/-- What the implementation does when the clause is broken. -/
inductive Enforcement where
  /-- Checked, and reported to the caller as an error code. -/
  | errorReturn
  /-- An `assert`.  ngtcp2's `CMakeLists.txt:102` strips `-DNDEBUG` from
      Release flags on purpose, so a standard build aborts the process; an
      embedder who defines `NDEBUG` gets no check at all. -/
  | assertOnly
  /-- Relied on with no check at all: memory unsafety or silent corruption. -/
  | implicit
  /-- The header demands it; the code does not need it (today). -/
  | proseOnly
  deriving DecidableEq, Repr

inductive Clause where
  /-- `ts` never goes backwards across calls.  `conn_update_timestamp`,
      c:88 `assert(conn->log.last_ts <= ts)`.  `ngtcp2.h` does not say so
      anywhere; the only statement is `doc/source/programmers-guide.rst:122`,
      "any timestamp which increases monotonically". -/
  | tsMonotonic
  /-- h:4286 / h:5348: "This function must not be called from inside the
      callback functions."  No check in the code. -/
  | notInCallback
  /-- While a packet is pending (`NGTCP2_CONN_FLAG_PPE_PENDING`, set by a
      `NGTCP2_ERR_WRITE_MORE` return) only `writev_stream` may be called.
      h:5324: "it must not call other ngtcp2 API functions"; c:10379 and
      c:11432 assert it in `read_pkt` and `handle_expiry`. -/
  | noCallWhilePending
  /-- The same clause for a function the code does not guard:
      `extend_max_stream_offset` has no assert and is not in h:5326's list of
      exceptions, so the header forbids what the code permits. -/
  | noCallWhilePendingUnguarded
  /-- h:5304: on resuming a pending packet "Application has to specify the same
      |conn|, |path|, |pi|, |dest|, |destlen|, and |ts| parameters, otherwise
      the behaviour is undefined."  The code keeps a pointer into the first
      `dest` (`conn->pkt.ppe`, c:3557) and never compares. -/
  | pendingSameArgs
  /-- h:4282: "|path| … must not be ``NULL``."  Dereferenced unchecked
      (c:10391). -/
  | pathNonNull
  /-- h:5238: |destlen| "must be at least `NGTCP2_MAX_UDP_PAYLOAD_SIZE`"
      (1200).  The code returns 0 for a buffer under `conn_min_pktlen`
      (c:3598) and otherwise writes what fits. -/
  | destlenMin
  /-- h:4301–4308: after `NGTCP2_ERR_CLOSING` / `NGTCP2_ERR_DRAINING`
      "no further packet transmission is allowed".  The code answers with the
      same error again (c:10455, c:12462). -/
  | notWhenClosed
  /-- After `NGTCP2_ERR_IDLE_CLOSE` (h:4741 "drop the connection"),
      `NGTCP2_ERR_DROP_CONN` / `NGTCP2_ERR_RETRY` (h:4295 "discard connection
      state") or any other negative error (h:4313: only
      `ngtcp2_conn_write_connection_close` is left) none of the four functions
      may be called again.  No check in the code. -/
  | notAfterTerminal
  deriving DecidableEq, Repr

namespace Clause

def enforcement : Clause → Enforcement
  | .tsMonotonic => .assertOnly
  | .notInCallback => .implicit
  | .noCallWhilePending => .assertOnly
  | .noCallWhilePendingUnguarded => .proseOnly
  | .pendingSameArgs => .implicit
  | .pathNonNull => .implicit
  | .destlenMin => .proseOnly
  | .notWhenClosed => .errorReturn
  | .notAfterTerminal => .implicit

def _root_.Quic.Api.Enforcement.name : Enforcement → String
  | .errorReturn => "error return"
  | .assertOnly => "assert only"
  | .implicit => "unchecked"
  | .proseOnly => "header only"

/-- Every clause, in the order of the bit it has in the C interface. -/
def all : List Clause :=
  [.tsMonotonic, .notInCallback, .noCallWhilePending, .noCallWhilePendingUnguarded,
   .pendingSameArgs, .pathNonNull, .destlenMin, .notWhenClosed, .notAfterTerminal]

def name : Clause → String
  | .tsMonotonic => "tsMonotonic"
  | .notInCallback => "notInCallback"
  | .noCallWhilePending => "noCallWhilePending"
  | .noCallWhilePendingUnguarded => "noCallWhilePendingUnguarded"
  | .pendingSameArgs => "pendingSameArgs"
  | .pathNonNull => "pathNonNull"
  | .destlenMin => "destlenMin"
  | .notWhenClosed => "notWhenClosed"
  | .notAfterTerminal => "notAfterTerminal"

end Clause

/-! ## 2. Calls, returns, state -/

/-- The arguments h:5304 requires to stay the same while a packet is pending.
    Pointers are compared by identity, so an address is all that is kept. -/
structure WriteCtx where
  path : Nat
  pi : Nat
  dest : Nat
  destlen : Nat
  ts : Nat
  deriving DecidableEq, Repr

inductive Call where
  | readPkt (pathNull : Bool) (ts : Nat)
  | writevStream (ctx : WriteCtx)
  | handleExpiry (ts : Nat)
  | extendMaxStreamOffset
  deriving DecidableEq, Repr

/-- A return value, as far as the typestate depends on it.  The mapping from
    ngtcp2's codes is `Exports.retOfCode`. -/
inductive Ret where
  /-- Zero or positive: done, no packet left pending. -/
  | done
  /-- `NGTCP2_ERR_WRITE_MORE`, or `NGTCP2_ERR_STREAM_DATA_BLOCKED` under
      `NGTCP2_WRITE_STREAM_FLAG_MORE` (c:4493–4500): a packet is now pending. -/
  | pending
  /-- `NGTCP2_ERR_STREAM_NOT_FOUND`, `NGTCP2_ERR_STREAM_SHUT_WR`,
      `NGTCP2_ERR_INVALID_ARGUMENT`, and `NGTCP2_ERR_STREAM_DATA_BLOCKED`
      without the flag: returned before the packet is touched, so whatever was
      pending still is. -/
  | unchanged
  /-- `NGTCP2_ERR_CLOSING` / `NGTCP2_ERR_DRAINING`. -/
  | closed
  /-- `NGTCP2_ERR_IDLE_CLOSE`, `NGTCP2_ERR_DROP_CONN`, `NGTCP2_ERR_RETRY`, or
      any other negative code. -/
  | terminal
  deriving DecidableEq, Repr

inductive Phase where
  | ready
  /-- A packet is half-built in the buffer of `ctx` (`PPE_PENDING`). -/
  | pending (ctx : WriteCtx)
  | closed
  | terminal
  deriving DecidableEq, Repr

structure State where
  phase : Phase := .ready
  /-- The largest timestamp passed so far (`conn->log.last_ts`). -/
  lastTs : Nat := 0
  /-- How many of the application's callbacks are on the stack. -/
  cbDepth : Nat := 0
  deriving DecidableEq, Repr

def State.isPending (s : State) : Bool :=
  match s.phase with
  | .pending _ => true
  | _ => false

/-! ## 3. Preconditions -/

def Call.ts? : Call → Option Nat
  | .readPkt _ ts => some ts
  | .writevStream ctx => some ctx.ts
  | .handleExpiry ts => some ts
  | .extendMaxStreamOffset => none

/-- h:4286, h:5348.  `handle_expiry` and `extend_max_stream_offset` carry no
    such sentence, and ngtcp2's own `examples/sim.cc:102` calls the latter
    from `recv_stream_data`. -/
def Call.forbiddenInCallback : Call → Bool
  | .readPkt .. | .writevStream .. => true
  | _ => false

private def when (b : Bool) (c : Clause) : List Clause := if b then [c] else []

/-- The clauses `c` breaks in state `s`; `[]` means the call is legal. -/
def check (s : State) (c : Call) : List Clause :=
  when (match c.ts? with | some ts => decide (ts < s.lastTs) | none => false) .tsMonotonic ++
  when (c.forbiddenInCallback && decide (0 < s.cbDepth)) .notInCallback ++
  (match s.phase, c with
   | .pending _, .readPkt .. | .pending _, .handleExpiry .. => [.noCallWhilePending]
   | .pending _, .extendMaxStreamOffset => [.noCallWhilePendingUnguarded]
   | .pending ctx, .writevStream ctx' => when (decide (ctx' ≠ ctx)) .pendingSameArgs
   | _, _ => []) ++
  (match c with
   | .readPkt true _ => [.pathNonNull]
   | .writevStream ctx => when (decide (ctx.destlen < 1200)) .destlenMin
   | _ => []) ++
  when (decide (s.phase = .closed)) .notWhenClosed ++
  when (decide (s.phase = .terminal)) .notAfterTerminal

def Legal (s : State) (c : Call) : Prop := check s c = []

instance (s : State) (c : Call) : Decidable (Legal s c) := inferInstanceAs (Decidable (_ = _))

/-! ## 4. Postconditions -/

/-- The phase after `c` returned `r`.  Only `writev_stream` can leave a packet
    pending or complete one; a terminal connection stays terminal. -/
def nextPhase (p : Phase) (c : Call) (r : Ret) : Phase :=
  match p, r with
  | .terminal, _ => .terminal
  | _, .terminal => .terminal
  | _, .closed => .closed
  | p, .unchanged => p
  | p, .pending =>
    (match c, p with
     | .writevStream _, .pending ctx => .pending ctx  -- the first buffer stands
     | .writevStream ctx, _ => .pending ctx
     | _, p => p)
  | p, .done =>
    (match c, p with
     | .writevStream _, .pending _ => .ready
     | _, p => p)

def post (s : State) (c : Call) (r : Ret) : State :=
  { s with
    phase := nextPhase s.phase c r
    lastTs := match c.ts? with | some ts => max s.lastTs ts | none => s.lastTs }

def enterCallback (s : State) : State := { s with cbDepth := s.cbDepth + 1 }
def exitCallback (s : State) : State := { s with cbDepth := s.cbDepth - 1 }

/-! ## 5. Traces -/

/-- Run a trace of calls with their returns; the result is every violation,
    with the index of the call that committed it. -/
def run (s : State) (tr : List (Call × Ret)) (i : Nat := 0) : List (Nat × Clause) :=
  match tr with
  | [] => []
  | (c, r) :: rest => (check s c).map (i, ·) ++ run (post s c r) rest (i + 1)

def Conforms (tr : List (Call × Ret)) : Prop := run {} tr = []

instance (tr : List (Call × Ret)) : Decidable (Conforms tr) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## 6. What the typestate guarantees -/

/-- While a packet is pending, none of the other three functions is legal. -/
theorem pending_excludes {s : State} {ctx : WriteCtx} (h : s.phase = .pending ctx) (c : Call)
    (hc : ∀ ctx', c ≠ .writevStream ctx') : ¬ Legal s c := by
  unfold Legal check
  cases c with
  | writevStream ctx' => exact absurd rfl (hc ctx')
  | readPkt _ _ | handleExpiry _ | extendMaxStreamOffset =>
    simp [h]

/-- …and `writev_stream` is legal only with the arguments the packet was
    started with (h:5304). -/
theorem pending_same_args {s : State} {ctx ctx' : WriteCtx} (h : s.phase = .pending ctx)
    (hl : Legal s (.writevStream ctx')) : ctx' = ctx := by
  unfold Legal check at hl
  simp only [h, List.append_eq_nil_iff, when] at hl
  have := hl.1.1.1.2
  by_cases hne : ctx' = ctx
  · exact hne
  · simp [hne] at this

/-- Nothing is legal once the connection is terminal, and it stays terminal. -/
theorem terminal_absorbing {s : State} (h : s.phase = .terminal) (c : Call) (r : Ret) :
    ¬ Legal s c ∧ (post s c r).phase = .terminal := by
  refine ⟨?_, by simp [post, nextPhase, h]⟩
  unfold Legal check
  simp [h, when]

/-- A legal call never moves the clock backwards, and `lastTs` is the running
    maximum either way, so one bad timestamp is reported once. -/
theorem lastTs_mono (s : State) (c : Call) (r : Ret) : s.lastTs ≤ (post s c r).lastTs := by
  unfold post
  cases c.ts? <;> simp [Nat.le_max_left]

/-- Only `writev_stream` starts or finishes a pending packet. -/
theorem isPending_post_of_not_write {s : State} {c : Call} {r : Ret}
    (hc : ∀ ctx, c ≠ .writevStream ctx) (hr : r ≠ .terminal ∧ r ≠ .closed) :
    (post s c r).isPending = s.isPending := by
  obtain ⟨h1, h2⟩ := hr
  cases c with
  | writevStream ctx => exact absurd rfl (hc ctx)
  | readPkt _ _ | handleExpiry _ | extendMaxStreamOffset =>
    cases hp : s.phase <;> cases r <;> simp_all [post, nextPhase, State.isPending]

/-! ## 7. Examples -/

private def ctxA : WriteCtx := ⟨1, 2, 0x1000, 1200, 5⟩

-- The loop h:5324 describes: keep calling until a packet is complete.
example : Conforms [(.writevStream ctxA, .pending), (.writevStream ctxA, .pending),
    (.writevStream ctxA, .done), (.readPkt false 6, .done), (.handleExpiry 7, .done)] := by decide

-- A timer firing in the middle of it.
example : run {} [(.writevStream ctxA, .pending), (.handleExpiry 5, .done)] =
    [(1, .noCallWhilePending)] := by decide

-- Resuming in a different buffer.
example : run {} [(.writevStream ctxA, .pending),
    (.writevStream { ctxA with dest := 0x2000 }, .done)] = [(1, .pendingSameArgs)] := by decide

-- A soft error leaves the packet pending (c:12177–12186 return before the packet
-- is touched), so the next `read_pkt` is still a violation.
example : run {} [(.writevStream ctxA, .pending), (.writevStream ctxA, .unchanged),
    (.readPkt false 5, .done)] = [(2, .noCallWhilePending)] := by decide

-- After an idle close nothing more may be called.
example : run {} [(.handleExpiry 9, .terminal), (.writevStream { ctxA with ts := 9 }, .done)] =
    [(1, .notAfterTerminal)] := by decide

end Quic.Api
