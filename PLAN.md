# Plan: formalizing the rest of QUIC transport in Lean

Source text: `spec/draft-ietf-quic-transport-34.txt` (line numbers below refer to it).
Done already: wire format (§12.4, §16, §17, §19), stub packet protection, frame
encoder and round-trip proof. Out of scope throughout: TLS internals (RFC 9001),
loss recovery and congestion control (RFC 9002), §21 security considerations,
§22 IANA, the PMTUD search algorithm (only its constraints).

## 1. The shape every component takes

Each component `X` lives in `QuicModel/Spec/X.lean` (or a directory) and exports
the same six things. Agents must not deviate from this; the composition layer
and the harness rely on it.

```lean
structure X.State                      -- plain data, DecidableEq
inductive X.Event                      -- inputs: frame received, app call, TLS event, timer
inductive X.Effect                     -- outputs: app event, frame to queue, timer to arm

/-- One outcome of handling an event. -/
inductive Outcome (σ ε : Type)
  | ok (s : σ) (effects : List ε)
  | error (code : TransportError) (reason : String)   -- connection error, §11
  | drop                                              -- "MUST discard / ignore"

/-- THE SPEC.  Every outcome the text permits.  Loose where the text is loose:
    one constructor per alternative ("STREAM_LIMIT_ERROR or FRAME_ENCODING_ERROR",
    "MAY ignore", "MAY treat as PROTOCOL_VIOLATION"). -/
inductive X.Step : X.State → X.Event → Outcome X.State X.Effect → Prop

/-- THE REFERENCE IMPLEMENTATION.  Total, structural, no partial/while/get!.
    Picks one permitted outcome. -/
def X.step : X.State → X.Event → Outcome X.State X.Effect

/-- THE CHECKER.  Decides whether an outcome observed elsewhere (ngtcp2) is
    permitted.  This is what the differential harness calls. -/
def X.accepts : X.State → X.Event → Outcome X.State X.Effect → Bool

theorem X.step_sound   : X.Step s e (X.step s e)
theorem X.accepts_iff  : X.accepts s e o = true ↔ X.Step s e o

/-- What the endpoint is permitted to send in state `s` (send side is a
    predicate only: the spec never says what to send next). -/
def X.MaySend  : X.State → Frame → Prop
def X.maySend  : X.State → Frame → Bool          -- with maySend_iff

/-- State invariant and its preservation; plus the component's named
    safety theorems (listed per work package below). -/
def X.Inv : X.State → Prop
theorem X.step_inv : X.Inv s → X.Step s e (.ok s' fx) → X.Inv s'
```

Rules that go with it:

- **Normative keywords.** `Step` encodes MUST / MUST NOT. SHOULD and MAY that
  *permit* behaviour add constructors to `Step`. SHOULD that *recommend*
  behaviour goes in a separate `X.Recommended` predicate so that a conforming
  implementation is never rejected for ignoring advice.
- **Traceability.** Every `Step` constructor and every error site carries a doc
  comment `§x.y, line N: "quoted sentence"`. Each file ends with a coverage
  table: every MUST/MUST NOT in the assigned line range → constructor or theorem
  name, or `out of scope: reason`.
- **Proof-friendliness.** State is finite maps as association lists or
  `Std.HashMap`-free sorted lists (pick one in WP0 and keep it); numbers are
  `Nat` with explicit `≤ maxVarint` side conditions; time is `Nat` microseconds
  passed in on events, never read.
- **Determinism is not required of `Step`, totality is required of `step`.**
- **Nothing abstract leaks.** TLS, tokens, stateless-reset token derivation and
  the Retry integrity tag are opaque parameters/events (like `Protection`).

What validates `Step` itself, since `step_sound` only shows `step ⊆ Step`:
(1) the coverage table, reviewed against the text by a second agent that did
not write it; (2) the safety theorems, which fail if `Step` is too permissive;
(3) the differential run against ngtcp2, which fails if `Step` is too strict.

## 2. Work packages

Wave 0 is sequential and small. Packages inside a wave are independent and own
disjoint files. Each later wave starts when the ones it lists under "needs" have
merged.

### Wave 0

| WP | Content | Text | Output |
|---|---|---|---|
| 0 Core | `TransportError` (§20.1), `Role`, `StreamId` with initiator/direction (§2.1), `PnSpace`, `PacketType`, `Outcome`, map type, the `Spec` typeclass bundling the six exports, one worked toy component as the template | 677–732, 4634–4726, 8249–8372 | `Spec/Core.lean`, `Spec/Template.lean` |

### Wave 1 (eight agents in parallel; need WP0)

| WP | Content | Text (lines) | Named theorems beyond the standard ones |
|---|---|---|---|
| 1 TransportParams | decode/encode/round trip; validity relation: which role may send which parameter, value limits, duplicates, 0-RTT remembered limits | 2506–2695, 6875–7154 | round trip; `decode` output always satisfies validity or is an error |
| 2 Stream | per-stream send and receive state machines; stream-level flow control; final size; which frames are legal in which state | 641–1292, 1461–1526 | final size immutable once known; bytes delivered ≤ advertised stream credit; terminal states absorb |
| 3 FrameRules | Table 3: frame × packet type legality, ack-eliciting, probing, flow-controlled; packet number spaces; duplicate suppression; ACK generation constraints as `MaySend`/`Recommended` | 4727–4988, 5018–5324 | legality table is total and matches §12.5 prose; ACK never acknowledges an unreceived pn |
| 4 ConnIds | issuing, sequence numbers, `retire_prior_to`, `active_connection_id_limit`, RETIRE_CONNECTION_ID rules, zero-length CID restrictions | 1608–1834, 7923–8058 | active CIDs ≤ limit; sequence numbers unique; retired never reused |
| 5 AddressValidation | anti-amplification budget, token handling (opaque), Retry processing, PATH_CHALLENGE/RESPONSE path validation | 2724–3271, 6557–6697 | bytes sent to an unvalidated address ≤ 3 × bytes received |
| 6 Termination | idle timeout, closing and draining states, immediate close, stateless reset detection, error → CONNECTION_CLOSE mapping | 3813–4515 | draining sends nothing; closing sends only CONNECTION_CLOSE; both reach closed |
| 7 VersionAndSize | version negotiation both roles, reserved versions, Initial datagram ≥ 1200, PMTU constraints | 2044–2156, 5640–5919 | client never reacts to a VN listing its own version |
| 8 CHarness | C only, no Lean: drive `ngtcp2_conn_read_pkt` with the stub crypto from `pkt_diff.c`, record per input packet the app callbacks fired, the close error code, and every packet written, as a text trace | `harness/`, `../fuzz/read_write_pkt.cc` | — |

### Wave 2 (three agents; need the listed packages)

| WP | Content | Text | Needs |
|---|---|---|---|
| 9 StreamTable | stream creation incl. implicit opening of lower-numbered streams, stream-count limits, connection-level flow control, composition of WP2 instances | 1293–1460, 1527–1576 | 2 |
| 10 Migration | probing, initiating and responding to migration, preferred address, CID use on new paths | 3272–3812 | 4, 5 |
| 11 Handshake | TLS as an event source (`keysAvailable`, `handshakeBytes`, `complete`, `confirmed`); CRYPTO stream per space; CID authentication via transport parameters; key discard; 0-RTT accept/reject | 2157–2505, 2696–2723 | 1, 3, 4 |

### Wave 3 (two agents; need everything)

| WP | Content |
|---|---|
| 12 Endpoint | `Endpoint.State` as the product of component states; `recv`: datagram → `decodePacket` → frame legality → dispatch to components → merge outcomes; `MaySend` for a whole packet as the conjunction of component predicates; top-level theorems lifted from components |
| 13 DiffHarness | export `Endpoint.accepts` / `maySend`; join with WP8's trace: every ngtcp2 outcome must be accepted, every ngtcp2 packet must satisfy `maySend`; seed corpus; triage doc for mismatches |

### Review agents

One per wave, started when the wave's packages report done, with no access to
the authors' reasoning: read the assigned text range and the `Step` relation
cold, list every normative sentence that is missing, misquoted, or encoded more
strictly or loosely than written. Findings go back to the owning agent.

## 3. Definition of done for a package

1. `lake build` clean: no `sorry`, no warnings, no `partial`, no `native_decide`
   outside `Tests`.
2. `#print axioms` on each headline theorem shows only `propext`,
   `Classical.choice`, `Quot.sound`.
3. `step_sound`, `accepts_iff`, `maySend_iff`, `step_inv` and the named theorems
   are proved.
4. Coverage table complete for the assigned line range.
5. At least five `example`s replaying scenarios the text itself describes
   (e.g. the stream state diagrams, the handshake flows of §7.1).
6. A short `NOTES` section: every place the text was ambiguous and which
   reading was encoded.

If a named theorem turns out false, that is a result, not a failure: report the
counterexample state and stop; do not weaken `Step` to make it provable.

## 4. Mechanics

- Agents: `Agent` tool, `model: opus`, one per package, brief = this file's §1
  and §3, the package row, the line range, and pointers to `Basic.lean`,
  `Frame.lean`, `RoundTrip.lean` as style references.
- Isolation: this is its own git repository, so each agent runs with
  `isolation: worktree`, gets its own `.lake`, and merges are trivial because
  packages own disjoint files. Only WP0 and WP12 touch `QuicModel.lean`.
- Order: WP0 → Wave 1 (8 parallel) → review 1 → Wave 2 (3) → review 2 →
  Wave 3 (2) → review 3. Seventeen agent runs in total.

## 5. Risks

- **`accepts_iff` for relations with existentials** (e.g. "some token the server
  issued") is where decidability gets hard. Rule: make the witness part of the
  event or the state so the checker never searches.
- **Composition (WP12)** is where independently designed states collide. WP0's
  template and the fixed six-export shape are the mitigation; WP12 should be
  given to the strongest run and reviewed twice.
- **Observability gap.** ngtcp2 exposes callbacks and a close code, not its
  state. `accepts` will be judged on traces, so WP8 decides how much of the
  spec is differentially testable; the rest is covered by theorems only.
- **The draft is -34, ngtcp2 implements RFC 9000 plus later RFCs** (9287 grease
  bit, 9221 datagram, 9369 v2). Expected mismatches from that gap should be
  listed in WP13's triage doc, not patched into `Step`.
