# Plan: formalizing the rest of QUIC transport in Lean

Source text: `spec/draft-ietf-quic-transport-34.txt` (line numbers below refer to it).
Done already: wire format (§12.4, §16, §17, §19), stub packet protection, frame
encoder and round-trip proof. Out of scope throughout: TLS internals (RFC 9001),
loss recovery and congestion control (RFC 9002), §21 security considerations,
§22 IANA, the PMTUD search algorithm (only its constraints).

## 1. The shape every component takes

Defined in `QuicModel/Spec/Core.lean` as the structure `Component`; a complete
worked example is `QuicModel/Spec/Template.lean`. Every work package produces
one `Component` value (or several) and must follow the template's file order.

```lean
structure Component where
  State Event Effect : Type                    -- plain data, DecidableEq
  Step     : State → Event → Outcome State Effect → Prop   -- THE SPEC
  outcomes : State → Event → List (Outcome State Effect)   -- executable: all permitted outcomes
  outcomes_iff : o ∈ outcomes s e ↔ Step s e o
  outcomes_ne  : outcomes s e ≠ []             -- the spec always permits something
  Inv      : State → Prop
  step_inv : Inv s → Step s e (.ok s' fx) → Inv s'
  MaySend  : State → Frame → Prop              -- send side; True for frames not governed
  maySend  : State → Frame → Bool
  maySend_iff : maySend s f = true ↔ MaySend s f
  -- optional, default "anything": rules about whole packets / datagrams
  MaySendPacket   : State → OutPacket → Prop     (+ maySendPacket, _iff)
  MaySendDatagram : State → OutDatagram → Prop   (+ maySendDatagram, _iff)

inductive Outcome σ ε | ok (s : σ) (effects : List ε) | error (code : TransportError) | drop
```

`Core` derives from this, once and for all components:

- `C.step` — the reference implementation: the first (preferred) permitted outcome;
  `step_sound : C.Step s e (C.step s e)`.
- `C.accepts s e o : Bool` with `accepts_iff` — is an outcome permitted?
- `C.track s e obs : Option State` — follow an implementation whose state is not
  visible, from what it observably did (`Obs` = effects, error code, or drop);
  `track_sound`, `track_complete`. This is what the ngtcp2 harness calls.
- `C.trackAll` / `C.trackSet s-list e pattern` — the same when observations do
  not determine the state (ngtcp2 cannot tell `ok []` from `drop`): follow the
  set of candidate states; a violation is the set becoming empty.
  `mem_trackSet` states soundness and completeness.
- `C.Reachable`, `reachable_induction`, `inv_of_reachable`.

Why a list of outcomes: receive-side looseness in QUIC is always a finite choice
(one of two error codes; ignore or reject), so enumerating it gives the
reference function, the checker and the tracker from one definition and one
proof (`outcomes_iff`).

Rules that go with it:

- **Normative keywords.** `Step` encodes MUST / MUST NOT. SHOULD and MAY that
  *permit* behaviour add constructors to `Step` (and entries to `outcomes`).
  SHOULD that *recommends* goes in a separate `Recommended` predicate so that a
  conforming implementation is never rejected for ignoring advice.
- **Traceability.** Every `Step` constructor carries a doc comment
  `§x.y, line N: "quoted sentence"`. Each file ends with a coverage table: every
  MUST/MUST NOT in the assigned line range → constructor or theorem name, or
  `out of scope: reason`, plus NOTES on every ambiguity and the reading chosen.
- **Proof-friendliness.** Total functions only: no `partial`, `while`, `get!`,
  `Id.run` loops. Keep `outcomes` a flat `match`/`if` so `outcomes_iff` is a case
  split plus `simp`. Finite maps are `Spec.Map` (association lists). Numbers are
  `Nat` with explicit bounds. Time is `Spec.Time` (µs) carried on events, never
  read. Stream IDs are `Spec.StreamId`.
- **Observability.** If two permitted outcomes have the same `Obs` but different
  next states, `track` cannot follow; add an effect that distinguishes them, or
  show the states coincide.
- **Retransmission.** Frames are idempotent (§12.4) and are re-sent after loss
  (§13.3). `MaySend` must accept an exact repeat of a frame it accepted before,
  even though the state has since moved on.
- **`MaySend` is never stricter than the text.** "Has no effect" or "is ignored
  by the receiver" does not mean "must not be sent".
- **Nothing abstract leaks.** TLS, tokens, stateless-reset token derivation and
  the Retry integrity tag are opaque parameters or events (like `Protection`).
- **Builds.** Always run Lean under a timeout (`timeout 300 lake build …`); a
  check that takes more than a minute means a tactic is searching — replace
  `simp_all`/`decide` on big terms with explicit steps.

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
| 0 Core (done) | `TransportError` (§20.1), `Role`, `StreamId` (§2.1), `PnSpace`, `PacketType`, `Time`, `Map`, `Outcome`/`Obs`, the `Component` structure with derived `step`/`accepts`/`track`, and a worked template | 677–732, 4634–4726, 8249–8372 | `Spec/Core.lean`, `Spec/Template.lean` |

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

### Wave 2b (added after the transport audit)

| WP | Content | Text (lines) |
|---|---|---|
| 14 Reliability | §13.3 retransmission of information: per frame type, what is re-sent and when it MUST NOT be (e.g. no STREAM data after RESET_STREAM, blocked frames carry the current limit, PATH_RESPONSE not retransmitted, CONNECTION_CLOSE handling) as `MaySend`/`Recommended` over an abstract "declared lost" event; §13.4 ECN: the transport-level MUSTs of ECN counting and validation (counts non-decreasing, validation failure disables ECN), with RFC 9002 state abstract | 5325–5639 |

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
3. A `Component` value is defined (so `outcomes_iff`, `outcomes_ne`, `step_inv`,
   `maySend_iff` are proved) and the package's named theorems are proved.
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
- Order: WP0 → Wave 1 (8 parallel) → review 1 → Wave 2 (3) + Wave 2b (1) →
  review 2 → Wave 3 (2) → review 3.

## 4a. What Wave 1 taught us (inputs to Wave 3)

From the ngtcp2 trace harness (`harness/conn_trace.c`, WP8):

- **`drop` and `ok []` look the same from outside.** `ngtcp2_conn_read_pkt`
  returns 0 for both. The harness-side comparison must treat them as one
  observation, so `track` must follow a *set* of candidate states rather than
  one (`Core` gets `trackAll`; the harness keeps the set and reports a mismatch
  only when it becomes empty).
- **Effects can precede an error.** ngtcp2 fires `stream_open` and then fails
  the same STREAM frame with FLOW_CONTROL_ERROR. The spec says nothing about
  application callbacks, so when the observation is an error only the error
  code is compared.
- **Only the error code is visible, never the rule**: `frame_type` is always 0
  and many rules share PROTOCOL_VIOLATION.
- **Send side is one-directional**: every frame ngtcp2 emits must satisfy
  `maySend`; the absence of a frame proves nothing (pacing, congestion window).
- **Not reachable through this harness**: the handshake and transport parameter
  validation (WP1, WP11 are theorem-only), second paths and migration,
  stateless reset, receive-side coalescing, the closing/draining periods after
  the first fatal error (cheap to add), application close.

From the spec packages:

- `Component.MaySend` is frame-level only; WP3, WP5, WP6 and WP7 each needed
  packet-type-, packet- or datagram-level send rules and exported them as free
  functions. Before Wave 3, `Core` gains optional packet- and datagram-level
  send predicates (default `True`) and the free functions are folded in.
- A server's general right to refuse a connection (CONNECTION_REFUSED, §5.2.2)
  belongs to connection acceptance in WP12, not to address validation.

## 4b. Disposition of TRANSPORT_AUDIT.md

The audit was written against the tree before WP2 merged; status as of the
commit that adds this section:

| Audit item | Status |
|---|---|
| ACK deadline can move later (§13.2.1) | confirmed; fix in progress on `wp3-ack-fix` (obligations tracked per ack-eliciting packet, separate from the ACK Delay timestamp) |
| Partial ACK clears all obligations | confirmed; same branch (`sentAck` carries its ranges; only covered packets are discharged); plus an exported `AckOverdue` predicate so the composed endpoint can require ACKs to be *sent*, not only be timely when sent |
| Packet-number exhaustion off by one (§12.3) | confirmed; bound fixed on `wp3-ack-fix`, the silent close added to Termination on `wp6-pn-exhaustion` (neither side owned it before) |
| Streams missing | stale: WP2 merged (send/receive machines, final size, stream credit); stream table and connection flow control are WP9, running |
| Handshake, migration missing | WP11 and WP10, running |
| Endpoint integration, behavioural differential | WP12, WP13, as planned; `Core` now has packet- and datagram-level send fields and set-based tracking for them to use |
| §13.3 / §13.4 unowned | correct: every package declared them out of scope and no package owned them. Added as WP14 |
| `step_sound` does not validate `Step` against the prose | agreed and by design (PLAN §1, "What validates `Step` itself"); this audit and the two Wave 1 review agents are that validation, and all three ACK defects passed every proof |
| Trace-level obligations | agreed: a per-step predicate cannot force something to happen. WP12 must state liveness-style MUSTs (ACK within max_ack_delay, RESET_STREAM owed after STOP_SENDING, second path validation) as requirements on timed traces, fed by exported predicates such as `AckOverdue` |
| Draft-34 vs RFC 9000, extension profile | open. The model follows draft-34 plus RFC 9221 (DATAGRAM), RFC 9287 (grease bit) and RFC 9369 (v2 type codes) at the wire layer only. Needs a text diff against RFC 9000 and an explicit profile before any conformance claim |

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
