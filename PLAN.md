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
| 9 StreamTable (merged) | stream creation incl. implicit opening of lower-numbered streams, stream-count limits, connection-level flow control, composition of WP2 instances | 1293–1460, 1527–1576 | 2 |
| 10 Migration (merged) | probing, initiating and responding to migration, preferred address, CID use on new paths | 3272–3812 | 4, 5 |
| 11 Handshake (merged) | TLS as an event source (`keysAvailable`, `handshakeBytes`, `complete`, `confirmed`); CRYPTO stream per space; CID authentication via transport parameters; key discard; 0-RTT accept/reject | 2157–2505, 2696–2723 | 1, 3, 4 |

### Wave 3 (two agents; need everything)

| WP | Content |
|---|---|
| 12 Endpoint (merged: layers 0–5 c785e51, examples + report 63a2d2d) | `Endpoint.State` as the product of component states; `recv`: datagram → `decodePacket` → frame legality → dispatch to components → merge outcomes; `MaySend` for a whole packet as the conjunction of component predicates; top-level theorems lifted from components |
| 13 DiffHarness (merged 1211000; results in TRIAGE.md) | export `Endpoint.accepts` / `maySend`; join with WP8's trace: every ngtcp2 outcome must be accepted, every ngtcp2 packet must satisfy `maySend`; seed corpus; triage doc for mismatches |

### Wave 2b (added after the transport audit)

| WP | Content | Text (lines) |
|---|---|---|
| 14 Reliability (merged) | §13.3 retransmission of information: per frame type, what is re-sent and when it MUST NOT be (e.g. no STREAM data after RESET_STREAM, blocked frames carry the current limit, PATH_RESPONSE not retransmitted, CONNECTION_CLOSE handling) as `MaySend`/`Recommended` over an abstract "declared lost" event; §13.4 ECN: the transport-level MUSTs of ECN counting and validation (counts non-decreasing, validation failure disables ECN), with RFC 9002 state abstract | 5325–5639 |

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

## 4c. Review of Wave 1, batch B (`reviews/wave1-b.md`): disposition

HIGH and MEDIUM findings, all accepted unless noted:

| Finding | Owner | Status |
|---|---|---|
| AV-1 anti-amplification binds a client's first packet | WP5 fix run | merged |
| PV-1 duplicate/late PATH_RESPONSE accepted as PROTOCOL_VIOLATION | WP5 fix run | merged |
| AV-2, AV-3 missing MAY-discard / SHOULD-proceed alternatives | WP5 fix run | merged |
| AV-5 server-side Retry send rules (§17.2.5.1) unmodelled | WP5 fix run | merged |
| T-1 stateless reset size rule drops the "unless" exemption | WP6 fix run | merged (7d0779c) |
| T-2 idle close mandatory at the exact deadline instant | WP6 fix run | merged (7d0779c) |
| T-5 `MaySend` in closing stricter than the text (lead's earlier instruction was wrong too) | WP6 fix run | merged (7d0779c) |
| T-6 `Recommended` drops a qualifier; T-7 `confirmed` lost on closing; wrong line numbers in §10.2 | WP6 fix run | merged (7d0779c) |
| DS-1 no `.drop` alternative for received datagrams | WP7 fix run | merged (5408e38) |
| DS-2 NO_VIABLE_PATH offered unconditionally; DS-3 local `OutDatagram` | WP7 fix run | merged (5408e38) |
| VN-1 CID check applied to the §6.2 abandon path | WP7 fix run | merged (5408e38) |
| T-4 §11 generic error codes | `Core`: `Obs.matchesSpec` | done |
| `Spec.OutDatagram` lacked destination and probe flag | `Core` | done |
| (resolved: `OutDatagram` now has `src`, `dcid`, `scid`, `isEcnMarked`) `Spec.OutDatagram` had no *local* address, so §8.2.2 line 3183 (PATH_RESPONSE on the path the challenge arrived on) cannot be a field rule; PathValidation and Migration each export a two-state `av → OutDatagram → Prop` rule needing AddressValidation's state | WP12 (decide: add a local address to `OutDatagram`, or conjoin by hand) | recorded |
| AV-4 CONNECTION_REFUSED (§5.2.2); T-4 second half, §11.1 "MAY discard an invalid Initial even where an error is mandated"; VN-2 "MUST drop under all other circumstances"; T-3 closing-state amplification rules (§10.2.1 lines 3993, 4008); conflicting `.drop` readings between PathValidation and Termination | WP12 | recorded: composition must take the *union* for connection-level refusals and let Termination's phase gate every other component |

## 4d. Review of Wave 1, batch A (`reviews/wave1-a.md`): disposition

All four HIGH findings are the model being stricter than the text; none admits
forbidden behaviour. All accepted.

| Finding | Owner | Status |
|---|---|---|
| W4-1 `peerActiveAfter` ignores Retire Prior To already sent; W4-2, W4-3 missing MAYs; W4-4 coverage rows | lead (done by hand, be159ea) | done |
| W2-1 RESET_STREAM: FINAL_SIZE_ERROR must also be permitted when both rules fire (ngtcp2 checks final size first); W2-2 MAX_STREAM_DATA after FIN is a SHOULD; W2-3 STREAM_DATA_BLOCKED has no bounds or errors; W2-4 "can safely ignore" made mandatory; W2-5..8 | WP2 fix run | merged; two ngtcp2 behaviours on STREAM_DATA_BLOCKED deliberately not encoded (Recv NOTES) → WP13 triage |
| W2-6 §13.3 "content of a RESET_STREAM MUST NOT change when sent again" | WP2 fix run (merged); WP14 coverage | WP14 running |
| W3-1 minimum-packet-number drop (§12.3) not permitted; W3-4 `MaySendPacket` for empty packets and frame/packet-type legality; W3-5/6 coverage | WP3 fix run | merged (4c98db1) |
| W1-1 duplicate parameters: first-copy-wins also conforms; W1-2 dropped SHOULDs; citation drift | WP1 fix run | merged; W1-3 ruling kept (§18.2 line 7125 is unconditional) |
| Ruling on `Recommended` vs "advice only" | BRIEF.md | done |
| Composition notes: `assembling` duplicated in FrameRules and Ack (both needed); `Send.written` means the harness must synthesise `appWrite`; grow-only state vs pruning implementations | WP12 / WP13 | recorded |

## 4e. Review of Wave 2 (`reviews/wave2.md`): disposition

| Finding | Owner | Status |
|---|---|---|
| S-1 HIGH connection credit charged from the frame's end offset, deleting the §4.5 "ignore" outcome and mis-accounting §4.5 line 1495 | WP9 fix run | merged |
| S-2 STREAM_STATE_ERROR mandated for all five frames on an uncreated local *bidirectional* stream; S-3, S-4 coverage; S-5 `MaySend` false on non-existent streams (WP13 must synthesise `appOpenStream`); S-6 ~20 wrong citations incl. four error-code rules | WP9 fix run | merged |
| M-1 HIGH a retired connection ID may be reused from a second local address (`dcidOn` overwritten; §9.5 line 3603) | WP10 fix run | merged (5c3d76e) |
| M-2 send rules read the state's send context instead of `OutDatagram.src/dest/dcid/scid`; M-3 `recvCase` narrows §9.3 line 3379; M-4 citations; witness for the theorem-(c) counterexample should be the reachable route | WP10 fix run | merged; M-4 finished by the lead (e5008f1, 23 corrections, 0 mismatches); the theorem-(c) witness is now a proved reachable route (`cliTwoPeers_reachable`) |
| K-1 fold Handshake's `SendHeader` into `MaySendDatagram` (now expressible); K-3, K-4, K-5 | WP11 fix run | merged; `Endpoint.MaySendDatagram` gained the `HandshakeHeaderOk` conjunct (peer-issued CIDs from ConnIds.Remote, all entries) |
| K-2 `recvHeader` only after successful unprotection is a hard requirement | WP12 | documented and exampled in Handshake NOTE 10; the pipeline's callers must honour it (to verify in WP12's examples/report) |
| Three copies of "handshake confirmed"; `.drop` precedence for Migration's MUST-discards; events WP13 must synthesise | WP12 / WP13 | recorded |

Ruling on citations: the line where the sentence's first word appears, even when it dangles at the end of a line (BRIEF). `Spec/Stream*` (WP2) used "the line with the operative words" in a few places; to be normalised in a later sweep (LOW).

Both WP10 theorems reported false as written were confirmed against the text
by the reviewer (reachable, conformant counterexamples).

## 4f. WP12 outcome

- Composition layer merged and documented (`QuicModel/Spec/Endpoint.lean` module
  doc is the report: merge rule, `.drop`/`ok []` conflict table, 30-row table of
  MUSTs other packages deferred to WP12, the 13 event families the harness must
  synthesise, the effect→callback table).
- All eight `harness/scripts` scenarios and §7.1 Figure 5 replay through
  `Endpoint.step`/`accepts` and agree with the recorded ngtcp2 traces.
- Defect found and fixed in the composition (TRIAGE WP13-5): `recvPackets`
  stopped at the first undecryptable coalesced packet, citing a sentence that is
  not in the draft; §12.2 line 4619 requires attempting the remaining packets.
  ngtcp2 also stops → triage entry.
- Known gap: §5.2.2 line 1936's CONNECTION_REFUSED is not modelled — refusal is
  a connection-*acceptance* decision and `Endpoint` models an established
  connection; needs an `Event.accept` above `Endpoint` (open decision).
- Wire-layer assertions in `Examples.lean` use `#guard` (build-time evaluation,
  no axiom) because `decodeFrames`/`Array.all` are well-founded and `decide`
  gets stuck; a structurally recursive `ByteArray.all` in `Basic.lean` would
  unlock `decide` there (open, low priority).
- `TRIAGE.md` started (WP13-1..5).

## 4g. WP13 outcome and the state of the differential comparison

- `harness/endpoint_diff` drives ngtcp2 and the Lean endpoint side by side with
  set tracking (`harness/endpoint_diff.md`). All eight scripted scenarios run
  with zero mismatches. First 10-minute fuzz (before the fixes below): 16 675
  inputs, 110 628 steps compared, 97.6 % exact matches, 75 distinct mismatch
  signatures, no crash or ASan report.
- Findings where the **model** must change (open): WP13-9 (§7.5's
  CRYPTO_BUFFER_EXCEEDED / discard alternatives missing in Handshake — the model
  is too *narrow*), WP13-10 (DATA_BLOCKED / STREAMS_BLOCKED past the advertised
  limit encoded inconsistently across Stream and StreamTable), WP13-7
  (`StreamTable.openedEffects` unevaluable for a huge stream index), WP13-6
  (received ACKs are not routed to StreamTable, so "all data acked" is
  unreachable), WP13-4 (§19.16 self-retirement unchecked on the send side),
  WP13-3 (blanket MAY-discard of any datagram, safe but masks defects).
- Resolved by the lead: WP13-13 (harness mapping error masked by WP13-3;
  `cidRetiredByPeer` no longer compared), WP13-17 (per-conjunct diagnostic
  export, proved to agree with `maySendDatagram`).
- ngtcp2 / text: WP13-5 (ngtcp2 stops at an undecryptable coalesced packet;
  §12.2 says attempt the rest), WP13-11 (FINAL_SIZE_ERROR for
  STREAM_DATA_BLOCKED), WP13-12 (idle-timeout comparison undecidable with the
  forced post-handshake state), WP13-8 (implicitly opened streams not
  announced; API, not normative).
- Harness bugs fixed by WP13: µs/ns, DRAINING/CLOSING mapped to
  PROTOCOL_VIOLATION, WP8's hard-coded 8-byte DCID in OUT records (WP13-15).
- Open change requests for the endpoint: WP13-16 (no event to declare a peer
  address validated), WP13-18 (observation pattern cannot express "ignore this
  callback" / subsequence). Design decision to revisit: the harness's level-3
  "subsequence" matching is a real weakening (30 residual signatures).

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
