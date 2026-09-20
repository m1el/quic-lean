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

## 4h. Disposition of TRANSPORT_AUDIT_2026-09-18.md

Four receive-path findings against `a6b74c2`, all in `Endpoint/Pipeline.lean`,
all reproduced and all fixed; `Examples.lean` §12b holds the audit's
counterexamples with the guards turned round to the required behaviour.

| Audit item | Status |
|---|---|
| D34-1 discarded packets restart the idle timer (§10.1) | fixed: `Effect.packetProcessed` marks a packet no component discarded; `idleGate` restarts the timer only for an outcome that carries it |
| D34-2 Retry integrity assumed to succeed (§17.2.5.2) | fixed: `Protection.retryTagOk` (abstract; the stub validates 16 × 0xA5) feeds `AddressValidation`'s `integrityOk` instead of a literal `true` |
| D34-3 undersized Initial accepted behind another packet (§14.1) | fixed: `.recvInitial buf.size` is asked per Initial packet in `recvOne`, before unprotection; the discard skips that packet only. `carriesInitial` is gone |
| D34-4 short header-protection sample stops coalesced processing (§12.2) | fixed: `.tooShortForSample` continues at `packetEndOf` like `.decryptFailed`; terminal only when the extent is unknown |
| Assurance limits (definitional `Step`, abstracted STREAM bytes, scheduling, extension profile) | unchanged and still open; see §4b's last rows |

Not done here: a fresh fuzzing campaign.  The eight scripts and the existing
`corpus/conn_trace` were replayed through `endpoint_diff` before and after.
`.fixedBitClear` on a long header has a known extent too and still ends the
datagram; the audit did not raise it and it is left for triage.

## 4i. Disposition of TRANSPORT_AUDIT_2026-09-18_3.md

Three send-side findings against the working tree after §4h, all in the
composition (`Endpoint/Send.lean`), all reproduced and all fixed.
`reviews/Audit3.lean` has its four defect guards turned round; `Examples.lean`
sections D34-5 to D34-7 are the regression guards.

| Audit item | Status |
|---|---|
| D34-5 frames each spend the same connection credit (§4.1) | fixed: `StreamTable.MaySendAll` (per stream, highest offset reached minus `sentHighest`, so retransmissions and overlaps count once) is a conjunct of `MaySendPacket` over `p.frames` and of `MaySendDatagram` over all coalesced packets. Proved: `sendCredit_of_maySendAll` (subsumes the per-frame rule), `maySendAll_singleton` |
| D34-6 retired DCID still sendable (§5.1.2) | fixed: `Send.DcidOk` resolves `OutDatagram.dcid` to a sequence number through `ConnIds.Remote` (`dcidSeq?`; the handshake's own DCID is sequence 0) and refuses a retired one. `HandshakeHeaderOk` is unchanged, so its allowances cannot bypass it |
| D34-7 §9.5 history bypassed by the empty `peerCids` (§9.5) | fixed in the same predicate: `DcidOk` applies `Migration.MaySendCidOn` with that sequence number. `Migration.State.peerCids` / `learnPeerCid` are left as they were and are unused by the endpoint |

Behaviour change to know about: a *nonempty DCID the peer never issued* is now
refused (previously any bytes passed for a 1-RTT packet).  `dcid := none` still
means "not looked at".

Differential check after the fix: eight scripts, 0 mismatches.  Five-minute
fuzz (`out/fuzz/refuzz300_audit3.log`, same command as `refuzz300`): 8 662
runs, 55 075 steps compared, 24 249 send checks, 44 signatures (36 outcome,
7 maysend, 1 obligation; was 36/5/1).  The two new maysend signatures
(`b3c10263…`, `f6e91f92…`, one input) are refused by `ackPacketOk` only — the
existing ACK class under a new frame combination.  Replaying all 43 saved
inputs (`out/fuzz/audit3-inputs/`) with `DIFF_SHOW=1`: no send is refused by
`dcidOk` or `StreamTable.maySendAll`.  As the audit says, this cannot show the
new rules are tight, only that ngtcp2 does not trip them; migration and
second paths remain outside the campaign.

§19.16 line 8050's send side (`WP13-4`: do not retire the DCID of the carrying
packet) was done next, on the same lookup: `Send.RetireNotSelf`, with
`retire_ne_dcid_of_maySendDatagram`; guards in `Examples.lean` section WP13-4.

## 4j. quiche as a second implementation (started 2026-09-19)

`out/quiche_diff` is `harness/endpoint_diff.c` built with `-DDRIVER_QUICHE`:
the model side is shared, `harness/quiche_driver.h` replaces conn_driver.h's
ngtcp2 engine (`./build_quiche_harness.sh`).  Same script grammar, same binary
fuzz format, same corpus.  Needs `../quiche` on branch `fuzz-mock-clock`
(`clock::CLOCK`, an `AtomicU64` every time read goes through under the
`fuzzing` feature; `quiche_fuzz_set_clock` in the FFI).  Not upstreamed, not
committed there.

What differs from the ngtcp2 harness, and why (details in quiche_driver.h):
real in-memory TLS handshake, then the peer is forged; quiche's crypto stub
(zero HP mask, no tag) converted to the model's at the boundary, so the model
sees the bytes it would see from ngtcp2; 1-RTT packet numbers relative to what
the handshake used, with the handshake's 1-RTT packets replayed into the model;
no callbacks, so only `recv_stream_data` / `stream_reset` are observable and the
exclusion-aware comparison is the first pass; `TlsEvent.tlsSend` read back off
the wire (`Harness.cryptoEnd`) because a real handshake sends a session ticket.
quiche pads Initial datagrams with raw zeros *after* the last packet, which the
`fuzzing` stub "decrypts"; the driver trims them (`q_trim`).

State: eight scripts, 0 mismatches on both engines, and quiche closes with the
same transport error as ngtcp2 in all five error scripts.  Corpus replay
(`-runs=0 corpus/conn_trace`, 2 458 inputs): ngtcp2 44 signatures (unchanged by
the refactor), quiche 26 (21 maysend, 4 outcome, 1 obligation), untriaged.

`DIFF_DIGEST=<file>` writes one line per compared step;
`harness/scripts/digest_diff.py A B` joins two engines' files over the same
inputs and classifies the first difference per input (latitude / A-only /
B-only / both / model-only).  First join: 2 306 common inputs, 1 857 identical,
276 "latitude" — **not yet cleaned of harness artefacts** (e.g. 47 are the
idle-timer difference of WP13-12, where quiche sides with the model).

Open, in order: (1) triage the 26 quiche signatures; the first looked at is a
candidate quiche finding — PATH_RESPONSE on a validated path leaves in a 63–78
byte datagram, §8.2.2 "MUST expand … to at least … 1200 bytes"; quiche pads
only `if has_initial || !path.validated()` (quiche/src/lib.rs:5389); ngtcp2
pads.  (2) `892de5bd…` (ACK refused by `ackPacketOk`) appears under both
engines: the model is the suspect.  (3) ACK frames in scripts name absolute
packet numbers, which mean different packets to the two engines.  (4) quiche's
randomness is not reproducible: BoringSSL's `RAND_reset_for_fuzzing` is not in
the vendored build.  (5) No fuzzing campaign with quiche_diff yet.

## 4k. Disposition of TRANSPORT_AUDIT_2026-09-19_1.md

All four recommended changes and the §6 harness items, in the audit's order.
`DIFFERENCES.md` has the per-finding detail and the before/after replay.

| Audit item | Status |
|---|---|
| 1. B3 datagram discard | fixed: `DatagramSize.Event.recvDatagram size required`, `FailsSizeConstraint`, `Pipeline.requiredSize`; `datagram_drop_iff`. §12.3 line 4717's minimum packet number, which the blanket discard had been standing in for, is `Pipeline.minimumRaised` |
| 2. B1 CRYPTO resource policy | fixed: `Handshake.BufferPolicy` (payload bytes and reordering span), `Admissible` = the 4096 floor under both; no absolute offset cutoff admitted |
| 3. B4 implicit stream opening | fixed: `Effect.streamsOpenedBelow` (one range), `Effect.streamFirstUsed` for the API moment, `no_reuse` over `Effect.opens`; harness skip off by default |
| 4. B6 completion mapping | fixed in `Exports.Effect.cbNames` only; model effects unchanged |
| 5. B2, A4, B5, B7, B8 | deferred, as the audit asks |
| 6. harness | `tlsDiscardKeys` priming; one `step_drain` before an overdue ACK is reported, none after the engine closed; reports and summary distinguish exhaustive rejection from rejection after candidate loss; `DIFF_ALL` |

Corpus replay, 2 458 inputs: ngtcp2 44 signatures / 649 steps → 27 / 138;
quiche 26 / 571 → 24 / 323.  New implementation finding: quiche ignores
STREAM_DATA_BLOCKED (`DIFFERENCES.md` A6); ngtcp2's A2 is now a pairwise
mismatch.  Open next: the quiche `bfd34bc6…` residue (201 steps), the candidate
cap (233 of quiche's 323 steps are after candidate loss), the digest join has
not been re-run.

## 4l. Google QUICHE (Chrome's QUIC) as a third implementation (2026-09-20)

`out/gquiche_diff` is `harness/endpoint_diff.c` built with `-DDRIVER_GQUICHE`
(`./build_gquiche_harness.sh`): `harness/gquiche_driver.h` is the engine,
`harness/gquiche/gquiche_shim.{h,cc}` puts QUICHE's C++ behind C calls, and a
one-target Bazel workspace there links it with an **unmodified**
`../google-quiche` (github.com/google/quiche at `535a2730`, 2026-09-18) into
`out/libgquiche_shim.so`.  Same scripts, same binary format, same corpus.
`harness/endpoint_diff.md` §11 has the design; in one line: crypto, clock,
alarms, writer and randomness are all QUICHE interfaces, so the model's stub
cipher is installed directly, nothing is converted, packet numbers are
absolute, and runs are reproducible.

State: eight scripts, 0 mismatches.  QUICHE closes with ngtcp2's code in
scripts 02, 05 and 06, and with PROTOCOL_VIOLATION where ngtcp2 says
FINAL_SIZE_ERROR (03) and FRAME_ENCODING_ERROR (04, MAX_STREAMS > 2^60) — which
the model accepts.  Corpus replay (`-runs=0
corpus/conn_trace`, 2 456 inputs): no crash, 14 581 steps compared, 14 438 send
checks, 0 unparsable datagrams, **23 signatures / 406 mismatches, untriaged**
beyond the first look below.  Every mismatching input was replayed on all three
engines; the artifacts are in `out/artifacts-gq`.  A first five-minute fuzzing
run (`out/corpus-gq` in front of `corpus/conn_trace`, so the shared corpus is
not written to): 26 881 runs at ~90/s, no crash, QUICHE coverage feeding
libFuzzer (823 new inputs), 36 signatures, `bebccbdd…` alone 1 012 of 1 746.

First look, by size:

1. `bebccbdd…` ×281 — ACK with Largest Acknowledged = 0 closes QUICHE with
   FRAME_ENCODING_ERROR ("QUIC_INVALID_ACK_DATA: Largest acked is 0"); the
   model permits OK or PROTOCOL_VIOLATION.  QUICHE never sends packet 0, so
   this is an acknowledgment of an unsent packet, for which §13.1 asks
   PROTOCOL_VIOLATION.  Mostly an artefact of a corpus grown against ngtcp2
   (which does send packet 0) — item (3) of §4j again — but the code is
   QUICHE's choice.
2. `1cdbc1cd…` ×42 — STREAMS_BLOCKED with Maximum Streams = 2^60 exactly:
   QUICHE closes with PROTOCOL_VIOLATION, §19.14 forbids only values *above*
   2^60 and names STREAM_LIMIT_ERROR / FRAME_ENCODING_ERROR.  Also mismatches
   under ngtcp2.
3. `892de5bd…` ×16 — ACK refused by `ackPacketOk`: now under all three
   engines; see §4j (2), the model is the suspect.
4. `405f42eb…` ×10 — a client accepts RETIRE_CONNECTION_ID for sequence
   numbers it never issued; the model wants §19.16's PROTOCOL_VIOLATION.
5. `dcidOk` ×2 — after NEW_CONNECTION_ID with Retire Prior To = 1, the ACK
   written in the same pass still carries the retired DCID; QUICHE switches in
   a zero-delay alarm.  §5.1.2 "MUST stop using".
6. `StreamTable` send refusals (STREAMS_BLOCKED after a refused `open`,
   STREAM/RESET_STREAM/MAX_STREAMS) ×~25 and `pathResponsesOnPath` ×~10: not
   looked at; the first suspect is the driver's `open`/`write` mapping, not
   QUICHE.
7. With `DIFF_GQ_CHECK_CLOSE`: every closing datagram is refused (ACK bundled
   with CONNECTION_CLOSE).  Off by default for parity with the other engines.

Open: triage 4–7; `DIFF_DIGEST` three-way join; `extend_max_*` callbacks
(`OnCanCreateNewOutgoingStream`, `OnCanWrite`) are not surfaced yet; QUICHE's
dependencies are built without coverage and the library without ASan.

## 4m. Consideration: raw and clean traces (2026-09-20; written down, not scheduled)

The yardstick for anything below is whether it improves the two checks this
project exists for — **conformance** (does the implementation do what the
specification permits: engine vs model, `may_send_datagram`, `track_trace`) and
**correctness of the specification as modelled** (is the model too strict or
too lax: "both engines MISMATCH" and "latitude" in `digest_diff.py`).  It is
not a goal in itself to make traces of different engines look alike.

The idea: keep two forms of every trace.  *Raw* is what is on the wire and is
what the model checks.  *Clean* replaces values an endpoint was free to choose
with a canonical name, and is what an engine-vs-engine diff triggers on.  It
came up because QUICHE numbers its packets from 1 (valid: §12.3's "start at
packet number 0" carries no MUST, §21.4 permits skipping, and no receiver can
tell), so a corpus input's `ACK largest=0` acknowledges ngtcp2's first packet
and a packet QUICHE never sent — `bebccbdd…`, 281 of 406 replay mismatches, and
§4j (3).

**How wide it goes.**  Exactly the values that are (i) chosen freely by the
endpoint and (ii) referred to later.  That is a short list: sent packet numbers
(order and gaps matter), issued connection-ID bytes, stateless reset tokens,
PATH_CHALLENGE data, NEW_TOKEN/Retry tokens (only equality matters), and — for
Cloudflare quiche only — the base of the forged peer's 1-RTT numbers.  Stream
IDs are *not* on it: §2.1 fixes them completely (initiator, direction, index),
all three engines produce the same ones, and a jump in index is an implicit
open, which the model already handles.

**Shape of a clean name.**  For ordered values `.nth k` (the k-th value the
binder introduced in that space) or `.unsent (after k)` (a reference to a value
never introduced, placed relative to those that were — an ACK of a skipped
number is an ACK of an unsent packet).  For equality-only values
`.fresh k | .unbound`.  A *decrease* in sent packet numbers is not a naming
matter: it is a MUST violation and belongs to the raw check — which at present
does **not** make it (`Ack.maySendPacketNumber` is not wired into `Endpoint`,
§4n item 2).

**It has to cover inputs, not only outputs.**  The immediate problem is on the
input side: an absolute reference in a step means different things to
different engines.  Symbolic references in the step grammar (`ack sent[0..2]`,
`retire issued[1]`, `path_response echo[0]`), resolved per engine by the
driver, fix that; the binary corpus can be reread with its small integers as
indices.  This would also retire `q_peer_pn_base` and the handshake-replay
special case of quiche_driver.h.

**What must stay raw, for conformance.**  The specification distinguishes raw
values in places a clean form erases: the packet-number encoding length
relative to the largest acknowledged (§17.1), gap sizes, exhaustion.  So the
model keeps checking raw; clean is for the cross-engine join only.

**What is not renaming, and costs findings if normalised.**  Packetisation
(→ byte ranges sent per stream per step), ACK timing (→ set of acknowledged
ordinals at step end, delay bucketed against `max_ack_delay`), MAX_* values
(→ the running limit), callback granularity (→ delivered offset + fin at step
end) are genuine latitude, not names.  Collapsing them makes the join quieter
and hides rules about exactly those things: three items of this session —
PATH_RESPONSE without the 1200-byte expansion, ACK bundled with
CONNECTION_CLOSE, a retired DCID used in the same pass — are packetisation and
ordering facts.  Padding length, frame order within a packet and the choice of
error code should stay raw.  Add such a projection only where `digest_diff.py`
shows the noise is drowning something.

**Where it would pay, in order.**  (1) Symbolic references in inputs: restores
conformance checking of ACK processing under QUICHE (at present most
ACK-bearing inputs close the connection at once, so the ACK rules are barely
exercised there) and removes the largest signature.  (2) A send-side digest
with `.nth` names — today's digest line is event, ok/err and two callback names
and says nothing about what was sent, so the "latitude" class (276 in the first
join) is mostly uncleaned.  (3) The byte-range and acknowledged-set
projections.  Stop there until the join says otherwise.

## 4n. Measured: which specification requirements the harness exercises (2026-09-20)

Method.  The C that Lean emits is built with `-fprofile-instr-generate
-fcoverage-mapping` (`out/obj-cov`, binaries `out/*_diff_cov`);
`corpus/conn_trace` is replayed under each engine (`-runs=0`; Google QUICHE
also over `out/corpus-gq`); `llvm-cov export` gives a count per C function;
`harness/scripts/spec_coverage.py` maps the back-quoted identifiers of every
coverage-table row in `QuicModel/Spec/**` to those functions.  Per-row result:
`out/spec_coverage_rows.tsv`.

**Initialisation must be subtracted.**  A run with no input executes 2 940
model functions: Lean evaluates closed terms (the Examples) at module
initialisation.  A first version of this section reported 28 % region coverage
that was almost entirely that.  A function counts only if the replay ran it
more often than initialisation did.

**By function** (definitions in `QuicModel/Spec`, without derived instances,
match splitters and `_boxed` wrappers): 1 811 functions, **504 exercised
(28 %)** — ngtcp2 501, Cloudflare quiche 491, Google QUICHE 496.  StreamTable
and Ack 54 %, FrameRules 41 %, Stream 37 %, Endpoint 34 %, Termination 33 %,
Handshake 31 %, ConnIds and AddressValidation 30 %, Migration and
PathValidation 24 %, VersionNegotiation and Core 19 %, DatagramSize 15 %,
Ecn 7 %, Retransmission 1 %, TransportParams 0 %.

**By requirement** (coverage-table rows whose sentence has a normative
keyword; `cq` = Cloudflare quiche, `gq` = Google QUICHE):

| component | norm.rows | unnamed | no-code | executable | direct/guard/outcomes | ngtcp2 | cq | gq | any |
|---|---|---|---|---|---|---|---|---|---|
| AddressValidation | 50 | 21 | 14 | 15 | 7/1/7 | 10 | 10 | 10 | 10 |
| Migration | 49 | 11 | 7 | 31 | 16/15/0 | 16 | 16 | 16 | 16 |
| Termination | 47 | 13 | 8 | 26 | 12/2/12 | 22 | 21 | 21 | 22 |
| Stream | 44 | 7 | 7 | 30 | 19/4/7 | 25 | 25 | 25 | 25 |
| Ack | 34 | 5 | 15 | 14 | 13/1/0 | 11 | 11 | 11 | 11 |
| Handshake | 28 | 3 | 17 | 8 | 7/0/1 | 5 | 5 | 5 | 5 |
| VersionNegotiation | 27 | 2 | 7 | 18 | 5/5/8 | 13 | 13 | 13 | 13 |
| DatagramSize | 26 | 5 | 5 | 16 | 7/1/8 | 16 | 16 | 16 | 16 |
| TransportParams | 24 | 5 | 0 | 19 | 18/1/0 | 0 | 0 | 0 | 0 |
| StreamTable | 21 | 1 | 3 | 17 | 10/2/5 | 16 | 16 | 16 | 16 |
| ConnIds | 20 | 4 | 4 | 12 | 10/2/0 | 12 | 8 | 12 | 12 |
| FrameRules | 20 | 2 | 8 | 10 | 8/1/1 | 6 | 6 | 6 | 6 |
| PathValidation | 20 | 3 | 1 | 16 | 10/1/5 | 13 | 13 | 13 | 13 |
| Ecn | 8 | 0 | 3 | 5 | 3/2/0 | 1 | 1 | 1 | 1 |
| Retransmission | 7 | 1 | 1 | 5 | 4/0/1 | 1 | 1 | 1 | 1 |
| Template | 3 | 1 | 0 | 2 | 0/0/2 | 0 | 0 | 0 | 0 |
| **total** | 428 | 84 | 100 | 244 | 149/38/57 | 167 | 162 | 166 | 167 |

Reading the columns.  *unnamed*: the row names no definition (out of scope,
informative, prose).  *no-code*: it names only theorems, types or `Prop`s with
no decision procedure in the binary — proved about, never checked at run time.
*executable*: resolved to code, split by how: *direct* (the named definition,
its Bool twin or `instDec*` instance), *guard* (`Step.foo` is a constructor of
a `Prop`; the definitions its hypotheses name stand in for it), *outcomes*
(nothing better than "the component's `outcomes` ran").  So of 428 normative
rows, 244 can be exercised at all and 167 were; of those 167 only 113 are
direct-or-guard evidence, 54 say no more than that the component was stepped.
Function granularity: `failCase` ran, not "`failCase` answered `.revert`".
Blind spot: a definition inlined everywhere reads as not exercised.

What it shows.

1. **Engines do not buy coverage.**  167 / 162 / 166, union 167.  The driver
   and the corpus decide what is reached.  (Cloudflare quiche is lower on
   ConnIds: `Local.canIssue` / `applyIssue` / `isReNewCid` never run, i.e. no
   `LocalAction.issueCid` is replayed under that driver.)
2. **A requirement that is modelled and never checked: §12.3.**
   `Ack.maySendPacketNumber` ("MUST increase the packet number by at least
   one", "MUST NOT reuse a packet number", the 2^62-1 bound) is referenced by
   nothing outside `Spec/Ack` — it is not a conjunct of
   `Endpoint.maySendPacket`.  An engine that reused or decreased a packet
   number would pass.  This came up only because QUICHE numbers from 1 and the
   question "is that valid" was asked; §4m's first draft wrongly assumed the
   rule was enforced.  Cheap to wire in: `parse_out` already recovers the
   number.
3. **Unreachable by construction** (endpoint_diff.md §10): TransportParams
   0/19, Migration's 15 unexercised rows, Handshake, VersionNegotiation,
   AddressValidation's token rows, Retransmission (no loss event is ever
   synthesised), Ecn (the peer's packets carry no ECN marks and its ACKs mostly
   no counts).
4. **Reachable in principle, not reached** — corpus or driver work, not model
   work: §3.5 line 1254 "STOP_SENDING MUST be answered with RESET_STREAM"
   (`Step.stopSending`'s guards — worth a look, the frame is common in the
   corpus, so this may be a mapping miss); §3.5 line 1243 and §19.13
   `RecommendedSend` (the harness does not evaluate the SHOULD predicates of
   Stream at all); §13.2.2 `Recommended.twoAckEliciting`; §11.1 line 4457
   `Step.recvClosingRespond` (every driver stops stepping once the engine has
   closed); §10.3 stateless reset sizes; §10.2.3 `convertCloseForHandshake`.
   `grep -P "NOT exercised" out/spec_coverage_rows.tsv`.
5. 100 *no-code* rows are requirements with a proof and no run-time check;
   whether each *should* have one is a review, not a measurement.

## 4o. Plan: check packet numbers; raise what a harness run covers (2026-09-20)

Yardstick as in §4m: conformance and correctness of the model.  The measure is
§4n's requirement table (`harness/scripts/spec_coverage.py`), re-run after each
step; a step is done when its rows move from "NOT exercised" to "exercised
(direct|guard)" on at least two engines and the corpus replay's signature list
has been compared before/after.

### A. §12.3 packet numbers (small, first)

Today: `Ack.maySendPacketNumber` exists with its theorems and is called by
nothing; `OutPacket` has no number; `Ack.Step.sent` takes any number
(`bumpSent` is a max).  An engine that reused or lowered a number passes.

A1. *Model.*  `Endpoint.MaySendDatagram` gets the numbers: either a `pn : Nat`
    field on `OutPacket` (touches every constructor site: Examples, Harness,
    FrameRules) or — smaller, preferred — a parallel predicate
    `Endpoint.maySendNumbers : State → List (PnSpace × Nat) → Bool`
    = per space, strictly increasing along the list *and* each
    `Ack.maySendPacketNumber`.  "Along the list" matters: two packets coalesced
    in one datagram share the pre-state, so the per-packet predicate alone
    would accept a repeat inside a datagram.  Theorem: accepted numbers keep
    `largestSent` strictly increasing over a run
    (`largestSent_strictMono_of_maySendNumbers`).
A2. *Export + harness.*  `quic_endpoint_may_send_numbers`; `md_out` builds the
    list from `ps[i].space / ps[i].pn` (already recovered by `parse_out`) and
    reports kind `maysend`, conjunct `pnOk`, in `..._why`.
A3. *The recovery is circular.*  `parse_out` decodes the truncated number with
    `ngtcp2_pkt_adjust_pkt_num(out_max_pn, …)`, i.e. *assuming* monotonicity: a
    reused number decodes as itself only when it is within half the window
    below the maximum, and a wrapped one decodes upward.  Keep that decoder
    (it is the receiver's, §A.3) but also pass the raw truncated value and
    length, and have the model check §17.1, line 6028: "the sender MUST use a
    packet number size able to represent more than twice as large a range than
    the difference between the largest acknowledged packet and packet number
    being sent" (not modelled today) — then the
    decode is *justified* rather than assumed.  Gives Ack rows §12.3 4685/4692
    and the §17.1 row.
A4. *Negative test.*  A script cannot make an engine misnumber.  Add
    `QuicModel/Spec/Endpoint/Examples.lean` guards (repeat, decrease, repeat
    inside one datagram, `maxPn`), and a `DIFF_SELFTEST=pn` mode in
    `endpoint_diff.c` that replays the last datagram into `md_out` twice and
    expects a `pnOk` mismatch — a harness check that the wire is connected,
    in the spirit of §4k's "acceptance must be evidence".
A5. Replay all three engines; expected: no new signature (QUICHE from 1,
    ngtcp2/quiche from 0, all strictly increasing).  Exhaustion (`pnExhausted`)
    stays unreachable; leave it to the Examples.

### B. Coverage of the specification by harness runs

Ordered by rows gained per unit of work; numbers are §4n's "NOT exercised" and
unreachable rows.  B1–B3 need no new model code — they are driver and corpus.

B1. *Make the measurement routine.*  `build_cov.sh` (the three `*_diff_cov`
    binaries + init profile) and `spec_coverage.py --diff old.tsv new.tsv`.
    Add branch-level evidence for `Step` guards where function level is blind
    (`failCase` ran vs answered `.revert`): llvm-cov region counts per C
    function are already in the export.  Then settle §4n item 4's open
    question (is §3.5 line 1254 a mapping miss?).
B2. *Inputs that mean the same to every engine* (§4m (1)): symbolic
    `ack sent[i..j]`, `retire issued[k]`, `path_response echo[k]`.  Without it
    most ACK-bearing inputs close QUICHE at once and Cloudflare quiche sees
    shifted numbers, so everything downstream of a *valid* ACK is thin:
    `Ack.recvAck`, `Ecn` validation, `Retransmission.acked`,
    `Stream.Send.allDataAcked` (TRIAGE WP13-6).
B3. *Keep stepping after the close.*  Drivers set `h->fatal` and stop.  Let
    `recv`/`time` continue in closing/draining, and show the closing datagram
    to the model on all three engines (today opt-in under QUICHE only).
    Reaches Termination §10.2.1–10.2.3, §11.1 line 4457
    `Step.recvClosingRespond`, the draining timer: ~6 rows.  Prerequisite:
    resolve `ackPacketOk` (§4j (2)) — it refuses every closing datagram that
    bundles an ACK, under all three engines.
B4. *Evaluate the SHOULDs.*  `Recommended*` predicates are never called
    (§13.2.2 two ack-eliciting packets, §19.13 *_BLOCKED, §3.5 line 1243,
    §13.3 line 5393, §8.2.1 line 3142).  Export `quic_endpoint_recommended_why`
    and count violations as a separate **advisory** class — never a mismatch,
    never narrows the candidate set.  ~10 rows, and the first data on how the
    engines treat SHOULD.
B5. *A loss step.*  Nothing ever declares a packet lost, so Retransmission is
    at 1 %.  New engine-neutral step `lose sent[i]`: the model gets
    `Event.lost`; the engines get there by time (PTO) plus an ACK that skips
    `sent[i]` by the reordering threshold — needs B2.  Send-side rules then
    checkable: RESET_STREAM content unchanged, no STREAM after reset,
    PATH_RESPONSE not retransmitted, blocked frames carry the current limit.
B6. *ECN.*  `recv` gains an ECN codepoint (ngtcp2 `pi.ecn`, quiche
    `recv_info`, QUICHE `QuicReceivedPacket` ecn argument) and forged ACKs
    gain counts.  Ecn 7 % → the §13.4.1 feedback rows and §13.4.2.1 validation.
B7. *A second path.*  `recv` from another 4-tuple; PATH_CHALLENGE/RESPONSE on
    it; NAT rebinding vs migration.  Opens Migration (15 guard rows),
    PathValidation's remaining 3, ConnIds' use-a-new-CID-on-a-new-path,
    AddressValidation's per-path amplification.  The largest single gain and
    the largest driver change (three engines' path APIs differ); do after B2–B6.
B8. *The handshake, scripted rather than forced.*  TransportParams 0/19,
    Handshake, VersionNegotiation, Retry/token rows are unreachable while setup
    forces the post-handshake state.  Two stages: (a) a pre-handshake *client*
    against forged server flights with the stub cipher at every level — ngtcp2
    and QUICHE allow it, Cloudflare quiche does not (real TLS), so this is a
    two-engine check; forged transport parameters become a fuzzable blob and
    the 19 TransportParams rows become reachable; (b) Version Negotiation and
    Retry packets as `recv` kinds.
B9. *Corpus.*  After each driver step, a fuzzing campaign per engine seeded
    from the shared corpus, merged with `-merge=1` into `corpus/conn_trace`
    only when `spec_coverage.py` shows new requirement rows — coverage of the
    *model*, not of the engines, is the criterion for keeping an input.

Not planned: more engines (§4n item 1: they add no coverage); the 100 *no-code*
rows — deciding which of them deserve a run-time check is a review of the
coverage tables, to be scheduled separately.

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
