# Wave 1 review, batch B — WP5 AddressValidation/PathValidation, WP6 Termination, WP7 VersionNegotiation/DatagramSize

Reviewer read the assigned text ranges of `spec/draft-ietf-quic-transport-34.txt`
before the Lean, then the `Step` relations, `outcomes`, `MaySend*`, `Recommended`,
`Inv`, named theorems and NOTES. All findings that are marked HIGH or MEDIUM and
are behavioural are backed by a probe in `out/probe_wp5.lean`,
`out/probe_wp6.lean`, `out/probe_wp7.lean` (all three compile clean:
`timeout 300 lake env lean out/probe_wp<n>.lean`, exit 0 — every `example` below
is a *passing* assertion about the model as it stands). The probe files live in
the `review1b` worktree under `out/`, which is `.gitignore`d, so they are not in
the commit; the snippets quoted below are self-contained apart from the private
`def`s they name, which are also quoted.

`lake build` on the merged tree: 67/67, clean.

---

## WP5 — `QuicModel/Spec/AddressValidation.lean`, `QuicModel/Spec/PathValidation.lean`

### Findings

| id | sev | text (§, line, quote) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| AV-1 | HIGH | §8.1, 2818: "Clients are only constrained by the congestion controller." (cf. §8, 2736 "*after receiving packets from* an address that is not yet validated") | `AddressValidation.MaySendDatagram` / `maySendDatagram` (l.544–548) | Role-independent, and `State.info` defaults an unheard-of address to `received = 0`, so a fresh **client** may send **0 bytes** — its first Initial (1200 B, §8.1 l.2783) is refused. NOTES 1 says "the limit rarely binds it"; in fact it binds it absolutely at t=0. | Add the client exemption, or gate the budget on "we have received from this address and it is unvalidated": `s.role = .server ∧ …`, or `(s.info a).received = 0 → True`. Either matches §8.1 l.2818. |
| PV-1 | HIGH | §19.18, 8110: "If the content of a PATH_RESPONSE frame **does not match** the content of a PATH_CHALLENGE frame previously sent by the endpoint, the endpoint MAY generate a connection error of type PROTOCOL_VIOLATION." | `PathValidation.Step.responseViolation`, `State.matching`, `State.clearPath` (l.87, 179, 186) | `matching` searches only *outstanding* challenges and `responseMatch` calls `clearPath`, which drops **every** challenge for the path. So a duplicated PATH_RESPONSE, a reordered response to a second PATH_CHALLENGE (which line 3141 explicitly encourages sending), and a response arriving after the abandon timer all become "unmatched" — and the model then **accepts a PROTOCOL_VIOLATION connection error** that §19.18 authorises for none of them. NOTES 8 records the `clearPath` choice but not this consequence. | Keep a `answered : List ByteArray` of data we have ever challenged with; `responseViolation` requires `d ∉ answered ∧ matching d = none`, `responseIgnore` keeps the rest. |
| AV-2 | MEDIUM | §8.1.3, 2920: "Servers MAY discard any Initial packet that does not carry the expected token." | `Step.initialValidated` (l.204), `Step.initialAbsent*` (l.209–214) | For a server whose address is already validated the **only** outcome for *any* `clientInitial` is `.ok s [.handshakeProceeds a]` — `.drop` is rejected. Same for an unvalidated server with `chk = .absent`. The MAY is only honoured for `.invalid .newToken`. | Add a `.drop` outcome (last) to `initialValidated` and to the `.absent` branch. |
| AV-3 | MEDIUM | §8.1.3, 2989: "If the token is invalid then the server SHOULD proceed as if the client did not have a validated address, including potentially sending a Retry." §8.1.2, 2876 is a SHOULD ("SHOULD immediately close … INVALID_TOKEN"). | `Step.initialInvalidRetry{Close,Discard}` (l.257–262) | For an invalid *Retry* token the model permits only `.error .invalidToken` or `.drop`. Line 2989 is written for tokens of either provenance, and per the project rules a SHOULD that merely recommends must not make `Step` reject the alternative. | Add `.ok s [.handshakeProceeds a]` (and arguably `.ok s [.sendRetry a]`) after the two existing outcomes. |
| AV-4 | MEDIUM | §5.2.2, 1936: "If a server refuses to accept a new connection, it SHOULD send an Initial packet containing a CONNECTION_CLOSE frame with error code CONNECTION_REFUSED." | `Step`, `outcomes` for `.clientInitial` | *(the lead's open point)* `.error .connectionRefused` is permitted **only** in the two `.valid .retry` branches. §5.2.2 gives the server an unconditional right to refuse **any** new connection; §8 does not take it away. If WP12 composes components by intersecting `accepts`, `AddressValidation` will veto a legitimate refusal of a token-less Initial. **Verdict on the open point: yes, it is too strict for the component itself**, though the right fix is probably at the composition level. | Either add `.error .connectionRefused` to every `clientInitial` branch (as the last outcome), or make WP12's merge for connection-level errors a union rather than an intersection and say so in `Core`. |
| AV-5 | MEDIUM | §17.2.5.1, 6597: "This value **MUST NOT be equal to** the Destination Connection ID field of the packet sent by the client." §17.2.5.1, 6616: "A server MUST NOT send more than one Retry packet in response to a single UDP datagram." | coverage rows "§17.2.5.1 (6597)" → `Step.retrySameCid`; "(6616)" → NOTES 6 | 6597 is a **server send** MUST NOT; only the *client* discard of 6598 is modelled, and the coverage row conflates the two. There is no send-side predicate for a Retry packet at all, so both 6597 and 6616 are handed to WP12 with nothing to hand over. | Export `maySendRetry (clientDcid clientScid retryScid : ByteArray) : Bool` (≥ `retryScid ≠ clientDcid`), and a per-datagram `atMostOneRetry` obligation on the effect list, so WP12 has something to conjoin. |
| AV-6 | LOW | §8.1.3, 2973: "A client SHOULD NOT reuse a NEW_TOKEN token for different connection attempts." | coverage row → "`Recommended`, NOTES 5" | No `Recommended` definition exists anywhere in the file (`grep -n Recommended QuicModel/Spec/AddressValidation.lean` finds only the two prose mentions). | Define it, or write "prose only, not encoded". |
| AV-7 | LOW | §8.1.2, 2876; §8.2.3, 3220 | `Step.initialInvalidRetryClose` doc ("line 2875"); `Step.pathValidates` doc + coverage ("line 3219") | Off-by-one citations; 2876's quote also silently drops "(Section 10.2)". Error code itself (`invalidToken`, 0x0b) is correct. | — |
| AV-8 | LOW | §8.1 2818; §8.1.3 2934, 3013; §8.1.4 3061, 3065; §17.2.5 6581; §17.2.5.1 6613; §17.2.5.3 6673, 6691 | coverage table | Normative sentences in range that the coverage table does not list at all (most are MAY/SHOULD or opaque-token rules, but the table is meant to be exhaustive over the range). 6581 ("a client MUST ignore these bits") is a MUST. | Add rows, most as `out of scope: …`. |
| PV-2 | LOW | §19.17 8084–8093, §19.18 8110 | `challengeSize` (l.15), `Step.responseIgnore`/`responseViolation` (l.180–187) | Two rules imported from outside WP5's range with no line number on §19.18, and neither appears in the coverage table as an out-of-range import (the table has one bare "§19.18" row). | Cite line 8110 and note the import. |
| PV-3 | LOW | §8.2.2, 3183: "A PATH_RESPONSE frame MUST be sent on the network path where the PATH_CHALLENGE was received." | `MaySend` (l.320–323) vs `MaySendResponseOn` (l.335) | The component's `MaySend` for `.pathResponse` ignores the path; the path-aware form is a free function that nothing calls, so `component.maySend` alone does **not** enforce a MUST. | Note it prominently for WP12 (it cannot become `MaySendPacket` either — the path is not in `OutPacket`). |
| PV-4 | LOW | §8.2.1, 3171 is about *size*-based discards only | `challenge_never_dropped`, `response_never_dropped` (l.533, 537) | `Step` forbids dropping a received PATH_CHALLENGE/PATH_RESPONSE for *any* reason in *any* state — stronger than 3171. Collides with §10.2.1 l.3984 ("An endpoint that is closing is not required to process any received frame") at composition. | Keep, but flag in NOTES as a composition constraint, or add an unconditional `.drop`. |

### Probes

```lean
-- P5.1 (AV-1) a brand-new client may send nothing at all
example : maySendDatagram (init .client c0) a1 1200 = false := by decide   -- its first Initial
example : maySendDatagram (init .client c0) a1 1    = false := by decide

-- P5.2 (AV-2) a validated server has exactly one permitted outcome
private def svV : State := ((init .server c0).addRecv a1 1200).validate a1
example : component.outcomes svV (.clientInitial a1 .absent)
    = [.ok svV [.handshakeProceeds a1]] := by decide
example : component.accepts svV (.clientInitial a1 .absent) .drop = false := by decide
example : component.accepts svV (.clientInitial a1 (.invalid .newToken)) .drop = false := by decide

-- P5.3 (AV-2) an unvalidated server may not discard a token-less Initial …
private def sv : State := (init .server c0).addRecv a1 1200
example : component.accepts sv (.clientInitial a1 .absent) .drop = false := by decide
-- … though it may discard one with an invalid NEW_TOKEN token
example : component.accepts sv (.clientInitial a1 (.invalid .newToken)) .drop = true := by decide

-- P5.4 (AV-3) invalid Retry token: "proceed as unvalidated" is rejected
example : component.outcomes sv (.clientInitial a1 (.invalid .retry))
    = [.error .invalidToken, .drop] := by decide
example : component.accepts sv (.clientInitial a1 (.invalid .retry))
    (.ok sv [.handshakeProceeds a1]) = false := by decide

-- P5.4b (AV-4) CONNECTION_REFUSED only in the two `.valid .retry` branches
example : component.accepts sv  (.clientInitial a1 .absent)                  (.error .connectionRefused) = false := by decide
example : component.accepts sv  (.clientInitial a1 (.valid .newToken true))  (.error .connectionRefused) = false := by decide
example : component.accepts svV (.clientInitial a1 .absent)                  (.error .connectionRefused) = false := by decide
example : component.accepts sv  (.clientInitial a1 (.valid .retry true))     (.error .connectionRefused) = true  := by decide

-- P5.7 (PV-1) a DUPLICATED PATH_RESPONSE is an accepted connection error
private def s1     : State := { init with outstanding := [⟨d1, p1, 400⟩] }
private def sAfter : State := (component.step s1 (.recvResponse p1 d1)).next s1
example : sAfter.outstanding = [] := by decide
example : component.accepts sAfter (.recvResponse p1 d1) (.error .protocolViolation) = true := by decide

-- P5.8 (PV-1) two challenges on one path: the first response clears BOTH,
-- so the response to the second challenge becomes an accepted error
private def s2  : State := { init with outstanding := [⟨d2, p1, 500⟩, ⟨d1, p1, 400⟩] }
private def s2' : State := (component.step s2 (.recvResponse p1 d1)).next s2
example : s2'.outstanding = [] := by decide
example : component.accepts s2' (.recvResponse p1 d2) (.error .protocolViolation) = true := by decide

-- P5.9 (PV-1) a late response, after the abandon timer, likewise
private def sT : State := (component.step s1 (.timeout p1 400)).next s1
example : component.accepts sT (.recvResponse p1 d1) (.error .protocolViolation) = true := by decide
```

### Free-standing send-side functions (for the fold-in)

| function | signature | fold-in note |
|---|---|---|
| `AddressValidation.MaySendDatagram` / `maySendDatagram` / `_iff` | `State → Addr → Nat → Prop` / `→ Bool` | **`Spec.OutDatagram` has no peer address.** `Component.MaySendDatagram : State → OutDatagram → Prop` cannot express this rule until `OutDatagram` gains one (or the state records a "current" address). |
| `AddressValidation.instDecidableMaySendDatagram` | `Decidable (MaySendDatagram s a n)` | — |
| `PathValidation.MaySendDatagram` / `maySendDatagram` / `_iff` | `AddressValidation.State → AddressValidation.Addr → List Frame → Nat → Prop`/`Bool` | Takes **another component's state**; cannot be a `Component` field without a joint state. Frames are passed as a list, not an `OutDatagram`. |
| `PathValidation.MaySendResponseOn` | `State → ByteArray → Path → Prop` | the real §8.2.2 l.3183 rule; not reachable from `OutPacket` (no path). |
| `PathValidation.RecommendedPacket` | `List Frame → Prop` | advice (§8.2.1 l.3142); keep out of `MaySendPacket`. |
| `PathValidation.isProbeFrame` / `expandRequired` | `Frame → Bool` / `List Frame → Bool` | helpers. |

### Checked and found correct (WP5)

- 3× arithmetic: 3600 permitted / 3601 not after a 1200-byte receive; cumulative across datagrams (`sv.addSent a 3600` then 1 byte ⇒ false); a fresh server may send 0.
- Retry handling in full: zero-length token, bad integrity tag, SCID = own Initial DCID, a second Retry after an Initial *or* a Retry from the server, `Effect.useToken`/`useDcid`, `Inv`, `atMostOneRetry`, `retry_discarded_after`, `retry_effects`.
- §8.1.2 l.2836: no `sendRetry` outcome exists after a valid Retry token (both `addrUnchanged` values).
- §8.1.4 l.3054: a valid token from a changed client address does **not** validate the address, for both token provenances.
- §8.2.1 l.3154 / §8.2.2 l.3197 expansion, including the anti-amplification exemption; boundary at 1199/1200 for both a 600-byte and a 300-byte budget.
- `MaySend` for PATH_CHALLENGE/PATH_RESPONSE correctly refuses an exact repeat — §13.3 l.5415 ("PATH_CHALLENGE frames include a different payload each time they are sent") and l.5418 ("Responses … are sent just once") forbid those specific repeats, so the BRIEF's idempotence rule does not apply.
- §8.2.3 l.3214 (a response on *any* path validates the challenged path) and §8.2.2 l.3186 (the initiator must not enforce the path) are both encoded correctly.
- `validated_only_by_response`, `validated_persists` (both files), `response_once`, `pending_only_from_challenge`, `antiAmplification` + `EventOk`/`ReachableOk`: each statement matches its doc comment and none is vacuous.

---

## WP6 — `QuicModel/Spec/Termination.lean`, `Termination/{Basic,Send}.lean`

### Findings

| id | sev | text (§, line, quote) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| T-1 | HIGH | §10.3.3, 4393: "An endpoint MUST ensure that every Stateless Reset that it sends is smaller than the packet that triggered it, **unless it maintains state sufficient to prevent looping**." | `Termination.maySendStatelessReset` (Send.lean l.152) | The "unless" exemption is dropped: `resetSize < triggerSize` is enforced unconditionally, with no parameter for an endpoint that *does* keep anti-loop state. The model rejects conforming behaviour. (The doc comment quotes the exemption but the definition ignores it.) | `maySendStatelessReset (preventsLooping : Bool) (triggerSize resetSize) := 21 ≤ r && (preventsLooping || r < t) && r < 3*t`; `statelessReset_needs_large_trigger` then needs `preventsLooping = false`. |
| T-2 | MEDIUM | §10.1, 3831: the connection is closed "when it remains idle for **longer than**" the effective value | `State.tickExpires` (Basic.lean l.181), `outcomes` for `.tick` (l.404) | `idleStart + effectiveIdle ≤ now`, **and** at that instant `.ok s []` is not among the outcomes, so an endpoint that closes at `idleStart + effectiveIdle + 1` is rejected. The NOTES record the `≤`/`<` choice but not that the model makes the close *mandatory* at that exact microsecond. | Use `<` and/or add `.ok s []` as a second outcome when `tickExpires` is true (the timeout has no deadline for noticing it). |
| T-3 | MEDIUM | §10.2.1, 3993: "such endpoints MUST limit the cumulative size of packets it sends to three times the cumulative size of the packets that are received"; §10.2.1, 4008: "An endpoint in the closing state MUST **either** discard packets received from an unvalidated address **or** limit the cumulative size …" | coverage rows → "out of scope: WP5" | WP5 owns **neither**: both lines are outside WP5's assigned range and appear nowhere in its coverage table. 4008 is an "either/or" that WP5's unconditional 3× rule does not express. Two MUSTs in range with no owner. | Either state them here over the closing phase, or add explicit rows to WP5's table and an `Addr`-aware clause there. |
| T-4 | MEDIUM | §11, 4434: "an endpoint MAY use **any applicable** error code when it detects an error condition; a generic error code (such as PROTOCOL_VIOLATION or INTERNAL_ERROR) **can always be used in place of** specific error codes." §11.1, 4485: "an endpoint MAY discard an invalid Initial packet. Discarding an Initial packet is permitted **even where this specification otherwise mandates a connection error**." | coverage rows → "choosing it belongs to the detecting component" | Nobody implements either: every wave-1 component enumerates exact codes and, in the Initial case, no `.drop` alternative. These are the two globally-widening MAYs of the whole document and they are in WP6's range; deferring them without an owner guarantees false mismatches from the differential harness. | Give them an explicit owner and mechanism (e.g. a `Core` wrapper `widenErrors : Outcome → List Outcome`, or a documented harness-side rule that any error code is accepted where the model expects one). |
| T-5 | MEDIUM | §10.2.1, 3963–3997 describes what a closing endpoint keeps and sends; **no sentence forbids other frames** | `Termination.MaySend` (Send.lean l.55) | In `.closing`, `MaySend` is false for every frame but CONNECTION_CLOSE and PADDING. Coalescing e.g. an ACK with the closing packet is not forbidden by the text; `MaySend` must never be stricter than the text. | Make `MaySend` in `.closing` `True` (or CONNECTION_CLOSE/PADDING/ACK) and keep the real rule in `closingPacketOk` ("must *contain* a CONNECTION_CLOSE"), which is where it belongs. |
| T-6 | MEDIUM | §10.2, 3949: "**Servers that retain an open socket for accepting new connections** SHOULD NOT end the closing or draining states early." | `Recommended.serverDoesNotEndEarly` (Send.lean l.176) | The qualifier is dropped: the predicate says *every* server must have `mayEndEarly = false`, while the doc comment quotes the sentence in full. Advice-only, so no behavioural effect, but it states something the text does not. | Add the condition as a parameter (`retainsOpenSocket : Bool`). |
| T-7 | MEDIUM | §10.2.3, 4056: "After the handshake is confirmed …, an endpoint MUST send any CONNECTION_CLOSE frames in a 1-RTT packet." | `maySendCloseIn` (Send.lean l.121); `Phase.active (confirmed : Bool)`, `State.toClosing` (Basic.lean l.54, 207) | `confirmed` is only carried in `Phase.active c`; `toClosing` replaces the phase, so by the time a CONNECTION_CLOSE is actually sent the bit is gone. The rule therefore **cannot** be expressed as `Component.MaySendPacket : State → OutPacket → Prop` — which is exactly the fold-in the lead plans. NOTES says "WP12 must supply it", but WP12 would have to reconstruct state WP6 discarded. | Move `confirmed` out of `Phase` into a top-level `State` field so it survives `toClosing`. |
| T-8 | LOW | see list | doc comments + coverage table | A cluster of wrong citations in §10.2/§10.3/§11/§19.19: `State.toClosing` "line 3931" (text **3912**); `State.toDraining` "line 3933" (text **3913**); `Step.localErrorActive` + coverage "line 3913" for *"Violations of the protocol lead to an immediate close"* (text **3925**); `Event.appClose`/`Step.appCloseActive` "line 3921" (text **3932**); `MaySend` doc "line 3961" (text **3963**); "line 4023" for the draining MUST NOT (text **4024**); "line 4447" (text **4446**); "line 4038" (text **4039**); `Event.statelessReset` "line 4322" vs `Step.statelessReset` "4323" vs `State.onStatelessReset` "4324" for one sentence (text **4323–4325**); "§19.19, line 8186" (text **8187–8188**); "§10.3, line 4206" (text **4205**); "§10.1, line 3833" (text **3834**). | Re-derive line numbers. |
| T-9 | LOW | §10.3.3, 4405: "Reducing the size of a Stateless Reset below 41 bytes **means that** the packet could reveal to an observer that it is a Stateless Reset" | `recommendedStatelessResetSize` second clause (Send.lean l.190) | Turns an observation into a recommendation (`43 < t → 41 ≤ r`) that the text does not state. | Drop the clause or mark it as inferred. |
| T-10 | LOW | §10.1, 3837: "By announcing a max_idle_timeout, an endpoint commits to initiating an immediate close … if it abandons the connection prior to the effective value." | coverage table | Absent from the table. | Add a row. |
| T-11 | LOW | §10.2.2, 4037: "MAY send a single packet containing a CONNECTION_CLOSE frame **before entering** the draining state" | `Step.recvCloseActiveReply` (Basic.lean l.359) | The effect is emitted by a step whose *resulting* state is `draining`, where `MaySend = False`. WP12 must check the frame against the pre-state, which nothing records. | Note it in the fold-in; or keep the phase at `.closing` for that one step. |
| T-12 | LOW | — | Termination package | No `init` function (every other package has one, so `Inv`'s non-vacuity has to be argued from `s0` in the examples). Coverage row names `Recommended.serverWithOpenSocketDoesNotEndEarly`; the field is `serverDoesNotEndEarly`. | — |

### Probes

```lean
-- P6.1 (T-2) the idle timeout is an exact-instant obligation
example : s0.effectiveIdle 5000000 = 15000000 := by decide
example : component.accepts s0 (.tick 15000000 5000000) (.ok s0 []) = false := by decide
example : component.outcomes s0 (.tick 15000000 5000000)
    = [.ok { s0 with phase := .closed } [.discardState]] := by decide

-- P6.3 (T-1) no way to express an endpoint that maintains anti-loop state
example : maySendStatelessReset 30 40 = false := by decide   -- 40 < 3*30, so §10.3 l.4215 allows it
example : maySendStatelessReset 30 30 = false := by decide

-- P6.4 (T-5) closing rejects every frame the text does not forbid
example : component.maySend sClosing (.ack 3 0 0 #[] none) = false := by decide
example : component.maySend sClosing .handshakeDone         = false := by decide
example : component.maySend sClosing .ping                  = false := by decide

-- P6.5 (T-11) the farewell close is emitted into a state that forbids sending
private def sDrained : State := (component.step s0 (.recvClose 2000 400 (.application 7))).next s0
example : sDrained.phase = .draining := by decide
example : component.maySend sDrained (.connectionClose 0 (some 0) ByteArray.empty) = false := by decide
example : component.accepts s0 (.recvClose 2000 400 (.application 7))
    (.ok sDrained [.sendFarewellClose]) = true := by decide
```

### Free-standing send-side functions (for the fold-in)

| function | signature | fold-in note |
|---|---|---|
| `closingPacketOk` (+ `maySend_of_closingPacketOk`) | `List Frame → Bool` | → `MaySendPacket`, only needs `OutPacket.frames`. Cleanest fold-in in the batch. |
| `maySendCloseIn` | `Bool → PacketType → Frame → Bool` | → `MaySendPacket` **only after T-7** (the `Bool` is handshake-confirmed, which the state loses on closing). |
| `appCloseAllowedIn` | `PacketType → Bool` | helper for the above. |
| `convertCloseForHandshake` | `Frame → Frame` | a transformation, not a predicate; keep free. |
| `maySendStatelessReset` (+ `statelessReset_needs_large_trigger`) | `Nat → Nat → Bool` (triggerSize, resetSize) | datagram-level, but needs the **triggering** packet's size, which `Spec.OutDatagram` does not carry. Also see T-1. |
| `Recommended` | `State → Role → Time → Nat → Prop` | advice; see T-6. |
| `recommendedFarewellReason` / `recommendedStatelessResetSize` | `CloseReason` / `Nat → Nat → Prop` | advice; see T-9. |
| `isConnectionClose` / `isPadding` | `Frame → Bool` | helpers. |
| `applicationErrorCode` / `minStatelessResetSize` / `closePeriod` | `Nat` / `Nat` / `Nat → Nat` | constants. |

### Checked and found correct (WP6)

- Idle timeout arithmetic: `negotiatedIdle` (min of two, sole non-zero, 0 = disabled), `effectiveIdle = max(negotiated, 3·PTO)` with 0 staying 0; probe P6.2 checks the 0/0, 0/7 and 7/0 cases and a tick at t = 999 999 999 with the timeout disabled.
- Restart rules: on receive (also clearing `ackElicitingSinceRecv`), and on the **first** ack-eliciting packet since the last receive only (`ackEliciting_restarts_first` / `_only_first`).
- Phase machine: `active → closing → draining → closed`, `phase_forward`, `confirmed_mono`, `drain_from_closing_keeps_deadline` (§10.2.2 l.4046), `statelessReset_drains_silently`, `onStatelessReset_phase_ne_active`.
- `draining_emits_no_packet` is genuinely stronger than `MaySend = False` and is correct; `close_period_reaches_closed(_phase)`, `idle_timeout_closes`, `idle_timeout_silent` all say what their doc comments claim and are non-vacuous.
- The three alternatives for a packet received while closing (respond / stay silent under the l.3969 SHOULD / move to draining on a CONNECTION_CLOSE) are exactly right, and `.sendStatelessReset` is correctly **not** among them (§11 l.4441). A local error while closing correctly changes nothing (§10.2.3 l.4116).
- Error → CONNECTION_CLOSE mapping: `CloseReason.transport err frameType` ↔ 0x1c, `.application code` ↔ 0x1d (§11.1 l.4451), frame type 0 for "unknown" (§19.19 l.8158); `maySendCloseIn` correctly requires 1-RTT once confirmed and restricts 0x1d to 0-RTT/1-RTT (§19.19 l.8187); `convertCloseForHandshake` implements §10.2.3 l.4084/4095 (type, APPLICATION_ERROR, empty reason).
- `maySend_of_phase_eq` / `maySend_stable` give exactly the retransmission-idempotence property the BRIEF asks for (§11.1 l.4457).
- `Inv` (`active ⇒ closedWith = none`) is weak enough that realistic initial states satisfy it.

---

## WP7 — `QuicModel/Spec/VersionNegotiation.lean`, `QuicModel/Spec/DatagramSize.lean`

### Findings

| id | sev | text (§, line, quote) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| DS-1 | HIGH | §14, 5697: "the endpoint **MAY however discard** such datagrams." (also §5.2, 1878 and §11.1, 4485 for Initial packets) | `DatagramSize.Step.datagramOk`, `Step.initialOk`, `outcomes` (l.89–94, 131–136) | **No received datagram has a `.drop` outcome in any state.** An endpoint that discards an undersized datagram — explicitly permitted — is rejected, as is a client or a server discarding an Initial it is allowed to discard. | Add `.drop` (after `.ok s [.deliver]`) to both `recvDatagram` and the `initialOk` branch. |
| VN-1 | HIGH | §6.2, 2098: "A client that supports only this version of QUIC **MUST abandon** the current connection attempt if it receives a Version Negotiation packet, **with the following two exceptions**" (l.2100 and l.2103). The connection-ID echo check is stated **only** in §6.2.1 "Version Negotiation Between Draft Versions" (l.2113: *"[[RFC editor: please remove this section before publication.]]"*). | `Client.Step.vnCidMismatch` (l.540), `Client.Step.vnAbandon` (l.546) | The CID check is made a precondition of the §6.2 abandon path, adding a **third** exception that §6.2 does not have. A conforming RFC 9000 client that abandons on a VN packet whose CIDs do not match is rejected, and the MUST of l.2098 is silently dropped in that case. | Require the CID match only for `vnRetry` (the §6.2.1 path); leave `vnAbandon` unconditional, and keep `.drop` as an additional outcome on a CID mismatch. |
| DS-2 | MEDIUM | §14.2, 5762: "An endpoint MAY terminate the connection **if an alternative path cannot be found**." (§8.2.4, 3263 adds "only possible if the network path exists but does not support the required MTU") | `Step.pathLostTerminate` (l.127) | `.error .noViablePath` is offered on **every** `.pathBelowMinimum`, with no notion of an alternative path. The two packages take opposite readings of the same MAY: `PathValidation` NOTES 6 deliberately excludes NO_VIABLE_PATH "because admitting it … is looser than the text"; `DatagramSize` admits it. | Pick one reading. If kept, gate on a `noAlternativePath : Bool` field or event argument. |
| DS-3 | MEDIUM | §14, §14.1, §14.2, §14.4 | `DatagramSize.OutDatagram` (l.228) | A **local structure that shadows `Spec.OutDatagram`** with an incompatible field set. `carriesInitial`/`initialAckEliciting`/`carriesConnectionClose` are derivable from `Spec.OutDatagram.packets`, but `isProbe` and `ackEliciting` are not. Folding into `Component.MaySendDatagram : State → Spec.OutDatagram → Prop` needs a `Core` change. | Add `isProbe`/`ackEliciting` to `Spec.OutDatagram` (or `Spec.OutPacket`) and derive the rest. |
| VN-2 | MEDIUM | §5.2.2, 1946: "Servers MUST drop incoming packets under all other circumstances." | coverage row → `Server.eventOfDatagram = none` + `Step.recvVersionNegotiation` | `eventOfDatagram = none` only covers *unparseable* datagrams; the `supported` branch always delivers. The MUST is really WP12's, but nothing is handed over. | Re-word the row as `out of scope: WP12 Endpoint` and say what predicate WP12 needs. |
| VN-3 | LOW | §5.2.1, 1898 | `Client.Event.recvOther (version : Nat)` (l.475) | No "no version field" case, unlike `Server.Event.datagram`'s `Option Nat`; a short-header 1-RTT packet has to be fed in as `version = s.chosen` or the model drops it. | Make it `Option Nat` for symmetry. |
| VN-4 | LOW | §6.2.1, 2134: "the client then selects an **acceptable** protocol version from the list" | `Client.usableVersions` (l.504) | Filters out reserved versions and version 0 — a narrowing of a MAY that the text does not make. NOTES flags it; harmless. | — |
| VN-5 | LOW | §17.2.1, 6227 and 6235 | NOTES ("line 6228"), `Vn` doc ("line 6237") | Off by one and two. Everything else spot-checked in WP7 is exact (see below). | — |
| DS-4 | LOW | §14.2, 5749: "In the absence of these mechanisms, QUIC endpoints SHOULD NOT send datagrams larger than the smallest allowed maximum datagram size." | coverage row (5746) → `RecommendedDatagram` first clause | The first clause is `isProbe = false → size ≤ maxDatagramSize`, which is l.5753's rule, not l.5749's (that one is about `smallestMaxDatagramSize` when no PMTUD is running). | Add a clause or mark 5749 as not encoded. |

### Probes

```lean
-- P7.1 (DS-1) no `.drop` for any received datagram
example : component.outcomes srv (.recvDatagram 20) = [.ok srv [.deliver]] := by decide
example : component.accepts  srv (.recvDatagram 20) .drop = false := by decide
example : component.accepts  cli (.recvInitial 200)  .drop = false := by decide
example : component.accepts  srv (.recvInitial 1200) .drop = false := by decide

-- P7.3 (DS-2) NO_VIABLE_PATH accepted unconditionally
example : component.accepts cli .pathBelowMinimum (.error .noViablePath) = true := by decide

-- P7.5 (VN-1) a conforming §6.2 abandon on a CID mismatch is rejected
example : Client.component.outcomes cli
    (.recvVersionNegotiation ⟨#[7,7]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d]) = [.drop] := by decide
example : Client.component.accepts cli
    (.recvVersionNegotiation ⟨#[7,7]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d])
    (.ok cli.afterVn [.abandon]) = false := by decide
```

### Free-standing send-side functions (for the fold-in)

| function | signature | fold-in note |
|---|---|---|
| `DatagramSize.MaySendDatagram` / `maySendDatagram` / `_iff` | `State → DatagramSize.OutDatagram → Prop` / `→ Bool` | → `MaySendDatagram` once `Spec.OutDatagram` carries the probe/ack-eliciting bits (DS-3). |
| `DatagramSize.RecommendedDatagram` | `State → DatagramSize.OutDatagram → Prop` | advice (§14.2 SHOULDs + `max_udp_payload_size`); keep out of `MaySendDatagram` — the NOTES justification is correct, §18.2 l.6957–6970 has no MUST. |
| `VersionNeg.Server.MaySendVn` / `maySendVn` / `_iff` | `State → Event → Vn → Prop` / `→ Bool` | **Indexed by the triggering event**, and `Vn` is not an `OutPacket` (a VN packet carries no frames). `MaySendPacket : State → OutPacket → Prop` cannot express "only in response to *this* datagram". Needs either a `Vn` case in `OutPacket` plus the trigger in the state, or to stay free. |
| `VersionNeg.Server.eventOfDatagram` | `State → ByteArray → Option Event` | parser glue over `Quic.versionCid`; keep free. |
| `VersionNeg.Client.MayStartNewAttempt` | `State → ByteArray → Prop` | §6.2.1 l.2136; a condition on *starting a new component instance*, not on a packet. |
| `VersionNeg.isReservedVersion` / `versionNegotiationVersion` / `Client.usableVersions` | `Nat → Bool` / `Nat` / `List Nat → List Nat` | constants/helpers. |
| `DatagramSize.smallestMaxDatagramSize` / `defaultMaxUdpPayloadSize` | `Nat` | 1200 / 65527; both correct. |

### Checked and found correct (WP7)

- **1200-byte boundaries everywhere**: `recvInitial` 1199 ⇒ drop-or-PROTOCOL_VIOLATION, 1200 ⇒ deliver; client Initial expansion 1199 ⇒ false, 1200 ⇒ true; VN reply threshold 1199 ⇒ drop only, 1200 ⇒ VN-or-silence.
- `MaySendDatagram`'s first clause parses as intended in Lean (`carriesInitial → (client ∨ initialAckEliciting) → 1200 ≤ size`, since `∨` binds tighter than `→`), and `client_initial_expanded` / `server_ackEliciting_initial_expanded` use it consistently; the server's non-ack-eliciting-Initial exemption (§14.1 l.5706) is right.
- ICMP (§14.2.1): ignore below 1200 (boundary 1199/1200 checked), never increase, reduce-or-defer as two outcomes. `icmp_never_increases`, `icmp_below_minimum_ignored`, and `Inv` (`1200 ≤ maxDatagramSize`, satisfied by a realistic initial state) are all correct and non-vacuous.
- §14.2 l.5758: `pathUsable = false ⇒ probe ∨ CONNECTION_CLOSE`, and `no_initial_on_dead_path`.
- `isReservedVersion` implements "any version number where the low four bits of all bytes is 1010" exactly (`0x0a0a0a0a`, `0x1a2a3a4a`, `0xfafafafa` true; `0x1a2a3a4b`, v1, 0 false).
- Server: never a VN in reply to a VN (`no_vn_in_response_to_vn`); `small_unsupported_drop`; the "MAY limit" silent alternative; SCID→DCID / DCID→SCID echo proved against the real parser (`vn_echoes_versionCid` over `Quic.versionCid`); `Inv` + `sendVn_maySendVn` + `vn_lists_supported`; a supported version delivered regardless of size (l.1916 correctly applies only to *unsupported* versions); `at_most_one_vn`.
- Client: `vnAfterOther` (l.2100), `vnListsChosen` (l.2103) + `never_acts_on_own_version`, `wrongVersion` (l.1898), `notProcessed` (l.1893). `acts_on_vn_once` genuinely holds across arbitrary intervening steps (via `flags_mono` / `processedAny_reachable`), and `acting_abandons` / `attempted_version_listed` say what they claim.
- **Citation accuracy in WP7 is the best of the three packages.** Spot-checked and exact: 1889, 1893, 1898, 1911, 1914, 1916, 1926, 2051, 2065, 2066, 2083, 2098, 2100, 2103, 2115, 2120, 2136, 2150, 5649, 5695, 5701, 5706, 5727, 5729, 5753, 5758, 5762, 5793, 5813, 5814, 5873, 5924, 5947, 5953, 6260, 6283, 6295, 6963, 6966. Only VN-5's two are off.

---

## Cross-cutting notes for the lead

1. **None of the six packages sets `Component.MaySendPacket` / `MaySendDatagram`.** All five components (`AddressValidation`, `PathValidation`, `Termination`, `VersionNeg.Server`, `VersionNeg.Client`, `DatagramSize`) use the defaults, so `component.maySendPacket _ _ = true` and `component.maySendDatagram _ _ = true` **everywhere**. A WP12 that conjoins those fields will silently enforce nothing. The free functions above are where the real rules live.
2. **`Spec.OutDatagram` is missing three things** the wave-1 rules need: a peer address (AV-1/anti-amplification), probe/ack-eliciting flags (DS-3), and the size of the *triggering* packet (T-1 stateless reset).
3. **Cross-component state.** `PathValidation.MaySendDatagram` already takes `AddressValidation.State` as an argument. `Termination.maySendCloseIn` needs handshake confirmation that `Termination.State` discards (T-7). Both are Core-shape problems, not spec-fidelity problems.
4. **Orphaned rules between packages**: §10.2.1 l.3993 and l.4008 (WP6 → WP5, WP5 does not have them); §11 l.4434 and §11.1 l.4485 (WP6 → "the detecting component", no component implements them); §5.2.2 l.1936 CONNECTION_REFUSED (WP7 → WP6, WP6 → nobody; and WP5 actively forbids it, AV-4). §8.2.4 l.3263 NO_VIABLE_PATH is claimed by DatagramSize and disclaimed by PathValidation with contradictory justifications (DS-2).
5. **Two packages disagree about what `.drop` means for a rule the other owns.** `PathValidation` proves `.drop ∉ outcomes` for received PATH_CHALLENGE/PATH_RESPONSE in *every* state (PV-4), while `Termination` requires that a draining/closed endpoint process nothing; composing them needs a decision.
