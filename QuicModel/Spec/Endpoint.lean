import QuicModel.Spec.Endpoint.Examples

/-!
# WP12 — the composed endpoint

`QuicModel/Spec/Endpoint/*`, in dependency order:

```
Lemmas → Basic → Merge → Dispatch → Pipeline → Events → Send → Component →
Obligations → Theorems → Exports → Examples
```

`Endpoint.component prot` is a `Component` whose `Step` is, by definition,
membership in `outcomes`.  That is deliberate and is the one place in the
project where it is done (`Endpoint/Component.lean` says why): this package owns
no normative sentence.  The receive pipeline is a *composition rule*; an
independent inductive presentation of it would restate the composition in a
second syntax and the proof would compare the pipeline with itself.  What is
proved instead is that `Inv` is preserved by applying each component's own
`step_inv` to its projection (`rawOutcomes_inv`), that every component's `Step`
is reachable through the endpoint's (`Endpoint/Theorems.lean` §(b)), and that
the endpoint never permits an outcome no component produced except where the
text gives the *endpoint* the right.

---

## 1. The merge rule, as implemented

Five combinators in `Endpoint/Merge.lean` and two in `Endpoint/Pipeline.lean`.

* **Lifting.**  `liftList put tag l` tags one component's effects and writes its
  state back.  The write always goes through `syncConfirmed`, which re-imposes
  WP11's `Handshake.State.confirmed` on WP6's and WP10's copies of it.
  `Endpoint/Dispatch.lean`'s thirteen `stepX` wrappers are the **only** writers
  of any component's state; that is what makes `step_inv` a proof rather than a
  re-derivation.

* **Sequencing is the product of the alternative lists.**
  `bindAll l f = l.flatMap (bindOut · f)`, and `bindOut (.ok s fx) f` continues
  from `s` for *every* outcome `f s` permits.  Nothing a component permits is
  dropped by composition, so the endpoint is never stricter than the components
  it merges — which is the property the differential run needs (PLAN §1, "the
  differential run fails if `Step` is too strict").

* **`.error` and `.drop` are terminal** for the rest of the sequence they occur
  in (`bindOut` returns `[.error c]` / `[.drop]`).

* **Effects before an error are dropped from the error outcome.**  `withFx fx`
  prepends `fx` to an `.ok`, and returns an `.error c` or a `.drop` *unchanged*,
  carrying no effects at all.  This is PLAN §4a's finding made into a rule:
  ngtcp2 fires `stream_open` and then fails the same STREAM frame with
  FLOW_CONTROL_ERROR, and only the error code is comparable.
  `Examples` §4 is the worked case (`outcomeCbsC` of the failing packet is `[]`).

* **A component's `.drop` discards *this packet*, not the datagram.**  `gate s l
  k` reads `.drop` as `[.ok s []]` and carries on with the state the gate
  started from, so the packets coalesced after it are still processed (§12.2,
  line 4619).  Because the continuation resumes from the *unchanged* state,
  `gate` is not a weakening of any component: `.drop` means "nothing changed",
  and that is exactly what it does.

* **Connection-level refusals are a union, never a subtraction.**  No
  component's `accepts = false` vetoes anything: every component is *sequenced*
  with `bindAll`/`gate`, never used as a filter, which is what
  `AddressValidation` NOTES 5 demands ("WP12 must not read
  `AddressValidation.accepts = false` as a veto").  Where the endpoint has a
  right of its own, the alternative is *added*: `packetErrOutcomes` appends
  §11.1 line 4485's `.drop` to the mandated error for an Initial packet, and
  `vnServerGate` / `vnPacket` return `[.drop]` for §5.2.2 line 1946.

* **`withPending` is the last pass.**  `Effect.sendPending f` markers (the
  frames a rule says are now *owed*) are appended to an `.ok`'s effect list;
  errors and drops carry none.  A `sendPending` is not a packet going out —
  §13.2 and §13.3 decide when a frame travels and both are out of scope.

* **Coalescing.**  `recvPackets` walks the packets of one datagram on a fuel
  loop.  §12.2, line 4619 ("the receiver MAY either discard or buffer the packet
  for later processing and MUST attempt to process the remaining packets") means
  a packet whose protection cannot be removed — the AEAD open failed, or the
  packet is too short to yield a header-protection sample (audit 2026-09-18,
  D34-4) — leaves `Effect.skippedRest` behind and the loop *continues*, at the offset `packetEndOf` computes from the long
  header's Length field (or the end of the datagram for a short header, §12.2
  line 4606).  It stops only where the text's "attempt" is impossible.  This was
  wrong until the examples layer: the loop used to end there, justified by a
  sentence that is not in draft-34.  `TRIAGE.md` `WP13-5` has the whole story,
  including that ngtcp2 stops too.

**One correction to the earlier text.**  `Endpoint/Component.lean`'s doc said
`addAlt` is "used only for §5.2.2 line 1936, §5.2.2 line 1946 and §11.1
line 4485".  `addAlt` and `addAlts` have **no call sites**: the last two
sentences are realised directly (as `[.drop]` in `vnServerGate`/`vnPacket`, and
as `if isInitial then [.error …, .drop]` in `packetErrOutcomes`), and the first
is not realised at all.  See §3 below.

---

## 2. Where the components' `.drop` / `ok []` readings conflicted

| Components | The conflict | How the pipeline resolves it |
|---|---|---|
| `Migration` vs all | §9 line 3325 and §9.3.2 line 3460 are MUST-discards that must beat any other component's `.ok` for the same packet (`reviews/wave2.md`, composition note 4) | `Migration` is the **first** gate of `processPayload`; its `.drop` short-circuits, so no frame is dispatched and `Handshake`'s §7.2 rules do not run. Proved: `migration_discard_wins` |
| `Termination` vs `PathValidation` | `recvChallenge` / `recvResponse` have no `.drop` in any state, which §10.2.1 line 3984 ("an endpoint that is closing is not required to process any received frame") contradicts (`PathValidation` NOTES 12) | `phaseGate` runs before anything is parsed: only `Phase.active` reaches `routeDatagram`. Proved: `no_dispatch_unless_active`, `closedPhase_is_term_only` |
| `DatagramSize` vs every error-producing component | §14 line 5697 permits discarding a datagram *that fails a size constraint*, §11.1 line 4485 an invalid Initial, *even where an error is mandated* | `dszGate` is sequenced with `bindAll`, so `DatagramSize`'s `.drop` — offered only under `DatagramSize.FailsSizeConstraint`, with `Pipeline.requiredSize` reading the constraint off the frames (audit 2026-09-19, B3) — is a top-level alternative beside every error the rest of the pipeline can raise. A datagram that meets its constraints has no such alternative (`Examples` B3). §11.1's Initial-only widening is `packetErrOutcomes` |
| `VersionNeg.Server` vs the rest | line 1946's blanket drop, and the fact that answering with a VN packet must *not* be followed by processing the datagram | `vnServerGate`: `eventOfDatagram = none → [.drop]`; an outcome whose effects contain `isSendVn` stops there; otherwise the continuation runs |
| `VersionNeg.Client` vs the rest | lines 1889 and 1898 must fire *before* the packet is processed, line 2100's `processedAny` *after* | `vnClientGate` is a pre-gate for the first two; `vnAfterPacket` fires `recvOther ver true` after the frames |
| `AddressValidation` on `newToken` / `serverInitialProcessed` | its `.drop` must not veto the packet (AV NOTES 5) | `gate s (stepAv …) keep` — the bookkeeping did not happen, the packet continues |
| `Ack` §12.3 duplicate suppression | a duplicate is a drop of the whole packet, not of one frame | `gate s2 (stepAck s2 sp (.recvPacket …))` wraps `processFrames` |
| `Ack` §12.3 (4717) minimum packet number | *when* an endpoint raises its minimum leaves no trace, and no endpoint event fired `Ack.Event.raiseMinimum` — the blanket datagram discard was standing in for it | `Pipeline.minimumRaised`: a non-duplicate packet older than the largest processed in its space has the alternative "the minimum moved past it" (`raiseMinimum (pn + 1)`, nothing processed). The newest packet never has it |
| `Handshake` NOTE 10 / review K-2 | `recvHeader` may be fired **only** after protection was successfully removed | `processPayload` runs it after `parseOne` succeeded; every failure path goes to `packetErrOutcomes`, which never touches `Handshake` |
| three copies of "handshake confirmed" | WP11 owns it, WP6 needs it for §10.2.3 line 4056 and WP10 for §9 line 3280 | `syncConfirmed` after every component write; `InvConfirmed`; justified by `handshake_confirmed_mono` |
| `Migration.Path` vs `PathValidation.Path` | `Migration` NOTES 1 leaves the bijection to WP12 | `State.pathIds` / `nextPathId` / `register`, with `InvPaths` (bounded and injective) and `pathOfId` for the reverse lookup in `pvEffects` |

---

## 3. The MUSTs other packages deferred to WP12

Every `WP12` mention under `QuicModel/Spec`, with where it landed.

| Deferred by | Sentence | Disposition |
|---|---|---|
| `DatagramSize` 556, `Termination` 745 | §11.1 (4485) MAY discard an invalid Initial "even where this specification otherwise mandates a connection error" | `Pipeline.packetErrOutcomes`: `if isInitial then [.error …, .drop]`, for `reservedBits`, `emptyPayload` and `frame`. **Partial**, and deliberately: it widens the errors the *decoder* raises. An error raised by a frame's semantics inside an Initial is not widened. Recorded for WP13 |
| `VersionNegotiation` 884 (review AV-4) | §5.2.2 (1936) a server refusing a connection SHOULD send CONNECTION_CLOSE(CONNECTION_REFUSED) | **Not handled — the one real gap.** `TransportError.connectionRefused` occurs nowhere in `Endpoint/*` except the decoder for a *received* CONNECTION_CLOSE. It is not an oversight that can be patched in place: refusal happens at connection *acceptance*, and `Endpoint.State` is an already-established connection (`init` presupposes that the handshake produced the parameters in `Config`). `Endpoint.Event` has no "a connection attempt arrived" constructor, so encoding it would mean inventing an event and a pre-`init` state. What is missing, precisely: an `Event.accept` (or a `Config`-less pre-connection state) plus an `addAlt`-style alternative `.error .connectionRefused` on it |
| `VersionNegotiation` 886 | §5.2.2 (1946) servers MUST drop incoming packets under all other circumstances | The in-connection half is `vnServerGate` / `vnPacket`. The "reaches no connection" half is out of the model by construction: `Endpoint.State` *is* one connection and there is no connection table. Belongs to a dispatcher above `Endpoint` |
| `Termination` 721 | §10.3 (4125) MAY send a stateless reset for a packet it cannot associate with a connection | same no-connection path, above `Endpoint`; `maySendStatelessReset` is exported for when it exists |
| audit 2026-09-18, D34-1 | §10.1 (3841) the idle timer restarts when a packet is "received and processed successfully" | `Effect.packetProcessed` is emitted at the end of a packet no component discarded (`Pipeline.processed`); `idleGate` runs `afterDatagram` only for an outcome that carries it. A datagram whose packets were all discarded leaves `term.idleStart` alone. `Examples` §12b |
| audit 2026-09-18, D34-2 | §17.2.5.2 (6626) discard a Retry whose Retry Integrity Tag cannot be validated | `Protection.retryTagOk` is the abstract check; `Pipeline.retryIntegrityOk` hands its verdict to `AddressValidation.Step.retryBadTag` through `retryPacket`. `Protection.stub` validates sixteen bytes of 0xA5 |
| audit 2026-09-18, D34-3 | §14.1 (5727) a server MUST discard an Initial carried in a datagram under 1200 bytes | per packet, in `Pipeline.recvOne`: `DatagramSize`'s `.recvInitial buf.size` is asked for *every* Initial of the datagram, before it is unprotected; its `.drop` skips that packet only (`gateElse` / `afterSkipped`), its PROTOCOL_VIOLATION (line 5729) is terminal. `dszGate` is now only the datagram-level `.recvDatagram`, whose `.drop` needs a failed size constraint (audit 2026-09-19, B3) |
| `Termination` 727 | §10.3 (4220) MUST discard packets too small to be a valid QUIC packet | receive half: the decoder's `.header` error → `[.ok s [.skippedRest]]`; send half: `Send.maySendStatelessReset` |
| `Termination` 718 | §10.2.3 (4099) CONNECTION_CLOSE in several packet types may be coalesced | `MaySendDatagram` quantifies `MaySendPacket` over `d.packets`, and `Termination.MaySendPacket` is per packet type, so each coalesced packet is checked on its own |
| `Termination` 719 | §10.2.3 (4111) MAY discard rather than close on errors in unauthenticated packets | `packetErrOutcomes`'s Initial `.drop`, as above |
| `Termination` 830 | the endpoint that emits a farewell close ends in `draining`, where nothing may be sent | `maySend_false_of_draining_or_closed`; `MaySendPacket` is `False` there |
| `Migration` 110 | the `Migration.Path ↔ PathValidation.Path` bijection | `State.pathIds`, `register`, `InvPaths` |
| `Migration/Send` 106 (NOTES 16) | §9.3.1 (3431) the limit on the path a datagram leaves on needs `AddressValidation`'s state | `MaySendDatagram`'s `Migration.MaySendDatagramOn s.av s.mig d` conjunct |
| `Migration/Send` 99 (`dcidSeqOf`), third audit D34-6/D34-7 | §9.5 (3603, 3608) and §5.1.2 (1811) are about the sequence number of the connection ID a datagram carries; `Migration.State.peerCids` is filled by no endpoint event | `Send.DcidOk`: `dcidSeq?` resolves `OutDatagram.dcid` through `ConnIds.Remote` (sequence 0 for the handshake's own DCID), refuses a retired or never-issued connection ID, and applies `Migration.MaySendCidOn`. `Examples` D34-6, D34-7 |
| `StreamTable/Send` 6b, third audit D34-5 | §4.1 (1330) connection credit is spent by all the frames of a packet or datagram together | `StreamTable.MaySendAll` in `MaySendPacket` (over `p.frames`) and `MaySendDatagram` (over `datagramFrames d`); `sendCredit_of_maySendAll` shows it subsumes the per-frame rule. `Examples` D34-5 |
| `PathValidation` 390, 934 (NOTES 11) | §8.2.2 (3183) a PATH_RESPONSE MUST be sent on the path the PATH_CHALLENGE arrived on | `Send.PathResponsesOnPath` / `frameResponseOk`, called with `s.pathOf (datagramPath d)`. PLAN §4c left WP12 to choose between adding a local address to `OutDatagram` and conjoining by hand: `OutDatagram.src` already existed by then, so the rule is a field rule after all |
| `PathValidation` 949 (NOTES 12) | `Termination`'s phase must gate challenge and response handling | `phaseGate` |
| `FrameRules` 850 | the frame-by-frame walk of a payload | `processFrames` fires `.recvFrame pt f` per frame, and `.recvPacketFrames pt []` for an empty payload |
| `Handshake` 889 | §7.1 (2264) coalescing | `recvPackets`, a fuel loop over `parseOne`; §12.2 line 4619's "MUST attempt to process the remaining packets" makes an undecryptable packet leave `Effect.skippedRest` and the loop go on (`packetEndOf`) |
| `Handshake` 914 | §7.5 (2703) buffer at least 4096 bytes of out-of-order CRYPTO | `ConfigOk.bufLimit` and `ConfigOk.bufSpan` (the two accountings of `Handshake.BufferPolicy`) — a side condition on the `Config`s WP12 may build, preserved by `step_inv` |
| `Handshake` 924 | §17.2.2 (6364) "A server sends its first Initial packet in response to a client Initial" | **Not encoded**, and reasoned: a liveness MUST with no deadline. `Obligations.lean` states only the obligations that have one (§13.2.1) or that can be checked at the end of a run (§3.5, §13.3, §13.4.1); a deadline-less "something must eventually happen" cannot be checked from a finite trace without inventing a bound |
| `Handshake` 927 | §17.2.2 (6376) first sentence: a client's first packet always includes a CRYPTO frame | **Not encoded**, and reasoned: `Endpoint` fires `sentPacket` but carries no "have we sent anything at all" flag, and requiring a CRYPTO frame in *every* first-flight Initial would wrongly reject the second packet of a ClientHello that spans packets. The second sentence (offset 0) *is* encoded, in `Handshake.MaySendPacket`; `Examples` §11 asserts both directions |
| `Handshake` 1060 (NOTE 10), review K-2 | `recvHeader` only after successful unprotection | honoured; see §2 |
| `Handshake` 1142 | a `MaySend`-style transport-parameter rule | **Not done.** WP1's `TransportParams` is theorem-only and not reachable through the harness (PLAN §4a), so there is nothing for WP13 to check it against |
| `Ack` 1155, 1582 | §13.2.1 (5075) acknowledge within `max_ack_delay`, as a run property | `Obligations.ackOverdue` / `Obligations` / `ObligationsMet`, exported as `quic_endpoint_obligations`. `Examples` §3 is the worked case |
| `Ack` 1554 | three instances, one per packet number space | `State.ack` / `setAck`, `InvSpaces`, `Inv.spaceOf` |
| `Ecn` 50, 83 | per-path and per-space composition; a datagram may be ECN-marked only if every instance allows it | `State.ecn` / `setEcn`, `Send.EcnMarkOk`, `Send.EcnPacketOk`, `maySendDatagram_ecn` |
| `Ecn` 71, 147 | §13.2.1 (5112) a CE-marked packet SHOULD be acknowledged immediately | **Not done**, and reasoned: `LocalAction.ecnEvent` and the ACK dispatch are separate events, so the endpoint never raises `Ack.State.ackImmediately` from an IP codepoint. It is a SHOULD that `Ack` records as advice, and the harness carries no IP header, so nothing is lost differentially. Recorded for a later run |
| `Retransmission` 122, 201 | §13.3 (5445) the repair obligation over a run | `Obligations.repairOwed`, `RepairSettled`, `RepairObligationMet`; exported as `quic_endpoint_repair_owed` |
| `ConnIds/Remote` 570 | §5.1.1 (1749) SHOULD supply a new connection ID when the peer retires one | trace-level advice; the moment is marked by `Effect.cidLocal (.cidRetiredByPeer _)` (the `remove_connection_id` callback) and left unchecked, as `ConnIds` asked |
| `ConnIds/Remote` 588 | §19.16 (8050) MUST NOT retire the connection ID of the packet that carries the frame — *send* side | Receive side: `dispatchFrame` passes `dcidSeqOf s dcid` into `ConnIds.Local.recvRetireCid`. Send side: `Send.RetireNotSelf`, a conjunct of `MaySendDatagram` (`Spec.OutPacket` has no `dcid`, `Spec.OutDatagram` does), with the sequence number from `Send.dcidSeq?` over `ConnIds.Remote`; `retire_ne_dcid_of_maySendDatagram`. `Examples` WP13-4; `TRIAGE.md` `WP13-4` |
| `StreamTable` 312, 343, 361 | `ok []` is indistinguishable from `drop`; grow-only state | `Exports.trackSetC` / `tracePattern`, over `Component.trackSet` |
| `StreamTable` 422 | build the initial state from the negotiated parameters | `Config`, `init`, `ConfigOk`, `init_inv` |
| `AddressValidation` 679, 709, 1184, 1193, 1203 | free-standing send predicates; the Retry/amplification pairing; "not a veto" | `Send.MaySendDatagram`'s first conjunct, `maySendRetryHeader`, `atMostOneRetry`; and `gate`-not-filter |
| `AddressValidation` 1269 | §11 (4434) a generic error code may stand in for a specific one | `Core.Obs.matchesSpec`, used by `trackSetC` and `tracePattern` |
| `Stream` 857 | the two halves conjoin | already inside `StreamTable` |
| `VersionNegotiation` 996, 1001, 1004 | call `maySendVn` with the triggering event; take the *union* with `DatagramSize`'s discard | `Send.maySendVn`; `dszGate` sequenced with `bindAll` |

---

## 4. What WP13 needs to drive the exports

### 4a. Events the harness must synthesise

ngtcp2 reports none of these; `Endpoint` will not invent them, and without them
the send-side predicates reject frames ngtcp2 legitimately wrote.

| Event | From which trace/script line | Why it is needed |
|---|---|---|
| `AppAction.openStream dir` | `open bidi\|uni`, `RET open_bidi_stream=OK id=` | `StreamTable.MaySend` is `false` on a stream that was never created (review S-5). Only *locally* initiated streams need it; peer streams are created implicitly by the receive side |
| `AppAction.write id len`, then `AppAction.fin id` | `write <sid> <n> <fin>` | `Stream.Send.written` is what `MaySend` compares a STREAM frame's end offset against. The script's `fin` flag is a **second** action in the model |
| `AppAction.reset` / `.stopSending` / `.read` / `.extendMaxStreamData` / `.extendMaxData` / `.extendMaxStreams` / `.close` | `shutdown_write`, `shutdown_read`, `extend_stream`, `extend_conn`, `extend_streams` | the application half of §2.4 and §4 |
| `LocalAction.sentFrameIn ptype path frame` | one per frame of every `OUT` record, **before** the packet event | moves `Stream.Send`, `PathValidation.responseSent`, `Ack.sentAck` and `Handshake.sentCrypto`. Without it a RESET_STREAM's Final Size stays 0 and `maySend` rejects the frame ngtcp2 just wrote — `Examples` §9 is that case, worked |
| `LocalAction.sentPacket ptype pn ackEliciting` | one per `OUT` record | §17.2.2.1 key discard, `Ack.sentPacket`, §10.1 idle-timer restart |
| `LocalAction.sentAck sp largest first ranges` | the ACK frame of an `OUT` record | discharges `ackOverdue`. `sentFrameIn` on an `.ack` frame does the same thing, so fire **one of the two**, not both |
| `LocalAction.sentDatagram addr n` | one per datagram written | the anti-amplification budget, which is per datagram, not per packet |
| `LocalAction.sentPacketFrames sp pn fs`, `LocalAction.rtxEvent` | §13.3 bookkeeping | RFC 9002 is out of scope, so the harness decides what "declared lost" means. Firing neither leaves `repairOwed` empty and `RepairSettled` vacuously true |
| `LocalAction.issueCid cid token rpt` | `CB get_new_connection_id2 cidlen= -> cid=` | *when* to issue a connection ID is not a transport MUST, so the model waits to be told |
| `LocalAction.ecnEvent sp e` | the IP header of each received packet, one event per QUIC packet | `Event.datagram` cannot carry an ECN codepoint (§13.4.1, line 5515) |
| `LocalAction.beginSendOn p dcidSeq` | **still exists**; §9.5, line 3600 | must be fired before the first datagram on a new path, or `Migration.MaySendDatagram` rejects it. Unreachable through the eight scripts (no second path) |
| `LocalAction.startPathValidation` / `.pathTimeout` / `.migrate` / `.probe` / `.learnPreferredAddress` / `.statelessReset` / `.pnExhausted` / `.localError` / `.icmpPtb` / `.pathBelowMinimum` / `.retireCid` / `.retirementBacklog` | the rest of §8.2, §9, §10, §12.3, §14.2 | none is reachable through the eight scripts |
| `Event.tls e` with `Handshake.Event.tlsKeys/.tlsSend/.tlsPeerParams/.tlsZeroRtt/.tlsComplete/.tlsAlert` | `CB recv_rx_key level=`, `CB recv_tx_key level=`, `CB handshake_completed` | the harness must fire all four `tlsKeys` and then `tlsComplete` before feeding any 1-RTT packet. `Examples.postHandshake` is the exact sequence `conn_trace.c`'s forced post-handshake state corresponds to |

**Do not fire** `Handshake.Event.recvHeader`, `.recvCrypto`, `.recvHandshakeDone`,
`.sentPacket` or `.sentCrypto` as `Event.tls`: the pipeline fires them itself,
and `recvHeader`'s contract (only after protection was successfully removed)
depends on that.  The one exception is `Endpoint.Examples`, which uses
`.tls (.tlsKeys …)` only.

### 4b. Effect → callback

`Exports.Effect.cbName` is the table and `Exports.observedCbs` applies it;
`Effect.render` is the human-readable form.  `none` means "do not compare".

| Effect | `CB` name |
|---|---|
| `st (.stream _ (.recv (.dataAvailable _)))` | `recv_stream_data` |
| `st (.stream _ (.recv (.allDataReceived _)))` | `stream_close` — **compare loosely**, see `TRIAGE.md` `WP13-1`; preceded by `recv_stream_data` when the step delivers no new bytes of that stream (the zero-length FIN read, `Exports.Effect.cbNames`) |
| `st (.stream _ (.recv (.streamReset _ _)))` | `stream_reset` |
| `st (.stream _ (.send (.creditAvailable _)))` | `extend_max_stream_data` |
| `st (.stream _ (.send (.peerStopSending _)))` | `recv_stop_sending` |
| `st (.stream _ (.send .allDataAcked))` | `acked_stream_data_offset` |
| `st (.streamOpened _)`, `st (.streamFirstUsed _)` | `stream_open` |
| `st (.dataCreditAvailable _)` | `extend_max_data` |
| `st (.streamsAvailable .bidi/.uni _)` | `extend_max_local_streams_bidi` / `_uni` |
| `hs .handshakeComplete` / `.handshakeConfirmed` | `handshake_completed` / `handshake_confirmed` |
| `hs (.deliverCrypto ..)` | `recv_crypto_data` |
| `av (.storeToken _)` / `av (.useToken _)` | `recv_new_token` / `recv_retry` |
| `pv (.pathValidated _)` / `pv (.pathFailed _)` / `ecn _ .ecnValidationFailed` | `path_validation` |
| `cidRemote (.stopUsing ..)` | `dcid_status` |
| `cidLocal (.sendNewCid ..)` / `(.cidRetiredByPeer _)` | `get_new_connection_id` / `remove_connection_id` |
| `vnClient .abandon` / `(.attemptVersion _)` | `recv_version_negotiation` / `version_negotiation` |
| everything else | `none` |

`none` covers `streamsOpenedBelow` (§2.1 line 718's range), `keysDiscarded`, `peerParams`, `cryptoDiscarding`, `dcidChanged`,
`addressValidated`, `handshakeProceeds`, `queueRetire`, `switchPath`,
`fr (.deliver _)`, `sendPending`, `skippedRest`, `packetProcessed`, the
`Ack`/`Termination`/
`DatagramSize`/`Retransmission` effects, and the three `Stream` *request*
effects (`stopSendingRequested`, `resetRequested`, `resetAcked`).  The last
group is not "ngtcp2 does not surface this": ngtcp2 *does* print
`CB stream_stop_sending`, but at the moment the frame is **written**, not when
the application calls `shutdown_stream_read`, and the model has no
effect-producing step at that later moment.  `TRIAGE.md` `WP13-2`.

Three ngtcp2 callbacks have no model effect at all and must be ignored:
`update_key` (RFC 9001 §6, out of scope), `get_new_connection_id2` (see 4a) and
`select_preferred_addr`.

### 4c. The `Obs` pattern to use

```lean
-- per trace record:
ss := quic_endpoint_track_trace ss e isError code cbs
-- a violation is `ss = []`
```

`Exports.tracePattern isError code cbs : Obs Effect → Bool` is the pattern; it
already identifies `ok []` with `drop` (PLAN §4a) and already applies §11
line 4434's generic-error-code allowance, exactly as `Core.Obs.matchesSpec`
does.  Start from the singleton `[Endpoint.init cfg]`, keep the *list* of
candidate states, and never fall back on `quic_endpoint_step`: `step` is only
the **preferred** outcome, and scenario 03 of `Examples` is a case where the
text permits three and ngtcp2 picks one.

Two warnings about what the set can and cannot falsify:

1. "Processed, no callbacks" is still a weak observation — `ok []` and `drop`
   look alike — but since the audit of 2026-09-19 (B3) it *can* empty the
   candidate set: a datagram that meets its size constraints has no `.drop`
   alternative, so an engine that silently ignores a frame whose error is
   mandated is a mismatch.  The discards that remain are the text's own:
   a failed size constraint, an undecryptable or duplicate packet, one below a
   minimum packet number (`Pipeline.minimumRaised`), §9, §5.2.
2. The send side is one-directional: every datagram ngtcp2 writes must satisfy
   `quic_endpoint_may_send_datagram`, but the absence of a datagram proves
   nothing (pacing, congestion window).

`quic_endpoint_obligations s now tolerance` is the only per-state liveness check
the harness can make; `quic_endpoint_resets_owed`, `quic_endpoint_repair_owed`
and `quic_endpoint_ecn_feedback_owed` are end-of-run checks.

---

## 5. Examples

`Endpoint/Examples.lean` replays all eight `harness/scripts/*` scenarios and
§7.1 Figure 5 end to end from `Endpoint.init`.  Its header explains why anything
that reaches `Quic.decodePacket` is checked with `#guard` rather than `decide`
(`Array.all` and `decodeFrames` compile to well-founded recursion, which the
kernel does not unfold, and `native_decide` is barred), and its NOTES list the
places where the model and the recorded traces differ.  `TRIAGE.md` at the
repository root carries them as WP13's first five triage entries; all but one
are about application callbacks, which the text does not govern, and the one
that is not (`WP13-5`, §12.2's coalescing rule) was fixed here.

Assertions about the received bytes use `#guard`, which evaluates the same
`Decidable` instance at build time and fails the build when it is false but is
not a proof; everything else — the send-side predicates, the obligations, the
application and TLS event families — is `decide` or `rfl`.  `#print axioms` on
the headline theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
-/
