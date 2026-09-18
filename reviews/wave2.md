# Wave 2 review — WP9 StreamTable, WP10 Migration, WP11 Handshake

Reviewer: independent (did not write any of the reviewed Lean).
Worktree `quic-lean-wt/review2`, branch `review2`, base `6ddbd91`.
`timeout 900 lake build` → clean, 99 jobs, 0 warnings.

Probe files: `out/probe_wp9.lean`, `out/probe_wp10.lean`, `out/probe_wp11.lean`.
All three were run under `timeout … lake env lean` and **all exit 0**, so every
`example` quoted below is a *true* statement about the model as committed — the
results are from runs, not from reading the code. No file under `QuicModel/`
was modified.

Method: each assigned text range was read and its normative sentences listed
before any Lean was opened (`grep -n 'MUST\|SHOULD\|MAY'` over the range, then
the prose for keyword-less rules); `Step`, `outcomes`, `MaySend*`,
`Recommended`, `Inv` and the theorem statements were then classified sentence by
sentence. Every line number attached to an error-code rule was checked with
`sed -n "<n>p"`, plus a sample of the rest.

---

## WP9 — StreamTable (§2.1 677–732; §4–4.3 1293–1460; §4.6 1527–1576; §19.9/19.11–19.14; the "not yet created" halves of §19.4/5/8/10/13)

Files: `QuicModel/Spec/StreamTable.lean`, `StreamTable/{Defs,Step,Inv,Send,Theorems}.lean`.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| S-1 | **HIGH** | §4.5 L1517–1525: "A receiver SHOULD treat receipt of data at or beyond the final size as a FINAL_SIZE_ERROR error, even after a stream is closed.  **Generating these errors is not mandatory** …"; §4.5 L1495: "The receiver MUST use **the final size** of the stream to account for all bytes sent on the stream in its connection level flow controller." | `StreamTable/Defs.lean` `connRecvViolation`/`recvEnd`; `StreamTable/Step.lean` `Step.existFlowControl`, `streamOutcomes` | Connection credit is charged from the **frame's** end offset, not from what the stream accepted. For a STREAM or RESET_STREAM frame carrying data beyond a known final size the table charges `(offset+len) − highest` again and raises FLOW_CONTROL_ERROR, and the `.ok`/`drop` branch is then **deleted** from `outcomes` (only errors survive the `filter isErr`). So the model rejects the behaviour §4.5 L1522 explicitly permits — ignoring the excess — *and* it reports a connection-level violation where, per §4.5 L1495, the stream consumes only its final size and no limit is exceeded. Probe P9-1. | Charge the connection controller by the *stream's* own movement rather than by the frame: compute the delta from the outcome WP2 chose (`recvHighest st' − recvHighest st`, which `afterStep` already uses), i.e. offer FLOW_CONTROL_ERROR only for outcomes in which the stream actually accepts the bytes, and keep `existDrop`/`existOk` available otherwise. Equivalently: cap `recvEnd` at the known final size when one exists. NOTES ("Connection-level credit is accounted from the frame, not from the stream's reply") records the design but not that it costs a permitted outcome. |
| S-2 | MEDIUM | §19.4 L7431: "An endpoint that receives a RESET_STREAM frame for **a send-only stream** MUST terminate the connection with error STREAM_STATE_ERROR."  §19.13 L7863: the same for STREAM_DATA_BLOCKED. Neither says anything about "a locally-initiated stream that has not yet been created" — only §19.5 L7473, §19.8 L7637 and §19.10 L7734 do. | `StreamTable/Step.lean` `Step.localNotCreated` (doc comment and hypotheses), coverage rows "§19.13 (7863)" and the `§19.4 (7431)` claim | `localNotCreated` fires for **every** peer frame on an uncreated locally-initiated stream and is the **only** outcome. For a locally-initiated *bidirectional* stream that has not been created, a received RESET_STREAM or STREAM_DATA_BLOCKED has no rule in the text at all, so mandating STREAM_STATE_ERROR rejects an implementation that ignores it (a plausible one: such an implementation cannot distinguish "never created" from "created and closed", which §4.5 L1522 says it need not track). The doc comment misquotes L7431 and L7863 as saying the "not yet created" rule. Probe P9-2. | Split the constructor: keep the mandatory STREAM_STATE_ERROR for the three frames the text names (STREAM, STOP_SENDING, MAX_STREAM_DATA), and for RESET_STREAM / STREAM_DATA_BLOCKED on an uncreated locally-initiated *bidi* stream offer both the error and `.ok s []`/`.drop`. Fix the two citations either way — those lines say "send-only stream", which is WP2's rule and already has its own row. |
| S-3 | MEDIUM | §4 L1311–1313: "To avoid excessive buffering at multiple layers, QUIC implementations SHOULD provide an interface for the cryptographic protocol implementation to communicate its buffering limits." | coverage table in `StreamTable.lean`, `Recommended` in `StreamTable/Send.lean` | The only SHOULD in the range with **no coverage row at all**. The §4 rows are 1298, 1304 and 1308; 1311 is absent. BRIEF requires every SHOULD to be a `Recommended` clause or a row reading `advice, not checkable here: <why>`. | Add the row: `advice, not checkable here: the CRYPTO buffer limit is WP11's `Handshake.State.bufLimit`; this component holds no crypto state`. (WP11 does model it, so the pointer is real.) |
| S-4 | MEDIUM | §4.2 spans L1386–1432, inside the assigned range 1293–1460. L1392: "a receiver MAY send a MAX_STREAM_DATA or MAX_DATA frame multiple times within a round trip"; L1422: "a receiver MUST NOT wait for a STREAM_DATA_BLOCKED or DATA_BLOCKED frame before sending a MAX_STREAM_DATA or MAX_DATA frame". | coverage row "§4.2 (1395–1429) … **out of scope by assignment** (advice)" | The stated reason is false: §4.2 is *in* the assignment. The MAY of L1392 happens to be satisfied (`sentMaxData`/`sentMaxStreams` accept any value repeatedly) and the MUST NOT of L1422 is discussed in NOTES, but the row tells a reader the section was not assigned. | Rewrite the row: MAY L1392 → `Step.sendMaxData`/`Step.sendMaxStreams` (repeats permitted, no monotonicity required); MUST NOT L1422 → `advice/strategy, not checkable per step: <NOTES pointer>`; L1405–1419 → `no normative keyword`. |
| S-5 | MEDIUM | §4.6 L1546 and §19.11 L7812 govern *opening*; nothing in the range forbids sending a frame on a stream the sender has opened. | `StreamTable/Send.lean` `streamMaySend` (`s.has id = true ∧ …`), NOTES 4 | `MaySend` is `False` for all five stream frames on a stream that does not exist, so a locally-initiated stream is unsendable until the model has seen an `appOpenStream` event. This is stricter than the text and is a live hazard for WP12/WP13: ngtcp2 emits a STREAM frame on a stream it opened internally, with no observable "open" event, so every such frame fails `maySend`. NOTES 4 records the decision but not the harness consequence (wave1-a made the same point about `Send.written`/`appWrite`). | Keep the design, but state it as a WP13 obligation: the harness must synthesise `appOpenStream dir` (and `appWrite`) before any locally-initiated stream frame. Add it to the NOTES and to WP13's triage list. |
| S-6 | LOW | ~20 citations | throughout `StreamTable/{Defs,Step,Send,Inv}.lean` and the coverage table | Widespread line drift, including **four error-code rules**. Table below; verified with `sed -n "<n>p"`. | Re-derive mechanically (`grep -n` on the quoted substring; the convention is the line where the sentence's first word sits). |

Wrong citations (cited → actual):

| cited | claimed sentence | actual | what is at the cited line |
|---|---|---|---|
| §4.6 **1554** (`Step.openLimit`, example L57) | "An endpoint that receives a frame with a stream ID exceeding the limit it has sent MUST treat this as a connection error of type STREAM_LIMIT_ERROR" — **error-code rule** | 1546 | blank line |
| §4.1 **1359** (`Step.existFlowControl`, `Inv` doc, coverage) | "A receiver MUST close the connection with a FLOW_CONTROL_ERROR error" — **error-code rule** | 1368 | "cumulative sum of bytes received on all streams, which is used to" |
| §4.6 **1543** (`maxStreamsLimit`, `Inv` doc, coverage) | the ">2^60 ⇒ FRAME_ENCODING_ERROR / TRANSPORT_PARAMETER_ERROR" rule — **error-code rule** | 1537 | mid-sentence ("type FRAME_ENCODING_ERROR if it was received in a frame; see") |
| §19.11 **7802** (`Step.maxStreamsTooLarge`, example L117) | "Receipt of a frame that permits opening of a stream larger than this limit MUST be treated as a FRAME_ENCODING_ERROR" — **error-code rule** | 7803 | the *other* sentence ("This value cannot exceed 2^60") |
| §19.8 **7638** (`Step.localNotCreated`, examples, coverage) | "An endpoint MUST terminate the connection with error STREAM_STATE_ERROR if it receives a STREAM frame …" — **error-code rule** | 7637 | "STREAM_STATE_ERROR if it receives a STREAM frame for a locally-" |
| §2.1 **712** (`State.opened`/`has`/`openThrough`, `Step.openOk`, coverage, 3 examples) | "A stream ID that is used out of order results in all streams of that type with lower-numbered stream IDs also being opened." | 718 | a table rule `+------+---…+` |
| §4.1 **1353** (`Step.maxDataRaise`, coverage) | "A receiver can advertise a larger limit for a connection by sending a MAX_DATA frame." | 1356 | "advertised based on the current offset of data consumed on that" |
| §4.1 **1357** (`Step.sendMaxData`, `Send.lean` header, NOTES, coverage, example L114) | "Once a receiver advertises a limit …, it is not an error to advertise a smaller limit" | 1364 | "MAX_DATA frame, which indicates the maximum of the sum of the" |
| §4.1 **1361** (`Step.maxDataStale`, coverage) | "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA frames that do not increase flow control limits." | 1372 | "limits.  A receiver could determine the maximum data limit to be" |
| §4.1 **1368** (`Recommended` `.dataBlocked`) | "If a sender has sent data up to the limit, it will be unable to send new data and is considered blocked." | 1375 | the FLOW_CONTROL_ERROR sentence |
| §4.6 **1553** (`withinPeerStreamLimit`, `sendCredit`, `streamMaySend`, `Step.openLocal`, `Inv` doc, coverage) | "Endpoints MUST NOT exceed the limit set by their peer." | 1546 | "ignore any MAX_STREAMS frame that does not increase the stream limit." |
| §4.6 **1559** (`Step.maxStreamsStale`, `Step.sendMaxStreams`, `Send.lean` header, NOTES, coverage) | "A receiver MUST ignore any MAX_STREAMS frame that does not increase the stream limit." / "Once a receiver advertises a stream limit …" | 1552 / 1551 | "streams available to peers roughly consistent." |
| §4.6 **1569** (`Step.openLocalBlocked`, `Recommended`, coverage) | "An endpoint that is unable to open a new stream due to the peer's limits SHOULD send a STREAMS_BLOCKED frame." | 1561 | blank (page break) |
| §4.6 **1536** (`Step.maxStreamsRaise`) | "Subsequent limits are advertised using MAX_STREAMS frames." | 1533 | blank line |
| §4.6 **1531** (`Step.openLimit`, coverage) | "Only streams with a stream ID less than (max_stream * 4 + initial_stream_id_for_type) can be opened" | 1530 | continuation line |
| §4.6 **1535** / **1563** (coverage) | "Separate limits apply …" / "this document leaves implementations to decide when …" | 1534 / 1555 | continuation / the "MUST NOT wait" sentence |
| §4.1 **1331** / **1355** / **1352** (coverage, `init`, `recvHighest`) | initial limits from transport parameters / cumulative sum / credit accounting | 1332 / 1358 / — | blank lines |
| §19.12 **7828**, §19.14 **7899** / **7903** (coverage, `Step.dataBlocked`, `Step.streamsBlockedOk`) | DATA_BLOCKED SHOULD / STREAMS_BLOCKED SHOULD / "does not open the stream" | 7827 / 7886 / 7901 | continuation and blank lines |

Correct, for the record: §2.1 687; §4.1 1330; §4.5 1495; §19.9 7710, 7712; §19.10 7736; §19.11 7809, 7812, 7820; §19.14 7919; §19.5 7473, 7476.

### Probes (`out/probe_wp9.lean`, `lake env lean` exit 0)

**P9-1 (S-1).** A client, `ours.maxData = 20`, `ours.maxStreamDataUni = 1000`.
Stream 3 (server-initiated unidirectional, receive-only at a client) receives
10 bytes with FIN, so its final size is 10 and `recvTotal = 10`.

```lean
private def s1 : State := run cli [.stream ⟨3⟩ (.recv (.recvStream 0 10 true))]
example : s1.recvTotal = 10 := by decide
example : s1.maxDataLocal = 20 := by decide

-- WP2 permits either the FINAL_SIZE_ERROR or ignoring the frame (§4.5 L1522):
example : Stream.outcomes (s1.get ⟨3⟩) (.recv (.recvStream 0 200 false))
    = [.error .finalSizeError, .ok (s1.get ⟨3⟩) []] := by decide

-- the table charges 200−10 = 190 bytes of connection credit and deletes it:
example : component.outcomes s1 (.stream ⟨3⟩ (.recv (.recvStream 0 200 false)))
    = [.error .flowControlError, .error .finalSizeError] := by decide
example : (component.outcomes s1 (.stream ⟨3⟩ (.recv (.recvStream 0 200 false)))).all
    (fun o => match o with | .error _ => true | _ => false) = true := by decide
```

The same through RESET_STREAM with a changed final size:

```lean
example : Stream.outcomes (s1.get ⟨3⟩) (.recv (.recvResetStream 0 200))
    = [.error .finalSizeError, .ok (s1.get ⟨3⟩) []] := by decide
example : component.outcomes s1 (.stream ⟨3⟩ (.recv (.recvResetStream 0 200)))
    = [.error .flowControlError, .error .finalSizeError] := by decide
```

**P9-2 (S-2).** Stream 0 at a client is client-initiated **bidirectional** and
has not been created; §19.4/§19.13 state no rule for it, yet:

```lean
example : (⟨0⟩ : StreamId).initiator = Role.client := by decide
example : (⟨0⟩ : StreamId).dir = StreamDir.bidi := by decide
example : cli.has ⟨0⟩ = false := by decide
example : component.outcomes cli (.stream ⟨0⟩ (.recv (.recvResetStream 0 5)))
    = [.error .streamStateError] := by decide
example : component.outcomes cli (.stream ⟨0⟩ (.recv (.recvStreamDataBlocked 5)))
    = [.error .streamStateError] := by decide
```

### Checked and found correct

* §4.6 / §19.11 boundaries: `MAX_STREAMS = 2^60` raises the limit, `2^60+1` is
  FRAME_ENCODING_ERROR and nothing else; STREAMS_BLOCKED `> 2^60` offers exactly
  STREAM_LIMIT_ERROR and FRAME_ENCODING_ERROR and no `.ok`.
* Connection credit exactly at `maxDataLocal` is accepted, one byte over is
  FLOW_CONTROL_ERROR (probe P9-3).
* §2.1 implicit opening: a frame for index 2 opens indices 0 and 1 first, in
  increasing stream-ID order, with one `streamOpened` each, and `has` is true
  for all of them afterwards; index 3 with an advertised limit of 3 is
  STREAM_LIMIT_ERROR.
* §19.11 L7812's own example (uni limit 3 ⇒ streams 3, 7, 11 but not 15) is
  replayed correctly by `appOpenStream`.
* `Step` is exhaustive over `has × peerFrame × initiator × limit × conn-fc ×
  WP2's outcome`, `outcomes_ne` holds, and where several rules fire at once
  every error the text attaches to any of them is offered (the W2-1 ruling).
* MAX_DATA / MAX_STREAMS "ignore if not increasing" is deterministic and correct
  in both directions; advertising a *smaller* limit is permitted on the send
  side (`MaySend` has no monotonicity conjunct) — the right reading of
  §4.1 L1364 and §4.6 L1551, and the deliberate departure from `Template.lean`.
* Routing into WP2 is faithful: the send-only / receive-only STREAM_STATE_ERRORs
  come out of `Stream.Step.sendMissing`/`recvMissing`, e.g. MAX_STREAM_DATA for
  a peer-initiated *unidirectional* stream opens it and then fails.
* `Inv` is satisfiable by a realistic initial state (`init_inv` needs only the
  four `max_streams` parameters ≤ 2^60, which WP1's `Valid` guarantees), and the
  named theorems say what their doc comments claim: `recvTotal_le_advertised`
  and `sentTotal_le_peer` are the two `Inv` conjuncts; `recvTotal_eq_sum` /
  `sentTotal_eq_sum` show the incremental totals equal the sum over the table
  (streams with no entry contributing 0, which is right); `no_reuse`,
  `has_forever`, `has_lower`, `opened_step` are the §2.1 monotonicity facts.
  None is vacuous.
* `Recommended` covers the two SHOULDs of §4.1 L1376/L1382 and §4.6 L1561 and is
  never used to reject anything.
* §13.3-driven `MaySend` for DATA_BLOCKED / STREAMS_BLOCKED requires the frame to
  carry the limit in force; a stale repeat after the limit moved is refused
  (probe P9-4). NOTES justifies this from §13.3 L5409 and I agree it does not
  clash with the retransmission rule.

---

## WP10 — Migration (§9, lines 3272–3812)

Files: `QuicModel/Spec/Migration.lean`, `Migration/{Basic,Step,Inv,Send,Theorems}.lean`.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| M-1 | **HIGH** | §9.5 L3603: "An endpoint MUST NOT reuse a connection ID when sending from more than one local address, for example when initiating connection migration … or when probing a new network path …" | `Migration/Basic.lean` `State.dcidOn : Map Path Nat`, `reusedAcrossLocal`; `Migration/Step.lean` `cidCase`/`Step.cidFresh`; `Migration/Send.lean` `MaySendPacket` clause 6; `Migration/Inv.lean` `InvOneLocalAddrPerCid` | `dcidOn` is keyed by path and `State.useCid` **overwrites** the entry, so changing the connection ID used on a path erases the record that the old one was ever used from that local address. The same ID may then be taken up from a second local address: `cidCase` returns `.fresh`, `Step.cidFresh` accepts, and `maySendPacket` permits transmitting with it. `InvOneLocalAddrPerCid` and `dcid_one_local_address` quantify over the *current* map, so neither catches it. This is `Step` accepting behaviour the text forbids. Probe M-1. | Make the record grow-only: keep a `used : List (Nat × LocalAddr)` (or `Map Nat LocalAddr`, sequence number → the one local address it has ever left from) alongside `dcidOn`, test `reusedAcrossLocal` against it, and state `InvOneLocalAddrPerCid` over it. `dcidOn` stays for "what is in use now"; the ban is about history. The same applies to `reusedAcrossPeer`, subject to the L3609 MAY. |
| M-2 | MEDIUM | §9.5 L3603/L3608 and §9 L3284 are rules about the datagram a packet actually leaves in. `Core`'s `Spec.OutDatagram` now carries `src`, `dest`, `dcid`, `scid` (one per datagram, because §12.2 forbids coalescing packets with different connection IDs). | `Migration/Send.lean` `MaySendPacket`, `MaySendDatagram`, `State.tx : SendCtx` | Every send-side clause reads `s.tx.path` / `s.tx.dcidSeq` — the state — and never the datagram's own fields, so a datagram claiming any `src`/`dest`/`dcid` at all is judged by whatever the last `beginSendOn` set. Probe M-6. WP12 must therefore synthesise a `beginSendOn` before every send, and a mismatch between `tx` and the real datagram is invisible. This duplicates, in state, exactly what the `OutDatagram` fields now provide. | Move the path and connection-ID clauses into `MaySendDatagram` over `d.src`/`d.dest`/`d.dcid`, keeping `tx` only for the *history* M-1 needs. NOTES 14's reason for the event ("so that §9.5 has a record of which CID is in use where") survives; the `MaySendPacket` re-check on `tx` does not. |
| M-3 | MEDIUM | §9.3 L3379: "Receiving a packet from a new peer address containing a non-probing frame indicates that the peer has migrated to that address"; L3382: "If the recipient permits the migration, it MUST send subsequent packets to the new peer address and MUST initiate path validation …" — no condition on the *local* address. | `Migration/Basic.lean` `recvCase` (`else if decide (p.loc ≠ s.active.loc) then .quiet`) | A non-probing packet from a new peer address that arrives at a local address other than the active path's is classified `.quiet`, so `Step.recvMigrate` can never fire for it and the MUST of L3382 is simply unavailable there. NOTES 3 records the design decision but frames it as an argument about reachability ("the only way a client can receive at a second local address is to have migrated there itself"), which is not what L3379 says. Probe M-4. | Either widen `recvCase` so that the branch is `.migrate` when the packet is non-probing, highest-numbered and from a new peer address whatever the local address (and let §9.6.2's extra conditions gate only the *server's preferred-address* switch), or add the narrowing to the coverage row for L3379 rather than only to NOTES. |
| M-4 | LOW | a dozen doc-comment citations | `Migration/{Basic,Step,Send}.lean` | Off-by-one/two, always inside the right paragraph: 3452 for a sentence starting at 3451 (`revertTo`, `switchTo`, `lastValidated`, `Step.failRevert`); 3461 for 3460 (`Effect.discardState`, `Step.recvGone`, `MaySendPacket` clause 1, `discarded_sends_nothing`); 3611 for 3609 (`Step.cidRebindKeep` — `rebindKeepsCid` itself cites 3609 correctly); 3722 for 3721 (`PathInfo.sawNonProbing`); 3326 for 3325 (`State.knownServerAddr`, `RecvCase.unknownServer`); 3747 for 3746 and 3760 for 3759 (coverage rows). | Re-derive; the **coverage table is otherwise accurate** — I checked all 73 rows' line numbers and found only those two wrong. |

### The two theorems WP10 reports as false

Both claims are **correct**; I checked them against the text independently.

**NOTES 5, theorem (a)** — "the active path never changes to a new path before
the handshake is confirmed". §9 L3280 forbids only *initiating* migration;
§9 L3309–3314 says explicitly that "Not all changes of peer address are
intentional, or active, migrations" and that an endpoint "MUST perform path
validation … if it detects any change to a peer's address"; §9.3 L3382 then
lets the recipient move its sending address, with no handshake condition
anywhere. The counterexample is reachable **from `init` in one step** and is
text-conformant:

```lean
private def srvEarly : State := init .server p00 0
example : srvEarly.handshakeConfirmed = false := by decide
example : recvCase srvEarly p01 5 false = .migrate := by decide
example : ((component.step srvEarly (.recvPacket p01 5 false 0)).next srvEarly).active
    = p01 := by decide
example : component.step srvEarly (.requestMigrate p10) = .drop := by decide   -- (a) as restated
```

The three theorems proved in its place (`no_migration_before_confirmed`,
`maySendPacket_unconfirmed`, `active_loc_stable_from_init`) do say what L3280
says, and none is vacuous.

**NOTES 7, theorem (c)** — "no connection ID sequence number is in use on two
different paths". §9.5 L3609–3613 is explicit: after receiving from a new
source address with the same destination connection ID, an endpoint "MAY
continue to use the current connection ID with the new remote address while
still sending from the same local address". So the peer-address half is not a
theorem, and `dcid_one_local_address` (the L3603 half) is the right
replacement. Two caveats worth recording:

* the witness `cliRebind` in `Migration/Theorems.lean` is hand-built
  (`{ cli with scidOn := [(p00,4),(p01,4)] }`) and is **not** obviously
  reachable, because a client drops packets from an unknown server address
  (§9 L3325). I reproduced it from `cli` through the permitted non-drop branch
  of §9.6 L3680 (probe M-3), so the situation *is* reachable — but the file
  should use the reachable route, or say that the state is a hypothesis;
* the textual case is weaker than NOTES 7 implies. L3611 permits *moving* the
  connection ID to the new remote address; the model shows it "in use on two
  paths" only because `dcidOn` never retires an entry — the same defect as M-1.
  It remains a genuine counterexample, because §9.3.3 L3498 requires the
  endpoint to go on probing the previous path, which is a send to the old
  destination; but that argument, not the map's forgetfulness, is what makes it
  one, and it belongs in the note.

### Probes (`out/probe_wp10.lean`, exit 0)

**M-1.** Directly, the model refuses the reuse; after one intervening change it
does not.

```lean
example : component.step cli (.beginSendOn p10 0) = .drop := by decide      -- correct

private def moved  : State := run cli [.beginSendOn p00 3]
example : moved.dcidOn = [(p00, 3)] := by decide                            -- CID 0 forgotten
example : component.step moved (.beginSendOn p10 0)
    = .ok (moved.useCid p10 0) [] := by decide                              -- ← forbidden
private def reused : State := run moved [.beginSendOn p10 0]
example : reused.dcidOn = [(p00, 3), (p10, 0)] := by decide
example : component.maySendPacket reused ⟨.oneRtt, [.ping]⟩ = true := by decide
-- and the invariant still holds of that state, so no theorem catches it:
example : ∀ e1 ∈ reused.dcidOn, ∀ e2 ∈ reused.dcidOn, e1.2 = e2.2 → e1.1.loc = e2.1.loc := by
  decide
```

`p00 = ⟨la0,pa0⟩`, `p10 = ⟨la1,pa0⟩`: connection ID 0 has now been sent from
both `la0` and `la1`.

**M-4 (M-3).** `recvCase srv ⟨la1, pa1⟩ 5 false = .quiet` — a non-probing packet
from a new peer address at a second local address never reaches `.migrate`.

**M-6 (M-2).** `maySendDatagram` ignores the datagram's own path:

```lean
example : component.maySendDatagram { srv with tx := ⟨p01, 1⟩ }
    { size := 1200, packets := [⟨.oneRtt, [.ping]⟩], src := ⟨0⟩, dest := ⟨0⟩ } = false := by decide
example : component.maySendDatagram srv
    { size := 1200, packets := [⟨.oneRtt, [.ping]⟩], src := ⟨9⟩, dest := ⟨9⟩,
      dcid := some [1,2,3] } = true := by decide
```

### Checked and found correct

* Coverage is genuinely complete for §9: all 73 normative sentences I listed
  from the range have a row, out-of-scope rows name an owner, and every
  RFC 9002 item (L3536, L3539, L3544, L3573) is declared rather than silently
  dropped.
* §9 L3289's either/or is exactly two outcomes and no third
  (`outcomes srvNoMig (.recvPacket p01 5 false 0) = [.drop, .ok (permit …)]`),
  and `observe` is *not* among them — the narrow reading of "this requirement"
  (NOTES 2) is the more permissive one, as the note says.
* §9.3 L3387's "highest-numbered non-probing packet": a reordered packet from
  the old address does not pull the connection back, a newer one does; probing
  packets never move the path (`recvCase_probing`, `probing_never_migrates`).
* §9 L3312's MUST really is unconditional on the receive side — `observe`
  emits `startValidation` whenever `mustValidate`, so `trackSet` on
  `ok []` after a probing packet from a new address is empty.
* §9.3.2: revert-or-close is total for a failure on the unvalidated active path
  (`failCase_active_ne`, `revert_or_close`), `lastValidated` really is validated
  (`InvLastValidated`), and the silent close sets `discarded`, after which
  `MaySendPacket` is false for everything.
* §9 L3284's ban covers probing packets (probed with a PATH_CHALLENGE-only
  packet), lifts on `preferredActedOn`, and never applies to a destination other
  than the handshake peer (`sendBanned_iff` and its three corollaries).
* §9.6: the client validates the preferred address before migrating
  (`migValidateFirst`), keeps the original address if validation fails
  (`MaySendPacket` clause 5), and `preferredAddressCidSeq = 1` matches §5.1.1.
* SHOULDs are `Recommended`/`RecommendedMigration`/`RecommendedRespondToChallenge`/
  `RecommendedNewTokens` and never restrict `Step` or `MaySendPacket`;
  `step_recommended` shows the reference implementation follows the advice.
* The mirror of `PathValidation`'s status is faithful, including "a validated
  path stays validated" in `markFailed`.

---

## WP11 — Handshake (§7–7.3 2157–2505; §7.5 2696–2723; §17.2.2/.1 6300–6409; §17.2.3/.4 6410–6556; §19.6 7509–7564; §19.20 8193–8211)

Files: `QuicModel/Spec/Handshake.lean`, `Handshake/{Basic,Component,Crypto}.lean`.

No HIGH findings. This is the most careful of the three packages: the coverage
table maps every normative sentence in the six ranges, every "out of scope" row
names an owner, the citations are accurate, and the MAYs of §7.5 and §5.2.1 are
all kept as *additional* outcomes.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| K-1 | MEDIUM | §7.2 L2340: "This Destination Connection ID MUST be at least 8 bytes in length."  L2341: "Until a packet is received from the server, the client MUST use the same Destination Connection ID value on all packets in this connection." | `Handshake.lean` `SendHeader`/`sendHeader` | Both MUSTs are encoded, correctly (probe H-8) — but in a **free-standing predicate**, not in any field of `component`. Anything that drives the `Component` record (WP12's composition, WP13's harness) checks neither. NOTE 6 asks for `OutPacket.dcid/scid`; since that note was written, `Core` has given `Spec.OutDatagram` the fields `dcid` and `scid` (one per datagram, precisely because §12.2 forbids coalescing packets with different connection IDs), which is enough to fold `SendHeader` into `MaySendDatagram` **today**, without a `Core` change. | Define `MaySendDatagram s d := ∀ p ∈ d.packets, SendHeader s p.ptype (d.dcid.getD …) (d.scid.getD …)` (with `none` meaning "the rule does not look at them", as `Core` documents) and add it to the `component` value. Re-file NOTE 6 as done-or-narrowed. |
| K-2 | MEDIUM | §17.2.2.1 L6399 ("receives"), §7.2 L2332 ("After processing"), L2371 ("a valid Initial packet"), §17.2.3 L6476 ("once it starts processing") | `Handshake/Basic.lean` `Event.recvHeader` doc, `cidOutcomes`, NOTE 10 | The reading is right and well argued, but the contract is only a comment. With read keys `.present` every §7.2 arm is a **singleton** (probe H-4), so `srvHandshakeDiscard` *mandates* discarding the Initial keys, `cliInitialFirst` *mandates* adopting a connection ID, and `cliOneRtt` *mandates* ending 0-RTT. If WP12 fires `recvHeader` before removing AEAD protection, a single forged packet makes the model demand key discard — and `Component.track` gives WP13 no way to notice. | Make it a hard requirement on WP12 rather than a note: either the composed `recv` fires `recvHeader` strictly after successful protection removal, or it adds the `recvUndecryptable` event NOTE 10 already proposes. Do **not** add `.drop` to these arms (that would lose the MUSTs of L2371 and L2381) — the note is right about that. |
| K-3 | LOW | §7.2 L2380: "Any further changes to the Destination Connection ID are only permitted if the values are taken from NEW_CONNECTION_ID frames" | `Handshake.lean` `SendHeader` (`s.dcidSent = some dcid` for `.initial`/`.zeroRtt`/`.handshake`) | `SendHeader` is stricter than L2380 for a long-header packet whose DCID came from a NEW_CONNECTION_ID frame: `sendHeader afterInit .handshake S4 C1 = false` (probe H-8), where `S4` is any connection ID other than the one adopted from the peer's first Initial. The coverage row for L2380 files it "out of scope: WP4 ConnIds; `SendHeader` covers only long-header packets", which is exactly where the conflict is. | Weaken the conjunct to `s.dcidSent = some dcid ∨ <dcid is an active peer CID>` once WP4's set is available to WP12, or record it as a known over-strictness in the row. Edge case in practice (Handshake keys are usually gone by then). |
| K-4 | LOW | §19.20 gives the receiver of an early HANDSHAKE_DONE no rule. | `Handshake/Basic.lean` `Step.doneEarly` | `.ok s []` is the **only** outcome for a client that receives HANDSHAKE_DONE before completing, so an implementation that raises PROTOCOL_VIOLATION there is rejected. NOTE 7 argues the state is unreachable on a conforming path (no 1-RTT read keys), which is right, but the singleton is still a narrowing where the text is silent. | Either leave it (unreachable) and say so in the coverage table, or offer `.error .protocolViolation` as a second outcome — `Inv`'s `confirmed → complete` is unaffected because an error changes no state. |
| K-5 | LOW | §7.2 L2382: "if subsequent Initial packets include a different Source Connection ID, they MUST be discarded." | `Handshake/Basic.lean` `cidOutcomes` comment, `HdrStep.srvInitialOther` doc, coverage row "§7.2 (2381)" | The quoted fragment starts at 2382; 2381 is "permitted if the values are taken from NEW_CONNECTION_ID frames; if". Similarly the coverage row headed "§7.2 (2337)" quotes "MUST be at least 8 bytes in length", which starts at 2340. | Two line numbers. Everything else I checked was right (see below). |

### Probes (`out/probe_wp11.lean`, exit 0)

**H-1, §7.5 L2703, the 4096-byte boundary at the *default* limit** (the file's
own examples use `bufLimit := 8` to keep `decide` small, so this is the first
check of the real number):

```lean
example : cli.bufLimit = 4096 := by decide
example : (component.outcomes cli (.recvCrypto .initial 10 4096)).length = 1 := by decide
example : component.accepts cli (.recvCrypto .initial 10 4096)
    (.error .cryptoBufferExceeded) = false := by decide
example : (component.outcomes cli (.recvCrypto .initial 10 4097)).length = 2 := by decide
example : component.accepts cli (.recvCrypto .initial 10 4097)
    (.error .cryptoBufferExceeded) = true := by decide
-- NOTE 2: an in-order frame of any size is accepted whole
example : component.outcomes cli (.recvCrypto .initial 0 10000)
    = [.ok (cli.setStream .initial ((cli.stream .initial).recv 0 10000))
         [.deliverCrypto .initial 0 10000]] := by decide
-- NOTE 15: three outcomes past the limit once complete
example : (component.outcomes cliDone (.recvCrypto .oneRtt 10 4097)).length = 3 := by decide
```

**H-2, NOTE 1, the DCID change count.** Retry then the server's Initial gives
exactly two changes, and nothing gives a third:

```lean
example : afterRetry.dcidChanges = 1 ∧ afterRetry.dcidSent = some S2 := …   -- (two examples)
example : afterInit.dcidChanges  = 2 ∧ afterInit.dcidSent  = some S3 := …
example : component.outcomes afterInit (.recvHeader .retry   C1 S4) = [.drop] := by decide
example : component.outcomes afterInit (.recvHeader .initial C1 S4) = [.drop] := by decide
example : component.outcomes afterInit (.recvHeader .initial C1 S3) = [.ok afterInit []] := by decide
example : (run cli [.recvHeader .initial C1 S3]).dcidChanges = 1 := by decide
```

**H-3, NOTE 9, when 0-RTT stops** — both routes, and only those:

```lean
example : component.maySendPacket cli0rtt      ⟨.zeroRtt, [.ping]⟩ = true  := by decide
example : cliAfter1Rtt.processed1Rtt = true := by decide                      -- §17.2.3 L6476
example : component.maySendPacket cliAfter1Rtt ⟨.zeroRtt, [.ping]⟩ = false := by decide
example : cliRejected.write.get .zeroRtt = .discarded := by decide            -- RFC 9001 §4.9.3
example : component.maySendPacket cliRejected  ⟨.zeroRtt, [.ping]⟩ = false := by decide
```

**H-4, NOTE 10, the `recvHeader` contract.** Keys present ⇒ singleton; keys
absent ⇒ the §5.2.1 MAY is preserved; keys discarded ⇒ drop only:

```lean
example : component.outcomes cli (.recvHeader .initial   C1 S3)
    = [.ok (cli.adoptScid S3) [.dcidChanged S3]] := by decide         -- no `.drop` alternative
example : component.outcomes cli (.recvHeader .handshake C1 S3) = [.ok cli [], .drop] := by decide
example : component.outcomes cliNoInit (.recvHeader .initial C1 S3) = [.drop] := by decide
example : component.outcomes cliNoInit (.recvCrypto .initial 0 10)  = [.drop] := by decide
```

**H-8, K-1/K-3:**

```lean
example : sendHeader cli .initial S1big C1 = true  := by decide   -- 8-byte DCID, unchanged
example : sendHeader (initClient C1 S2) .initial S2 C1 = false := by decide   -- L2340, 1 byte
example : sendHeader cli .initial (List.replicate 8 (9:UInt8)) C1 = false := by decide  -- L2341
example : sendHeader afterInit .handshake S4 C1 = false := by decide          -- K-3, vs L2380
```

### Checked and found correct

* NOTE 15 and NOTE 18 are right and matter: past the buffer limit,
  `expand` (§7.5 L2707/L2711) stays available after completion, and the
  CRYPTO_BUFFER_EXCEEDED close is granted **per frame**, so `alreadyDiscarding`
  is not a trap. Both fix real "a MAY became the only outcome" defects.
* §7.5 L2719 is respected everywhere: the discarding outcomes are `.ok`, never
  `.drop`, so the packet is still acknowledged.
* §19.6 L7545: exactly FRAME_ENCODING_ERROR and CRYPTO_BUFFER_EXCEEDED at
  `2^62`, nothing at `2^62 − 1`.
* §19.20: `MaySend .handshakeDone` iff server ∧ complete; a client never sends
  it; the server is `confirmed` on completion and the client only on the frame;
  `Step.doneServer` is silent and NOTE 8's claim checks out — `FrameRules`
  `senderOf .handshakeDone = some .server` with `mustReject receiver :=
  … || decide (senderOf f = some receiver)` really does give PROTOCOL_VIOLATION
  at a server, so the MUST of L8208 survives composition.
* Retransmission: `maySend (.crypto off data)` accepts an exact repeat and any
  sub-range of what TLS handed over, and refuses one byte past it; `handed` and
  `sentNext` only grow.
* §17.2.2.1 both halves: the client discards Initial keys on `sentPacket
  .handshake`, the server on the first Handshake `recvHeader`; discarded keys
  are stable (`read_discarded_stable`, `write_discarded_stable`) and
  `maySendPacket` then refuses Initial packets entirely.
* §7.3: `missingCid` → TRANSPORT_PARAMETER_ERROR alone (L2428 names one code);
  `cidMismatch` → both TRANSPORT_PARAMETER_ERROR and PROTOCOL_VIOLATION (L2433
  names two); `cids_ok_iff` and the three role/Retry corollaries are Figures 7
  and 8 exactly; zero-length connection IDs compare as `some []`.
* `Inv` (`confirmed → complete`, `4096 ≤ bufLimit`, streams well-formed) is
  satisfiable by `initClient`/`initServer` and the theorem statements match
  their doc comments. `deliverCrypto_contiguous` and `deliverCrypto_received`
  are the real content of "reliable, ordered delivery" and are not vacuous.
* NOTE 21's claim that the ranges contain exactly two SHOULDs (L6467, L6483) is
  correct — I re-grepped all six ranges — and both are carried as
  `advice, not checkable here: <why>` rows with a real reason.
* Citations: I checked ~35, including every error-code rule (2428, 2433, 6341,
  6542, 7546, 8208) and every §7.5 and §17.2.2.1 line. All correct except the
  two in K-5.

---

## Composition notes for WP12

1. **"Handshake confirmed" exists three times**: `Handshake.State.confirmed`
   (authoritative — set by `completeServer` at a server and `doneClient` at a
   client), `Migration.State.handshakeConfirmed` (set by
   `Event.handshakeConfirmed`) and `Termination.State.confirmed`. WP12 must
   drive the other two from `Handshake.Effect.handshakeConfirmed` and never
   independently.
2. **`Obs.matchesSpec` is not duplicated** by any of the three. Each enumerates
   the specific code(s) the text names, and where several *rules* fire at once
   (StreamTable) it offers each rule's own code — a different thing from the
   §11 L4434 generic-code permission, which stays where it belongs, in the
   harness comparison. Nothing to remove.
3. **`OutDatagram`'s new fields make two local mechanisms redundant**: Migration
   carries `tx : SendCtx` and checks `s.tx.path`/`s.tx.dcidSeq` (M-2), and
   Handshake keeps `SendHeader` outside the `Component` for want of packet
   connection IDs (K-1). Both should move to `MaySendDatagram` over
   `d.src`/`d.dest`/`d.dcid`/`d.scid`. Handshake's NOTE 6 "requested `Core`
   change" is already satisfied at datagram granularity.
4. **`.drop` precedence.** StreamTable uses `.drop` for "not sent / impossible
   local action", Handshake for "no keys, or keys gone", Migration for both a
   MUST-discard (§9 L3325 `recvUnknownServer`, §9.3.2 L3460 `recvGone`) and a
   refused local request. Under `matchesLoosely` these merge harmlessly with
   `ok []`, *except* that Migration's two MUST-discards must **win** over
   another component's `ok s' fx` for the same datagram — the same gating PLAN
   §4c already records for Termination's phase.
5. **State that only grows.** StreamTable: `opened`, `maxStreamsLocal/Peer`,
   `maxDataLocal/Peer`, `recvTotal`, `sentTotal`, `streams` — all monotone, with
   theorems. Handshake: `dcidChanges`, `handed`, `sentNext`, `delivered`,
   key states (toward `discarded`) — all monotone. Migration: `paths` and
   `scidOn` grow, but **`dcidOn` does not** — `useCid` overwrites per path.
   That is finding M-1, and it is the one place in Wave 2 where a
   forget-the-past state lets forbidden behaviour through.
6. **Events WP13 must synthesise** (none is observable in an ngtcp2 trace):
   `StreamTable.Event.appOpenStream` (S-5), `Migration.Event.beginSendOn`
   (M-2), `Handshake.Event.{sentPacket,sentCrypto,sentRetry,tls*}`. WP11's
   `Effect.cryptoDiscarding` and `Effect.keysDiscarded` are model-level signals
   the API does not report, so the harness needs `trackSet`, as NOTE 16 says.
