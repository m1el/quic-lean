# Triage: model vs. ngtcp2

Started by WP12's examples layer (`QuicModel/Spec/Endpoint/Examples.lean`), which
replays the eight scripts of `harness/scripts/` through `Endpoint.step` /
`Endpoint.accepts` and compares the result with the recorded traces in
`harness/scripts/expected/`.  WP13 owns this file from here on.

Each entry: what ngtcp2 does, what the model permits, the sentence, the verdict.
"Verdict: model" means the model must change; "verdict: ngtcp2" means ngtcp2
deviates from draft-34; "verdict: text" means the text does not decide and the
difference is legitimate on both sides, so the comparison must be loosened.

Nothing in the eight scripts produced a disagreement about an **error code** or
about a **frame the model forbids ngtcp2 from sending**.  `WP13-1` and `WP13-2`
are about the observation channel (application callbacks), `WP13-3` about the
model being looser than the text, `WP13-4` about a send rule that is not
expressible with the current `Spec.OutPacket`, and `WP13-5` is a model defect
that was **found and fixed** while writing the examples.

---

## WP13-1 — `stream_close` fires earlier in the model than in ngtcp2

* **Scenario:** `01-stream-in-order`, second packet
  (`STREAM id=0 off=3 len=3 fin`).
* **ngtcp2:** `CB recv_stream_data id=0 off=3 len=3 fin=1 early=0`, and nothing
  else.  Its `stream_close` callback fires only once *both* directions of the
  stream have reached a terminal state, which in this script never happens.
* **Model:** `Stream.Recv.Effect.allDataReceived 6`, which
  `Endpoint.Effect.cbName` renders as `stream_close`, so
  `observedCbs = ["recv_stream_data", "stream_close"]`.
* **Sentence:** none.  §2.4 leaves the API to the implementation, and PLAN §4a
  records that "the spec says nothing about application callbacks".  The
  underlying transport state — the receive half of stream 0 is in *Data Recvd*
  with final size 6 (§3.2) — is the same in both.
* **Verdict: text** (no sentence decides it).  WP13 must not treat a missing
  `stream_close` as a mismatch.  Two ways out, either is fine: drop the
  `stream_close` row from `Endpoint.Effect.cbName` (making it `none`, i.e. "do
  not compare"), or keep it and make `tracePattern` compare callback lists up to
  removal of `stream_close`.  The first is the smaller change and is what this
  file recommends.

## WP13-2 — `stream_stop_sending` fires at a different moment

* **Scenario:** `07-local-stream-write`, `shutdown_read 4 9`.
* **ngtcp2:** `CB stream_stop_sending id=4 app_error_code=9`, printed when the
  STOP_SENDING frame is **written** (it appears in the trace next to the
  `OUT … STOP_SENDING id=4 err=9` record, not next to
  `RET shutdown_stream_read=OK`).
* **Model:** `Stream.Recv.Effect.stopSendingRequested 9`, produced by the
  *application* event `AppAction.stopSending`, i.e. one step earlier; and
  `Endpoint.Effect.cbName` maps it to `none`, so it is invisible to
  `observedCbs`.  There is no effect-producing step at the later moment: the
  model's `sentStopSending` changes state and emits nothing.
* **Sentence:** §3.5, line 1254 ("A STOP_SENDING frame requests that the
  receiving endpoint send a RESET_STREAM frame") describes the frame, not a
  callback.
* **Verdict: text.**  Leaving `cbName` at `none` is correct for a per-event
  comparison; mapping it to `stream_stop_sending` would compare two different
  points of the trace.  WP13 must add `stream_stop_sending` to the list of
  ngtcp2 callbacks it ignores, alongside `update_key`,
  `get_new_connection_id2` and `select_preferred_addr`.

## WP13-3 — the model permits discarding *any* received datagram

* **Scenario:** all eight.  `Endpoint.outcomes` for a received datagram always
  ends in `DROP`, whatever else it contains.
* **ngtcp2:** processes the datagram (or fails it with a code).  It never
  silently discards a well-formed 1-RTT datagram in these scripts.
* **Model:** `DatagramSize.Step.datagramDiscard` gives `.drop` for
  `Event.recvDatagram n` at any `n`, and `Endpoint.dszGate` sequences it with
  `bindAll`, so the discard is a top-level alternative beside every error the
  rest of the pipeline can raise.
* **Sentence:** §14, line 5695: "Therefore, an endpoint MUST NOT close a
  connection when it receives a datagram that does not meet size constraints;
  the endpoint MAY however discard such datagrams."  "Such datagrams" are the
  ones that *do not meet size constraints*; the permission is conditional, and
  the model applies it unconditionally.  WP7's own NOTES say why: the component
  "cannot see which size constraint (if any) a datagram had to meet".
* **Verdict: model, low priority.**  The looseness is in the safe direction for
  differential testing — it can only make `accepts` more permissive, never
  reject a conforming ngtcp2 — but it costs the harness a discriminator: an
  observation of "processed, no callbacks" can never empty the candidate set.
  Tightening it needs the datagram's size constraint at the point of the
  decision, i.e. `DatagramSize.Event.recvDatagram` would have to carry whether
  a constraint applied.  That is a WP7 change, not a WP12 one, so it is recorded
  rather than made.

## WP13-4 — §19.16's self-retirement rule is unchecked on the send side

* **Scenario:** none of the eight (no RETIRE_CONNECTION_ID is sent).  Found
  while auditing the `WP12` deferrals, not from a trace.
* **ngtcp2:** does not send a RETIRE_CONNECTION_ID for the connection ID in the
  Destination Connection ID field of the packet carrying it.
* **Model:** the *receive* side is checked (`Endpoint.dispatchFrame` passes
  `dcidSeqOf s dcid` into `ConnIds.Local.Event.recvRetireCid`, and
  `ConnIds.Local.Step.retireSelf` is the PROTOCOL_VIOLATION).  The *send* side
  is not: `Endpoint.MaySendPacket` cannot see it, because `Spec.OutPacket`
  carries no Destination Connection ID.
* **Sentence:** §19.16, line 8050: "The sequence number specified in a
  RETIRE_CONNECTION_ID frame MUST NOT refer to the Destination Connection ID
  field of the packet in which the frame is contained."
* **Verdict: model.**  The fix is well defined and small: `Spec.OutDatagram`
  *does* have a `dcid` field, so the rule belongs in
  `Endpoint.MaySendDatagram`, as one more conjunct over
  `d.packets`/`p.frames` — "no RETIRE_CONNECTION_ID in this datagram names the
  sequence number `d.dcid` has in `s.cidLocal.issued`".  Not made here because
  WP12's examples layer is not the place to add a send rule and nothing in the
  eight scripts exercises it.

## WP13-5 — coalesced packets after an undecryptable one (model fixed; ngtcp2 also deviates)

* **Scenario:** none of the eight — `conn_trace.c` sends one packet per datagram,
  and it installs a stub AEAD that "verifies nothing", so decryption can never
  fail in the present harness.  Found while checking WP12's own citations; the
  case now lives in `Examples` §12: a Handshake packet with a wrong AEAD tag
  coalesced before a 1-RTT packet carrying `STREAM id=0 off=0 len=3`.
* **Sentence:** §12.2, line 4619: "The receiver of coalesced QUIC packets MUST
  individually process each QUIC packet and separately acknowledge them, as if
  they were received as the payload of different UDP datagrams.  For example, if
  decryption fails (because the keys are not available or any other reason), the
  receiver MAY either discard or buffer the packet for later processing and MUST
  attempt to process the remaining packets."
* **Model, before the fix:** `Endpoint.recvPackets` returned
  `[.ok s [.skippedRest]]` and stopped, so the STREAM frame in the second packet
  was never dispatched.  The doc comments of `Endpoint/Pipeline.lean` and of
  `Endpoint.Effect.skippedRest` justified that by quoting "if the packet cannot
  be processed, an endpoint MUST discard the remainder of the datagram" as §12.2
  line 4622.  **That sentence is not in draft-34** — `grep -n "remainder of the
  datagram" spec/draft-ietf-quic-transport-34.txt` finds nothing — and the text
  at that line says the opposite.
* **ngtcp2:** stops too.  `conn_recv_cpkt` (`lib/ngtcp2_conn.c`) loops over the
  coalesced packets, and on `NGTCP2_ERR_DISCARD_PKT` it does
  `++conn->cstat.pkt_discarded; return 0;` — it leaves the loop rather than
  advancing to the next packet.  `conn_recv_pkt` returns exactly that code when
  the AEAD open fails ("could not decrypt packet payload"), for both long and
  short headers.  So ngtcp2 discards the packet, which the text permits, but does
  not "attempt to process the remaining packets", which the text requires.
* **Verdict: model fixed, and ngtcp2 deviates.**  Two things follow, and they
  point in opposite directions, so both are recorded rather than reconciled:

  1. *The model was wrong and is fixed on `wp12-examples`.*
     `Endpoint/Pipeline.lean` gains `packetEndOf` (a long header's own Length
     field, or the end of the datagram for a short header, which "can only be the
     last packet included in a UDP datagram", §12.2 line 4606), and
     `recvPackets` now skips the failing packet and continues at that offset,
     still leaving `Effect.skippedRest` behind so the observation records that a
     packet was dropped.  The loop stops only where the text's "attempt" is
     impossible — the header did not parse, or the Length runs past the datagram.
     `recvPackets_ne` and `recvPackets_inv` gained two cases each; nothing else
     in `Endpoint` changed, and the false citations in `Pipeline.lean` and
     `Basic.lean` were corrected.  PLAN §1's rule applies: spec fidelity beats
     agreement with the implementation.
  2. *WP13 will see a mismatch here if it ever reaches this case.*  It cannot
     today: the harness's stub AEAD never fails.  If WP13 makes it fail (a
     one-line change to `pkt_diff.c`'s decrypt), the model will permit the second
     packet's callbacks and ngtcp2 will fire none.  That is **not** a model
     defect to patch back out; it is a genuine ngtcp2 deviation from §12.2
     line 4619, and this entry is the record of it.  Note that the candidate set
     will not actually empty, because `WP13-3`'s unconditional datagram discard
     keeps a `.drop` alternative alive — so the deviation is only visible if WP13
     checks for it deliberately.
* **Follow-up for WP13:** the other five `PacketErr`s that leave the loop
  (`.header`, `.lengthExceedsDatagram`, `.tooShortForSample`, `.fixedBitClear`,
  `.badVersionList`, `.badRetry`) were left alone.  `.fixedBitClear` is the one
  worth a second look: §17.2 line 6095 makes the packet itself discardable, but
  says nothing about the packets coalesced after it, and its extent *is* known,
  so the same argument from §12.2 line 4619 probably applies to it too.  Not
  changed here because no sentence says so outright.

---

# WP13's own entries (`harness/endpoint_diff.c`)

From here on the entries come from the differential harness itself
(`harness/endpoint_diff.md` describes it), which drives the Lean endpoint beside
a real `ngtcp2_conn` through the eight scripts and then through libFuzzer.
Every entry gives a reproducing script in `conn_trace`'s `--script` grammar;
run it with

```sh
export ASAN_OPTIONS=detect_leaks=0 DIFF_OUT=out/artifacts
./out/endpoint_diff --script <file>
```

`WP13-1` and `WP13-2` above were confirmed empirically and are now handled by
the harness: `stream_close` and `acked_stream_data_offset` are removed from both
sides of the callback comparison (level 2 of `endpoint_diff.md` §3), and
`stream_stop_sending` is in the list of ngtcp2 callbacks the harness ignores.
`WP13-3` was confirmed too: every received datagram has a `DROP` alternative, so
"processed, no callbacks" never falsifies anything — the discriminating
observations are the error codes and the non-empty callback lists, exactly as
WP12 predicted.  `WP13-4` was not reached (no RETIRE_CONNECTION_ID is sent in
any run).  `WP13-5` was not reached either: the stub AEAD cannot fail.

## WP13-6 — `acked_stream_data_offset`: nothing routes a received ACK to `StreamTable`

* **Reproducer**

  ```
  role client
  open bidi
  write last 16 0
  drain
  recv app 0 0200000000      # ACK largest=0 delay=0 first=0
  ```
* **ngtcp2:** `CB acked_stream_data_offset id=0 off=0 len=16`.
* **Model:** nothing.  `Endpoint.dispatchFrame` sends an `.ack` frame to
  `stepAck` and to nothing else; `StreamTable` never hears that a stream's data
  was acknowledged, so `Stream.Send.Effect.allDataAcked` — which
  `Effect.cbName` maps to `acked_stream_data_offset` — is unreachable through a
  received frame.  The effect can only be produced by `Stream.Send.Event`s the
  endpoint never fires.
* **Sentence:** §3.1, line 940 ff. is the send-side state machine, whose "Data
  Sent → Data Recvd" transition is "Recv All ACKs".  RFC 9002 owns *which*
  packets are acknowledged and is out of scope by PLAN §1, but the *transition*
  is draft-34's and the model has the effect for it.
* **Verdict: model, low priority.**  It is a wiring gap, not a wrong rule: the
  endpoint would need `Ack`'s `recvAck` outcome to say which packet numbers were
  newly acknowledged and a mapping from those to the stream ranges they carried
  — which is `LocalAction.sentPacketFrames`' bookkeeping plus RFC 9002.  Until
  then the callback is not comparable and the harness excludes it from both
  sides (1296 of 112 275 compared steps in the ten-minute run needed that
  exclusion or `WP13-1`'s).
* **Also:** the same argument makes the model's `Stream.Send` phases
  "Data Sent"/"Data Recvd" unreachable in a differential run, so nothing on the
  send side that depends on them is tested.

## WP13-7 — `outcomes` is not evaluable for a large stream ID

* **Reproducer** (binary, not a script; libFuzzer found it first)

  ```sh
  printf '\x00\x00\x02\x00\x00\x14\x15\xef' > oom.bin
  ./out/conn_trace oom.bin        # IN STREAM_DATA_BLOCKED id=3386706919782612992
  ```
* **ngtcp2:** `RET read_pkt=STREAM_LIMIT`, in constant time.
* **Model:** `Endpoint.outcomes` does not terminate in any usable sense.
  `StreamTable.streamOutcomes` takes the over-the-limit branch

  ```lean
  .error .streamLimitError ::
    (delegate (s.openThrough id) id (s.freshStream id) (openedEffects s id) e).filter isErr
  ```

  and `openedEffects` is `List.range' opened (id.index + 1 - opened)`, i.e. one
  `Effect.streamOpened` per implicitly created stream — here about 8.5 × 10^14
  of them.  The tail is dropped by `.filter isErr`, but it is built first.
  `s.openThrough id` has the same shape.
* **Sentence:** §2.1, line 718: "A stream ID that is used out of order results in
  all streams of that type with lower-numbered stream IDs also being opened."
  The *rule* is right; the executable form enumerates what the rule only
  describes.
* **Verdict: model.**  `Step` is fine and the theorems are unaffected, but PLAN
  §1 says `outcomes` is "the executable form", and it is the form the harness,
  `decide` and `#guard` all use.  A first-class fix is to test the limit before
  building the effects (the `.error` alternative does not need the delegated
  outcomes at all when `id.index` is above the limit — the frame cannot be
  legal); a cheaper one is to make `openedEffects` return `[]` above the limit,
  since no conforming peer can reach those streams.
* **Harness:** `endpoint_diff` reads the plaintext frames of every incoming
  packet first and, above `DIFF_MAX_STREAM_INDEX` (16384), skips the step and
  stops tracking that run — 2197 of 114 472 steps in the ten-minute run.

## WP13-8 — ngtcp2 does not announce §2.1's implicitly opened streams

* **Reproducer**

  ```
  role client
  recv app 0 0a0703616263      # STREAM id=7 off=0 len=3 "abc"
  ```
* **ngtcp2:** `CB stream_open id=7`, `CB recv_stream_data id=7 …`.
* **Model:** `stream_open id=3`, `stream_open id=7`, `recv_stream_data id=7`.
  Stream 7 is the server's second unidirectional stream, so §2.1 opens stream 3
  with it.
* **Sentence:** §2.1, line 718, as above.  ngtcp2 *does* create the lower stream
  (it has to, for the stream limit and for flow control); it does not call the
  application back for it.
* **Verdict: text** — §2.4 leaves the API to the implementation, as PLAN §4a
  already says for callbacks in general.  The harness treats it as a **soft**
  finding: if the names ngtcp2 printed are a subsequence, in order, of the
  effects the model produced, the step is accepted, counted and listed at the
  end of the run rather than reported.  727 of 112 275 compared steps in the
  ten-minute run; 42 distinct patterns, of which `stream_open` alone (186),
  `stream_open, stream_reset` (158) and `stream_open, recv_stream_data` (89) are
  the largest.  Nothing else in the trace differs in those steps: not the error
  code, not the packets.

## WP13-9 — §7.5's CRYPTO_BUFFER_EXCEEDED is not among the permitted outcomes

* **Reproducer**

  ```
  role client
  recv app 0 06800300031000000000000000000000000000000000
  # CRYPTO off=196611 len=16
  ```
* **ngtcp2:** `RET read_pkt=CRYPTO_BUFFER_EXCEEDED`, i.e. QUIC error 0xd.
* **Model:** `OK [… deliver CRYPTO off=196611 …]` and `DROP`; no error at all.
  `Handshake`'s `bufLimit` is carried in `Config` (and `ConfigOk` requires it to
  be at least 4096) but nothing compares an out-of-order CRYPTO frame's offset
  with it.
* **Sentence:** §7.5, line 2713: "If an endpoint does not expand its buffer, it
  MUST close the connection with a CRYPTO_BUFFER_EXCEEDED error code", and
  line 2716: "Once the handshake completes, if an endpoint is unable to buffer
  all data in a CRYPTO frame, it MAY discard that CRYPTO frame and all CRYPTO
  frames received in the future, or it MAY close the connection with a
  CRYPTO_BUFFER_EXCEEDED error code."
* **Verdict: model.**  This is the *opposite* of the usual defect: the model is
  too **narrow**, not too strict — it omits an outcome the text permits, and a
  conforming implementation (ngtcp2) is rejected for choosing it.  Both
  sentences make the error a permitted alternative whenever the frame's data
  does not fit in `bufLimit`, and after the handshake the discard is a second
  one.  The fix is one more constructor in `Handshake.Step` for `recvCrypto`
  when `off + len` exceeds what the buffer holds, with `.error
  .cryptoBufferExceeded` and (post-handshake) `.drop` as alternatives beside the
  existing `.ok`.  Note that `Handshake` already owns the 4096 lower bound, so
  the information is there.
* **Frequency:** every CRYPTO frame in the fuzz corpus whose offset is past the
  buffer; one of the recurring `ERR code=13` signatures.

## WP13-10 — "blocked at a limit we never granted": three frames, one rule, encoded once

* **Reproducers**

  ```
  role server
  recv app 0 145008            # DATA_BLOCKED v=4104   (initial_max_data is 4096)
  ```
  ```
  role server
  recv app 0 1703              # STREAMS_BLOCKED dir=uni v=3  (our limit is 2)
  ```
* **ngtcp2:** FLOW_CONTROL_ERROR (0x3) for the first,
  STREAM_LIMIT_ERROR (0x4) for the second
  (`conn_recv_data_blocked`, `conn_recv_streams_blocked_uni`: "Maximum Streams
  is larger than advertised value").
* **Model:** `StreamTable.outcomes` has `| .recvDataBlocked _ => [.ok s []]` and
  `| .recvStreamsBlocked _ v => if maxStreamsLimit < v then [.error …] else
  [.ok s []]`, where `maxStreamsLimit` is 2^60 — the *encoding* bound of
  §19.14, not the advertised limit.  So neither frame can ever produce the error
  ngtcp2 raises.
* **Sentence:** §4.1, line 1368: "A receiver MUST close the connection with an
  error of type FLOW_CONTROL_ERROR if the sender violates the advertised
  connection or stream data limits"; §4.6, line 1553 is its stream-count
  analogue.  §19.12 and §19.14 themselves attach no error to the frame's value
  beyond the 2^60 encoding bound.
* **Verdict: model — inconsistently encoded, and that is the finding.**  WP2's
  `Stream/Recv.lean` NOTES took a position on exactly this question for
  STREAM_DATA_BLOCKED: "Two readings of §4.1, line 1368 are possible: the narrow
  one … and the wider one, in which a peer that reports being blocked at an
  offset we never granted has claimed credit beyond the advertised limit.  The
  wider reading is encoded, because it is the only one under which the frame has
  any check at all and because the error is added as an *alternative*."  The
  same argument applies word for word to DATA_BLOCKED (§4.1's connection-level
  limit) and to STREAMS_BLOCKED (§4.6's stream limit), and WP9 encoded neither.
  Either reading is defensible; having one frame follow the wider reading and
  its two siblings the narrow one is not.  The fix is two `.error` alternatives
  in `StreamTable.Step`, beside the existing `.ok`, so the model stays no
  stricter than either reading — the shape WP2 already used.

## WP13-11 — FINAL_SIZE_ERROR for a STREAM_DATA_BLOCKED (predicted by WP2)

* **Reproducer**

  ```
  role server
  recv app 0 0b0003616263      # STREAM id=0 off=0 len=3 fin  -> final size 3
  recv app 1 15001e            # STREAM_DATA_BLOCKED id=0 v=30
  ```
* **ngtcp2:** `RET read_pkt=FINAL_SIZE` (0x6).
* **Model:** `OK [… deliver STREAM_DATA_BLOCKED id=0 v=30]` and `DROP`.
* **Sentence:** §4.5, line 1517 attaches FINAL_SIZE_ERROR to "a RESET_STREAM or
  STREAM frame"; line 1520 to "receipt of data".  A STREAM_DATA_BLOCKED is
  neither.
* **Verdict: ngtcp2 (harmless), text ambiguous.**  This is exactly WP2's
  prediction, written before the harness existed: `Stream/Recv.lean` NOTES, "Two
  things ngtcp2 does with this frame are deliberately **not** encoded, and
  belong on WP13's triage list as expected mismatches: (i)
  `conn_recv_stream_data_blocked` returns FINAL_SIZE_ERROR when the receiving
  part is already `SHUT_RD` … and the reported offset is beyond the highest
  received".  Confirmed.  §11 line 4434 does not rescue it: FINAL_SIZE_ERROR is
  not a generic code, so the candidate set does empty.  No change to the model;
  the entry exists so that the mismatch is not rediscovered.
  WP2's second prediction — "(ii) it advances `rx.last_offset` to the reported
  offset, spending connection-level credit for data that was never received" —
  is **not** directly observable (it changes no callback and no error code); it
  would show up only as a later FLOW_CONTROL_ERROR that the model does not
  expect, which the ten-minute run did not produce.

## WP13-12 — the model closes on the idle timeout where ngtcp2 keeps running

* **Reproducer:** none minimal.  It appears in the fuzz corpus after several
  `time` steps totalling more than 30 s of trace time with traffic in between;
  the harness records it as the soft finding "model in closing/draining/closed
  at now=…us while ngtcp2 runs on", 129 runs of 16 796 in the ten-minute run.
  The straightforward case agrees on both sides:

  ```
  role client
  time 80000000000             # 80 s, in ngtcp2's nanoseconds
  recv app 0 0a0103616263
  ```

  gives `RET handle_expiry=IDLE_CLOSE` and no mismatch.
* **Sentence:** §10.1, line 3838: the connection is silently closed "when it
  remains idle for longer than the minimum of the max_idle_timeout value
  advertised by both endpoints"; line 3841: "An endpoint restarts its idle timer
  when a packet from its peer is received and processed successfully", and
  restarts it on sending an ack-eliciting packet "if no other ack-eliciting
  packets have been sent since last receiving and processing a packet".
* **Verdict: undecided — do not change either side on this evidence.**  The two
  disagree about *when the timer restarts*, not about the timeout, and the
  harness cannot settle it: `conn_driver.h` forces
  `NGTCP2_CS_POST_HANDSHAKE` with `conn->idle_ts` still at
  `settings.initial_ts = 0`, so ngtcp2's timer starts from a moment that never
  happened, and the model's `Termination` starts from `init`.  Deciding it needs
  a harness that runs a real handshake, which PLAN §4a lists as out of reach.
  What the harness does meanwhile: once **every** candidate is in the closing,
  draining or closed phase while ngtcp2 is still running, it stops tracking that
  run and counts it, rather than reporting the hundred consequences of one
  divergence.
* **Second-order note, worth its own look:** the model's idle close is
  *mandatory* at the deadline (WP6 review finding T-2, "idle close mandatory at
  the exact deadline instant"), so there is no non-closed alternative for the
  candidate set to keep.  If §10.1's "is silently closed" is read as permitting
  a late close — and every implementation closes late, because the check runs on
  a timer — then a `.ok` alternative belongs beside it, and the divergence above
  would not empty the set.  That is a WP6 question, recorded not made.

## WP13-13 — a connection ID the peer retires does not free a slot in the model

* **Reproducer**

  ```
  role server
  open bidi
  write last 4 0
  drain                        # ngtcp2 issues NEW_CONNECTION_ID seq=1,2,3
  recv app 0 1902              # RETIRE_CONNECTION_ID seq=2
  drain                        # ngtcp2 issues seq=4 to replace it
  ```
* **ngtcp2:** writes NEW_CONNECTION_ID with sequence number 4, a fifth
  connection ID, while `active_connection_id_limit` is 4.
* **Model:** `ConnIds.Local.MaySend` refuses it, so
  `quic_endpoint_may_send_datagram` is `false` for every candidate.
* **Sentence:** §5.1.1, line 1721: "An endpoint MUST NOT provide more connection
  IDs than the peer's limit."  The limit counts *active* (unretired) connection
  IDs, and the two sides disagree about how many are active.
* **The sharp observation:** after the `recv` step, *every* candidate still
  reports `activeCidsLocal=4` — the connection ID the peer retired did not free
  a slot.  `Endpoint.dispatchFrame` does route the frame
  (`stepCidLocal s (.recvRetireCid seq (some dcidSeq))`), the step itself does
  not mismatch, and §19.16's self-retirement guard does not apply here (the
  packet is addressed to sequence number 0 and the frame retires 2).  So either
  `ConnIds.Local.State.activeCount` does not count what §5.1.1 line 1721 counts,
  or `recvRetireCid`'s `.ok` is not the branch the candidate set kept.
* **Verdict (lead, confirmed by hand): harness mapping, fixed — not a model
  defect.**  `ConnIds.Local` is correct: issuing 1, 2, 3, then `recvRetireCid 2`
  gives `activeCount = 3` and the replacement issue is permitted (checked with a
  direct `#eval`).  The diagnostic export added for WP13-17
  (`quic_endpoint_may_send_datagram_why`) showed every surviving candidate with
  `retired = []`: the candidates that had applied the retirement were rejected
  by the *observation*, because the model rendered `Effect.cidRetiredByPeer` as
  ngtcp2's `remove_connection_id` callback, which ngtcp2 fires when it later
  removes the ID, not on receipt of the frame.  The candidates that survived
  were the ones in which the packet was discarded, which WP13-3's blanket
  `.drop` alternative permits and which matches "no callbacks".  Fix: the
  effect is no longer mapped to a callback (same class as WP13-1).  After the
  fix the reproducer and the eight scenarios run with zero mismatches.
  WP13-3 remains worth closing: it is what let a wrong candidate survive.

## WP13-14 — harness: `NGTCP2_ERR_DRAINING` is not a PROTOCOL_VIOLATION (fixed)

* **Reproducer**

  ```
  role server
  recv app 0 1c0000            # CONNECTION_CLOSE (transport) err=0 ftype=0
  ```
* **What happened:** `ngtcp2_conn_read_pkt` returns `NGTCP2_ERR_DRAINING` to say
  "the datagram was processed and the connection has entered the draining
  period" (§10.2.2).  `ngtcp2_ccerr_set_liberr` has no case for it, so it falls
  through to `ngtcp2_err_infer_quic_transport_error_code`, which answers
  PROTOCOL_VIOLATION for anything it does not recognise.  The harness was
  comparing a phase change against a connection error, and the model — which
  correctly answers `OK [… send_farewell_close]` — looked wrong.
* **Verdict: harness mapping error, fixed.**  `obs_error` now treats
  `NGTCP2_ERR_DRAINING` and `NGTCP2_ERR_CLOSING` as "no error".  Recorded
  because anyone else joining this trace will hit it.

## WP13-15 — harness: the trace's unprotection assumes an 8-byte connection ID

* **Reproducer**

  ```
  role server
  recv app 0 18110108c1c1c1c1c1c111110f070000000a001f000000fff9fd0531f80000000000000000
  # NEW_CONNECTION_ID seq=17 rpt=17 with a 17-byte connection ID
  open bidi
  write last 16 0
  drain
  ```
* **What happens:** ngtcp2 accepts the 17-byte connection ID and addresses the
  peer with it, so its short headers are 18 bytes, not 9.
  `conn_driver.h`'s `dump_out_datagram` — WP8's, unchanged — calls
  `ngtcp2_pkt_decode_hd_short(&hd, p, left, CIDLEN)` with `CIDLEN = 8`, so the
  packet number offset, the header-protection sample and the payload are all
  read nine bytes early.  The `OUT` records then show a nonsense packet number
  and end in `BADFRAME`, and `endpoint_diff` was offering that nonsense to
  `quic_endpoint_may_send_datagram`.
* **Verdict: harness, pre-existing (WP8), worked around not fixed.**
  `endpoint_diff` now checks with `Quic.decodeFrames` that a written packet's
  payload parses to its last byte and skips the datagram otherwise — 3986 of
  53 549 written datagrams in the ten-minute run, which is a real loss of send-side
  coverage.  The proper fix belongs in `conn_driver.h`: track the current
  Destination Connection ID length (the `dcid_status`/`get_new_connection_id`
  callbacks and the NEW_CONNECTION_ID frames both carry it) instead of assuming
  8.  It would also fix `conn_trace`'s own traces, which are wrong in the same
  way today.

## WP13-16 — change request: the endpoint has no way to be told its peer's address is validated

* **Not a mismatch**, a hole in the exports found by hitting it.
* **What happens:** `conn_driver.h` forces `NGTCP2_CS_POST_HANDSHAKE` and marks
  the path validated, as ngtcp2's own `read_write_pkt` fuzzer does.  The model
  starts from `Endpoint.init`, where a server's `AddressValidation` budget is
  zero, so the very first datagram a server writes is one
  `AddressValidation.MaySendTo` forbids and every send-side check afterwards is
  meaningless.
* **Sentence:** §8.1, line 2757: "the successful use of Handshake packets
  indicates that … the peer's address is validated".
* **What the harness does:** replays the packet that must have caused it — one
  Handshake packet carrying only PADDING, fed as an ordinary `Event.datagram` at
  start-up.  PADDING is not ack-eliciting, so it leaves no acknowledgment
  obligation behind, and the datagram's bytes count towards the budget exactly
  as the real packet's would.  It works, and it is honest, but it is a
  *simulation* of a fact the harness already knows.
* **Request:** either a `LocalAction.addressValidated (a : Addr)` — the effect
  `AddressValidation.Effect.addressValidated` already exists, and §8.1 line 2749
  ("an endpoint MAY consider the peer's address validated" after a token) shows
  the model already admits out-of-band validation — or a documented
  `Endpoint.initValidated` beside `Endpoint.init` for harnesses that start after
  a handshake.  The same hole makes `Handshake.State.confirmed` reachable only
  through `tlsComplete`, which is fine, and `Migration`'s `handshakeConfirmed`
  fine with it; address validation is the only one with no event.

## WP13-17 — change request: the send side needs `MaySendDatagram` to be answerable per candidate (done: `quic_endpoint_may_send_datagram_why`, printed per candidate under `DIFF_SHOW=1`)

* **Not a mismatch.**  `quic_endpoint_may_send_datagram` takes one state, so the
  harness asks it once per candidate and accepts the datagram if *any* candidate
  allows it.  That is right, but it is O(candidates) Lean calls per datagram and,
  more importantly, it gives the harness no way to say *why* the others refused:
  `MaySendDatagram` is an eight-way conjunction and the export returns one bit.
  A mismatch report can print the state and the frames, but not the conjunct.
  Three quarters of the time spent triaging the `maysend` signatures went on
  guessing which conjunct it was.
* **Request:** an export that returns the conjuncts as a bitmask, or a rendering
  function `maySendDatagramWhy : State → OutDatagram → String`, beside the
  existing boolean.  The same applies to `maySendPacket` and `maySend`.  Nothing
  in the specification changes; it is a diagnostic.

## WP13-18 — change request: `quic_endpoint_track_trace` cannot express "ignore this callback"

* **Not a mismatch.**  `Exports.tracePattern` compares `observedCbs fx` with the
  harness's list by equality.  `WP13-1`, `WP13-2`, `WP13-6` and `WP13-8` are all
  cases where the right comparison is equality *up to a named set of callbacks*
  or *up to a subsequence*, and the harness therefore re-implements
  `Obs.matchesSpec` in C (`outcome_matches` in `endpoint_diff.c`) to be able to
  filter both sides.  That is a second implementation of a model function, which
  is exactly what `Exports.lean` set out to avoid.
* **Request:** `quic_endpoint_track_trace_with (ss) (e) (isError) (code) (cbs)
  (ignored : List String) (subsequence : UInt8)`, or simply make
  `Effect.cbName` return `none` for `stream_close` and `.allDataAcked` as
  `WP13-1` recommends and add a subsequence flag.  Then the harness would call
  the model for every level of the comparison instead of only the first.

---

# WP13 results

Harness: `harness/endpoint_diff.c` at this commit, built with
`./build_harness.sh endpoint_diff` (clang, ASan, libFuzzer, `-O1 -g`), against
`QuicModel/Spec/Endpoint` as merged on `master` (WP11 review fixes, WP12
examples layer, the §12.2 coalescing fix).

## The eight scripted scenarios

| scenario | mismatches |
|---|---|
| 01-stream-in-order | 0 |
| 02-stream-flow-control | 0 |
| 03-final-size-error | 0 |
| 04-max-streams-too-large | 0 |
| 05-cid-limit | 0 |
| 06-handshake-done-at-server | 0 |
| 07-local-stream-write | 0 |
| 08-stream-limit | 0 |

**8 of 8 clean.**  Two of them (01 and 03) mismatch on `stream_close` alone if
`WP13-1`'s exclusion is removed; nothing else in the eight disagrees about an
error code, a callback list or a frame on the wire.  `harness/scripts/run.sh`
still matches all eight recorded traces byte for byte, so the driver refactoring
is transparent.

## Ten minutes of fuzzing

`./out/endpoint_diff -max_total_time=600 -max_len=4096 -rss_limit_mb=4096
-timeout=30 out/corpus-ep corpus/conn_trace`, ASan on, seeded from WP8's 2041-input
`corpus/conn_trace`.

| | |
|---|---|
| inputs executed | 16 675 (peak RSS 651 MB) |
| connections driven | 16 669 |
| receive/timer steps compared | 110 628 |
| … of which needed the `stream_close`/`acked_stream_data_offset` exclusion | 1 338 (1.2 %) |
| … of which needed the subsequence rule (`WP13-8`) | 667 (0.6 %) |
| steps not compared (`WP13-7`'s guard, non-transport error codes) | 2 008 (1.8 %) |
| written datagrams checked against `maySendDatagram` | 51 812 |
| … unparsable (`WP13-15`, after the fix) | 0 |
| runs abandoned after every candidate had closed (`WP13-12`) | 98 (0.6 %) |
| **distinct mismatch signatures** | **75** |
| total mismatch occurrences | 3 718 |
| distinct soft findings (`WP13-8`) | 42 |

So **about 97.6 % of compared steps matched exactly**, a further 2.0 % matched
under the two documented relaxations, and the residue is the 75 signatures
below.

## The 75 signatures by class

| class | signatures | root cause | entry |
|---|---|---|---|
| `outcome`, `ERR code=13` | 1 | CRYPTO past the buffer: the model omits a permitted outcome | `WP13-9` |
| `outcome`, `ERR code=3` / `code=4` | 2 | DATA_BLOCKED / STREAMS_BLOCKED past the advertised limit | `WP13-10` |
| `outcome`, `ERR code=6` | 1 | FINAL_SIZE_ERROR for a STREAM_DATA_BLOCKED | `WP13-11` |
| `outcome`, `OK cbs=[… recv_crypto_data …]` | 8 | consequences of `WP13-9`: after the model accepted a CRYPTO frame ngtcp2 rejected, the two disagree about every later CRYPTO frame | `WP13-9` |
| `outcome`, `OK cbs=[… stream_open …]`, `[… stream_reset …]`, `[… recv_stop_sending …]` | 30 | ngtcp2 reporting *more* than the model, or a different order — the residue `WP13-8`'s subsequence rule does not cover, e.g. a `stream_open` ngtcp2 fires where the model produced none because the stream limit had already been exceeded | not yet split |
| `outcome`, `OK cbs=[dcid_status]`, `[remove_connection_id]` | 4 | connection-ID accounting | `WP13-13` |
| `outcome`, other | 2 | — | — |
| `maysend`, every combination containing NEW_CONNECTION_ID | 20 | the model has no free connection-ID slot | `WP13-13` |
| `maysend`, `ACK`, `ACK,STREAM`, `ACK,MAX_DATA`, `STREAM`, `MAX_STREAMS,STREAM` | 6 | one conjunct of the eight in `MaySendDatagram`; the export returns one bit, so which one is a guess | `WP13-17` |
| `obligation` | 1 | one run in 16 669 where §13.2.1's deadline passed in every candidate, at the default tolerance of 25 ms | see below |

The single `obligation` signature is worth stating precisely because it is the
only *liveness* finding: in one run, after several `time` steps, the
acknowledgment deadline of a packet number space passed in every candidate with
no ACK having been written.  It is **not** a conformance claim against ngtcp2:
the driver only writes when a `write` or `drain` step calls the writer, and that
run had none after the last `time`, so an endpoint that behaves perfectly still
looks late.  It shows the check works, not that ngtcp2 is late.  A driver that
drained after every clock step would turn this into a real test.

## What this run did *not* test

Unchanged from PLAN §4a: the handshake proper, transport parameters, Retry,
stateless reset, migration and second paths, receive-side coalescing (the driver
puts one packet per datagram), application close, and anything needing the stub
AEAD to fail (`WP13-5`).  Added by this run: `Stream.Send`'s "Data Sent" and
"Data Recvd" phases, which need `WP13-6`'s missing wiring to be reachable, and
everything downstream of a stream ID above `DIFF_MAX_STREAM_INDEX` (`WP13-7`).

## Re-run after the WP13-13 / WP13-17 fixes (lead, 5 minutes)

`./out/endpoint_diff corpus/conn_trace -max_total_time=300 -max_len=4096`,
log `out/fuzz/refuzz300.log`: 8 380 runs, 49 318 steps compared, 23 565 send
checks, no crash or ASan report. **42 distinct mismatch signatures** (was 75 in
the 10-minute run): 36 `outcome`, **5 `maysend`** (was 26 — the 24 connection-ID
signatures of WP13-13 are gone), 1 `obligation`. Soft findings: 29 distinct.
The remaining signatures are the open items WP13-9, WP13-10, WP13-7, WP13-6 and
the callback-ordering residue; not re-classified here.

