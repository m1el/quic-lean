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
