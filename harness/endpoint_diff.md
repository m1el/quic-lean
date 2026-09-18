# `endpoint_diff` — joining the Lean endpoint model to ngtcp2's trace

WP13.  `harness/endpoint_diff.c` runs the Lean endpoint of
`QuicModel/Spec/Endpoint/*` beside a real `ngtcp2_conn` and checks every
observable thing ngtcp2 does against what the specification permits.

```sh
NGTCP2=../ngtcp2 ./build_ngtcp2.sh           # once
NGTCP2=../ngtcp2 ./build_harness.sh endpoint_diff

export ASAN_OPTIONS=detect_leaks=0 DIFF_OUT=out/artifacts && mkdir -p out/artifacts
./out/endpoint_diff --script harness/scripts/01-stream-in-order.txt
./out/endpoint_diff -max_total_time=600 -max_len=4096 -rss_limit_mb=4096 \
    -timeout=30 corpus/conn_trace
```

| environment variable | default | meaning |
|---|---|---|
| `DIFF_OUT` | `.` | where a mismatching fuzz input is saved |
| `DIFF_ACK_TOLERANCE` | `25000` (µs) | slack allowed on §13.2.1's acknowledgment deadline |
| `DIFF_MAX_CANDS` | `12` | cap on the candidate-state set |
| `DIFF_MAX_STREAM_INDEX` | `16384` | above this the model is not evaluable (see "Tractability") |
| `DIFF_FAIL_ON_MISMATCH` | unset | make `--script` exit 3 when anything mismatched |
| `TRACE_SHOW` | unset | print the ngtcp2 trace of a fuzz input |

## 1. One driver, two consumers

`harness/conn_trace.c` (WP8) was split.  Everything that *drives* ngtcp2 — the
stub crypto, the transport parameters, the fixed connection IDs and path, the
packet builder, the eight step kinds, the script and binary front ends, the
trace grammar — now lives in `harness/conn_driver.h` behind ten no-op hook
macros.  `conn_trace.c` keeps its documentation and its two entry points and
produces byte-for-byte the traces in `harness/scripts/expected/`;
`endpoint_diff.c` defines `MODEL_HOOKS` and fills the macros in.  Nothing in the
driver knows the model exists, so the two harnesses cannot drift apart.

| hook | where | what `endpoint_diff` does with it |
|---|---|---|
| `MH_START` | `harness_start` | build `quic_endpoint_init`, prime the model (§2) |
| `MH_MARK` | start of every step | remember `tr.len`, so the step's `CB` lines can be read back out of the trace |
| `MH_RECV` | after `ngtcp2_conn_read_pkt` | compare and narrow (§3) |
| `MH_TIME` | after `ngtcp2_conn_handle_expiry` | compare and narrow |
| `MH_OPEN`, `MH_WRITE`, `MH_SHUTDOWN` | the application steps | drive `Event.app` (§4) |
| `MH_OUT` | per datagram written | the whole send side (§5) |
| `MH_TICK` | end of every step (`tr_time`) | `quic_endpoint_obligations` (§6) |
| `MH_FINISH` | `harness_finish` | release the candidate set |

## 2. Putting the model where `conn_driver.h` puts ngtcp2

`setup_conn` installs the Initial, Handshake and 1-RTT keys by hand, forces
`NGTCP2_CS_POST_HANDSHAKE`, sets `HANDSHAKE_COMPLETED | HANDSHAKE_CONFIRMED` and
marks the current path validated.  The model is put in the same place through
its own events — never by writing a field:

1. `quic_endpoint_init(isServer, a0…a7, b0…b7, 4096, 1024, 4, 2, 30000000,
   25000, 4, 100000)` — `conn_trace.c`'s `fill_params()` and its two fixed
   connection IDs.  **Times are microseconds**: `max_idle_timeout` 30 s is
   `30000000`, `max_ack_delay` 25 ms is `25000`.
2. `Event.tls (.tlsKeys .read .handshake)`, `… .write .handshake`,
   `… .read .oneRtt`, `… .write .oneRtt`, then `Event.tls .tlsComplete` — the
   sequence `Endpoint.Examples.postHandshake` uses, and what the four
   `CB recv_rx_key` / `recv_tx_key` lines of every expected trace record.
3. One synthesised **Handshake packet carrying only PADDING**, fed as an
   ordinary `Event.datagram`.  §8.1, line 2757: "the successful use of Handshake
   packets indicates that … the peer's address is validated".  ngtcp2 is forced
   into a state that can only have been reached that way, and `Endpoint` has no
   event by which the harness could simply *assert* the fact, so the harness
   replays the packet that would have caused it.  PADDING is not ack-eliciting,
   so this leaves no acknowledgment obligation behind; the datagram's bytes
   count towards the anti-amplification budget exactly as the real packet's
   would.  Without it a server's very first datagram is rejected by
   `AddressValidation.MaySendTo` and every later send check is meaningless.

**Time unit.**  ngtcp2 keeps time in nanoseconds (`NGTCP2_SECONDS = 1e9`);
`Spec.Time` is microseconds.  `model_now(h) = h->ts / 1000` is the only
conversion point.  Getting this wrong makes every deadline in the model fire a
thousand times too early — the idle timeout closed the connection after 30 ms of
trace time and the entire receive side then mismatched.

## 3. Set tracking on the receive side

`Endpoint.outcomes` is a *list* of permitted outcomes and ngtcp2 shows only a
return code and some callbacks, so the harness keeps the **set** of candidate
model states (PLAN §4a, `Core.Component.trackSet`) and narrows it after every
step.  A violation is the set becoming empty.

The observation of a step is a triple:

* **error** — `rv != 0` run through `ngtcp2_ccerr_set_liberr`, exactly as
  `conn_driver.h`'s `tr_fatal` does.  Only `NGTCP2_CCERR_TYPE_TRANSPORT` has a
  QUIC error code; an idle close or a drop-connection has none, so those steps
  are **not compared** (counted separately) and the candidate set is advanced by
  every permitted successor instead.
* **callbacks** — the `CB <name>` lines printed since `MH_MARK`, mapped through
  the table of §7 and with the names ngtcp2 has and the model has not removed.
* On an error the callbacks are ignored: `withFx` drops the effects that precede
  an error, which is PLAN §4a's finding ("ngtcp2 fires `stream_open` and then
  fails the same STREAM frame") turned into a rule.

The narrowing itself is `quic_endpoint_track_trace ss e isError code cbs` — the
model's own `Component.trackSet` under `Exports.tracePattern`, so the identity
of `ok []` with `drop` and §11 line 4434's generic-error-code allowance are
applied by the model, not re-implemented here.

Three levels, because the two sides' callback contracts do not agree (§7):

1. **exact** — `quic_endpoint_track_trace` as above.
2. **excluded** — the same comparison with `stream_close` and
   `acked_stream_data_offset` removed from *both* sides.  Both name a transport
   state the two sides agree about but announce at different moments; both have
   a `TRIAGE.md` entry.  Counted separately.
3. **subsequence** — the names ngtcp2 printed are a subsequence, in order, of
   the effects the model produced.  ngtcp2 then reported strictly *fewer* events
   than the spec says happened, at the same points; the commonest case is §2.1
   line 718's implicit opening of the lower-numbered streams, which ngtcp2
   performs but does not announce.  This is recorded as a **soft finding** —
   counted, listed by signature at the end of the run, and not a mismatch.

Only when all three fail is a mismatch reported.  Levels 2 and 3 are
deliberately *not* silent: the summary prints how many steps needed each, so a
reader can see how much discrimination was actually in play.

`quic_endpoint_track_trace` is also not the only thing the harness calls: the
per-candidate outcome lists (`quic_endpoint_recv_datagram` / `_app_event` /
`_tls_event` / `_tick` / `_local_event`) are what levels 2 and 3, the
diagnostics and the resynchronisation are built from.

## 4. Events the harness synthesises

`QuicModel/Spec/Endpoint.lean` §4a lists what has to be invented.  What
`endpoint_diff` fires, and from what:

| model event | from | note |
|---|---|---|
| `tlsKeys` ×4, `tlsComplete` | `MH_START` | §2 |
| a Handshake/PADDING datagram | `MH_START` | §2, address validation |
| `AppAction.openStream dir` | `open bidi\|uni`, only when ngtcp2 returned OK | if ngtcp2 refused, the model's `.drop` agrees and nothing is fired |
| `AppAction.write id n` then `AppAction.fin id` | `write <sid> <n> <fin>` | two separate actions, as §4a requires |
| `AppAction.reset` / `.stopSending` | `shutdown_write` / `shutdown_read` / `shutdown` | `shutdown` fires both |
| `LocalAction.issueCid cid token rpt` | every NEW_CONNECTION_ID **on the wire**, replayed in increasing sequence number | ngtcp2 decides inside the writer; the frame is the only record. `ConnIds.Local.Event.issueCid` numbers them itself and ngtcp2 writes them in decreasing order, hence the sort |
| `LocalAction.retireCid seq` | every RETIRE_CONNECTION_ID on the wire | same reason |
| `LocalAction.startPathValidation p d deadline` | every PATH_CHALLENGE on the wire | same reason; the deadline is `now + 3·PTO` |
| `LocalAction.sentFrameIn ptype path f` | one per frame of every packet written, **before** the packet event | `Stream.Send.written`, `PathValidation.responseSent`, `Ack.sentAck`, `Handshake.sentCrypto` |
| `LocalAction.sentPacket ptype pn ae` | one per packet written; `ae` from `FrameRules.packetAckEliciting` | §17.2.2.1, §13.1, §10.1 |
| `LocalAction.sentDatagram peer n` | one per datagram written | the anti-amplification budget is per datagram |
| `LocalAction.localError code 0` | a `read_pkt` / `handle_expiry` that failed with a transport code | ngtcp2 answers with a CONNECTION_CLOSE; without this `Termination` is still `active` and every frame of that close is one the spec forbids |

Three things are deliberately **not** driven:

* `Handshake.Event.recvHeader` / `.recvCrypto` / `.recvHandshakeDone` /
  `.sentPacket` / `.sentCrypto` — the pipeline fires them itself, and
  `recvHeader`'s contract (only after protection was successfully removed)
  depends on that.
* `extend_stream` / `extend_conn` / `extend_streams`: ngtcp2's API is *relative*
  ("extend by n"), the model's event is the *absolute* limit.  The frame is
  picked up on the wire instead, where the value is visible, as
  `sentFrameIn` of MAX_DATA / MAX_STREAM_DATA / MAX_STREAMS.
* `LocalAction.sentPacketFrames` / `.rtxEvent` / `.ecnEvent` — RFC 9002 and the
  IP header are out of scope and the trace carries neither, so firing nothing
  leaves `repairOwed` empty and `RepairSettled` vacuously true.

A synthesised event has no observation to compare against, so it is applied by
`quic_h_advance_all` (= `trackSet` under a pattern that accepts everything),
which keeps every permitted successor and, importantly, removes duplicate
states — without that the candidate set doubles at every branch and the run
exhausts memory.  If *every* outcome of a synthesised event is a connection
error, that is itself reported (kind `synth`): the model refuses something
ngtcp2 just did.

## 5. The send side

For every datagram ngtcp2 writes, `MH_OUT` unprotects it with the stub crypto
(the same arithmetic as `dump_out_datagram`: mask = first five bytes of the
sample, tag = last sixteen), recovers each packet's number with
`ngtcp2_pkt_adjust_pkt_num`, and turns the payload into a `List Frame` with
`Quic.decodeFrames` — the decoder `harness/frame_diff.c` already tests
differentially.  Then, in this order:

1. the pre-send decisions read off the wire (`issueCid`, `retireCid`,
   `startPathValidation`);
2. `quic_endpoint_may_send_datagram s src=0 dest=1 size isPmtuProbe=0
   isEcnMarked=0 dcid scid packets` against **each** candidate.  `false` from
   every candidate is a mismatch of kind `maysend`: *ngtcp2 sent what the spec
   forbids*.  The converse proves nothing — the absence of a datagram is
   pacing, a congestion window or an application that did not write (PLAN §4a);
3. `sentFrameIn` per frame, then `sentPacket` per packet, then `sentDatagram`.

`isPmtuProbe` is `false` because `conn_driver.h` sets `settings.no_pmtud = 1`;
`isEcnMarked` is `false` because the harness never sets an ECT codepoint and
`ngtcp2_pkt_info.ecn` is zero throughout.  `dcid`/`scid` are the first packet's
(§12.2 forbids coalescing packets with different connection IDs).

## 6. Obligations

At every `TIME` record — that is, after every step — `quic_endpoint_obligations
s now tolerance` is evaluated for each candidate.  If §13.2.1's acknowledgment
deadline has passed in **every** candidate, that is a mismatch of kind
`obligation`: *ngtcp2 failed to do what the spec requires*.  It is reported once
per run (the deadline stays passed, so every later record would repeat it).

**The tolerance, and why it is what it is.**  `Ack.ackDeadline` is
`min arrival + ackDelayBudget`, and `ackDelayBudget` is `max_ack_delay`
(25 ms) in the application-data space and **0** in the Initial and Handshake
spaces, where §13.2.1 says "immediately".  A harness cannot demand zero: in this
driver the clock only moves when a `time` step says so and a packet can only
leave when a `write` or `drain` step calls the writer, so an endpoint that does
everything right still looks late by however long the script waits before
draining.  `Obligations.lean`'s own doc says the harness must supply the bound
it is willing to allow.  The default here is `DIFF_ACK_TOLERANCE = 25000 µs`,
one further `max_ack_delay`: enough to cover the gap to the next send
opportunity in every scripted scenario, small enough that an endpoint that never
acknowledges is still caught (the deadline then recedes no further and every
later record is past it).  ngtcp2's own ACK timer fires at `max_ack_delay / 2`
(the traces show `expiry=12500000`), well inside this.

`quic_endpoint_repair_owed`, `_resets_owed` and `_ecn_feedback_owed` are
end-of-run checks; the harness does not fire `rtxEvent`, so `repairOwed` is
empty by construction and they are not used.

## 7. The mapping table

`Exports.Effect.cbName` is the model's half.  `map_cb` is the harness's half:
which of ngtcp2's callback names is which model effect, and which are dropped.

| ngtcp2 `CB` name | model effect | compared |
|---|---|---|
| `recv_stream_data` | `st (.stream _ (.recv (.dataAvailable _)))` | yes |
| `stream_open` | `st (.streamOpened _)` | yes, up to §2.1's implicit opening (level 3) |
| `stream_reset` | `st (.stream _ (.recv (.streamReset _ _)))` | yes |
| `recv_stop_sending` | `st (.stream _ (.send (.peerStopSending _)))` | yes |
| `extend_max_stream_data` | `st (.stream _ (.send (.creditAvailable _)))` | yes |
| `extend_max_data` | `st (.dataCreditAvailable _)` | yes |
| `extend_max_local_streams_bidi\|uni` | `st (.streamsAvailable dir _)` | yes |
| `handshake_completed` / `handshake_confirmed` | `hs .handshakeComplete` / `.handshakeConfirmed` | yes |
| `recv_crypto_data` | `hs (.deliverCrypto ..)` | yes |
| `recv_new_token` / `recv_retry` | `av (.storeToken _)` / `av (.useToken _)` | yes |
| `path_validation` | `pv (.pathValidated _)` / `(.pathFailed _)` / `ecn _ .ecnValidationFailed` | yes |
| `dcid_status`, `dcid_status2` | `cidRemote (.stopUsing ..)` | yes |
| `remove_connection_id` | `cidLocal (.cidRetiredByPeer _)` | yes |
| `recv_version_negotiation` / `version_negotiation` | `vnClient .abandon` / `(.attemptVersion _)` | yes |
| `stream_close`, `stream_close2` | `st (.stream _ (.recv (.allDataReceived _)))` | level 2 only — TRIAGE `WP13-1` |
| `acked_stream_data_offset` | `st (.stream _ (.send .allDataAcked))` | level 2 only — TRIAGE `WP13-6` |
| `get_new_connection_id`, `get_new_connection_id2` | `cidLocal (.sendNewCid ..)` | no: it announces a decision the harness has already replayed from the wire, and at a different moment |
| `update_key`, `recv_rx_key`, `recv_tx_key`, `tls_early_data_rejected` | — | no: RFC 9001, out of scope |
| `stream_stop_sending` | `st (.stream _ (.recv (.stopSendingRequested _)))` | no: fired when the frame is *written*, not when the application asks — TRIAGE `WP13-2` |
| `extend_max_remote_streams_bidi\|uni` | — | no: "the peer may open more", which is not `streamsAvailable` |
| `recv_datagram`, `ack_datagram`, `lost_datagram` | — | no: RFC 9221 and RFC 9002 |
| `begin_path_validation`, `get_path_challenge_data[2]`, `select_preferred_addr` | — | no |
| `client_initial`, `recv_client_initial`, `recv_stateless_reset[2]` | — | no |

## 8. Reporting

A mismatch is printed once per **signature** and the run carries on.  The
signature is deliberately coarse, so that a thousand STREAM frames differing
only in offset are one line of triage:

* `outcome`: the event family, whether it was an error, the error code, and the
  observed callback names — not the packet length;
* `maysend`: the frame *kinds* of the first packet;
* `app`, `synth`: the action's name; `obligation`: one per run.

The first occurrence prints the observation, the number of candidates, each
candidate's `quic_endpoint_state_render`, **every outcome every candidate
permits** as `quic_endpoint_outcome_render`, and the ngtcp2 trace so far; the
fuzz input is saved under `$DIFF_OUT`.  Afterwards the candidate set is
**resynchronised** — rebuilt from the previous set by keeping every permitted
successor — so that one disagreement does not turn the rest of the run into
noise.  A summary at exit lists every distinct signature with its count, and
every soft (level-3) finding.

## 9. Tractability

`StreamTable.openedEffects` is §2.1 line 718 made executable: `List.range'` over
the stream *index*.  A frame naming stream 2^60 therefore makes `Endpoint.outcomes`
allocate ~10^14 list cells — even on the branch that answers
STREAM_LIMIT_ERROR, because that branch still evaluates the delegated outcomes
in order to filter the errors out of them.  ngtcp2 answers STREAM_LIMIT in
constant time.

Before every received packet the harness therefore reads the plaintext frames
(`g_build_plain`, what the driver's builder encrypted) and takes the largest
stream index they name.  Above `DIFF_MAX_STREAM_INDEX` the step is skipped and
tracking for that run stops: the model could not be advanced past the packet, so
comparing the rest of the run would produce false mismatches.  Skipped steps are
counted and reported; in the ten-minute run they are 1.8 % of steps.
`TRIAGE.md` `WP13-7` has the finding.

Two further guards, both for comparisons the harness cannot make honestly rather
than for comparisons it does not like:

* a written packet whose payload `Quic.decodeFrames` cannot parse to its last
  byte is not offered to the send-side predicates.  It used to happen whenever
  the peer had made ngtcp2 switch to a connection ID that is not 8 bytes long
  (`TRIAGE.md` `WP13-15`); since both `conn_driver.h` and `parse_out` now take
  the length from `conn->dcid.current.cid.datalen` it no longer happens at all,
  and the guard stays as a check on that;
* once **every** candidate is in the closing, draining or closed phase while
  ngtcp2 is still running, the two have diverged irrecoverably (a closed
  endpoint processes nothing and sends nothing), so the run is abandoned and
  counted instead of producing a hundred consequences of one divergence.
  `TRIAGE.md` `WP13-12`.

The candidate set is capped at `DIFF_MAX_CANDS` (12).  `quic_h_advance_all` is
`trackSet`, so duplicates collapse first, and the cap keeps the *head* of
`outcomes`, which is the preferred outcome.  A cap can only ever cost a later
match — it can never invent one — so it is sound for the direction the harness
tests in.

## 10. What the harness cannot see

Unchanged from PLAN §4a, plus what this run added:

* The handshake proper, transport-parameter validation, Retry, stateless reset,
  second paths and migration: the driver has one path and forces the
  post-handshake state.
* Receive-side coalescing: the driver puts one packet in a datagram.
* Anything the stub AEAD cannot fail: `TRIAGE.md` `WP13-5`'s coalescing case
  needs a decrypt that fails.
* Application close (`ngtcp2_conn_write_connection_close` is only called on a
  library error, and that datagram is not offered to `may_send_datagram`).
* The send side is one-directional throughout: a frame ngtcp2 does *not* send is
  never a finding.
