# Third QUIC transport conformance audit

Date: 2026-09-18  
Base revision: `a6b74c246c6bc4805e425ec9a84db67f13a03947`  
Reviewed target: the current working tree, including the uncommitted receive-path
fixes following `TRANSPORT_AUDIT_2026-09-18.md`.  
Reference: `draft-ietf-quic-transport-34.txt`.

## Assessment

Three new send-side conformance defects are reproduced below. All are in
endpoint composition: the individual components contain relevant checks, but
the endpoint either applies them to the wrong state or omits the information
needed to enforce them. The model remains unsuitable as a definitive transport
conformance oracle.

This review read both previous transport audits, inspected the current fixes,
and concentrated on send predicates, connection-ID lifecycle, and migration
integration. It is a targeted source review with executable counterexamples,
not exhaustive certification or a new differential fuzzing campaign.

The second audit's D34-1 through D34-4 have corresponding fixes and regression
guards in `QuicModel/Spec/Endpoint/Examples.lean:683`. The current build passes:
idle restart is conditional on successful processing, Retry integrity has an
abstract validation callback, Initial size is checked per packet, and a known
packet extent permits continuing after an insufficient protection sample.
The first audit's ACK fixes remain present. These historical findings are not
counted again below.

## D34-5 — High: packet send checks allow aggregate flow-control overflow

**Location:** `QuicModel/Spec/Endpoint/Send.lean:93` (`maySendPacket`), and
line 211 (`maySendDatagram`); underlying credit calculation in
`QuicModel/Spec/StreamTable/Send.lean:41`.

Every frame is checked against the same pre-packet state via
`p.frames.all (maySend s)`. Consequently, several frames can each spend the
same remaining connection credit. The datagram predicate also checks all
packets against the same state.

**Reproduction:** initialize a client with connection send credit 10, open
bidirectional streams 0 and 4, and write 6 bytes to each. A single 1-RTT packet
containing both six-byte STREAM frames passes both `maySendPacket` and
`maySendDatagram`, although its 12 new bytes exceed the connection limit.
Recording the first frame raises `sentTotal` to 6 and makes the frame-level
predicate correctly refuse the second. Thus the problem is the batch check,
not the stream-table credit formula.

**Specification:** §4.1, line 1330: “Senders MUST NOT send data in excess of
either limit.” Connection flow control counts data across all streams.

**Impact:** the exported packet/datagram predicates can certify an invalid
send. A caller that separately validates and records every frame in sequence
can catch this example, but the advertised packet/datagram predicates do not.

**Correction:** validate the complete proposed send against cumulative credit,
either by simulating checked state transitions in wire order or by aggregating
the per-stream increases over the entire datagram. Count retransmitted and
overlapping offsets only once; summing frame lengths is insufficient.

**Probe:** `reviews/Audit3.lean:37`.

## D34-6 — High: a retired destination connection ID remains sendable

**Location:** `QuicModel/Spec/Endpoint/Send.lean:176` (`peerIssuedCids`) and
line 189 (`MaySendDatagram`).

The handshake header check sees all peer-issued IDs, including retired ones.
Its comment assigns retirement enforcement to the connection-ID component,
but the composed datagram predicate has no check that the actual DCID remains
usable. `ConnIds.Remote.MaySend` only constrains RETIRE_CONNECTION_ID frames;
it does not inspect outgoing packet headers.

**Reproduction:** receive an authenticated NEW_CONNECTION_ID with sequence 1
and Retire Prior To 1. The endpoint marks sequence 0 retired. A subsequent
PING datagram explicitly carrying the original sequence-0 DCID still passes
`maySendDatagram`. Both DCID and SCID are supplied in this probe, so this is
not caused by the optional-header abstraction.

**Specification:** §5.1.2, lines 1811–1814: upon an increased Retire Prior To,
the peer MUST stop using the corresponding connection IDs and retire them
before adding the newly provided ID to the active set.

**Impact:** the oracle permits a sender to continue addressing packets with an
ID that the peer has required it to stop using, risking connection failure.

**Correction:** add a datagram-level check of the actual DCID against remote
CID retirement state, including sequence 0 and IDs introduced during the
handshake. Filtering the handshake's peer-issued list alone is insufficient:
its separate current-handshake-DCID allowance must not bypass retirement.

**Probe:** `reviews/Audit3.lean:61`.

## D34-7 — High: migration CID reuse enforcement is bypassed by an empty map

**Location:** `QuicModel/Spec/Endpoint/Basic.lean:238` (migration initialization),
`QuicModel/Spec/Endpoint/Dispatch.lean:109` (`stepCidRemote`), and
`QuicModel/Spec/Migration/Send.lean:99`–111 (DCID lookup and unknown-ID allowance).

Migration records CID-use history by sequence number, while outgoing datagrams
supply CID bytes. Its `peerCids` map bridges those representations through
`Migration.Event.learnPeerCid`. Endpoint initialization leaves this map empty;
NEW_CONNECTION_ID dispatch only updates `cidRemote`; endpoint local actions
do not expose `learnPeerCid` either. As a result, the ordinary endpoint cannot
populate the map, and `Migration.MaySendCid` takes its permissive `none` branch
even for a known, nonempty DCID.

**Reproduction:** confirm a client's handshake by receiving HANDSHAKE_DONE.
Sequence 0 is already associated with the original local address in migration
history. For a different local address, `reusedAcrossLocal newPath 0` is true
and `Migration.MaySendCidOn ... newPath 0` is false. Nevertheless, an outgoing
PING datagram from that new address, explicitly using sequence 0's CID bytes,
passes endpoint `maySendDatagram`. The probe also checks that `peerCids` is
empty. Handshake confirmation removes the separate pre-confirmation migration
restriction from this example.

**Specification:** §9.5, line 3603: an endpoint MUST NOT reuse a connection ID
when sending from more than one local address. The same missing lookup also
prevents evaluating the corresponding destination-address history rule.

**Impact:** component proofs about CID history do not protect the composed
send API; its lookup prevents those rules from being consulted.

**Correction:** seed the mapping for the handshake CID and propagate newly
learned peer CIDs to migration, or resolve the DCID through `cidRemote` directly
at composition time. Preserve mappings needed for historical checks, and
distinguish an unknown nonempty CID from the zero-length-CID case. Keep the
retirement check from D34-6 as a separate requirement.

**Probe:** `reviews/Audit3.lean:70`.

## Existing differential evidence from TRIAGE.md

The earlier WP13 campaign tested the Lean endpoint against ngtcp2, not just
wire decoding. `TRIAGE.md` records eight scripted scenarios passing under the
documented callback exclusions, followed by a ten-minute fuzz run with 110,628
receive/timer comparisons, 51,812 send checks, and 75 mismatch signatures.

The subsequent five-minute run is the latest result recorded there. Its saved
log, `out/fuzz/refuzz300.log:2501`, confirms 49,318 compared steps, 23,565 send
checks, **42 distinct mismatch signatures and 1,503 mismatch occurrences**.
There were 1,034 steps not compared and 48 runs abandoned after model closure;
703 comparisons needed callback exclusions and 320 needed the subsequence
relaxation. LibFuzzer reports 8,380 executions; the harness reports 8,375 runs.
The 42 signatures comprise 36 outcome, five send, and one obligation signature.
These are historical measurements, not results from the reviewed working tree.

This is valuable evidence of exercised behavior and unresolved disagreement,
not a clean conformance result. Signatures are not independent bugs: some are
downstream consequences or observation/harness mismatches. WP13-13's apparent
CID-accounting defect was traced to callback mapping and fixed; the obligation
finding is confounded by the driver not draining after every clock advance.
WP13-3's unconditional discard alternative can mask receive defects. The run
explicitly excludes migration/second paths, real handshake behavior, Retry,
receive coalescing, and failing AEAD validation, among other coverage limits.

The triage file also mixes historical states. For example, its WP13-9 claim
that CRYPTO buffering is never checked no longer describes the current
`Handshake/Basic.lean`, which checks buffered bytes and includes buffer-error
alternatives. This does not establish that its old reproducer now agrees with
ngtcp2; replay and renewed adjudication are needed. WP13-7's costly stream
enumeration and WP13-10's unconditional DATA_BLOCKED acceptance remain visible
in `StreamTable/Step.lean`.

The new send findings are compatible with these results: checking actual
ngtcp2 sends cannot expose an overly permissive model unless ngtcp2 emits the
forbidden send, and the migration example is outside the recorded campaign's
scope. The audit's new counterexamples supplement the differential evidence.

## Validation and limits

Commands completed successfully:

```sh
lake build
lake env lean reviews/Audit3.lean
cmp draft-ietf-quic-transport-34.txt spec/draft-ietf-quic-transport-34.txt
git diff --check
```

- Build: 145 jobs, including the existing receive-fix regression guards.
- All new probe guards pass. They deliberately assert the defective behavior;
  after fixes, invert the affected expectations for regression testing.
- Probe states are constructed with endpoint initialization, TLS/application
  events, and authenticated stub-protected receive packets, rather than by
  directly editing endpoint component state.
- The probes are evaluator checks, not general kernel proofs.
- The draft copies are identical. No final-RFC comparison or fuzzing rerun was
  performed.
- Only this report and `reviews/Audit3.lean` were added by this review. Existing
  implementation changes and historical audits were preserved.

The passing equivalence and invariant proofs remain useful, but do not prove
that composed send permissions enforce all the transport's cross-frame and
cross-component requirements. All three counterexamples coexist with the
current proofs.
