# QUIC draft-34 transport conformance audit

Date: 2026-09-18  
Reviewed revision: `a6b74c246c6bc4805e425ec9a84db67f13a03947`  
Specification: `draft-ietf-quic-transport-34.txt`; the root and `spec/` copies are byte-identical.

## Assessment and scope

The current model has substantial transport coverage, but should not yet be
treated as a definitive conformance oracle. Four receive-path problems were
reproduced in the composed endpoint, despite the existing proofs and build
checks passing.

This is a targeted source review with executable counterexamples, concentrating
on endpoint receive composition and its interaction with component rules. It is
not an exhaustive sentence-by-sentence certification, a fresh differential
fuzzing campaign, or a review against the final RFC 9000.

This audit updates the assessment in `TRANSPORT_AUDIT.md` without replacing that
historical file. Streams, flow control, migration, handshake, endpoint
composition, retransmission, ECN, and behavioral harness integration are now
present. The earlier audit's three ACK findings have been addressed: outstanding
ACK obligations determine deadlines, partial ACKs retain uncovered obligations,
and the maximum packet number is rejected.

## Confirmed findings

### D34-1 — High: discarded packets restart the idle timer

**Location:** `QuicModel/Spec/Endpoint/Pipeline.lean:889` (`phaseGate`), with
`packetErrOutcomes` at line 158 and `afterDatagram` in the same file.

The active-phase pipeline calls `afterDatagram` whenever routing returns an
`.ok` outcome. Parsing and authentication failures can return `.ok s
[skippedRest]`; consequently, unsuccessful processing also restarts the idle
timer.

**Specification:** §10.1 says an endpoint restarts its idle timer when a packet
from its peer is received and processed successfully.

**Reproduction:** receive a Handshake packet with an invalid authentication tag
at time `12345`. The resulting `term.idleStart` is `12345`.

**Impact:** unauthenticated traffic can keep the modeled connection alive. An
implementation that correctly leaves its idle timer unchanged can diverge from
the oracle.

**Suggested correction:** carry an explicit indication that at least one packet
was successfully processed through the receive pipeline. Restart the timer only
when that indication is true. Preserve the distinction between discarding a
packet and successfully processing it without visible application effects.

### D34-2 — High: Retry integrity validation is assumed to succeed

**Location:** `QuicModel/Spec/Endpoint/Pipeline.lean:453` (`retryPacket`) and
`QuicModel/Packet.lean:215` (Retry decoding).

`retryPacket` supplies a literal `true` to `AddressValidation.recvRetry` for
`integrityOk`. The decoder checks packet shape and extracts the tag, but does
not validate it. `processPacket` discards the extracted tag. The general
`Protection` abstraction does not supply a Retry integrity check.

**Specification:** §17.2.5.2 requires clients to discard Retry packets whose
Retry Integrity Tags cannot be validated.

**Reproduction:** otherwise identical, structurally valid Retry packets with
all-zero and all-`0xff` tags both increment `retriesAccepted` to 1. The Retry
Source Connection ID differs from the client's original Destination Connection
ID, and the token is nonempty. These examples demonstrate that tag contents
cannot influence acceptance; no real cryptographic validation is performed.

**Impact:** the endpoint cannot represent the required rejection of an invalid
Retry tag and can accept an injected or corrupted Retry.

**Suggested correction:** keep the cryptographic algorithm abstract, but expose
a Retry validation callback or an explicit validation result. Pass that result
to the existing component rule instead of hard-coding success.

### D34-3 — High: an undersized Initial is accepted after another packet

**Location:** `QuicModel/Spec/Endpoint/Pipeline.lean:787` (`carriesInitial`) and
line 792 (`dszGate`).

`carriesInitial` examines only the first packet of the UDP datagram. An Initial
later in the datagram bypasses the Initial-specific minimum-size gate.

**Specification:** §14.1 requires a server to discard an Initial packet carried
in a UDP datagram with a payload smaller than 1200 bytes; the server may also
close the connection. §12.2 describes increasing encryption-level order as
helpful for processing, but does not mandate that order.

**Reproduction:** send a datagram smaller than 1200 bytes containing a Handshake
packet followed by an Initial packet to the initial server state. `carriesInitial`
returns false, and the server records Initial packet number 0 as received.

**Impact:** the endpoint accepts and acknowledges an Initial the draft requires
it to discard.

**Suggested correction:** enforce the Initial size rule per packet using the
enclosing datagram's size. Do not infer the presence of all Initial packets from
the first header alone.

### D34-4 — Medium: a short header-protection sample stops coalesced processing

**Location:** `QuicModel/Spec/Endpoint/Pipeline.lean:601` (`recvPackets`) and
line 158 (`packetErrOutcomes`).

The receive loop continues past `.decryptFailed`, but `.tooShortForSample`
takes the terminal error-handling path even when the long header gives a valid,
known packet extent.

**Specification:** §12.2 requires receivers to attempt the remaining coalesced
packets when one packet cannot be decrypted. Failure to obtain a sufficient
header-protection sample prevents processing that packet, but does not prevent
locating the following packet in this case.

**Reproduction:** a long-header packet with a known extent and insufficient
header-protection sample, followed by a valid Handshake packet, leaves the
Handshake receive set empty. The following packet is accepted and recorded as
packet number 1 when received alone.

**Impact:** a malformed packet suppresses processing of a subsequent valid
packet despite the latter's location being known.

**Suggested correction:** use the known packet extent to continue after this
failure, as is already done for `.decryptFailed`. Retain terminal handling when
the extent cannot be determined safely.

## Strengths and assurance limits

The model combines executable total definitions, wire-format round-trip proofs,
explicit permitted-outcome alternatives, component invariants, and a composed
endpoint. Coverage now includes streams and connection flow control, ACKs,
connection IDs, address validation, migration, handshake, termination,
retransmission, and ECN. These are meaningful foundations for testing and further
formalization.

Proofs of internal consistency do not establish that the encoded rules are a
correct translation of the prose. In particular,
`QuicModel/Spec/Endpoint/Component.lean:52` defines endpoint `Step` as membership
in `outcomes`, so their equivalence is definitional. Invariant preservation is
useful, but all four counterexamples above coexist with the current proofs.

Deliberate abstractions also limit the conformance claim:

- STREAM byte contents are abstracted; this does not establish byte-content
  consistency at overlapping offsets.
- TLS internals and recovery/congestion-control calculations are external.
  Abstracting cryptography is appropriate, but required validation outcomes
  still need to reach the transport rules, as D34-2 illustrates.
- Some scheduling obligations remain outside the modeled behavior. Per-step
  send permissions alone cannot establish eventual sending.
- The wire model includes later extensions such as DATAGRAM and QUIC v2.
  Strict draft-34 conformance requires an explicit extension profile.

## Reproduction and validation

The executable probe is `out/ReviewDraft34.lean`. It reuses packet-building and
endpoint-setup helpers copied from `QuicModel/Spec/Endpoint/Examples.lean`, then
checks the counterexamples with `#guard`. These guards assert the current
defective behavior; they are evidence for this audit, not desired regression
expectations after a fix. They are evaluator checks, not general kernel proofs.

Commands run successfully during the review:

```sh
lake build
lake env lean out/ReviewDraft34.lean
cmp draft-ietf-quic-transport-34.txt spec/draft-ietf-quic-transport-34.txt
```

- Build: passed, 145 jobs.
- Probe: passed all guards; diagnostic output was idle-start time `12345`,
  Initial receive range `[{ lo := 0, hi := 0 }]`, and Retry acceptance count `1`.
- Draft comparison: identical.
- Implementation files were not changed.
- Differential fuzzing was not rerun; historical results are not new evidence
  from this review.

Prioritize the receive-pipeline corrections above, then add regression checks
for the required behavior and rerun the behavioral comparison. A broader
conformance claim needs a separate requirement-by-requirement coverage review.
