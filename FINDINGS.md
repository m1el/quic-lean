# Findings

Target: ngtcp2 @ 3c23148e, Debug build (asserts on), ASan, clang libFuzzer.
Coverage feedback comes from both ngtcp2 and the C that Lean generates.

## Result

| Harness / mode | Compared | Inputs | Mismatches |
|---|---|---|---|
| `frame_diff` | `ngtcp2_frame_decoder_decode` loop vs `Quic.decodeFrames` | 21 upstream corpus files + 1.65M (3 min) + 1.70M (10 min) fuzzed | 0 |
| `frame_diff` encoder | model re-encodes what it decoded; model and ngtcp2 must both read it back as the same frames | 1.1M fuzzed + corpus | 0 |
| `pkt_diff` headers | `ngtcp2_pkt_decode_hd_long/_short`, `ngtcp2_pkt_decode_version_cid` vs `Quic.header`, `Quic.versionCid` | 1.97M + 0.52M fuzzed across the three modes (the second run is after the fixed-bit change below) | 0 |
| `pkt_diff` pktnum | `ngtcp2_pkt_adjust_pkt_num` vs `Quic.decodePacketNumber` | | 0 (domain restricted, see 1) |
| `pkt_diff` roundtrip | `ngtcp2_ppe` writer with stub crypto → `Quic.decodePacket` | | 0 |

No ASan reports and no assertion failures inside the fuzzed domain.

The harnesses were checked by seeding a bug into the model each (CID length
limit 21 instead of 20; wrong QUIC v2 long-type rotation). libFuzzer found both
within seconds.

## 1. `ngtcp2_pkt_adjust_pkt_num` asserts where RFC 9000 A.3 has a guard

RFC 9000 A.3 only moves the candidate up a window `if candidate_pn <
(1 << 62) - pn_win`. ngtcp2 turns that condition into
`assert(cand <= NGTCP2_MAX_VARINT - win)` (`lib/ngtcp2_pkt.c:2197`).

    ngtcp2_pkt_adjust_pkt_num((1LL << 62) - 2, 0, 1)   /* aborts in a debug build */

Found by reading the code while writing the model, confirmed with a standalone
call. With `NDEBUG` the function returns a value above `NGTCP2_MAX_PKT_NUM`,
which both callers in `ngtcp2_conn.c` reject.  That does not make release
builds safe: `CMakeLists.txt` strips `-DNDEBUG`, so the assert is live in a
normal build (`DIFFERENCES.md` A5 and section F).
Reaching it remotely needs `max_pkt_num` within half a window of 2^62, and a
peer can raise that by at most 2^31 per authenticated packet, so this is a
latent debug-build assert, not a practical attack. `pkt_diff` keeps the expected
packet number below 2^62 − 2^33 to stay clear of it.

## 2. Deliberate differences between the model and ngtcp2's decoder

These are absorbed by the comparison and are not bugs:

- **Error codes.** The model distinguishes truncated input, unknown frame type,
  non-minimal frame type encoding (RFC 9000 §12.4, e.g. `40 01` for PING) and bad
  CID length. ngtcp2 reads the frame type as one byte and returns
  `NGTCP2_ERR_FRAME_ENCODING` for all of them. Accept/reject agrees everywhere;
  only `ERR` is compared.
- **ACK ranges.** ngtcp2 parses every range but stores the first 32
  (`NGTCP2_MAX_ACK_RANGES`). The dump truncates the model's list the same way.
  Dropping ranges is safe for a receiver (it under-acknowledges), but it means
  frames with > 32 ranges are only compared on their first 32.
- **PADDING.** Both sides coalesce a run of `0x00` into one frame.
- **Version Negotiation with CIDs > 20 bytes.** `ngtcp2_pkt_decode_hd_long`
  rejects it; RFC 8999 permits it. The model follows ngtcp2 here because a
  v1/v2 client never uses a CID that long, so such a VN cannot echo its CIDs.
  `versionCid` (the server-side routing view) does accept long CIDs for unknown
  versions, as does `ngtcp2_pkt_decode_version_cid`.

## 3. Value constraints outside the decoder

`Frame.check` lists per-frame rules that RFC 9000 attaches to the frame itself.
`ngtcp2_pkt.c` does not check them; each one is enforced later in
`ngtcp2_conn.c` (checked by reading, not by fuzzing):

| Rule | Where |
|---|---|
| ACK ranges must not underflow | `ngtcp2_pkt_validate_ack`, called from `conn_recv_pkt` paths |
| STREAM / CRYPTO offset + length ≤ 2^62−1 | `ngtcp2_conn.c:7371`, `:7546` |
| NEW_TOKEN non-empty | `:8442` |
| MAX_STREAMS ≤ 2^60 | `:8135` |
| NEW_CONNECTION_ID retire_prior_to ≤ seq | `:8191` |
| STREAMS_BLOCKED ≤ 2^60 | covered indirectly: `:8461`/`:8480` reject anything above the advertised limit |

## 4. Check against draft-ietf-quic-transport-34

The model was first written from memory of RFC 9000, then read against the
draft text in the repo root: §5.2.2, §12.4, §16, §17.1–17.3.1, all of §19, and
Appendix A.1/A.3.

- §19 (every frame layout, the 1..20 CID length rule, and the six value rules in
  `Frame.check`), §12.4 (unknown type → FRAME_ENCODING_ERROR; shortest type
  encoding, MAY be PROTOCOL_VIOLATION), §16 and A.3 all match the model as
  written. A.3's guard `candidate_pn < (1 << 62) - pn_win` is exactly the
  condition ngtcp2 asserts (finding 1).
- **One omission fixed.** §17.2 and §17.3.1: packets with the fixed bit (0x40)
  clear "MUST be discarded". `decodePacket` now rejects them unless
  `greaseQuicBit` is set (RFC 9287, which postdates the draft); Version
  Negotiation is exempt because those bits are Unused (§17.2.1). ngtcp2 does the
  same in `conn_verify_fixed_bit`; its header decoders only record the bit, as
  does `Quic.header`, so the differential results were unaffected.
- §17.2.1 gives Version Negotiation CIDs as `0..2040` bits, confirming that
  `ngtcp2_pkt_decode_hd_long` is stricter than the format for VN (section 2).
  It is harmless for a client: §17.2.1 also requires the VN to echo the client's
  own CIDs, which are at most 20 bytes.
- §19.14: STREAMS_BLOCKED above 2^60 may be STREAM_LIMIT_ERROR *or*
  FRAME_ENCODING_ERROR, so ngtcp2's indirect check (section 3) is conformant.

DATAGRAM (RFC 9221) and the v2 type codes (RFC 9369) are not in the draft and
remain unchecked against a text.

## Not covered

- The receive path inside `ngtcp2_conn.c` (header-protection removal, reserved
  bits, empty payload, Length vs datagram size). `Quic.decodePacket` models it,
  but it is only compared against packets that ngtcp2's *writer* produced, so
  malformed protected packets are not yet diffed. Doing that needs a harness
  that drives `ngtcp2_conn_read_pkt` with the stub crypto callbacks.
- Retry integrity tag, stateless reset, transport parameters.
- Proofs so far. `Theorems.lean`: varint length classes, `take` bounds, ACK
  range check soundness (§19.3.1), packet number recovery preserving the wire
  bits (A.3). `RoundTrip.lean`: `decodeFrame_encodeFrame`, for every well-formed
  frame, in any surrounding bytes (PADDING must not be followed by a zero byte,
  length-less DATAGRAM by anything). Axioms: `propext`, `Classical.choice`,
  `Quot.sound` only.
- Not yet proved: the converse direction (everything `decodeFrame` returns is
  `WF`, and re-encoding it reproduces the input when the input was minimally
  encoded); the list version for `decodeFrames`/`encodeFrames`; the cursor never
  passing `buf.size`. The fuzzer checks the first two on every input.
