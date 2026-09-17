# Lean model of the QUIC packet format, diffed against ngtcp2

An executable Lean 4 model of QUIC's wire format (RFC 8999 / 9000 / 9221 / 9369),
linked into libFuzzer harnesses next to `libngtcp2` so that every input is decoded
by both and the results compared.

## Layout

| Path | What |
|---|---|
| `QuicModel/Basic.lean` | Total parser monad over a `ByteArray` (results carry a cursor-progress proof), varints, hex. |
| `QuicModel/Frame.lean` | `Frame` type, `decodeFrame`, `decodeFrames`, and `Frame.check` (RFC value constraints that ngtcp2 enforces in `ngtcp2_conn.c`, not in the decoder). |
| `QuicModel/Packet.lean` | Long/short/VN/Retry headers, `versionCid` routing, packet-number recovery (RFC 9000 A.3), `Protection` abstraction with `Protection.stub`, `decodePacket`. |
| `QuicModel/Encode.lean` | `encodeFrame` (= type byte ++ `encodeBody`), `Frame.WF`, `Frame.SelfDelimiting`. |
| `QuicModel/RoundTrip.lean` | Proof that `decodeFrame` inverts `encodeFrame`, plus the varint round trip. |
| `QuicModel/Dump.lean` | Canonical text rendering and the `@[export]`ed C entry points. |
| `QuicModel/Tests.lean` | RFC test vectors, checked at build time (`native_decide`: concrete inputs only). |
| `QuicModel/Theorems.lean` | General theorems about the same functions the harness calls. |
| `harness/frame_diff.c` | `ngtcp2_frame_decoder_decode` vs `Quic.decodeFrames`; then the model re-encodes and both the model and ngtcp2 must decode that to the same frames. |
| `harness/pkt_diff.c` | Header decoders, `ngtcp2_pkt_adjust_pkt_num`, and writer round trip (`ngtcp2_ppe` → `Quic.decodePacket`). |
| `FINDINGS.md` | What the comparison showed. |
| `PLAN.md` | Plan for formalizing the rest of the transport spec. |
| `spec/` | The draft text the model is written against. |
| `corpus/` | Fuzzing corpora for the two harnesses. |

## Style: executable total functions

Every definition is a total function that both compiles into the fuzz harness
and can be unfolded in a proof: no `partial`, no `while`, no `get!`/`set!`, no
mutable loops.

- `P α := buf → pos → Except Err { r : α × Nat // pos ≤ r.2 }`. The monad's
  `bind` composes the `≤` proofs, so any parser written in `do` notation is
  monotone by construction.
- `decodeFrame` returns `{ r // pos < r.2 }`: it reads the type byte itself and
  runs the rest as a `P`. `decodeFrames` therefore terminates by
  `termination_by buf.size - pos` with no fuel and no unreachable branch.
- Repetition is structural recursion on a count that was checked against the
  remaining input first (ACK ranges, version lists); PADDING runs use
  `zeroRun`, recursive on `buf.size - pos`.
- Indexing is either `buf[i]` with a proof or `byteAt` (total, default 0) where
  a preceding length check makes the default unreachable.

## Stubbed encryption

`Protection` is a record of `tagLen`, `hpMask` and `aeadOpen`. `Protection.stub`
leaves the payload in the clear, uses a tag of `0xA5` bytes and takes the
header-protection mask from the first five bytes of the sample. The C harness
installs the same stubs as `ngtcp2_crypto_cc` callbacks. Unlike an all-zero
stub, this still checks the sample offset, which header bits get masked, and
where the tag sits.

## Build and run

```sh
export NGTCP2=../ngtcp2            # default; an ngtcp2 checkout
./build_ngtcp2.sh                  # once: libngtcp2 with ASan + libFuzzer coverage, asserts on
./build_harness.sh frame_diff pkt_diff

export ASAN_OPTIONS=detect_leaks=0 DIFF_OUT=out/artifacts
mkdir -p out/artifacts
./out/frame_diff corpus/frame -max_len=4096          # fuzz
./out/frame_diff -runs=0 corpus/frame                # replay only
DIFF_SHOW=1 ./out/frame_diff some_input              # show both decodings
lake exe quicmodel some_input                        # model only, verbose
```

A mismatch prints both renderings, saves the input under `$DIFF_OUT`, and aborts.
