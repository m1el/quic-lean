import QuicModel.Spec.Endpoint.Exports

/-!
  WP12 "Endpoint", part 9: **the scenarios**.

  The eight scripts of `harness/scripts/*.txt` replayed through
  `Endpoint.step` / `Endpoint.accepts`, with the error codes and the
  application-visible effects that `harness/scripts/expected/*.trace` records,
  and the handshake flow of §7.1 Figure 5 (line 2272) driven end to end from
  `Endpoint.init`.

  The packets are built with `Quic.encodeFrame` and the same stub protection the
  harness installs (`Quic.Protection.stub 16`, `Endpoint.harnessProtection`), so
  these are the very bytes `conn_trace.c` feeds to `ngtcp2_conn_read_pkt`, and
  the transport parameters and connection IDs are the ones of its header
  comment's table.

  **Why `#guard` and not `decide` for anything that decodes bytes.**  The
  receive pipeline reaches `Quic.decodePacket`, which calls `Array.all` (inside
  `Protection.stub.aeadOpen`) and `Quic.decodeFrames`.  Both compile to
  well-founded recursion, whose `WellFounded.fix` the kernel does not unfold, so
  `decide` does not merely run slowly — it gets *stuck*:

  ```
  Tactic `decide` failed … reduction got stuck at the `Decidable` instance
    match (decodePacket Protection.stub (dgram 0 [Frame.handshakeDone]) 8 0).isOk, true with …
  ```

  That is why `QuicModel/Tests.lean` reaches for `native_decide` at the wire
  layer.  `native_decide` is out (it adds `Lean.ofReduceBool` as an axiom), so
  the byte-level scenarios are checked with `#guard`, which evaluates the very
  same `Decidable` instance at build time and **fails the build** when it is
  false, while adding no axiom to any theorem.  Every assertion that does not
  decode bytes — state fields, `MaySend`/`MaySendPacket`/`MaySendDatagram`, the
  obligations, the application and TLS event families — is a real `decide` or
  `rfl` proof.

  **`step` or `accepts`.**  Where the text mandates the outcome ngtcp2 produced
  (scenarios 02, 04, 05, 06) the assertion is about `Endpoint.step`, the
  preferred outcome.  Where the text permits ngtcp2's behaviour among others —
  scenario 03, whose FINAL_SIZE_ERROR §4.5 line 1522 explicitly makes optional —
  the assertion is `accepts = true`, as the assignment requires, and the number
  of alternatives is shown next to it.

  NOTES at the end of the file record the places where the model and the
  recorded trace differ; `TRIAGE.md` at the repository root carries them as
  WP13's first triage entries.
-/
set_option maxRecDepth 40000

namespace Quic.Spec.Endpoint.Examples

open Quic Quic.Spec Quic.Spec.Endpoint

/-! ## 1. The connection `harness/conn_trace.c` sets up

Connection IDs are the fixed 8-byte values of its header comment: the local
Source Connection ID (what the peer addresses us with) is `a0..a7`, the remote
one (our Destination Connection ID) is `b0..b7`.  The path is fixed; addresses
are opaque in the model, so the local one is 0 and the peer 1. -/

private def localCid : ByteArray := ⟨#[0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7]⟩
private def peerCid : ByteArray := ⟨#[0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7]⟩

/-- The transport parameters of `conn_trace.c`'s table, identical on both sides:
    `initial_max_data` 4096, `initial_max_stream_data_*` 1024,
    `initial_max_streams_bidi` 4, `initial_max_streams_uni` 2,
    `max_idle_timeout` 30 s, `max_ack_delay` 25 ms,
    `active_connection_id_limit` 4, and `initial_rtt` 100 ms as the PTO. -/
private def cfgOf (isServer : Bool) : Config :=
  harnessConfig isServer localCid peerCid 4096 1024 4 2 30000000 25000 4 100000

private def prot : Protection := harnessProtection

private def peerAddr : Addr := ⟨1⟩
private def selfAddr : Addr := ⟨0⟩
private def thePath : Migration.Path := ⟨⟨0⟩, peerAddr⟩

private def tls (s : State) (e : TlsEvent) : State := (step prot s (.tls e)).next s
private def app (s : State) (a : AppAction) : State := (step prot s (.app a 0)).next s
private def loc (s : State) (a : LocalAction) : State := (step prot s (.local a 0)).next s

/-! ### Putting `Endpoint.State` into the post-handshake state

`conn_trace.c` installs the Handshake and the 1-RTT keys directly and forces the
connection past the handshake, exactly as ngtcp2's own `fuzz/read_write_pkt.cc`
does.  There is no `init`-with-keys variant in `Endpoint`, and none is needed:
the same state is reached from `Endpoint.init` by the five TLS events WP11
defines, which is what the four `CB recv_rx_key` / `CB recv_tx_key` lines at the
top of every expected trace record.  RFC 9001 §4.1.2: the *server*'s handshake
is confirmed as soon as the handshake completes; a client's is not, until a
HANDSHAKE_DONE frame arrives (§19.20, line 8195). -/

private def postHandshake (isServer : Bool) : State :=
  tls (tls (tls (tls (tls (init (cfgOf isServer))
    (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)) .tlsComplete

private def srv : State := postHandshake true
private def cli : State := postHandshake false

example : srv.hs.complete = true := by rfl
example : srv.hs.confirmed = true := by rfl
example : cli.hs.complete = true := by rfl
example : cli.hs.confirmed = false := by rfl

-- …and WP6 and WP10 see the same bit, because `Endpoint.syncConfirmed` writes it
-- back after every step (`Endpoint.InvConfirmed`).
example : srv.term.handshakeConfirmed = true := by rfl
example : srv.mig.handshakeConfirmed = true := by rfl
example : cli.term.handshakeConfirmed = false := by rfl
example : cli.mig.handshakeConfirmed = false := by rfl

/-! ## 2. Building the packets the scripts feed to ngtcp2

The stub of `harness/pkt_diff.c` and `Quic.Protection.stub`: the payload travels
in the clear, the AEAD tag is sixteen 0xA5 bytes, and the header-protection mask
is the first five bytes of the sixteen-byte sample that starts four bytes after
the packet number field.  Nothing masks the sample itself, so the mask can be
computed from the unprotected packet. -/

private def stubTag : ByteArray := ⟨Array.replicate 16 0xa5⟩

/-- Pad a payload out to at least `n` bytes with zeros, which decode as a
    PADDING frame (§19.1).  `conn_trace.c`'s writer does the same: a payload
    shorter than four bytes leaves no room for the header-protection sample. -/
private def padTo (n : Nat) (b : ByteArray) : ByteArray :=
  b ++ ⟨Array.replicate (n - b.size) 0⟩

/-- A 1-RTT packet addressed to us, with a one-byte packet number.  First byte
    `0x40`: short header, fixed bit set, key phase 0, reserved bits clear,
    packet number length 1 (§17.3.1). -/
private def shortPacket (pn : UInt8) (payload : ByteArray) : ByteArray :=
  let body := padTo 4 payload ++ stubTag
  let pnOff := 1 + localCid.size
  let plain := (ByteArray.empty.push 0x40) ++ localCid ++ (ByteArray.empty.push pn) ++ body
  let mask := (Protection.stub 16).hpMask (plain.extract (pnOff + 4) (pnOff + 4 + 16))
  (ByteArray.empty.push (0x40 ^^^ (byteAt mask 0 &&& 0x1f))) ++ localCid ++
    (ByteArray.empty.push (pn ^^^ byteAt mask 1)) ++ body

/-- A long-header packet of type bits `ty` (§17.2: 0 Initial, 2 Handshake),
    version 1, with the connection IDs the harness fixes.  Only an Initial
    carries a Token field.  `tag` is the AEAD tag: `stubTag` for a packet the
    stub protection accepts, anything else for one it rejects. -/
private def longPacketTagged (ty : UInt8) (tag dcid scid token : ByteArray) (pn : UInt8)
    (payload : ByteArray) : ByteArray :=
  let body := padTo 4 payload ++ tag
  let pnAndBody := (ByteArray.empty.push pn) ++ body
  let b0 : UInt8 := (0xc0 : UInt8) ||| (ty <<< 4)
  let preTok := (ByteArray.empty.push b0) ++ bytes [0, 0, 0, 1] ++
    bytes [dcid.size.toUInt8] ++ dcid ++ bytes [scid.size.toUInt8] ++ scid
  let preamble :=
    (if ty == 0 then preTok ++ encodeVarint token.size ++ token else preTok) ++
      encodeVarint pnAndBody.size
  let plain := preamble ++ pnAndBody
  let pnOff := preamble.size
  let mask := (Protection.stub 16).hpMask (plain.extract (pnOff + 4) (pnOff + 4 + 16))
  (ByteArray.empty.push (b0 ^^^ (byteAt mask 0 &&& 0x0f))) ++
    preamble.extract 1 preamble.size ++
    (ByteArray.empty.push (pn ^^^ byteAt mask 1)) ++ body

private def longPacket (ty : UInt8) (dcid scid token : ByteArray) (pn : UInt8)
    (payload : ByteArray) : ByteArray :=
  longPacketTagged ty stubTag dcid scid token pn payload

private def dgram (pn : UInt8) (fs : List Frame) : ByteArray :=
  shortPacket pn (encodeFrames fs.toArray)

private def initialDgram (pn : UInt8) (fs : List Frame) : ByteArray :=
  longPacket 0 localCid peerCid ByteArray.empty pn (encodeFrames fs.toArray)

private def handshakeDgram (pn : UInt8) (fs : List Frame) : ByteArray :=
  longPacket 2 localCid peerCid ByteArray.empty pn (encodeFrames fs.toArray)

/-- A Handshake packet whose AEAD tag is wrong, so `Protection.stub` refuses it
    (`PacketErr.decryptFailed`). -/
private def badHandshakePacket : ByteArray :=
  longPacketTagged 2 ⟨Array.replicate 16 0⟩ localCid peerCid ByteArray.empty 0
    (encodeFrames #[.ping])

/-- The event one received datagram is. -/
private def dgEvent (b : ByteArray) (now : Time := 0) : Event :=
  .datagram peerAddr selfAddr b now

private def recvOut (s : State) (b : ByteArray) (now : Time := 0) : Out :=
  step prot s (dgEvent b now)

private def recvNextB (s : State) (b : ByteArray) (now : Time := 0) : State :=
  (recvOut s b now).next s

private def recv (s : State) (pn : UInt8) (fs : List Frame) (now : Time := 0) : Out :=
  recvOut s (dgram pn fs) now

private def recvNext (s : State) (pn : UInt8) (fs : List Frame) (now : Time := 0) : State :=
  (recv s pn fs now).next s

-- The packets this file builds really are the ones `Quic.decodePacket` reads back.
#guard (Quic.decodePacket prot (dgram 0 [.handshakeDone]) 8 0).isOk = true
#guard (Quic.decodePacket prot (dgram 7 [.ping, .padding 20]) 8 0).isOk = true
#guard (Quic.decodePacket prot (initialDgram 0 [.crypto 0 ⟨Array.replicate 90 1⟩]) 8 0).isOk = true
#guard (Quic.decodePacket prot (handshakeDgram 0 [.crypto 0 ⟨Array.replicate 90 1⟩]) 8 0).isOk
  = true

/-! ## 3. `harness/scripts/01-stream-in-order`

```
recv app 0 0a0003616263            # STREAM id=0 off=0 len=3 "abc"
recv app 1 0f000303646566          # STREAM id=0 off=3 len=3 "def" fin
```
`01-stream-in-order.trace`: `CB stream_open id=0`, `CB recv_stream_data …`,
`RET read_pkt=OK`; then the same for the second packet, and after the ACK timer
the server acknowledges. -/

private def abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩
private def defg : ByteArray := ⟨#[0x64, 0x65, 0x66]⟩

#guard outcomeErrorC (recv srv 0 [.stream 0 0 false abc]) = 0xffffffff
#guard outcomeCbsC (recv srv 0 [.stream 0 0 false abc]) = ["stream_open", "recv_stream_data"]

private def srv01 : State := recvNext srv 0 [.stream 0 0 false abc]

#guard outcomeErrorC (recv srv01 1 [.stream 0 3 true defg]) = 0xffffffff
-- NOTE 1: ngtcp2's trace has only `recv_stream_data` here; the model's
-- `allDataReceived` renders as `stream_close`, which ngtcp2 defers until both
-- directions are closed.  Callbacks are not normative (PLAN §4a).
#guard outcomeCbsC (recv srv01 1 [.stream 0 3 true defg]) = ["recv_stream_data", "stream_close"]

-- §4.5, line 1517: the final size is now known, and it is 6.
#guard (recvNext srv01 1 [.stream 0 3 true defg]).st.recvTotal = 6

/-! ### §13.2.1, line 5075, the rest of script 01: `time 30000` then `drain`

The trace's `OUT … ACK largest=1 …` is the acknowledgment the deadline demands.
`Endpoint.obligations` is the exported form: "nothing is past its deadline". -/

private def srv01b : State := recvNext srv01 1 [.stream 0 3 true defg]

-- `max_ack_delay` is 25 ms, so 25 ms after the packet the ACK is still in time …
#guard obligations srv01b 25000 0 = true
-- … and one microsecond later it is not.
#guard obligations srv01b 25001 0 = false
-- Sending an ACK that covers packets 0 and 1 discharges it.
#guard obligations (loc srv01b (.sentAck .appData 1 1 [])) 25001 0 = true

/-! ## 4. `harness/scripts/02-stream-flow-control`

```
recv app 0 0e0044000161            # STREAM id=0 off=1024 len=1 "a"
```
`initial_max_stream_data_bidi_remote` is 1024, so one byte at offset 1024 is one
byte too many: `RET read_pkt=FLOW_CONTROL`, `ERR type=transport code=3`.

§19.9, line 7712: "An endpoint MUST terminate a connection with a
FLOW_CONTROL_ERROR error if it receives more data than the maximum data value
that it has sent."  The error is mandated, so this is an assertion about
`Endpoint.step`. -/

#guard outcomeErrorC (recv srv 0 [.stream 0 1024 false ⟨#[0x61]⟩]) = 3
#guard acceptsC srv (dgEvent (dgram 0 [.stream 0 1024 false ⟨#[0x61]⟩]))
  (.error .flowControlError) = 1
-- One byte fewer is accepted.
#guard outcomeErrorC (recv srv 0 [.stream 0 1023 false ⟨#[0x61]⟩]) = 0xffffffff

-- PLAN §4a: ngtcp2 fires `stream_open` and *then* fails the same frame.  The
-- merge rule drops the effects an error outcome produced before it (`withFx`),
-- so the model's error carries none and only the code is compared.
#guard outcomeCbsC (recv srv 0 [.stream 0 1024 false ⟨#[0x61]⟩]) = []

/-! ## 5. `harness/scripts/03-final-size-error`

```
recv app 0 0b0003616263            # STREAM id=0 off=0 len=3 "abc" fin
recv app 1 0b00056162636465        # STREAM id=0 off=0 len=5 "abcde" fin
```
`RET read_pkt=FINAL_SIZE`, `ERR type=transport code=6`.

§4.5, line 1517: "Once a final size for a stream is known, it cannot change.  If
a RESET_STREAM or STREAM frame is received indicating a change in the final size
for the stream, an endpoint SHOULD respond with a FINAL_SIZE_ERROR error".  It
is a SHOULD, and line 1522 says so in as many words — "Generating these errors
is not mandatory" — so the model permits both closing and carrying on, and what
is asserted of ngtcp2's choice is `accepts`, not `step`. -/

private def srv03 : State := recvNext srv 0 [.stream 0 0 true abc]
private def badFin : Frame := .stream 0 0 true ⟨#[0x61, 0x62, 0x63, 0x64, 0x65]⟩

#guard acceptsC srv03 (dgEvent (dgram 1 [badFin])) (.error .finalSizeError) = 1
-- Two alternatives: the error and processing it anyway.  ngtcp2 takes the
-- first, and so does `Endpoint.step`.  Discarding the datagram is not a third:
-- it meets its size constraints, so §14 line 5697 does not apply (B3, below).
#guard (outcomes prot srv03 (dgEvent (dgram 1 [badFin]))).length = 2
#guard accepts prot srv03 (dgEvent (dgram 1 [badFin])) .drop = false
#guard outcomeErrorC (recvOut srv03 (dgram 1 [badFin])) = 6

/-! ## 6. `harness/scripts/04-max-streams-too-large`

```
recv app 0 12d000000000000001      # MAX_STREAMS bidi = 2^60 + 1
```
`RET read_pkt=FRAME_ENCODING`, `ERR type=transport code=7`.

§4.6, line 1537: "If a max_streams transport parameter or a MAX_STREAMS frame is
received with a value greater than 2^60 … the connection MUST be closed
immediately with a connection error of type … FRAME_ENCODING_ERROR if it was
received in a frame"; §19.11, line 7803 repeats it. -/

#guard outcomeErrorC (recv srv 0 [.maxStreams .bidi (2 ^ 60 + 1)]) = 7
#guard acceptsC srv (dgEvent (dgram 0 [.maxStreams .bidi (2 ^ 60 + 1)]))
  (.error .frameEncodingError) = 1
-- 2^60 exactly is within the limit.
#guard outcomeErrorC (recv srv 0 [.maxStreams .bidi (2 ^ 60)]) = 0xffffffff

/-! ## 7. `harness/scripts/05-cid-limit`

Four NEW_CONNECTION_ID frames with sequence numbers 1..4 in one packet.
`active_connection_id_limit` is 4 and sequence number 0 is the connection ID the
connection started with, so 1..3 fill the limit and 4 is one too many:
`RET read_pkt=CONNECTION_ID_LIMIT`, `ERR type=transport code=9`.

§5.1.1, line 1743: "After processing a NEW_CONNECTION_ID frame and adding and
retiring active connection IDs, if the number of active connection IDs exceeds
the value advertised in its active_connection_id_limit transport parameter, an
endpoint MUST close the connection with an error of type
CONNECTION_ID_LIMIT_ERROR." -/

private def cidOf (b : UInt8) : ByteArray := ⟨Array.replicate 8 b⟩
private def tokOf (b : UInt8) : ByteArray := ⟨Array.replicate 16 b⟩
private def ncid (n : Nat) (b : UInt8) : Frame := .newConnectionId n 0 (cidOf b) (tokOf b)
private def fourCids : List Frame := [ncid 1 0xc1, ncid 2 0xc2, ncid 3 0xc3, ncid 4 0xc4]

#guard outcomeErrorC (recv srv 0 fourCids) = 9
#guard acceptsC srv (dgEvent (dgram 0 fourCids)) (.error .connectionIdLimitError) = 1
-- Three of them stay within the limit.
#guard outcomeErrorC (recv srv 0 [ncid 1 0xc1, ncid 2 0xc2, ncid 3 0xc3]) = 0xffffffff
#guard (recvNext srv 0 [ncid 1 0xc1, ncid 2 0xc2, ncid 3 0xc3]).cidRemote.activeCount = 4

/-! ## 8. `harness/scripts/06-handshake-done-at-server`

```
recv app 0 1e                      # HANDSHAKE_DONE
```
`RET read_pkt=PROTO`, `ERR type=transport code=10`.

§19.20, line 8207: "A HANDSHAKE_DONE frame can only be sent by the server."
Line 8208: "A server MUST treat receipt of a HANDSHAKE_DONE frame as a
connection error of type PROTOCOL_VIOLATION." -/

#guard outcomeErrorC (recv srv 0 [.handshakeDone]) = 10
#guard acceptsC srv (dgEvent (dgram 0 [.handshakeDone])) (.error .protocolViolation) = 1

-- A *client* that receives one takes it as §19.20 line 8195's confirmation of
-- the handshake, and WP6 and WP10 hear about it through `syncConfirmed`.
#guard outcomeCbsC (recv cli 0 [.handshakeDone]) = ["handshake_confirmed"]
#guard (recvNext cli 0 [.handshakeDone]).hs.confirmed = true
#guard (recvNext cli 0 [.handshakeDone]).term.handshakeConfirmed = true
#guard (recvNext cli 0 [.handshakeDone]).mig.handshakeConfirmed = true

/-- A client that has the keys but whose handshake TLS has not yet reported as
    complete.  §19.20, line 8208's PROTOCOL_VIOLATION is written for a *server*;
    the WP11 review added `Handshake.Step.doneEarlyClose`, which lets a client in
    this state close too rather than only ignore the frame.  Both are permitted,
    so both are `accepts`. -/
private def cliIncomplete : State :=
  tls (tls (tls (tls (init (cfgOf false))
    (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)

example : cliIncomplete.hs.complete = false := by rfl

#guard acceptsC cliIncomplete (dgEvent (dgram 0 [.handshakeDone]))
  (.error .protocolViolation) = 1
-- Ignoring it is the preferred outcome, and it does *not* confirm anything.
#guard outcomeErrorC (recv cliIncomplete 0 [.handshakeDone]) = 0xffffffff
#guard outcomeCbsC (recv cliIncomplete 0 [.handshakeDone]) = []
#guard (recvNext cliIncomplete 0 [.handshakeDone]).hs.confirmed = false

/-! ## 9. `harness/scripts/07-local-stream-write`

```
role client
open bidi / write last 16 0 / open bidi / write last 8 1 / drain
shutdown_write 0 7 / shutdown_read 4 9 / drain
```
The trace shows `OUT … STREAM id=0 off=0 fin=0 data=<16 bytes>`, then
`OUT … STREAM id=4 off=0 fin=1 data=<8 bytes>`, then
`OUT … RESET_STREAM id=0 err=7 final=16; STOP_SENDING id=4 err=9`.

This is the send side, so what is asserted is `maySend` / `maySendPacket` /
`maySendDatagram`, in the shape WP13 will call them.  None of it decodes bytes,
so all of it is `decide`.

`open bidi` is `StreamTable.Event.appOpenStream`, which the harness must
synthesise (`reviews/wave2.md`, composition note 6: `MaySend` is `false` on a
stream that was never created). -/

/-- `n` bytes of payload.  The harness writes `'a' + i % 26`; nothing in the
    model reads the bytes of a STREAM frame, only `data.size`, and
    `Array.replicate` is what the kernel can reduce, so the filler is `n`
    copies of `'a'`. -/
private def filler (n : Nat) : ByteArray := ⟨Array.replicate n 0x61⟩

/-- `open bidi`, `write last 16 0`, `open bidi`, `write last 8 1`.  The script's
    `fin` flag is a separate application action in the model (§2.4, line 805). -/
private def cli07 : State :=
  app (app (app (app (app cli (.openStream .bidi)) (.write ⟨0⟩ 16)) (.openStream .bidi))
    (.write ⟨4⟩ 8)) (.fin ⟨4⟩)

-- §2.1, Table 1: a client's first two bidirectional streams are 0 and 4.
example : cli07.st.opened.byClient.bidi = 2 := by decide
example : cli07.st.has ⟨0⟩ = true := by decide
example : cli07.st.has ⟨4⟩ = true := by decide
example : cli07.st.has ⟨8⟩ = false := by decide

-- §3.3, line 1141: what may go on the wire for stream 0 now.
example : maySend cli07 (.stream 0 0 false (filler 16)) = true := by decide
-- …but nothing on a stream that was never opened (review S-5).
example : maySend cli07 (.stream 8 0 false abc) = false := by decide
-- §2.4: not data the application has not written …
example : maySend cli07 (.stream 0 16 false abc) = false := by decide
-- … and §4.1: not past the peer's `initial_max_stream_data` of 1024.
example : maySend cli07 (.stream 0 1024 false ⟨#[0x61]⟩) = false := by decide

-- The two packets the trace's first `drain` writes.
example : maySendPacket cli07 ⟨.oneRtt, [.stream 0 0 false (filler 16)]⟩ = true := by decide
example : maySendPacket cli07 ⟨.oneRtt, [.stream 4 0 true (filler 8)]⟩ = true := by decide
-- §14.1: a client's 1-RTT datagram is not bound to 1200 bytes, and §8.1
-- line 2818 exempts a client from the amplification limit on this path.
-- `#guard`, not `decide`: `DcidOk` reads the connection ID's bytes.
#guard maySendDatagram cli07
    { size := 129, packets := [⟨.oneRtt, [.stream 0 0 false (filler 16)]⟩],
      dest := peerAddr, src := selfAddr,
      dcid := some peerCid.toList, scid := some localCid.toList }

/-- The state after the two STREAM frames have actually travelled: this is what
    `LocalAction.sentFrameIn` is for, and it is what makes the Final Size of the
    RESET_STREAM 16 rather than 0 (§4.5, line 1481: "More generally, this is one
    higher than the offset of the byte with the largest offset sent on the
    stream, or zero if no bytes were sent"). -/
private def cli07sent : State :=
  loc (loc cli07 (.sentFrameIn .oneRtt thePath (.stream 0 0 false (filler 16))))
    (.sentFrameIn .oneRtt thePath (.stream 4 0 true (filler 8)))

-- `shutdown_write 0 7` is a RESET_STREAM, `shutdown_read 4 9` a STOP_SENDING.
private def cli07b : State := app (app cli07sent (.reset ⟨0⟩ 7)) (.stopSending ⟨4⟩ 9)

example : maySend cli07b (.resetStream 0 7 16) = true := by decide
-- …with any other Final Size it is not the frame §4.5 line 1481 describes.
example : maySend cli07b (.resetStream 0 7 0) = false := by decide
example : maySend cli07b (.stopSending 4 9) = true := by decide

-- The third `OUT` record of the trace, as one packet and as one datagram.
example : maySendPacket cli07b ⟨.oneRtt, [.resetStream 0 7 16, .stopSending 4 9]⟩ = true := by
  decide
#guard maySendDatagram cli07b
    { size := 33, packets := [⟨.oneRtt, [.resetStream 0 7 16, .stopSending 4 9]⟩],
      dest := peerAddr, src := selfAddr,
      dcid := some peerCid.toList, scid := some localCid.toList }

-- §3.5, line 1255: "An endpoint that receives a STOP_SENDING frame MUST send a
-- RESET_STREAM frame if the stream is in the Ready or Send state."
-- `Endpoint.resetsOwed` is the exported predicate WP13 checks at the end of a
-- run; here it is the application's own `shutdown_write` that owes the frame,
-- and the debt is outstanding until the RESET_STREAM is actually written.
example : resetsOwed cli07b = [⟨0⟩] := by decide

-- §3.3, line 1147: "A sender MUST NOT send a STREAM or STREAM_DATA_BLOCKED
-- frame for a stream in the 'Reset Sent' state."
private def cli07c : State :=
  loc cli07b (.sentFrameIn .oneRtt thePath (.resetStream 0 7 16))

example : resetsOwed cli07c = [] := by decide
example : maySend cli07c (.stream 0 0 false abc) = false := by decide
-- §13.3, line 5359: "The content of a RESET_STREAM frame MUST NOT change when it
-- is sent again" — WP14's rule, now part of the endpoint's `MaySend`.
example : maySend cli07c (.resetStream 0 7 16) = true := by decide
example : maySend cli07c (.resetStream 0 8 16) = false := by decide

/-! ## 10. `harness/scripts/08-stream-limit`

```
role client
open bidi × 5                      # the fifth is RET open_bidi_stream=STREAM_ID_BLOCKED
recv app 0 1208                    # MAX_STREAMS bidi = 8
open bidi                          # RET open_bidi_stream=OK id=16
```
§4.6, line 1546: "Endpoints MUST NOT exceed the limit set by their peer." -/

private def openN : Nat → State → State
  | 0, s => s
  | n + 1, s => openN n (app s (.openStream .bidi))

private def cli08 : State := openN 4 cli

example : cli08.st.opened.byClient.bidi = 4 := by decide
-- The fifth is refused.  §4.6 line 1546 is a MUST NOT on the *sender*: the
-- stream is simply not created, which is a `.drop`, not an error — which is
-- exactly ngtcp2's `RET open_bidi_stream=STREAM_ID_BLOCKED` (a local API
-- refusal; no packet is written and the connection is not closed).
example : step prot cli08 (.app (.openStream .bidi) 0) = .drop := by decide
example : (app cli08 (.openStream .bidi)).st.opened.byClient.bidi = 4 := by decide

-- §19.14, line 7886: "A sender SHOULD send a STREAMS_BLOCKED frame … when it
-- wishes to open a stream but is unable to do so due to the maximum stream
-- limit set by its peer"; §13.3, line 5409: "These frames always include the
-- limit that is causing blocking at the time that they are transmitted."
example : maySend cli08 (.streamsBlocked .bidi 4) = true := by decide
example : maySend cli08 (.streamsBlocked .bidi 8) = false := by decide
example : maySendPacket cli08 ⟨.oneRtt, [.streamsBlocked .bidi 4]⟩ = true := by decide

-- MAX_STREAMS bidi = 8 raises the limit and tells the application …
#guard outcomeCbsC (recv cli08 0 [.maxStreams .bidi 8]) = ["extend_max_local_streams_bidi"]

private def cli08b : State := recvNext cli08 0 [.maxStreams .bidi 8]

-- … the fifth stream now opens …
#guard (app cli08b (.openStream .bidi)).st.opened.byClient.bidi = 5
-- … and a STREAMS_BLOCKED frame would now have to carry the new limit.
#guard maySend cli08b (.streamsBlocked .bidi 8) = true
#guard maySend cli08b (.streamsBlocked .bidi 4) = false

/-! ## 11. §7.1, Figure 5 (line 2272): the 1-RTT handshake, end to end

```
   Client                                                  Server

   Initial[0]: CRYPTO[CH] ->

                                    Initial[0]: CRYPTO[SH] ACK[0]
                          Handshake[0]: CRYPTO[EE, CERT, CV, FIN]
                                    <- 1-RTT[0]: STREAM[1, "..."]

   Initial[1]: ACK[0]
   Handshake[0]: CRYPTO[FIN], ACK[0]
   1-RTT[0]: STREAM[0, "..."], ACK[0] ->

                                             Handshake[1]: ACK[0]
            <- 1-RTT[1]: HANDSHAKE_DONE, STREAM[3, "..."], ACK[0]
```

Driven from `Endpoint.init` with TLS events (`tlsSend`, `tlsKeys`,
`tlsComplete`), with `LocalAction.sentFrameIn` / `sentPacket` for the client's
own flights, and with real protected packets for the server's — so the whole
receive pipeline runs on them.  The CRYPTO bytes are opaque (WP11): TLS hands
them over with `tlsSend` and takes them back as `Effect.deliverCrypto`. -/

private def fig5_0 : State := init (cfgOf false)

-- The client starts with Initial keys in both directions (RFC 9001 §5.2).
example : fig5_0.hs.read.initial = .present := by decide
example : fig5_0.hs.write.initial = .present := by decide
example : fig5_0.hs.read.oneRtt = .absent := by decide
example : fig5_0.hs.write.handshake = .absent := by decide

private def crypto (off len : Nat) : Frame := .crypto off ⟨Array.replicate len 1⟩

/-- `Initial[0]: CRYPTO[CH] ->`.  §17.2.2, line 6378: "The first CRYPTO frame
    sent always begins at an offset of 0." -/
private def fig5_1 : State := tls fig5_0 (.tlsSend .initial 100)

example : maySend fig5_1 (crypto 0 100) = true := by decide
-- …but not bytes TLS has not produced, and not at a non-zero offset first.
example : maySend fig5_1 (crypto 0 101) = false := by decide
example : maySendPacket fig5_1 ⟨.initial, [crypto 0 100]⟩ = true := by decide
example : maySendPacket fig5_1 ⟨.initial, [crypto 4 90]⟩ = false := by decide

private def fig5_2 : State :=
  loc (loc fig5_1 (.sentFrameIn .initial thePath (crypto 0 100))) (.sentPacket .initial 0 true)

private def srvFlight1 : ByteArray := initialDgram 0 [.ack 0 0 0 #[] none, crypto 0 90]

/-- `<- Initial[0]: CRYPTO[SH] ACK[0]`. -/
private def fig5_3 : State := recvNextB fig5_2 srvFlight1

#guard outcomeErrorC (recvOut fig5_2 srvFlight1) = 0xffffffff
#guard outcomeCbsC (recvOut fig5_2 srvFlight1) = ["recv_crypto_data"]
-- §7.2, line 2365: the client adopts the server's Source Connection ID.
#guard fig5_3.hs.peerScid = some peerCid.toList

/-- TLS produces the Handshake keys, then
    `<- Handshake[0]: CRYPTO[EE, CERT, CV, FIN]`. -/
private def fig5_4 : State :=
  recvNextB (tls (tls fig5_3 (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (handshakeDgram 0 [crypto 0 200])

#guard fig5_4.hs.read.handshake = Handshake.KeyState.present
#guard outcomeCbsC (recvOut (tls (tls fig5_3 (.tlsKeys .read .handshake))
  (.tlsKeys .write .handshake)) (handshakeDgram 0 [crypto 0 200])) = ["recv_crypto_data"]

/-- `Initial[1]: ACK[0]` and `Handshake[0]: CRYPTO[FIN], ACK[0] ->`.
    §17.2.2.1, line 6398: "A client stops both sending and processing Initial
    packets when it sends its first Handshake packet." -/
private def fig5_5 : State :=
  loc (loc (loc (loc (loc (tls fig5_4 (.tlsSend .handshake 40))
    (.sentAck .initial 0 0 [])) (.sentPacket .initial 1 false))
    (.sentFrameIn .handshake thePath (crypto 0 40))) (.sentAck .handshake 0 0 []))
    (.sentPacket .handshake 0 true)

-- From here on the state descends from a decoded packet, so the assertions are
-- `#guard` for the reason the header gives.
#guard fig5_5.hs.write.initial = Handshake.KeyState.discarded
#guard fig5_5.hs.read.initial = Handshake.KeyState.discarded
#guard fig5_5.hs.write.handshake = Handshake.KeyState.present
-- §13.1's bookkeeping has moved with it.
#guard fig5_5.ackHandshake.largestSent = some 0

/-- TLS reports completion and the 1-RTT keys.  For a client that is *not*
    confirmation (RFC 9001 §4.1.2; §19.20, line 8195). -/
private def fig5_6 : State :=
  tls (tls (tls fig5_5 .tlsComplete) (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)

#guard fig5_6.hs.complete = true
#guard fig5_6.hs.confirmed = false
-- §9, line 3280: "An endpoint MUST NOT initiate connection migration before the
-- handshake is confirmed."
#guard (step prot fig5_6 (.local (.migrate ⟨⟨5⟩, peerAddr⟩) 0) == Outcome.drop) = true

/-- `1-RTT[0]: STREAM[0, "..."], ACK[0] ->`.  The stream has to be opened first:
    `MaySend` is `false` on a stream the application never created (review S-5,
    the reason WP13 must synthesise `appOpenStream`). -/
private def fig5_7 : State := app (app fig5_6 (.openStream .bidi)) (.write ⟨0⟩ 5)

#guard maySendPacket fig5_7 ⟨.oneRtt, [.stream 0 0 false (filler 5)]⟩ = true
#guard maySendPacket fig5_6 ⟨.oneRtt, [.stream 0 0 false (filler 5)]⟩ = false

private def fig5_8 : State :=
  loc (loc (loc fig5_7 (.sentFrameIn .oneRtt thePath (.stream 0 0 false (filler 5))))
    (.sentAck .appData 0 0 [])) (.sentPacket .oneRtt 0 true)

private def srvFlight3 : List Frame :=
  [.handshakeDone, .stream 3 0 false (filler 5), .ack 0 0 0 #[] none]

/-- `<- 1-RTT[1]: HANDSHAKE_DONE, STREAM[3, "..."], ACK[0]` — the last line of
    Figure 5, and the one that confirms the handshake. -/
private def fig5_9 : State := recvNext fig5_8 1 srvFlight3

#guard outcomeErrorC (recv fig5_8 1 srvFlight3) = 0xffffffff
#guard outcomeCbsC (recv fig5_8 1 srvFlight3) =
  ["handshake_confirmed", "stream_open", "recv_stream_data"]

-- The point of the whole flow: the handshake is confirmed, in all three copies.
#guard fig5_9.hs.confirmed = true
#guard fig5_9.term.handshakeConfirmed = true
#guard fig5_9.mig.handshakeConfirmed = true
-- …and only now may the client migrate (§9.2, line 3345).
#guard (step prot fig5_9 (.local (.migrate ⟨⟨5⟩, peerAddr⟩) 0) != Outcome.drop) = true

/-! ## 12. §12.2: coalesced packets, and a packet that will not unprotect

Not one of the eight scripts — `conn_trace.c` sends one packet per datagram —
but writing them turned up a defect in the pipeline, so the case that reveals it
is kept.

§12.2, line 4619: "The receiver of coalesced QUIC packets MUST individually
process each QUIC packet and separately acknowledge them, as if they were
received as the payload of different UDP datagrams.  For example, if decryption
fails (because the keys are not available or any other reason), the receiver MAY
either discard or buffer the packet for later processing and MUST attempt to
process the remaining packets."

`Endpoint/Pipeline.lean` used to stop the loop at the first packet it could not
unprotect, quoting a sentence ("an endpoint MUST discard the remainder of the
datagram") that does not occur in draft-34 — the text says the opposite.  The
fix is in `recvPackets`, which now skips the failing packet and carries on;
`packetEndOf` is how it finds the next one.

ngtcp2 stops too (`conn_recv_cpkt` returns 0 on `NGTCP2_ERR_DISCARD_PKT`), so
the model is now deliberately stricter than the implementation it is tested
against, which PLAN §1's "spec fidelity beats provability" and PLAN §5's
"expected mismatches … should be listed in WP13's triage doc" both call for.
The case is unreachable through `conn_trace.c` as it stands — its stub AEAD
"verifies nothing", so decryption never fails.  `TRIAGE.md` `WP13-5`. -/

private def coalesced : ByteArray :=
  badHandshakePacket ++ dgram 0 [.stream 0 0 false abc]

-- The first packet really is undecryptable, and the datagram really is two
-- packets long.
#guard (Quic.decodePacket prot coalesced 8 0).isOk = false
#guard coalesced.size = badHandshakePacket.size + (dgram 0 [.stream 0 0 false abc]).size

-- The STREAM frame in the second packet is processed all the same.
#guard outcomeErrorC (recvOut srv coalesced) = 0xffffffff
#guard outcomeCbsC (recvOut srv coalesced) = ["stream_open", "recv_stream_data"]
#guard (recvNextB srv coalesced).st.recvTotal = 3

/-! ## 12b. The receive-path findings of `TRANSPORT_AUDIT_2026-09-18.md`

Four counterexamples the audit reproduced against the composed endpoint, each
now asserting the behaviour the text requires.  Like §12 they are out of
`conn_trace.c`'s reach, so they are regression checks for the model alone. -/

/-! ### D34-1 — §10.1, line 3841: only a packet "received and processed
successfully" restarts the idle timer -/

-- A Handshake packet that fails authentication leaves the idle timer alone …
#guard (recvNextB cli badHandshakePacket 12345).term.idleStart = cli.term.idleStart
#guard cli.term.idleStart ≠ 12345
-- … a packet that is processed restarts it, even one with no visible effect …
#guard (recvNextB cli (handshakeDgram 0 [.ping]) 12345).term.idleStart = 12345
#guard outcomeCbsC (recvOut cli (handshakeDgram 0 [.ping]) 12345) = []
-- … and so does a datagram in which only the *second* packet is processed.
#guard (recvNextB srv coalesced 12345).term.idleStart = 12345
-- §12.3's duplicate is discarded, not processed: no restart the second time.
#guard (recvNextB (recvNextB cli (handshakeDgram 0 [.ping]) 100)
          (handshakeDgram 0 [.ping]) 12345).term.idleStart = 100

/-! ### D34-2 — §17.2.5.2, line 6626: a Retry whose Retry Integrity Tag cannot
be validated is discarded -/

/-- A structurally valid Retry: Source Connection ID `c0 01 … 07` (not the
    client's original Destination Connection ID), a one-byte token, and sixteen
    bytes of `tag` as the Retry Integrity Tag. -/
private def retryBytes (tag : UInt8) : ByteArray :=
  bytes [0xf0, 0, 0, 0, 1, 8] ++ localCid ++ bytes [8] ++
    bytes [0xc0, 1, 2, 3, 4, 5, 6, 7] ++ bytes [1] ++ ⟨Array.replicate 16 tag⟩

private def fresh : State := init (cfgOf false)

-- The stub's valid tag (0xA5 × 16) is accepted; any other tag is not, and the
-- rejected Retry changes neither the token nor the idle timer.
#guard (recvNextB fresh (retryBytes 0xa5)).av.retriesAccepted = 1
#guard (recvNextB fresh (retryBytes 0)).av.retriesAccepted = 0
#guard (recvNextB fresh (retryBytes 0xff)).av.retriesAccepted = 0
#guard (recvNextB fresh (retryBytes 0) 12345).term.idleStart = fresh.term.idleStart
#guard outcomeCbsC (recvOut fresh (retryBytes 0xa5)) = ["recv_retry"]
#guard outcomeCbsC (recvOut fresh (retryBytes 0)) = []

/-! ### D34-3 — §14.1, line 5727: an Initial in a datagram under 1200 bytes is
discarded wherever in the datagram it sits -/

private def mixed : ByteArray := handshakeDgram 0 [.ping] ++ initialDgram 0 [.ping]
private def freshSrv : State := init (cfgOf true)

#guard mixed.size < 1200
-- The Initial behind the Handshake packet is not recorded as received …
#guard (recvNextB freshSrv mixed 100).ackInitial.received = []
-- … §14.1, line 5729's PROTOCOL_VIOLATION close is permitted as well …
#guard accepts prot freshSrv (dgEvent mixed 100) (.error .protocolViolation) = true
-- … and the same two packets padded out to 1200 bytes are both processed.
#guard (recvNextB freshSrv (mixed ++ ⟨Array.replicate (1200 - mixed.size) 0⟩) 100
          ).ackInitial.received = [⟨0, 0⟩]

/-! ### B3 (audit 2026-09-19) — §14, line 5697 permits discarding a datagram
"that does not meet size constraints", and no other -/

/-- `DIFFERENCES.md` A2's frame: a NEW_CONNECTION_ID whose Retire Prior To
    exceeds its Sequence Number (§19.15, line 7993: FRAME_ENCODING_ERROR), with
    a sequence number already seen. -/
private def badNcid : Frame := .newConnectionId 0 2 (cidOf 0xc1) (tokOf 0x11)

-- An authenticated, processable packet carrying it has the error as its *only*
-- outcome: it can no longer be evaded through `DatagramSize`.
#guard (outcomes prot cli (dgEvent (dgram 0 [badNcid]))).all (outcomeErrorC · == 7)
#guard accepts prot cli (dgEvent (dgram 0 [badNcid])) .drop = false
-- A PATH_CHALLENGE in a datagram under 1200 bytes fails §8.2.1 line 3154's size
-- constraint, so discarding that datagram is still permitted …
private def challenge : Frame := .pathChallenge ⟨Array.replicate 8 7⟩
#guard requiredSize prot srv (dgram 0 [challenge]) = 1200
#guard accepts prot srv (dgEvent (dgram 0 [challenge])) .drop = true
-- … never closing on it (§14, line 5695) …
#guard (outcomes prot srv (dgEvent (dgram 0 [challenge]))).all (outcomeErrorC · == 0xffffffff)
-- … and not once it is expanded.
#guard accepts prot srv (dgEvent (dgram 0 [challenge, .padding 1200])) .drop = false
-- The discards other rules permit are untouched.  §12.3: a duplicate packet is
-- not processed again …
#guard outcomeCbsC (recvOut (recvNext srv 0 [.stream 0 0 false abc]) (dgram 0 [.stream 0 0 false abc]))
          = []
-- §12.3, line 4717: a packet older than the largest one processed may have
-- fallen below a minimum packet number, so it may be dropped whatever it carries
-- (`Pipeline.minimumRaised`) — but not the newest packet, and not the first.
private def srvAt9 : State := recvNext srv 9 [.ping]
#guard (outcomes prot srvAt9 (dgEvent (dgram 3 [badNcid]))).any
          (fun o => match o with | .ok s' _ => s'.ackAppData.minPn == 4 | _ => false)
#guard (outcomes prot srvAt9 (dgEvent (dgram 10 [badNcid]))).all (outcomeErrorC · == 7)
-- … and §12.2 line 4619: skipping an undersized Initial (D34-3 above) or an
-- unreadable packet (D34-4 below) still leaves the packets behind it processed.

/-! ### B1 (audit 2026-09-19) — §7.5: a CRYPTO frame the buffer cannot hold

`recv app 0 0680030003100000…` — CRYPTO offset 196611, length 16, after the
handshake.  Sixteen payload bytes, a reordering span of 196627
(`Handshake.BufferPolicy`). -/

private def farCrypto : Frame := .crypto 196611 ⟨Array.replicate 16 0⟩

-- Both engines close with CRYPTO_BUFFER_EXCEEDED (13), which is permitted …
#guard acceptsC cli (dgEvent (dgram 0 [farCrypto])) (.error .cryptoBufferExceeded) = 1
-- … as is discarding the frame (line 2716).  That is not a packet-level drop:
-- line 2719, "Packets containing discarded CRYPTO frames MUST be acknowledged",
-- so the packet is processed and its number becomes acknowledgeable.
#guard (outcomes prot cli (dgEvent (dgram 0 [farCrypto]))).any (fun o =>
  match o with
  | .ok s' fx => fx.contains (.hs (.cryptoDiscarding .oneRtt)) &&
      fx.contains .packetProcessed && s'.ackAppData.received == [⟨0, 0⟩]
  | _ => false)
#guard accepts prot cli (dgEvent (dgram 0 [farCrypto])) .drop = false
-- In-order CRYPTO data is never a buffer error.
#guard (outcomes prot cli (dgEvent (dgram 0 [.crypto 0 ⟨Array.replicate 16 0⟩]))).all
  (outcomeErrorC · == 0xffffffff)

/-! ### B6 (audit 2026-09-19) — reaching the final size without new bytes is a
FIN-bearing read, in the observation layer only -/

-- `recv app 0 0f070000`: STREAM id=7 off=0 len=0 fin.  Both engines hand the
-- application a zero-length read with fin set.  The model's effects are
-- unchanged — completion, and no `dataAvailable`, because no byte arrived …
#guard match recv cli 0 [.stream 7 0 true .empty] with
  | .ok _ fx => !deliversData fx ⟨7⟩ | _ => false
-- … and the observation of that completion is the read.
#guard outcomeCbsC (recv cli 0 [.stream 7 0 true .empty])
          = ["stream_open", "recv_stream_data", "stream_close"]
-- Data with FIN is one read, as before: the FIN rides on the data.
#guard outcomeCbsC (recv cli 0 [.stream 7 0 true abc])
          = ["stream_open", "recv_stream_data", "stream_close"]
-- A FIN that arrives after the data is a second read, with nothing in it …
#guard outcomeCbsC (recvOut (recvNext cli 0 [.stream 7 0 false abc]) (dgram 1 [.stream 7 3 true .empty]))
          = ["recv_stream_data", "stream_close"]
-- … and repeating it is neither a read nor a second completion.
#guard outcomeCbsC (recvOut (recvNext cli 0 [.stream 7 0 true .empty]) (dgram 1 [.stream 7 0 true .empty]))
          = []

/-! ### D34-4 — §12.2, line 4619: a packet too short for a header-protection
sample does not stop the coalesced packets after it -/

/-- A Handshake long header whose Length is 1: the extent is known, the sample
    cannot be taken. -/
private def shortSample : ByteArray :=
  bytes [0xe0, 0, 0, 0, 1, 8] ++ localCid ++ bytes [8] ++ peerCid ++ bytes [1, 0]

#guard match parseOne prot cli shortSample 0 with
  | .error .tooShortForSample => true | _ => false
#guard (recvNextB cli (shortSample ++ handshakeDgram 1 [.ping])).ackHandshake.received
          = [⟨1, 1⟩]
-- On its own it is simply skipped.
#guard outcomeRenderC (recvOut cli shortSample) = "OK [dsz_deliver; skipped_rest]"

/-! ### D34-5 — §4.1, line 1330: the frames of one packet or datagram spend the
connection's send credit together, not each against the same state -/

private def creditCli : State :=
  let cfg := cfgOf false
  let s := tls (tls (tls (tls (tls (init { cfg with theirs := { cfg.theirs with maxData := 10 } })
    (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)) .tlsComplete
  app (app (app (app s (.openStream .bidi)) (.openStream .bidi)) (.write ⟨0⟩ 6)) (.write ⟨4⟩ 6)

private def six (id : Nat) (offset : Nat := 0) : Frame := .stream id offset false (filler 6)

private def auditDg (fs : List (List Frame)) (src : Addr := selfAddr)
    (dcid : ByteArray := peerCid) : OutDatagram :=
  { size := 100, packets := fs.map (⟨.oneRtt, ·⟩), src := src, dest := peerAddr,
    dcid := some dcid.toList, scid := some localCid.toList }

-- Each six-byte frame fits the ten bytes of credit; the two together do not,
-- in one packet or coalesced in one datagram.
#guard maySendPacket creditCli ⟨.oneRtt, [six 0]⟩ && maySendPacket creditCli ⟨.oneRtt, [six 4]⟩
#guard !maySendPacket creditCli ⟨.oneRtt, [six 0, six 4]⟩
#guard !maySendDatagram creditCli (auditDg [[six 0, six 4]])
#guard !maySendDatagram creditCli (auditDg [[six 0], [six 4]])
#guard maySendDatagramWhy creditCli (auditDg [[six 0], [six 4]]) = ["StreamTable.maySendAll"]
-- A stream is counted once, up to its highest offset: the same six bytes twice
-- (a retransmission in the same datagram) cost six, and 0–6 with 4–10 costs ten.
#guard maySendPacket creditCli ⟨.oneRtt, [six 0, six 0]⟩
#guard maySendPacket { creditCli with st := { creditCli.st with maxDataPeer := 100 } }
    ⟨.oneRtt, [six 0, six 0 4]⟩ = false  -- the stream wrote six bytes, not ten
#guard StreamTable.batchIncrease creditCli.st [(⟨0⟩, 6), (⟨0⟩, 10), (⟨4⟩, 3), (⟨0⟩, 6)] = 13

/-! ### D34-6 — §5.1.2, line 1811: a Destination Connection ID the peer has made
us retire is not sendable, although §7.2 (`HandshakeHeaderOk`) still lists it -/

private def newCid : ByteArray := bytes [0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7]

private def retiredCli : State :=
  recvNext cli 0 [.newConnectionId 1 1 newCid (bytes (List.replicate 16 1))]

#guard retiredCli.cidRemote.isRetired 0
#guard maySendDatagram cli (auditDg [[.ping]])
#guard !maySendDatagram retiredCli (auditDg [[.ping]])
#guard (maySendDatagramWhy retiredCli (auditDg [[.ping]])).map (fun w => (w.splitOn "(").head!) = ["dcidOk"]
#guard maySendDatagram retiredCli (auditDg [[.ping]] (dcid := newCid))
-- A connection ID the peer never issued is not one either (§5.1, line 1668).
#guard !maySendDatagram cli (auditDg [[.ping]] (dcid := bytes [1,2,3,4,5,6,7,8]))

/-! ### D34-7 — §9.5, line 3603: `Migration`'s connection-ID history is
consulted with the sequence number WP4 holds for the datagram's bytes -/

private def confirmedCli : State := recvNext cli 0 [.handshakeDone]
private def issuedCli : State :=
  recvNext confirmedCli 1 [.newConnectionId 1 0 newCid (bytes (List.replicate 16 1))]

#guard confirmedCli.hs.confirmed
#guard dcidSeq? issuedCli newCid.toList = some 1
-- Sequence number 0 has left from local address 0, so it may not leave from 2;
-- sequence number 1 has left from nowhere yet.
#guard !maySendDatagram issuedCli (auditDg [[.ping]] (src := ⟨2⟩))
#guard (maySendDatagramWhy issuedCli (auditDg [[.ping]] (src := ⟨2⟩))).map (fun w => (w.splitOn "(").head!) = ["dcidOk"]
#guard maySendDatagram issuedCli (auditDg [[.ping]] (src := ⟨2⟩) (dcid := newCid))
-- … and once it has (`LocalAction.beginSendOn`), it may not come back to 0.
#guard !maySendDatagram (loc issuedCli (.beginSendOn ⟨⟨2⟩, peerAddr⟩ 1)) (auditDg [[.ping]] (dcid := newCid))

/-! ### WP13-4 — §19.16, line 8050: a RETIRE_CONNECTION_ID does not name the
Destination Connection ID of the packet that carries it -/

-- `issuedCli` holds sequence numbers 0 (`peerCid`) and 1 (`newCid`), both
-- active, so a first retirement of either passes `ConnIds.Remote.MaySend`.
#guard maySend issuedCli (.retireConnectionId 0) && maySend issuedCli (.retireConnectionId 1)
#guard !maySendDatagram issuedCli (auditDg [[.retireConnectionId 0]])
#guard maySendDatagramWhy issuedCli (auditDg [[.retireConnectionId 0]]) = ["retireNotSelf"]
#guard maySendDatagram issuedCli (auditDg [[.retireConnectionId 1]])
#guard maySendDatagram issuedCli (auditDg [[.retireConnectionId 0]] (dcid := newCid))
#guard !maySendDatagram issuedCli (auditDg [[.retireConnectionId 1]] (dcid := newCid))
-- Every coalesced packet shares the connection ID.
#guard !maySendDatagram issuedCli (auditDg [[.ping], [.ping, .retireConnectionId 0]])
-- The usual order: retire 0 (`retiredCli`), then send its frame under 1.
#guard maySendDatagram retiredCli (auditDg [[.retireConnectionId 0]] (dcid := newCid))

/-! ## 13. The phase gate, and what a closing endpoint may send -/

private def withPhase (s : State) (p : Termination.Phase) : State :=
  { s with term := { s.term with phase := p } }

/-- §10.2.2, line 4023: a draining endpoint processes nothing and sends
    nothing. -/
private def srvDraining : State := withPhase srv .draining

#guard outcomeCbsC (recv srvDraining 0 [.stream 0 0 false abc]) = []
#guard outcomeErrorC (recv srvDraining 0 [.handshakeDone]) = 0xffffffff
example : maySend srvDraining .ping = false := by decide
example : maySendPacket srvDraining ⟨.oneRtt, [.ping]⟩ = false := by decide

/-- §10.2.1, line 3965: a closing endpoint answers incoming packets with one
    containing a CONNECTION_CLOSE, and dispatches no frame. -/
private def srvClosing : State :=
  { srv with term :=
      { srv.term with phase := Termination.Phase.closing,
                      closedWith := some (.transport .protocolViolation 0) } }

#guard outcomeRenderC (recv srvClosing 0 [.stream 0 0 false abc]) =
  "OK [send_connection_close; send_pending CONNECTION_CLOSE kind=transport err=10 ftype=0 reason=]"
-- §10.2.3, line 4056: the handshake is confirmed, so the close goes in a 1-RTT
-- packet and in no other.
example : maySendPacket srvClosing
    ⟨.oneRtt, [.connectionClose 10 (some 0) ByteArray.empty]⟩ = true := by decide
example : maySendPacket srvClosing
    ⟨.handshake, [.connectionClose 10 (some 0) ByteArray.empty]⟩ = false := by decide
example : maySendPacket srvClosing ⟨.oneRtt, [.ping]⟩ = false := by decide

/-! ## 14. §8, line 2735: the anti-amplification budget -/

private def outDg (size : Nat) (fs : List Frame) : OutDatagram :=
  { size, packets := [⟨.oneRtt, fs⟩], dest := peerAddr, src := selfAddr }

-- Nothing has been received from the peer yet, so a server's budget is zero.
example : maySendDatagram srv (outDg 1 [.ping]) = false := by decide
-- After a 35-byte datagram arrives, up to three times as many bytes may go
-- back: 60 is within the budget and 100000 is not.
#guard maySendDatagram srv01 (outDg 60 [.ping]) = true
#guard maySendDatagram srv01 (outDg 100000 [.ping]) = false
-- §8.1, line 2818: "Clients are only constrained by the congestion controller."
example : maySendDatagram cli (outDg 1200 [.ping]) = true := by decide

/-! ## 15. §13.4.2.2, line 5626: ECN, once validation has failed -/

private def srvEcnFailed : State :=
  { srv01 with ecnAppData := { srv01.ecnAppData with phase := .failed } }

#guard maySendDatagram srv01 { outDg 60 [.ping] with isEcnMarked := true } = true
#guard maySendDatagram srvEcnFailed { outDg 60 [.ping] with isEcnMarked := true } = false
#guard maySendDatagram srvEcnFailed (outDg 60 [.ping]) = true

/-! ## NOTES

1. **`stream_close` (script 01).**  The model's
   `Stream.Recv.Effect.allDataReceived` renders as the callback name
   `stream_close`; ngtcp2 fires `stream_close` only once *both* directions of the
   stream are closed, so its trace for the second packet of script 01 has
   `recv_stream_data` alone.  Neither is a spec question — §2.4 leaves the API
   entirely to the implementation and PLAN §4a records that "the spec says
   nothing about application callbacks".  Recorded as `WP13-1` in `TRIAGE.md`:
   WP13 must compare `stream_close` loosely, not as a mismatch.

2. **`stream_stop_sending` (script 07).**  `Effect.cbName` maps
   `Stream.Recv.Effect.stopSendingRequested` to `none`, but `conn_trace.c` does
   print a `CB stream_stop_sending id= app_error_code=` line — at the moment the
   STOP_SENDING frame is *written*, not when the application calls
   `shutdown_stream_read`.  The model has no separate "this frame went out" step
   for STOP_SENDING that produces an effect, so equating the two would compare
   events at different points of the trace.  Left as `none`; recorded as
   `WP13-2`.

3. **Datagram discard (fixed, audit 2026-09-19 B3).**  `DatagramSize.Step.datagramDiscard`
   used to permit `.drop` for *any* received datagram, so every scenario's
   `outcomes` ended in `DROP` and a trace in which ngtcp2 silently ignored a
   datagram could never falsify the model (`WP13-3`).  The discard is now gated
   on `DatagramSize.FailsSizeConstraint`, with the constraint read off the
   datagram's frames by `Pipeline.requiredSize`; §8 "B3" above asserts both
   directions.

4. **The post-handshake state.**  There is no `init`-with-keys variant; the five
   TLS events of `postHandshake` are how `Endpoint.State` is put where
   `conn_trace.c` forces `ngtcp2_conn`.  The one visible difference is that the
   model's *client* leaves `Handshake.State.confirmed = false` until a
   HANDSHAKE_DONE arrives, while `conn_trace.c` forces the connection past the
   handshake for both roles; scripts 07 and 08 never depend on the bit, and
   script 06's client half asserts the transition explicitly.

5. **What could not be expressed.**  Nothing in the eight scripts.  Three things
   the traces show are outside the model by construction and are therefore not
   asserted here: `CB update_key` (RFC 9001 §6 key update, out of scope
   throughout), `CB get_new_connection_id2` (the model issues connection IDs only
   when the endpoint decides to, through `LocalAction.issueCid`; *when* to do so
   is not a transport MUST), and the `TIME … expiry=` column (RFC 9002 timers are
   out of scope, and `Endpoint.State.pto` is carried rather than computed).

6. **A defect the examples turned up.**  §12 above is a case none of the eight
   scripts reaches, kept because writing it showed `Endpoint.recvPackets` to be
   stricter than §12.2 line 4619.  The fix is described there and in `TRIAGE.md`
   `WP13-5`; it is the only change this layer made outside `Examples.lean`,
   apart from doc comments.

7. **Citations corrected while writing this file** (the draft the previous run
   left behind had them wrong, and they are fixed above): §4.6's "Endpoints MUST
   NOT exceed the limit set by their peer" is line 1546, not 1553; §4.5's "More
   generally, this is one higher than the offset of the byte with the largest
   offset sent" is line 1481, not 1479; §19.11's MAX_STREAMS bound is line 7803,
   not 7802; "A server MUST treat receipt of a HANDSHAKE_DONE frame" is
   line 8208, while line 8207 is the sentence before it; and §12.2's coalescing
   sentences are lines 4597, 4606 and 4619 — the "line 4622" `Pipeline.lean` and
   `Basic.lean` cited carried a sentence that is not in the draft at all.
-/

end Quic.Spec.Endpoint.Examples
