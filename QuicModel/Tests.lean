import QuicModel.Dump

/-
  Test vectors taken from the text of RFC 9000, checked at build time.
-/
namespace Quic.Tests

private def varintOf (bytes : List UInt8) : Option Nat :=
  match P.varint.run ⟨bytes.toArray⟩ with
  | .ok (v, _) => some v
  | .error _ => none

-- RFC 9000 §A.1 / §16 sample encodings
example : varintOf [0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c] = some 151288809941952652 := by native_decide
example : varintOf [0x9d, 0x7f, 0x3e, 0x7d] = some 494878333 := by native_decide
example : varintOf [0x7b, 0xbd] = some 15293 := by native_decide
example : varintOf [0x25] = some 37 := by native_decide
example : varintOf [0x40, 0x25] = some 37 := by native_decide
example : varintOf [0x40] = none := by native_decide

-- encode ∘ decode on the boundaries of each length class
example : [0, 63, 64, 16383, 16384, 1073741823, 1073741824, maxVarint].all
    (fun v => varintOf (encodeVarint v).data.toList == some v) = true := by native_decide

-- RFC 9000 §A.3: largest 0xa82f30ea, 16-bit truncation 0x9b32
example : decodePacketNumber (0xa82f30ea + 1) 0x9b32 2 = 0xa82f9b32 := by native_decide

-- §12.4: a frame type must use its shortest encoding (0x4001 is a 2-byte PING)
example : dumpFrames ⟨#[0x40, 0x01]⟩ (verbose := true) = "ERR non-minimal-frame-type 1\n" := by
  native_decide
example : dumpFrames ⟨#[0x01, 0x00, 0x00, 0x1e]⟩ = "PING n=1\nPADDING len=2 n=2\nHANDSHAKE_DONE n=1\nEND\n" := by
  native_decide

-- draft-34 §17.3.1: a 1-RTT packet with the fixed bit clear is discarded,
-- unless grease_quic_bit (RFC 9287) was negotiated.  Bytes: first byte, 4-byte
-- DCID, 1-byte packet number, PING + 2 PADDING, 16-byte stub tag.  The header
-- protection mask is the first five bytes of the sample, here all 0xa5.
private def shortPkt (b0 : UInt8) : ByteArray :=
  ⟨#[b0, 1, 2, 3, 4, 0x07, 0x01, 0x00, 0x00] ++ Array.replicate 16 0xa5⟩

example : dumpPacket (shortPkt (0x40 ^^^ 0x05)) 4 16 0 (verbose := true) =
    "SHORT fixed=1 dcid=01020304 hdlen=5\nPN pn=162 pnlen=1 keyphase=0\nPING n=1\nPADDING len=2 n=2\nNEXT 25\n" := by
  native_decide
example : dumpPacket (shortPkt (0x00 ^^^ 0x05)) 4 16 0 (verbose := true) =
    "PKT ERR fixed bit clear\n" := by native_decide

end Quic.Tests
