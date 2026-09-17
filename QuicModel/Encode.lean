import QuicModel.Frame

/-
  Frame encoder.  Canonical choices: every integer uses its shortest varint
  encoding; STREAM frames always carry a Length and carry an Offset iff it is
  non-zero.  `Frame.WF` is what the encoder needs for the result to decode back.
-/
namespace Quic

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

abbrev vi := encodeVarint

def encodeAckRanges : List AckRange → ByteArray
  | [] => .empty
  | r :: rs => vi r.gap ++ (vi r.len ++ encodeAckRanges rs)

/-- The frame type, which for every frame in the model fits one byte. -/
def Frame.typeByte : Frame → UInt8
  | .padding _ => 0x00
  | .ping => 0x01
  | .ack _ _ _ _ ecn => if ecn.isSome then 0x03 else 0x02
  | .resetStream .. => 0x04
  | .stopSending .. => 0x05
  | .crypto .. => 0x06
  | .newToken _ => 0x07
  -- 0x08 | OFF 0x04 | LEN 0x02 | FIN 0x01; LEN is always set
  | .stream _ off fin _ =>
    if off ≠ 0 then (if fin then 0x0f else 0x0e) else (if fin then 0x0b else 0x0a)
  | .maxData _ => 0x10
  | .maxStreamData .. => 0x11
  | .maxStreams .bidi _ => 0x12
  | .maxStreams .uni _ => 0x13
  | .dataBlocked _ => 0x14
  | .streamDataBlocked .. => 0x15
  | .streamsBlocked .bidi _ => 0x16
  | .streamsBlocked .uni _ => 0x17
  | .newConnectionId .. => 0x18
  | .retireConnectionId _ => 0x19
  | .pathChallenge _ => 0x1a
  | .pathResponse _ => 0x1b
  | .connectionClose _ (some _) _ => 0x1c
  | .connectionClose _ none _ => 0x1d
  | .handshakeDone => 0x1e
  | .datagram false _ => 0x30
  | .datagram true _ => 0x31

/-- Everything after the type byte. -/
def Frame.encodeBody : Frame → ByteArray
  | .padding len => ⟨Array.replicate (len - 1) 0⟩
  | .ping | .handshakeDone => .empty
  | .ack largest delay first ranges ecn =>
    vi largest ++ (vi delay ++ (vi ranges.size ++ (vi first ++
      (encodeAckRanges ranges.toList ++
        (match ecn with
         | some e => vi e.ect0 ++ (vi e.ect1 ++ vi e.ce)
         | none => .empty)))))
  | .resetStream id err fs => vi id ++ (vi err ++ vi fs)
  | .stopSending id err => vi id ++ vi err
  | .crypto off data => vi off ++ (vi data.size ++ data)
  | .newToken token => vi token.size ++ token
  | .stream id off _ data =>
    vi id ++ ((if off ≠ 0 then vi off else .empty) ++ (vi data.size ++ data))
  | .maxData v | .dataBlocked v | .maxStreams _ v | .streamsBlocked _ v
  | .retireConnectionId v => vi v
  | .maxStreamData id v | .streamDataBlocked id v => vi id ++ vi v
  | .newConnectionId seq rpt cid token =>
    vi seq ++ (vi rpt ++ (bytes [cid.size.toUInt8] ++ (cid ++ token)))
  | .pathChallenge d | .pathResponse d => d
  | .connectionClose err (some fty) reason => vi err ++ (vi fty ++ (vi reason.size ++ reason))
  | .connectionClose err none reason => vi err ++ (vi reason.size ++ reason)
  | .datagram false data => data
  | .datagram true data => vi data.size ++ data

def encodeFrame (f : Frame) : ByteArray := bytes [f.typeByte] ++ f.encodeBody

/-- Frames whose end is visible from their own bytes.  The other two absorb
    whatever follows: a PADDING run swallows further zero bytes, and DATAGRAM
    without a Length runs to the end of the packet. -/
def Frame.SelfDelimiting : Frame → Prop
  | .padding _ | .datagram false _ => False
  | _ => True

/-- Frames the wire format can represent. -/
def Frame.WF : Frame → Prop
  | .padding len => 1 ≤ len
  | .ping | .handshakeDone => True
  | .ack largest delay first ranges ecn =>
    largest ≤ maxVarint ∧ delay ≤ maxVarint ∧ first ≤ maxVarint ∧ ranges.size ≤ maxVarint ∧
    (∀ r ∈ ranges.toList, r.gap ≤ maxVarint ∧ r.len ≤ maxVarint) ∧
    (∀ e, ecn = some e → e.ect0 ≤ maxVarint ∧ e.ect1 ≤ maxVarint ∧ e.ce ≤ maxVarint)
  | .resetStream id err fs => id ≤ maxVarint ∧ err ≤ maxVarint ∧ fs ≤ maxVarint
  | .stopSending id err => id ≤ maxVarint ∧ err ≤ maxVarint
  | .crypto off data => off ≤ maxVarint ∧ data.size ≤ maxVarint
  | .newToken token => token.size ≤ maxVarint
  | .stream id off _ data => id ≤ maxVarint ∧ off ≤ maxVarint ∧ data.size ≤ maxVarint
  | .maxData v | .dataBlocked v | .maxStreams _ v | .streamsBlocked _ v
  | .retireConnectionId v => v ≤ maxVarint
  | .maxStreamData id v | .streamDataBlocked id v => id ≤ maxVarint ∧ v ≤ maxVarint
  | .newConnectionId seq rpt cid token =>
    seq ≤ maxVarint ∧ rpt ≤ maxVarint ∧ 1 ≤ cid.size ∧ cid.size ≤ 20 ∧ token.size = 16
  | .pathChallenge d | .pathResponse d => d.size = 8
  | .connectionClose err fty reason =>
    err ≤ maxVarint ∧ (∀ t, fty = some t → t ≤ maxVarint) ∧ reason.size ≤ maxVarint
  | .datagram _ data => data.size ≤ maxVarint

def encodeFrames (fs : Array Frame) : ByteArray :=
  fs.foldl (fun acc f => acc ++ encodeFrame f) .empty

end Quic
