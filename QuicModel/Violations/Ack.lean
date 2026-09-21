import QuicModel.Spec.Ack
import QuicModel.Spec.FrameRules
import QuicModel.Violations.Trace

/-!
  One manufactured violation per executable Ack requirement.
  `must` is a MUST / MUST NOT: the checker has to reject it.
  `advice` is a SHOULD / MAY: ignoring it has to stay accepted.
-/
namespace Quic.Violations.Ack

open Quic Quic.Spec

def s0 : Ack.State := {
  space := .appData
  received := []
  minPn := 0
  largest := none
  largestTime := 0
  largestAckEliciting := none
  outstanding := []
  ackImmediately := false
  largestSent := none
  maxAckDelay := 25000
}

def sent (pn : Nat) : Ack.State := { s0 with largestSent := some pn }

def saw (pn : Nat) : Ack.State :=
  { s0 with received := [{ lo := pn, hi := pn }], largest := some pn, largestTime := 0 }

def owe (sp : PnSpace) (arrived : Time) : Ack.State :=
  { s0 with space := sp, outstanding := [(0, arrived)], largestAckEliciting := some 0 }

def ackFrame (largest first : Nat) : Frame := .ack largest 0 first #[] none

def checks : List Trace := [
  -- §12.3: the next packet number does not increase.
  must "Ack §12.3 (4685)" (Ack.maySendPacketNumber (sent 5) 5 = false),
  -- §12.3: a packet number already used.
  must "Ack §12.3 (4692)" (Ack.maySendPacketNumber (sent 5) 3 = false),
  -- §17.1: a 1-byte packet number before any acknowledgment, for a number that needs two bytes.
  must "Ack §17.1 (6023)" (Ack.maySendPacketNumberSize s0 256 1 = false),
  -- §17.1: after an ack of 0, a 1-byte encoding of packet 200 is too small.
  must "Ack §17.1 (6027)" (Ack.maySendPacketNumberSize { s0 with largestAcked := some 0 } 200 1 = false),
  -- §12.3: the number 2^62-1 itself must not be sent.
  must "Ack §12.3 (4693)" (Ack.maySendPacketNumber s0 Ack.maxPn = false),
  -- §12.3: a duplicate is an error instead of a discard.
  must "Ack §12.3 (4709)" (Ack.component.accepts (saw 5) (.recvPacket 5 1 true) (.error .protocolViolation) = false),
  -- §13.1: an ACK names a packet that was never processed.
  must "Ack §13.1 (5020)" (Ack.ackFrameSendable s0 (ackFrame 1 1) = false),
  -- §13.1 SHOULD: discarding a detectable unsent ACK is not a permitted outcome.
  must "Ack §13.1 (5030)" (Ack.component.accepts { s0 with largestSent := some 0 }
      (.recvAck 5 0 []) .drop = false),
  -- §13.2.1: an ack-eliciting packet is still outstanding past max_ack_delay.
  must "Ack §13.2.1 (5064)" (Ack.ackOverdue (owe .appData 0) 25001 0 = true),
  -- §13.2.1: an Initial ack-eliciting packet is still outstanding after its arrival.
  must "Ack §13.2.1 (5075)" (Ack.ackOverdue (owe .initial 0) 1 0 = true),
  -- §13.2.1 SHOULD: not sending immediately is advice. The send predicate does not reject a PING.
  advice "Ack §13.2.1 (5101)" (Ack.maySend { (owe .appData 0) with ackImmediately := true } .ping = false),
  -- §13.2.2 SHOULD: two outstanding packets do not forbid the next send.
  advice "Ack §13.2.2 (5163)" (Ack.maySend { s0 with outstanding := [(0, 0), (1, 1)] } .ping = false),
  -- §13.2.6: an ACK in this space names a packet this space never received.
  must "Ack §13.2.6 (5293)" (Ack.maySendPacket s0 { ptype := .oneRtt, frames := [ackFrame 0 0] } = false),
  -- §13.2.6: a 0-RTT packet carries an ACK of application data.
  must "Ack §13.2.6 (5298)" (FrameRules.maySendIn .server .zeroRtt (ackFrame 0 0) = false),
  -- §19.3: a well-formed ACK (the ECN and non-ECN layouts share these numbers) is treated as malformed.
  must "Ack §19.3 (7236)" (Ack.component.accepts (saw 0) (.recvAck 0 0 []) (.error .frameEncodingError) = false),
  -- §19.3.1: First ACK Range larger than Largest Acknowledged, and the packet is accepted.
  must "Ack §19.3.1 (7375)" (Ack.component.accepts s0 (.recvAck 0 1 []) (.ok s0 []) = false),
]

end Quic.Violations.Ack
