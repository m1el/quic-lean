import QuicModel.Spec.Core

/-
  WP14 (b), part 1: the vocabulary of §13.4 — codepoints, markings, the ECN
  state of a path, and the per-space counting state.  See `Spec/Ecn.lean` for
  the package's header, coverage table and notes.
-/
namespace Quic.Spec.Ecn

/-! ## 1. State, events, effects -/

/-- The ECN field of an IP header (RFC 3168), as §13.4.1, line 5509 reads it. -/
inductive Codepoint where
  | notEct | ect0 | ect1 | ce
  deriving DecidableEq, Repr

def Codepoint.ect0Delta : Codepoint → Nat | .ect0 => 1 | _ => 0
def Codepoint.ect1Delta : Codepoint → Nat | .ect1 => 1 | _ => 0
def Codepoint.ceDelta : Codepoint → Nat | .ce => 1 | _ => 0

/-- What an endpoint may set on a packet it sends: §13.4.2, line 5539 "The
    endpoint sets an ECT(0) codepoint in the IP header of early outgoing packets
    sent on a new path", and line 5568 "Implementations that use the ECT(1)
    codepoint need to perform ECN validation using the reported ECT(1) counts."
    An endpoint never sets CE itself. -/
inductive Mark where
  | notEct | ect0 | ect1
  deriving DecidableEq, Repr

def Mark.ect0Delta : Mark → Nat | .ect0 => 1 | _ => 0
def Mark.ect1Delta : Mark → Nat | .ect1 => 1 | _ => 0
def Mark.isMarked : Mark → Bool | .notEct => false | _ => true

/-- The ECN state of a path.  The four names are Appendix A.4's (line 10257),
    which §13.4.2, line 5563 points at; A.4 is explicitly informative
    ("Endpoints can implement different methods"), so the transitions between
    `testing` and `unknown`, and from `unknown` to `capable`, are permissions
    rather than requirements (NOTE 3). -/
inductive Phase where
  | testing | unknown | capable | failed
  deriving DecidableEq, Repr

/-- §13.4.2.2, line 5626: once validation has failed the endpoint stops setting
    ECT codepoints. -/
def Phase.marksPackets : Phase → Bool
  | .testing | .capable => true
  | .unknown | .failed => false

/-- Appendix A.4, line 10272: "After the testing period ends, the ECN state for
    the path becomes "unknown"." -/
def Phase.afterTesting : Phase → Phase
  | .testing => .unknown
  | p => p

/-- §13.4.2.1, line 5578: "Any increase in the ECN counts is validated based on
    the ECN markings that were applied to packets that are newly acknowledged in
    the ACK frame."  The markings are RFC 9002's record of what went out, so
    they arrive on the event. -/
structure NewlyAcked where
  /-- How many packets the ACK frame newly acknowledges. -/
  total : Nat
  /-- …of which this many were sent with ECT(0). -/
  ect0 : Nat
  /-- …and this many with ECT(1). -/
  ect1 : Nat
  deriving DecidableEq, Repr

/-- §13.4.2, line 5561: "An endpoint thus attempts to use ECN and validates this
    for each new connection, when switching to a server's preferred address, and
    on active connection migration to a new path"; §13.4.2.2, line 5630: "Even
    if validation fails, an endpoint MAY revalidate ECN for the same path at any
    later time in the connection." -/
inductive Trigger where
  | newConnection | preferredAddress | migration | revalidation
  deriving DecidableEq, Repr

structure State where
  /-- §13.4.1, line 5514: "Each packet number space maintains separate
      acknowledgment state and separate ECN counts."  One instance per space
      (NOTE 1). -/
  space : PnSpace
  /-- §13.4.1, line 5500: "If an endpoint does not implement ECN support or does
      not have access to received ECN fields, it does not report ECN counts for
      packets it receives." -/
  reportsEcn : Bool := true
  /-- §13.4.1, line 5509 and §19.3.2, line 7407: the total number of packets
      received with each codepoint *in this packet number space*. -/
  ect0 : Nat := 0
  ect1 : Nat := 0
  ce : Nat := 0
  /-- §13.4.2.1, line 5577: the counts "from the last successfully processed ACK
      frame". -/
  peerEct0 : Nat := 0
  peerEct1 : Nat := 0
  peerCe : Nat := 0
  /-- §13.4.2.1, line 5613: the largest acknowledged packet number of the last
      ACK frame that was used for validation. -/
  largestAcked : Option Nat := none
  /-- §13.4.2 / Appendix A.4: the ECN state of the current path. -/
  phase : Phase := .testing
  /-- §13.4.2.1, line 5617: "the total number of packets sent with each
      corresponding ECT codepoint" on the path being validated. -/
  sentEct0 : Nat := 0
  sentEct1 : Nat := 0
  /-- ECN-marked packets that have been acknowledged, and ones declared lost
      (§13.4.2, line 5549). -/
  markedAcked : Nat := 0
  markedLost : Nat := 0
  deriving DecidableEq, Repr

/-- The number of ECN-marked packets sent on this path. -/
def State.markedSent (s : State) : Nat := s.sentEct0 + s.sentEct1

/-- The number of ECN-marked packets sent that are still unacknowledged. -/
def State.markedUnacked (s : State) : Nat := s.markedSent - s.markedAcked

inductive Event where
  /-- §13.4.1, line 5509: a QUIC packet of *this* packet number space was taken
      from an IP packet whose ECN field was `cp`.  `processed` is line 5524:
      "ECN counts are only incremented when QUIC packets from the received IP
      packet are processed.  As such, duplicate QUIC packets are not processed
      and do not increase ECN counts."  Line 5515's coalescing is handled by
      there being one such event per QUIC packet, not per datagram. -/
  | recvPacket (cp : Codepoint) (processed : Bool)
  /-- A packet of this space went out with this ECN marking (§13.4.2, line 5539). -/
  | sentPacket (m : Mark)
  /-- §13.4.2.1: an ACK frame arrived, with or without ECN counts, newly
      acknowledging packets whose markings `newly` records. -/
  | recvAck (largest : Nat) (counts : Option Ecn) (newly : NewlyAcked)
  /-- §13.4.2, line 5549: RFC 9002 declared `n` further ECN-marked packets lost. -/
  | lostMarked (n : Nat)
  /-- §13.4.2, line 5561 / §13.4.2.2, line 5630: (re)start validation. -/
  | beginValidation (trigger : Trigger)
  /-- Appendix A.4, line 10265: "The testing period runs for a number of packets
      or a limited time, as determined by the endpoint."  §13.4.2, line 5553
      suggests "the first ten outgoing packets on a path, or … three PTOs". -/
  | testingEnded
  deriving DecidableEq, Repr

inductive Effect where
  /-- §13.4.2.1: validation failed. -/
  | ecnValidationFailed
  /-- §13.4.2.2, line 5626: "If validation fails, then the endpoint MUST disable
      ECN.  It stops setting the ECT codepoint in IP packets that it sends". -/
  | disableEcn
  /-- §13.4.2.2, line 5634: "Upon successful validation, an endpoint MAY continue
      to set an ECT codepoint in subsequent packets it sends". -/
  | ecnValidated
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

end Quic.Spec.Ecn
