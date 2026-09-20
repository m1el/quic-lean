import QuicModel.Spec.Endpoint.Events

/-!
  WP12 "Endpoint", part 6: **the send side**.

  Three predicates, each the conjunction of the merged components' own:

  * `MaySend s f` — the frame-level rules (`Component.MaySend`);
  * `MaySendPacket s p` — every component's `MaySendPacket`, plus `FrameRules`'
    packet-type table, plus `MaySend` applied to every frame in the packet
    and `StreamTable.MaySendAll` to all of them at once;
  * `MaySendDatagram s d` — every component's `MaySendDatagram`, plus
    `MaySendPacket` for every packet coalesced in it, plus the three rules the
    packages could not state from one state alone and left here:
    `PathValidation.maySendDatagramOn av` (§8.2.1 line 3154, §8.2.2 lines 3197
    and 3200), `Migration.MaySendDatagramOn av` (§9.3.1, line 3431) and
    §8.2.2 line 3183's "a PATH_RESPONSE frame MUST be sent on the network path
    where the PATH_CHALLENGE was received", which needs `OutDatagram.src` as
    well as `dest` (`PathValidation` NOTES 11), and §7.2's connection ID fields
    (`Handshake.MaySendDatagramOn`), whose line 2380 needs WP4's issued
    connection IDs alongside WP11's state.

  Two rules belong to no single frame and no single component, so they are
  stated here over the whole unit being sent (third audit, D34-5 to D34-7):
  `StreamTable.MaySendAll`, §4.1 line 1330's connection credit for all the
  frames of a packet, and of a datagram, *together*; and `DcidOk`, which looks
  the datagram's Destination Connection ID up in WP4's `ConnIds.Remote` and
  asks that it is not retired (§5.1.2, line 1811) and that WP10's history
  allows it on this path (§9.5, lines 3603 and 3608).  `RetireNotSelf` uses the
  same lookup for §19.16 line 8050: no RETIRE_CONNECTION_ID for the connection
  ID the datagram itself carries (`TRIAGE.md` `WP13-4`).

  Three more rules are about things that are not datagrams of QUIC packets at
  all, so they stay free functions with their own arguments, exactly as WP5,
  WP6 and WP7 exported them: the Retry header (`maySendRetryHeader`), the
  Version Negotiation packet (`maySendVn`), and the Stateless Reset
  (`maySendStatelessReset`).
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-- Bookkeeping for one number, identical to `Ack.Step.sent`.  Send checks
    use a temporary state so coalesced packets cannot reuse a number. -/
def afterSendNumber (s : State) (sp : PnSpace) (pn : Nat) : State :=
  s.setAck sp { s.ack sp with largestSent := Ack.bumpSent (s.ack sp).largestSent pn }

/-- §12.3, lines 4685/4692: "Subsequent packets sent in the same packet
    number space MUST increase the packet number by at least one"; "MUST NOT
    reuse a packet number".  The list is in wire order, across all spaces. -/
def maySendNumbers (s : State) : List (PnSpace × Nat) → Bool
  | [] => true
  | (sp, pn) :: rest =>
    Ack.maySendPacketNumber (s.ack sp) pn &&
      maySendNumbers (afterSendNumber s sp pn) rest

/-- Relational counterpart: each number is below exhaustion and greater than
    the previous number in its own space, including earlier packets in this
    datagram. -/
def MaySendNumbers (s : State) : List (PnSpace × Nat) → Prop
  | [] => True
  | (sp, pn) :: rest =>
    ((∀ old ∈ (s.ack sp).largestSent, old < pn) ∧ pn < Ack.maxPn) ∧
      MaySendNumbers (afterSendNumber s sp pn) rest

theorem maySendNumbers_iff (s : State) (ns : List (PnSpace × Nat)) :
    maySendNumbers s ns = true ↔ MaySendNumbers s ns := by
  induction ns generalizing s with
  | nil => simp [maySendNumbers, MaySendNumbers]
  | cons n ns ih =>
    rcases n with ⟨sp, pn⟩
    simp only [maySendNumbers, MaySendNumbers, Bool.and_eq_true, ih,
      Ack.maySendPacketNumber]
    cases (s.ack sp).largestSent <;> simp

/-- Each accepted send strictly advances its space's largest sent number.
    Applying this at successive tails of `maySendNumbers` gives strict
    monotonicity throughout a datagram or a concatenated run. -/
theorem largestSent_strictMono_of_maySendNumbers {s : State} {sp : PnSpace}
    {pn old : Nat} {rest : List (PnSpace × Nat)}
    (h : maySendNumbers s ((sp, pn) :: rest) = true)
    (ho : (s.ack sp).largestSent = some old) :
    old < pn ∧ ((afterSendNumber s sp pn).ack sp).largestSent = some pn := by
  have hp := ((maySendNumbers_iff s _).mp h).1.1 old (by simp [ho])
  refine ⟨hp, ?_⟩
  simp [afterSendNumber, Ack.bumpSent, ho, Nat.max_eq_right (Nat.le_of_lt hp)]

/-- Checks can be split at datagram boundaries without losing history. -/
theorem maySendNumbers_append (s : State) (xs ys : List (PnSpace × Nat)) :
    maySendNumbers s (xs ++ ys) =
      (maySendNumbers s xs &&
        maySendNumbers (xs.foldl (fun st n => afterSendNumber st n.1 n.2) s) ys) := by
  induction xs generalizing s with
  | nil => simp [maySendNumbers]
  | cons n xs ih =>
    rcases n with ⟨sp, pn⟩
    simp [maySendNumbers, ih, Bool.and_assoc]

/-! ## 6.1 Frame level -/

/-- Six of the thirteen components govern a frame on its own; the other seven
    have `MaySend = True` by design, and their rules are packet- or
    datagram-level (`FrameRules` NOTES 8, `Ack` NOTES 15, `Migration` part 6). -/
def MaySend (s : State) (f : Frame) : Prop :=
  Handshake.MaySend s.hs f ∧ StreamTable.MaySend s.st f ∧
  ConnIds.Local.MaySend s.cidLocal f ∧ ConnIds.Remote.MaySend s.cidRemote f ∧
  PathValidation.MaySend s.pv f ∧ Termination.MaySend s.term f ∧
  Retransmission.MaySend s.rtx f

def maySend (s : State) (f : Frame) : Bool :=
  Handshake.maySend s.hs f && StreamTable.maySend s.st f &&
  ConnIds.Local.maySend s.cidLocal f && ConnIds.Remote.maySend s.cidRemote f &&
  PathValidation.maySend s.pv f && Termination.maySend s.term f &&
  Retransmission.maySend s.rtx f

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp only [maySend, MaySend, Bool.and_eq_true, Handshake.maySend_iff, StreamTable.maySend_iff,
    ConnIds.Local.maySend_iff, ConnIds.Remote.maySend_iff, PathValidation.maySend_iff,
    Termination.maySend_iff, Retransmission.maySend_iff, and_assoc]

instance instDecidableMaySend (s : State) (f : Frame) : Decidable (MaySend s f) :=
  decidable_of_iff _ (maySend_iff s f)

/-! ## 6.2 Packet level -/

/-- `Ack` has one instance per packet number space, and each instance's rule is
    conditioned on the packet belonging to *its* space, so all three apply. -/
def AckPacketOk (s : State) (p : OutPacket) : Prop :=
  Ack.MaySendPacket s.ackInitial p ∧ Ack.MaySendPacket s.ackHandshake p ∧
  Ack.MaySendPacket s.ackAppData p

def ackPacketOk (s : State) (p : OutPacket) : Bool :=
  Ack.maySendPacket s.ackInitial p && Ack.maySendPacket s.ackHandshake p &&
  Ack.maySendPacket s.ackAppData p

theorem ackPacketOk_iff (s : State) (p : OutPacket) :
    ackPacketOk s p = true ↔ AckPacketOk s p := by
  simp only [ackPacketOk, AckPacketOk, Bool.and_eq_true, Ack.maySendPacket_iff, and_assoc]

/-- §13.4.1, line 5509: the ECN counts an ACK frame reports are the ones of its
    own packet number space, so all three instances apply exactly as `Ack`'s
    do. -/
def EcnPacketOk (s : State) (p : OutPacket) : Prop :=
  Ecn.MaySendPacket s.ecnInitial p ∧ Ecn.MaySendPacket s.ecnHandshake p ∧
  Ecn.MaySendPacket s.ecnAppData p

def ecnPacketOk (s : State) (p : OutPacket) : Bool :=
  Ecn.maySendPacket s.ecnInitial p && Ecn.maySendPacket s.ecnHandshake p &&
  Ecn.maySendPacket s.ecnAppData p

theorem ecnPacketOk_iff (s : State) (p : OutPacket) :
    ecnPacketOk s p = true ↔ EcnPacketOk s p := by
  simp only [ecnPacketOk, EcnPacketOk, Bool.and_eq_true, Ecn.maySendPacket_iff, and_assoc]

def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  FrameRules.MaySendPacket s.fr p ∧ Handshake.MaySendPacket s.hs p ∧
  Termination.MaySendPacket s.term p ∧ Migration.MaySendPacket s.mig p ∧
  AckPacketOk s p ∧ EcnPacketOk s p ∧
  -- §4.1, line 1330: the connection credit the frames consume *together*;
  -- `MaySend` alone lets each frame spend the same remaining credit (D34-5)
  StreamTable.MaySendAll s.st p.frames ∧ ∀ f ∈ p.frames, MaySend s f

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  FrameRules.maySendPacket s.fr p && Handshake.maySendPacket s.hs p &&
  Termination.maySendPacket s.term p && Migration.maySendPacket s.mig p &&
  ackPacketOk s p && ecnPacketOk s p && StreamTable.maySendAll s.st p.frames &&
  p.frames.all (maySend s)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  simp only [maySendPacket, MaySendPacket, Bool.and_eq_true, FrameRules.maySendPacket_iff,
    Handshake.maySendPacket_iff, Termination.maySendPacket_iff, Migration.maySendPacket_iff,
    ackPacketOk_iff, ecnPacketOk_iff, StreamTable.maySendAll_iff, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun f hf => (maySend_iff s f).mp (h8 f hf)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, fun f hf => (maySend_iff s f).mpr (h8 f hf)⟩

instance instDecidableMaySendPacket (s : State) (p : OutPacket) : Decidable (MaySendPacket s p) :=
  decidable_of_iff _ (maySendPacket_iff s p)

/-! ## 6.3 Datagram level -/

/-- The path a datagram leaves on: §8.2, line 3075's two-tuple, built from
    `OutDatagram.src` and `OutDatagram.dest`. -/
def datagramPath (d : OutDatagram) : Migration.Path := ⟨⟨d.src.id⟩, d.dest⟩

/-- §8.2.2, line 3183: "A PATH_RESPONSE frame MUST be sent on the network path
    where the PATH_CHALLENGE was received."  `PathValidation.MaySendResponseOn`
    is the rule; this is it applied to one frame of a datagram
    (`PathValidation` NOTES 11). -/
def frameResponseOk (s : State) (pa : PathValidation.Path) : Frame → Prop
  | .pathResponse bs => PathValidation.MaySendResponseOn s.pv bs pa
  | _ => True

def frameResponseOkB (s : State) (pa : PathValidation.Path) : Frame → Bool
  | .pathResponse bs => PathValidation.maySendResponseOn s.pv bs pa
  | _ => true

theorem frameResponseOk_iff (s : State) (pa : PathValidation.Path) (f : Frame) :
    frameResponseOkB s pa f = true ↔ frameResponseOk s pa f := by
  cases f <;>
    simp [frameResponseOkB, frameResponseOk, PathValidation.maySendResponseOn_iff]

def PathResponsesOnPath (s : State) (d : OutDatagram) : Prop :=
  ∀ p ∈ d.packets, ∀ f ∈ p.frames, frameResponseOk s (s.pathOf (datagramPath d)) f

def pathResponsesOnPath (s : State) (d : OutDatagram) : Bool :=
  d.packets.all (fun p => p.frames.all (frameResponseOkB s (s.pathOf (datagramPath d))))

theorem pathResponsesOnPath_iff (s : State) (d : OutDatagram) :
    pathResponsesOnPath s d = true ↔ PathResponsesOnPath s d := by
  simp only [pathResponsesOnPath, PathResponsesOnPath, List.all_eq_true]
  constructor
  · intro h p hp f hf
    exact (frameResponseOk_iff _ _ f).mp (h p hp f hf)
  · intro h p hp f hf
    exact (frameResponseOk_iff _ _ f).mpr (h p hp f hf)

/-- §13.4.2.2, line 5626: "If validation fails, then the endpoint MUST disable
    ECN.  It stops setting the ECT codepoint in IP packets that it sends."
    `Ecn.MayMarkEcn` is per packet number space and `Spec.OutDatagram.isEcnMarked`
    is per datagram, so the datagram may be marked only if every instance allows
    it (`Ecn` NOTES 1 and 6). -/
def EcnMarkOk (s : State) (d : OutDatagram) : Prop :=
  Ecn.MayMarkEcn s.ecnInitial d.isEcnMarked ∧ Ecn.MayMarkEcn s.ecnHandshake d.isEcnMarked ∧
  Ecn.MayMarkEcn s.ecnAppData d.isEcnMarked

def ecnMarkOk (s : State) (d : OutDatagram) : Bool :=
  Ecn.mayMarkEcn s.ecnInitial d.isEcnMarked && Ecn.mayMarkEcn s.ecnHandshake d.isEcnMarked &&
  Ecn.mayMarkEcn s.ecnAppData d.isEcnMarked

theorem ecnMarkOk_iff (s : State) (d : OutDatagram) :
    ecnMarkOk s d = true ↔ EcnMarkOk s d := by
  simp only [ecnMarkOk, EcnMarkOk, Bool.and_eq_true, Ecn.mayMarkEcn_iff, and_assoc]

/-- §7.2, lines 2340, 2341 and 2380: the connection ID fields of the packets in
    a datagram, which WP11 states over `OutDatagram.dcid`/`scid` as
    `Handshake.MaySendDatagramOn`.  Line 2380 ("Any further changes to the
    Destination Connection ID are only permitted if the values are taken from
    NEW_CONNECTION_ID frames") is about values WP11 never sees — WP4
    `ConnIds.Remote` holds them — so WP11 exports the rule with the set as a
    parameter, in the shape `Migration.MaySendDatagramOn` already uses, and it is
    supplied here.  Every connection ID the peer ever issued counts, retired or
    not: not using a retired one is §5.1.2's rule, not §7.2's, and is `DcidOk`
    below. -/
def peerIssuedCids (s : State) : List ConnIds.Cid := s.cidRemote.entries.map (·.cid)

def HandshakeHeaderOk (s : State) (d : OutDatagram) : Prop :=
  Handshake.MaySendDatagramOn (some (peerIssuedCids s)) s.hs d

def handshakeHeaderOk (s : State) (d : OutDatagram) : Bool :=
  Handshake.maySendDatagramOn (some (peerIssuedCids s)) s.hs d

theorem handshakeHeaderOk_iff (s : State) (d : OutDatagram) :
    handshakeHeaderOk s d = true ↔ HandshakeHeaderOk s d :=
  Handshake.maySendDatagramOn_iff _ _ _

/-- The sequence number of the peer-issued connection ID with these bytes.
    §9.5 and §5.1.2 are written about sequence numbers and `OutDatagram.dcid`
    carries bytes; WP4 `ConnIds.Remote` holds every connection ID the peer ever
    issued, so the lookup is made against it, here, and not against
    `Migration.State.peerCids`, which no endpoint event fills (audit D34-7).
    Bytes WP4 does not hold are sequence number 0 when they are the handshake's
    current Destination Connection ID — §5.1.1, line 1706: "The sequence number
    of the initial connection ID is 0" — which covers the unpredictable value of
    a client's first flight (§7.2, line 2337); anything else is a connection ID
    the peer never issued. -/
def dcidSeq? (s : State) (cid : ConnIds.Cid) : Option Nat :=
  match s.cidRemote.entries.find? (fun e => decide (e.cid = cid)) with
  | some e => some e.seq
  | none => if s.hs.dcidSent = some cid then some 0 else none

/-- The Destination Connection ID a datagram actually carries.

* §5.1, line 1668 and §7.2, line 2380: it is one the peer issued;
* §5.1.2, line 1811: "Upon receipt of an increased Retire Prior To field, the
  peer MUST stop using the corresponding connection IDs" — it is not retired.
  `HandshakeHeaderOk` deliberately admits retired connection IDs and the
  handshake's current one, so neither of its allowances may stand in for this
  (audit D34-6);
* §9.5, lines 3603 and 3608: it has not been used from another local address
  or, line 3611's rebinding apart, to another destination — `Migration`'s
  history, consulted with the sequence number `dcidSeq?` found.  With a
  zero-length connection ID there is nothing to reuse (`Migration.MaySendCid`).

`none` is "the rule being checked does not look at them" (`Spec.OutDatagram`),
as everywhere else. -/
def DcidOk (s : State) (d : OutDatagram) : Prop :=
  match d.dcid with
  | none => True
  | some cid =>
    match dcidSeq? s cid with
    | none => False
    | some n =>
      s.cidRemote.isRetired n = false ∧
        (s.cidRemote.peerZeroLen = true ∨ Migration.MaySendCidOn s.mig (datagramPath d) n)

def dcidOk (s : State) (d : OutDatagram) : Bool :=
  match d.dcid with
  | none => true
  | some cid =>
    match dcidSeq? s cid with
    | none => false
    | some n =>
      !s.cidRemote.isRetired n &&
        (s.cidRemote.peerZeroLen || decide (Migration.MaySendCidOn s.mig (datagramPath d) n))

theorem dcidOk_iff (s : State) (d : OutDatagram) : dcidOk s d = true ↔ DcidOk s d := by
  unfold dcidOk DcidOk
  cases d.dcid with
  | none => simp
  | some cid =>
    dsimp only
    cases dcidSeq? s cid <;> simp

/-- Every frame of every packet coalesced in a datagram: what §4.1, line 1330
    is judged over at datagram level (`StreamTable.MaySendAll`). -/
def datagramFrames (d : OutDatagram) : List Frame := d.packets.flatMap (·.frames)

/-- Is `f` a RETIRE_CONNECTION_ID for sequence number `n`? -/
def retiresSeq (n : Nat) : Frame → Bool
  | .retireConnectionId m => m == n
  | _ => false

/-- §19.16, line 8050: "The sequence number specified in a RETIRE_CONNECTION_ID
    frame MUST NOT refer to the Destination Connection ID field of the packet in
    which the frame is contained."  The frame retires one of the *peer's*
    connection IDs and the Destination Connection ID is one of them too, so the
    sequence number is `dcidSeq?`'s, from WP4 `ConnIds.Remote` — not
    `cidLocal`'s, as `TRIAGE.md` `WP13-4` first had it.  One connection ID per
    datagram (§12.2), so every packet coalesced in it is covered.

    `DcidOk` does not already imply this: `ConnIds.Remote.MaySend` allows the
    *first* RETIRE_CONNECTION_ID of a connection ID that is still active, which
    is exactly the one `DcidOk` lets the datagram carry.  Bytes `dcidSeq?` cannot
    resolve are `DcidOk`'s to refuse; here they forbid nothing.  The receive
    side is `ConnIds.Local.Step.retireSelf`. -/
def RetireNotSelf (s : State) (d : OutDatagram) : Prop :=
  match d.dcid.bind (dcidSeq? s) with
  | none => True
  | some n => ∀ f ∈ datagramFrames d, retiresSeq n f = false

def retireNotSelf (s : State) (d : OutDatagram) : Bool :=
  match d.dcid.bind (dcidSeq? s) with
  | none => true
  | some n => (datagramFrames d).all (fun f => !retiresSeq n f)

theorem retireNotSelf_iff (s : State) (d : OutDatagram) :
    retireNotSelf s d = true ↔ RetireNotSelf s d := by
  unfold retireNotSelf RetireNotSelf
  cases d.dcid.bind (dcidSeq? s) <;> simp

/-- Everything the model knows about a datagram this endpoint may send. -/
def MaySendDatagram (s : State) (d : OutDatagram) : Prop :=
  -- §8, line 2735 / §8.1, line 2773: the anti-amplification budget
  AddressValidation.MaySendTo s.av d.dest d.size ∧
  -- §14.1, §14.2, §14.4
  DatagramSize.MaySendDatagram s.dsz d ∧
  -- §9: the path and connection-ID rules, for every packet in it
  Migration.MaySendDatagram s.mig d ∧
  -- §8.2.1 line 3154 and §8.2.2 lines 3197/3200: expansion to 1200 bytes,
  -- unless the anti-amplification limit forbids it
  PathValidation.MaySendDatagramOn s.av d ∧
  -- §9.3.1, line 3431: the limit on the path the datagram leaves on
  Migration.MaySendDatagramOn s.av s.mig d ∧
  -- §8.2.2, line 3183
  PathResponsesOnPath s d ∧
  -- §13.4.2.2, line 5626: once ECN validation has failed on this path the ECT
  -- codepoint may not be set again.  One instance per space, so all three.
  EcnMarkOk s d ∧
  -- §7.2, lines 2340, 2341 and 2380: the connection IDs the datagram carries
  HandshakeHeaderOk s d ∧
  -- §5.1.2, line 1811 and §9.5, lines 3603/3608: the connection ID it carries
  DcidOk s d ∧
  -- §19.16, line 8050: no RETIRE_CONNECTION_ID for that very connection ID
  RetireNotSelf s d ∧
  -- §4.1, line 1330: the connection credit all its packets consume together
  StreamTable.MaySendAll s.st (datagramFrames d) ∧
  -- every packet coalesced in it
  ∀ p ∈ d.packets, MaySendPacket s p

def maySendDatagram (s : State) (d : OutDatagram) : Bool :=
  AddressValidation.maySendTo s.av d.dest d.size &&
  DatagramSize.maySendDatagram s.dsz d &&
  Migration.maySendDatagram s.mig d &&
  PathValidation.maySendDatagramOn s.av d &&
  decide (Migration.MaySendDatagramOn s.av s.mig d) &&
  pathResponsesOnPath s d &&
  ecnMarkOk s d &&
  handshakeHeaderOk s d &&
  dcidOk s d &&
  retireNotSelf s d &&
  StreamTable.maySendAll s.st (datagramFrames d) &&
  d.packets.all (maySendPacket s)

/-- Diagnostic: the components whose frame-level `maySend` refuses `f`. -/
def maySendWhy (s : State) (f : Frame) : List String :=
  let checks : List (String × Bool) :=
    [("Handshake", Handshake.maySend s.hs f), ("StreamTable", StreamTable.maySend s.st f),
     ("ConnIds.Local" ++ (match f with
        | .newConnectionId seq rpt cid token =>
          s!"(nextSeq={s.cidLocal.nextSeq} peerLimit={s.cidLocal.peerLimit} issued={s.cidLocal.issued.map (·.seq)} retired={s.cidLocal.retired} sentRpt={s.cidLocal.sentRetirePriorTo} peerActiveAfter={s.cidLocal.peerActiveAfter rpt} canIssue={ConnIds.Local.canIssue s.cidLocal cid.toList token.toList rpt} reNew={ConnIds.Local.isReNewCid s.cidLocal seq rpt cid.toList token.toList})"
        | _ => ""), ConnIds.Local.maySend s.cidLocal f),
     ("ConnIds.Remote", ConnIds.Remote.maySend s.cidRemote f),
     ("PathValidation", PathValidation.maySend s.pv f),
     ("Termination", Termination.maySend s.term f),
     ("Retransmission", Retransmission.maySend s.rtx f)]
  (checks.filter (fun c => !c.2)).map (·.1)

/-- Diagnostic: the packet-level conjuncts refusing `p`, then, per refused
    frame, the components refusing it. -/
def maySendPacketWhy (s : State) (p : OutPacket) : List String :=
  let checks : List (String × Bool) :=
    [("FrameRules.maySendPacket", FrameRules.maySendPacket s.fr p),
     ("Handshake.maySendPacket", Handshake.maySendPacket s.hs p),
     ("Termination.maySendPacket", Termination.maySendPacket s.term p),
     ("Migration.maySendPacket", Migration.maySendPacket s.mig p),
     ("ackPacketOk", ackPacketOk s p), ("ecnPacketOk", ecnPacketOk s p),
     ("StreamTable.maySendAll", StreamTable.maySendAll s.st p.frames)]
  (checks.filter (fun c => !c.2)).map (·.1) ++
    (p.frames.zipIdx.filter (fun fi => !maySend s fi.1)).map
      (fun fi => s!"frame#{fi.2}: {maySendWhy s fi.1}")

/-- Diagnostic twin of `maySendDatagram`: the names of the conjuncts that refuse
    `d` (empty iff `maySendDatagram s d = true`).  For the differential harness,
    which otherwise sees one bit for a twelve-way conjunction (TRIAGE WP13-17). -/
def maySendDatagramWhy (s : State) (d : OutDatagram) : List String :=
  let checks : List (String × Bool) :=
    [("AddressValidation.maySendTo", AddressValidation.maySendTo s.av d.dest d.size),
     ("DatagramSize.maySendDatagram", DatagramSize.maySendDatagram s.dsz d),
     ("Migration.maySendDatagram", Migration.maySendDatagram s.mig d),
     ("PathValidation.maySendDatagramOn", PathValidation.maySendDatagramOn s.av d),
     ("Migration.MaySendDatagramOn", decide (Migration.MaySendDatagramOn s.av s.mig d)),
     ("pathResponsesOnPath", pathResponsesOnPath s d),
     ("ecnMarkOk", ecnMarkOk s d),
     ("handshakeHeaderOk", handshakeHeaderOk s d),
     ("dcidOk" ++ (match d.dcid with
        | none => ""
        | some cid =>
          s!"(seq={dcidSeq? s cid} entries={s.cidRemote.entries.map (·.seq)} retired={s.cidRemote.retired} dcidSent={s.hs.dcidSent.isSome} reusedLocal={(dcidSeq? s cid).map (s.mig.reusedAcrossLocal (datagramPath d))} reusedPeer={(dcidSeq? s cid).map (s.mig.reusedAcrossPeer (datagramPath d))} path={(datagramPath d).loc.id}->{(datagramPath d).peer.id} active={s.mig.active.loc.id}->{s.mig.active.peer.id})"),
      dcidOk s d),
     ("retireNotSelf", retireNotSelf s d),
     ("StreamTable.maySendAll", StreamTable.maySendAll s.st (datagramFrames d)),
     ("maySendPacket", d.packets.all (maySendPacket s))]
  (checks.filter (fun c => !c.2)).map (·.1) ++
    (d.packets.filter (fun p => !maySendPacket s p)).flatMap (maySendPacketWhy s)

theorem maySendDatagramWhy_nil_iff (s : State) (d : OutDatagram) :
    maySendDatagramWhy s d = [] ↔ maySendDatagram s d = true := by
  simp only [maySendDatagramWhy, maySendDatagram, List.append_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true]
  constructor
  · rintro ⟨h, -⟩
    have h1 := h _ (Or.inl rfl)
    have h2 := h _ (Or.inr (Or.inl rfl))
    have h3 := h _ (Or.inr (Or.inr (Or.inl rfl)))
    have h4 := h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have h5 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have h6 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    have h7 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    have h8 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    have h9 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    have h10 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl rfl))))))))))
    have h11 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl rfl)))))))))))
    have h12 := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr rfl)))))))))))
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false]
      at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
    refine ⟨fun c hc => ?_, ?_⟩
    · rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;> rw [hc] <;>
        simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, Bool.not_true,
          Bool.false_eq_true, not_false_eq_true]
    · simp only [List.flatMap_eq_nil_iff, List.mem_filter]
      intro p hp
      have := List.all_eq_true.mp h12 p hp.1
      simp [this] at hp

theorem maySendDatagram_iff (s : State) (d : OutDatagram) :
    maySendDatagram s d = true ↔ MaySendDatagram s d := by
  simp only [maySendDatagram, MaySendDatagram, Bool.and_eq_true, AddressValidation.maySendTo_iff,
    DatagramSize.maySendDatagram_iff, Migration.maySendDatagram_iff,
    PathValidation.maySendDatagramOn_iff, pathResponsesOnPath_iff, ecnMarkOk_iff,
    handshakeHeaderOk_iff, dcidOk_iff, retireNotSelf_iff, StreamTable.maySendAll_iff,
    decide_eq_true_eq, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      fun p hp => (maySendPacket_iff s p).mp (h12 p hp)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      fun p hp => (maySendPacket_iff s p).mpr (h12 p hp)⟩

instance instDecidableMaySendDatagram (s : State) (d : OutDatagram) :
    Decidable (MaySendDatagram s d) := decidable_of_iff _ (maySendDatagram_iff s d)

/-! ## 6.4 The three things that are not datagrams of QUIC packets

Each is exported by its package as a free function with arguments
`Spec.OutDatagram` cannot carry; they are collected here so that WP13 has one
place to look. -/

/-- §17.2.5.1, lines 6592 and 6597: the connection IDs of a Retry packet a
    server sends in answer to a client Initial. -/
def maySendRetryHeader (h : AddressValidation.RetryHeader) : Bool :=
  AddressValidation.maySendRetry h

/-- §17.2.5.1, line 6616: "A server MUST NOT send more than one Retry packet in
    response to a single UDP datagram" — a property of the effects one received
    datagram produced, so it is checked over the whole outcome. -/
def atMostOneRetry (fx : List Effect) : Prop :=
  (fx.filter (fun e => match e with | .av (.sendRetry _) => true | _ => false)).length ≤ 1

def atMostOneRetryB (fx : List Effect) : Bool :=
  decide ((fx.filter (fun e => match e with | .av (.sendRetry _) => true | _ => false)).length ≤ 1)

theorem atMostOneRetryB_iff (fx : List Effect) : atMostOneRetryB fx = true ↔ atMostOneRetry fx := by
  simp [atMostOneRetryB, atMostOneRetry]

/-- §5.2.2, §6.1 and §17.2.1: the Version Negotiation packet a server may send
    in answer to a particular datagram.  `VersionNeg` NOTES: WP12 must call it
    with the triggering event, not with `maySendPacket`. -/
def maySendVn (s : State) (e : VersionNeg.Server.Event) (vn : VersionNeg.Server.Vn) : Bool :=
  VersionNeg.Server.maySendVn s.vnServer e vn

/-- §10.3, line 4215 and §10.3.3, line 4393: a Stateless Reset uses a whole UDP
    datagram and its size is bounded by the size of the datagram that triggered
    it, which `Spec.OutDatagram` does not carry (`Termination` part 6.3). -/
def maySendStatelessReset (preventsLooping : Bool) (triggerSize resetSize : Nat) : Bool :=
  Termination.maySendStatelessReset preventsLooping triggerSize resetSize

/-! ## 6.5 Named send-side facts -/

/-- §10.2.2, line 4023 and §10.2, line 3953: a draining or closed endpoint may
    send no frame at all, whatever the other components think. -/
theorem maySend_false_of_draining_or_closed {s : State} (f : Frame)
    (hp : s.term.phase = .draining ∨ s.term.phase = .closed) : ¬ MaySend s f := by
  rintro ⟨-, -, -, -, -, h, -⟩
  exact Termination.maySend_false_of_draining_or_closed _ f hp h

/-- §12.3, line 4693: once a packet number space is spent, no packet of that
    space may be sent.  Lifted from `Ack.not_maySendPacket_of_exhausted`. -/
theorem not_maySendPacket_of_pnExhausted {s : State} {p : OutPacket} {sp : PnSpace}
    (hsp : p.ptype.space = some sp) (hspace : (s.ack sp).space = sp)
    (hx : Ack.pnExhausted (s.ack sp) = true) : ¬ MaySendPacket s p := by
  rintro ⟨-, -, -, -, ⟨hi, hh, ha⟩, -, -⟩
  have : Ack.MaySendPacket (s.ack sp) p := by cases sp <;> assumption
  exact Ack.not_maySendPacket_of_exhausted hx (by rw [hsp, hspace]) this

/-- §19.16, line 8050: a datagram this endpoint may send carries no
    RETIRE_CONNECTION_ID for the connection ID it is addressed with. -/
theorem retire_ne_dcid_of_maySendDatagram {s : State} {d : OutDatagram}
    (h : MaySendDatagram s d) {cid : ConnIds.Cid} {n : Nat} (hd : d.dcid = some cid)
    (hn : dcidSeq? s cid = some n) {p : OutPacket} (hp : p ∈ d.packets) :
    Frame.retireConnectionId n ∉ p.frames := by
  have hr : RetireNotSelf s d := h.2.2.2.2.2.2.2.2.2.1
  unfold RetireNotSelf at hr
  simp only [hd, Option.bind_some, hn] at hr
  intro hf
  have := hr _ (List.mem_flatMap.mpr ⟨p, hp, hf⟩)
  simp [retiresSeq] at this

/-- §12.4, line 4740: a packet this endpoint sends always carries a frame. -/
theorem maySendPacket_frames_ne_nil {s : State} {p : OutPacket} (h : MaySendPacket s p) :
    p.frames ≠ [] := h.1.1

end Quic.Spec.Endpoint
