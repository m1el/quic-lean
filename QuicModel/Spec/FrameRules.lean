import QuicModel.Spec.Core

/-
  WP3 (a): Table 3 of §12.4 as total functions on `Frame`, the packet-number
  space rules of §12.5, and the receive rule "this frame is not allowed in this
  packet type" as a `Component`.

  Text: draft-ietf-quic-transport-34, lines 4634–4988 (§12.3 packet numbers,
  §12.4 frames and frame types, §12.5 frames and number spaces), plus the two
  role restrictions the table's prose defers to §19 (§19.7 NEW_TOKEN,
  §19.20 HANDSHAKE_DONE).

  Packet-number receive tracking and acknowledgment generation are in
  `QuicModel/Spec/Ack.lean`.
-/
namespace Quic.Spec.FrameRules

/-! ## 0. Table 3 (§12.4, lines 4824–4862)

Four total functions on `Frame`, one per column of Table 3 that carries
normative content: "Pkts", and the N / C / P / F characters of "Spec".
They are total by construction: Lean's exhaustiveness check is the proof that
every frame type has a row. -/

/-- §12.4, line 4897: "ih: Only a CONNECTION_CLOSE frame of type 0x1c can
    appear in Initial or Handshake packets."  In `Frame`, `frameType = none` is
    the application variant 0x1d and `some _` is the transport variant 0x1c. -/
def ccPkts : Option Nat → List PacketType
  | some _ => [.initial, .handshake, .zeroRtt, .oneRtt]              -- 0x1c: ih01
  | none => [.zeroRtt, .oneRtt]                                      -- 0x1d: __01

/-- Table 3, "Pkts" column, line 4886: "The "Pkts" column in Table 3 lists the
    types of packets that each frame type could appear in".  `I` = Initial,
    `H` = Handshake, `0` = 0-RTT, `1` = 1-RTT.  Retry and Version Negotiation
    packets carry no frames at all (§12.4, line 4731), so they appear in no
    row. -/
def pkts : Frame → List PacketType
  | .padding _ => [.initial, .handshake, .zeroRtt, .oneRtt]          -- IH01
  | .ping => [.initial, .handshake, .zeroRtt, .oneRtt]               -- IH01
  | .ack .. => [.initial, .handshake, .oneRtt]                       -- IH_1
  | .resetStream .. => [.zeroRtt, .oneRtt]                           -- __01
  | .stopSending .. => [.zeroRtt, .oneRtt]                           -- __01
  | .crypto .. => [.initial, .handshake, .oneRtt]                    -- IH_1
  | .newToken _ => [.oneRtt]                                         -- ___1
  | .stream .. => [.zeroRtt, .oneRtt]                                -- __01
  | .maxData _ => [.zeroRtt, .oneRtt]                                -- __01
  | .maxStreamData .. => [.zeroRtt, .oneRtt]                         -- __01
  | .maxStreams .. => [.zeroRtt, .oneRtt]                            -- __01
  | .dataBlocked _ => [.zeroRtt, .oneRtt]                            -- __01
  | .streamDataBlocked .. => [.zeroRtt, .oneRtt]                     -- __01
  | .streamsBlocked .. => [.zeroRtt, .oneRtt]                        -- __01
  | .newConnectionId .. => [.zeroRtt, .oneRtt]                       -- __01
  | .retireConnectionId _ => [.zeroRtt, .oneRtt]                     -- __01
  | .pathChallenge _ => [.zeroRtt, .oneRtt]                          -- __01
  | .pathResponse _ => [.oneRtt]                                     -- ___1
  | .connectionClose _ ft _ => ccPkts ft                             -- ih01
  | .handshakeDone => [.oneRtt]                                      -- ___1
  -- RFC 9221 §5, outside draft-34's Table 3; see NOTE 3
  | .datagram .. => [.zeroRtt, .oneRtt]                              -- __01

@[simp] theorem mem_ccPkts_oneRtt (ft : Option Nat) : PacketType.oneRtt ∈ ccPkts ft := by
  cases ft <;> simp [ccPkts]

@[simp] theorem not_mem_ccPkts_retry (ft : Option Nat) : PacketType.retry ∉ ccPkts ft := by
  cases ft <;> simp [ccPkts]

@[simp] theorem not_mem_ccPkts_vn (ft : Option Nat) :
    PacketType.versionNegotiation ∉ ccPkts ft := by
  cases ft <;> simp [ccPkts]

/-- May a frame of this shape appear in a packet of this type? -/
def allowedIn (f : Frame) (pt : PacketType) : Bool := decide (pt ∈ pkts f)

/-- Table 3, "Spec" column, character `N`, line 4909: "Packets containing only
    frames with this marking are not ack-eliciting".  So a *frame* is
    ack-eliciting exactly when it is not marked `N`: PADDING (NP), ACK (NC) and
    CONNECTION_CLOSE (N) are the marked ones. -/
def ackEliciting : Frame → Bool
  | .padding _ => false                                              -- N
  | .ping => true
  | .ack .. => false                                                 -- N
  | .resetStream .. => true
  | .stopSending .. => true
  | .crypto .. => true
  | .newToken _ => true
  | .stream .. => true
  | .maxData _ => true
  | .maxStreamData .. => true
  | .maxStreams .. => true
  | .dataBlocked _ => true
  | .streamDataBlocked .. => true
  | .streamsBlocked .. => true
  | .newConnectionId .. => true
  | .retireConnectionId _ => true
  | .pathChallenge _ => true
  | .pathResponse _ => true
  | .connectionClose .. => false                                     -- N
  | .handshakeDone => true
  | .datagram .. => true                                             -- RFC 9221 §5

/-- Table 3, "Spec" column, character `C`, line 4912: "Packets containing only
    frames with this marking do not count toward bytes in flight for congestion
    control purposes".  ACK is the only row marked `C`. -/
def inFlight : Frame → Bool
  | .padding _ => true
  | .ping => true
  | .ack .. => false                                                 -- C
  | .resetStream .. => true
  | .stopSending .. => true
  | .crypto .. => true
  | .newToken _ => true
  | .stream .. => true
  | .maxData _ => true
  | .maxStreamData .. => true
  | .maxStreams .. => true
  | .dataBlocked _ => true
  | .streamDataBlocked .. => true
  | .streamsBlocked .. => true
  | .newConnectionId .. => true
  | .retireConnectionId _ => true
  | .pathChallenge _ => true
  | .pathResponse _ => true
  | .connectionClose .. => true
  | .handshakeDone => true
  | .datagram .. => true

/-- Table 3, "Spec" column, character `P`, line 4916: "Packets containing only
    frames with this marking can be used to probe new network paths during
    connection migration".  §9.1: "PATH_CHALLENGE, PATH_RESPONSE,
    NEW_CONNECTION_ID, and PADDING frames are "probing frames", and all other
    frames are "non-probing frames"." -/
def probing : Frame → Bool
  | .padding _ => true                                               -- P
  | .ping => false
  | .ack .. => false
  | .resetStream .. => false
  | .stopSending .. => false
  | .crypto .. => false
  | .newToken _ => false
  | .stream .. => false
  | .maxData _ => false
  | .maxStreamData .. => false
  | .maxStreams .. => false
  | .dataBlocked _ => false
  | .streamDataBlocked .. => false
  | .streamsBlocked .. => false
  | .newConnectionId .. => true                                      -- P
  | .retireConnectionId _ => false
  | .pathChallenge _ => true                                         -- P
  | .pathResponse _ => true                                          -- P
  | .connectionClose .. => false
  | .handshakeDone => false
  | .datagram .. => false

/-- Table 3, "Spec" column, character `F`, line 4920: "The content of frames
    with this marking are flow controlled".  STREAM is the only row marked `F`.
    (RFC 9221 §5: DATAGRAM frames are explicitly *not* flow controlled.) -/
def flowControlled : Frame → Bool
  | .padding _ => false
  | .ping => false
  | .ack .. => false
  | .resetStream .. => false
  | .stopSending .. => false
  | .crypto .. => false
  | .newToken _ => false
  | .stream .. => true                                               -- F
  | .maxData _ => false
  | .maxStreamData .. => false
  | .maxStreams .. => false
  | .dataBlocked _ => false
  | .streamDataBlocked .. => false
  | .streamsBlocked .. => false
  | .newConnectionId .. => false
  | .retireConnectionId _ => false
  | .pathChallenge _ => false
  | .pathResponse _ => false
  | .connectionClose .. => false
  | .handshakeDone => false
  | .datagram .. => false                                            -- RFC 9221 §5

/-! ### Packet-level readings of the same four characters

Each `Spec` character is stated about a *packet* ("packets containing only
frames with this marking …"), so each frame-level function above lifts to the
payload of a packet. -/

/-- A packet is ack-eliciting unless every frame in it is marked `N`. -/
def packetAckEliciting (fs : List Frame) : Bool := fs.any ackEliciting

/-- A packet counts toward bytes in flight unless every frame in it is
    marked `C`.  §13.2.7, line 5307: "Packets containing PADDING frames are
    considered to be in flight for congestion control purposes" — consistent
    with PADDING not carrying the `C` marking. -/
def packetInFlight (fs : List Frame) : Bool := fs.any inFlight

/-- §9.1: a packet that can be used to probe a new path — every frame in it is
    a probing frame.  A packet must contain at least one frame (§12.4). -/
def packetProbing (fs : List Frame) : Bool := !fs.isEmpty && fs.all probing

/-! ## 0b. Who may send a frame at all

Two frame types may be sent by one role only; Table 3's prose defers the detail
to §19. -/

/-- The only role permitted to send this frame, if the frame is restricted.

* §19.7, line 7597: "Clients MUST NOT send NEW_TOKEN frames.  A server MUST
  treat receipt of a NEW_TOKEN frame as a connection error of type
  PROTOCOL_VIOLATION."
* §19.20, line 8207: "A HANDSHAKE_DONE frame can only be sent by the server.
  … A server MUST treat receipt of a HANDSHAKE_DONE frame as a connection
  error of type PROTOCOL_VIOLATION." -/
def senderOf : Frame → Option Role
  | .newToken _ => some .server
  | .handshakeDone => some .server
  | _ => none

/-- §12.5, line 4976: "Note that it is not possible to send the following
    frames in 0-RTT packets for various reasons: ACK, CRYPTO, HANDSHAKE_DONE,
    NEW_TOKEN, PATH_RESPONSE, and RETIRE_CONNECTION_ID." -/
def forbiddenIn0Rtt : Frame → Bool
  | .ack .. | .crypto .. | .handshakeDone | .newToken _ | .pathResponse _
  | .retireConnectionId _ => true
  | _ => false

/-- The MUST-level reasons for a receiver in role `receiver` to reject frame
    `f` arriving in a packet of type `pt`.

* §12.4, line 4901: "An endpoint MUST treat receipt of a frame in a packet type
  that is not permitted as a connection error of type PROTOCOL_VIOLATION."
* §19.7 / §19.20: a frame only our own role is allowed to send cannot have been
  legitimately sent by the peer. -/
def mustReject (receiver : Role) (pt : PacketType) (f : Frame) : Bool :=
  !allowedIn f pt || decide (senderOf f = some receiver)

/-- §12.5, line 4978: "A server MAY treat receipt of these frames in 0-RTT
    packets as a connection error of type PROTOCOL_VIOLATION."  Of the six
    frames listed there, only RETIRE_CONNECTION_ID is permitted in 0-RTT by
    Table 3, so only it reaches this discretionary rule. -/
def mayReject (pt : PacketType) (f : Frame) : Bool :=
  decide (pt = .zeroRtt) && forbiddenIn0Rtt f && allowedIn f .zeroRtt

/-! ## 1. State, events, effects -/

/-- The endpoint's own role.  Nothing else: every rule of §12.4 and §12.5 is a
    function of the frame and the packet type, and the packet type reaches the
    send side through `Component.MaySendPacket`, which sees the real
    `OutPacket.ptype` rather than a shadow copy in the state. -/
structure State where
  role : Role
  deriving DecidableEq, Repr

inductive Event where
  /-- Frame `f` arrived in a packet of type `pt` (sent by our peer). -/
  | recvFrame (pt : PacketType) (f : Frame)
  /-- The whole frame sequence of a received packet of type `pt`, before the
      frames are handed out one by one.  This event decides §12.4's
      "at least one frame" rule. -/
  | recvPacketFrames (pt : PacketType) (fs : List Frame)
  deriving DecidableEq

inductive Effect where
  /-- The frame is legal in this packet type; hand it to the component that
      owns its semantics. -/
  | deliver (f : Frame)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §12.4, line 4901: "An endpoint MUST treat receipt of a frame in a packet
      type that is not permitted as a connection error of type
      PROTOCOL_VIOLATION." (together with §19.7 and §19.20). -/
  | frameForbidden {s pt f} (h : mustReject s.role pt f = true) :
      Step s (.recvFrame pt f) (.error .protocolViolation)
  /-- An otherwise legal frame is delivered to its owning component. -/
  | frameOk {s pt f} (h : mustReject s.role pt f = false) :
      Step s (.recvFrame pt f) (.ok s [.deliver f])
  /-- §12.5, line 4978: "A server MAY treat receipt of these frames in 0-RTT
      packets as a connection error of type PROTOCOL_VIOLATION." -/
  | frameZeroRttMay {s pt f} (h : mustReject s.role pt f = false)
      (h2 : mayReject pt f = true) :
      Step s (.recvFrame pt f) (.error .protocolViolation)
  /-- §12.4, line 4740: "The payload of a packet that contains frames MUST
      contain at least one frame … An endpoint MUST treat receipt of a packet
      containing no frames as a connection error of type
      PROTOCOL_VIOLATION." -/
  | packetEmpty {s pt} : Step s (.recvPacketFrames pt []) (.error .protocolViolation)
  /-- §12.4, line 4901, applied to a whole payload. -/
  | packetForbidden {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = true) :
      Step s (.recvPacketFrames pt fs) (.error .protocolViolation)
  /-- Every frame is legal: all of them are delivered, in order. -/
  | packetOk {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false) :
      Step s (.recvPacketFrames pt fs) (.ok s (fs.map .deliver))
  /-- §12.5, line 4978, applied to a whole payload. -/
  | packetZeroRttMay {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false)
      (h2 : fs.any (mayReject pt) = true) :
      Step s (.recvPacketFrames pt fs) (.error .protocolViolation)

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvFrame pt f =>
    if mustReject s.role pt f then [.error .protocolViolation]
    else if mayReject pt f then [.ok s [.deliver f], .error .protocolViolation]
    else [.ok s [.deliver f]]
  | .recvPacketFrames pt fs =>
    if fs.isEmpty then [.error .protocolViolation]
    else if fs.any (mustReject s.role pt) then [.error .protocolViolation]
    else if fs.any (mayReject pt) then
      [.ok s (fs.map .deliver), .error .protocolViolation]
    else [.ok s (fs.map .deliver)]

/-! ## 4. The two forms agree -/

theorem mem_outcomes_frameOk {s : State} {pt : PacketType} {f : Frame}
    (h : mustReject s.role pt f = false) :
    Outcome.ok s [Effect.deliver f] ∈ outcomes s (.recvFrame pt f) := by
  by_cases hm : mayReject pt f = true <;> simp [outcomes, h, hm]

theorem mem_outcomes_packetForbidden {s : State} {pt : PacketType} {fs : List Frame}
    (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = true) :
    Outcome.error TransportError.protocolViolation ∈ outcomes s (.recvPacketFrames pt fs) := by
  have hne : ¬ (fs.isEmpty = true) := by simp [h0]
  simp [outcomes, hne, h]

theorem mem_outcomes_packetOk {s : State} {pt : PacketType} {fs : List Frame}
    (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false) :
    Outcome.ok s (fs.map Effect.deliver) ∈ outcomes s (.recvPacketFrames pt fs) := by
  have hne : ¬ (fs.isEmpty = true) := by simp [h0]
  by_cases hm : fs.any (mayReject pt) = true <;> simp [outcomes, hne, h, hm]

theorem mem_outcomes_packetMay {s : State} {pt : PacketType} {fs : List Frame}
    (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false)
    (h2 : fs.any (mayReject pt) = true) :
    Outcome.error TransportError.protocolViolation ∈ outcomes s (.recvPacketFrames pt fs) := by
  have hne : ¬ (fs.isEmpty = true) := by simp [h0]
  simp [outcomes, hne, h, h2]

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvFrame pt f =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .frameForbidden ‹_›
      · rename_i h1
        simp only [Bool.not_eq_true] at h1
        split at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> subst h
          · exact .frameOk h1
          · exact .frameZeroRttMay h1 ‹_›
        · simp only [List.mem_singleton] at h; subst h; exact .frameOk h1
    | recvPacketFrames pt fs =>
      simp only [outcomes] at h
      split at h
      · rename_i he
        rw [List.isEmpty_iff] at he; subst he
        simp only [List.mem_singleton] at h; subst h; exact .packetEmpty
      · rename_i he
        rw [List.isEmpty_iff] at he
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .packetForbidden he ‹_›
        · rename_i h1
          simp only [Bool.not_eq_true] at h1
          split at h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .packetOk he h1
            · exact .packetZeroRttMay he h1 ‹_›
          · simp only [List.mem_singleton] at h; subst h; exact .packetOk he h1
  · intro h
    cases h with
    | frameForbidden h => simp [outcomes, h]
    | frameOk h => exact mem_outcomes_frameOk h
    | frameZeroRttMay h h2 => simp [outcomes, h, h2]
    | packetEmpty => simp [outcomes]
    | packetForbidden h0 h => exact mem_outcomes_packetForbidden h0 h
    | packetOk h0 h => exact mem_outcomes_packetOk h0 h
    | packetZeroRttMay h0 h h2 => exact mem_outcomes_packetMay h0 h h2

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant

This component holds no accumulating state: `role` is fixed for the lifetime of
the connection and `assembling` is set by `beginPacket`.  The invariant is
therefore trivial; the property worth stating — that the role never changes —
is `role_const` in §8. -/

def Inv (_ : State) : Prop := True

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (_ : Inv s) (_ : Step s e (.ok s' fx)) : Inv s' := trivial

/-! ## 6. Send side -/

/-- May an endpoint in role `role` put frame `f` into a packet of type `pt`?

* §12.4, line 4901 / Table 3: only frames the packet type permits;
* §19.7, line 7597: "Clients MUST NOT send NEW_TOKEN frames";
  §19.20, line 8207: "A HANDSHAKE_DONE frame can only be sent by the server";
* §12.5, line 4976: none of ACK, CRYPTO, HANDSHAKE_DONE, NEW_TOKEN,
  PATH_RESPONSE, RETIRE_CONNECTION_ID in a 0-RTT packet.

It depends only on the frame, the packet type and our role, so it accepts an
exact repeat of a frame it accepted before: frames are idempotent (§12.4,
line 4936) and are retransmitted after loss (§13.3). -/
def MaySendIn (role : Role) (pt : PacketType) (f : Frame) : Prop :=
  allowedIn f pt = true
  ∧ (∀ r, senderOf f = some r → r = role)
  ∧ (pt = .zeroRtt → forbiddenIn0Rtt f = false)

def maySendIn (role : Role) (pt : PacketType) (f : Frame) : Bool :=
  allowedIn f pt
  && (match senderOf f with | none => true | some r => decide (r = role))
  && (if pt = .zeroRtt then !forbiddenIn0Rtt f else true)

theorem maySendIn_iff (role : Role) (pt : PacketType) (f : Frame) :
    maySendIn role pt f = true ↔ MaySendIn role pt f := by
  simp only [maySendIn, MaySendIn, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro r hr; rw [hr] at h2; simpa using h2
    · intro hz; rw [hz] at h3; simpa using h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · cases hs : senderOf f with
      | none => rfl
      | some r => simpa using h2 r hs
    · by_cases hz : pt = .zeroRtt
      · simp [hz, h3 hz]
      · simp [hz]

/-- Nothing about a single frame can be decided without knowing which packet
    type it is going into, and `Component.MaySend` does not see one.  Every
    send-side rule of this component is therefore in `MaySendPacket`, and this
    is `True` so that components still compose by conjunction. -/
def MaySend (_ : State) (_ : Frame) : Prop := True

def maySend (_ : State) (_ : Frame) : Bool := true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-- The whole packet we are about to send.

* §12.4, line 4740: "The payload of a packet that contains frames MUST contain
  at least one frame".
* Every frame in it must be one we may send in a packet of that type
  (`MaySendIn`).

Retry and Version Negotiation packets carry no frames (line 4731); `allowedIn`
is `false` for every frame in them, so `MaySendPacket` is unsatisfiable for
those packet types, which is the intended reading — this component never
builds one. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  p.frames ≠ [] ∧ ∀ f ∈ p.frames, MaySendIn s.role p.ptype f

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  !p.frames.isEmpty && p.frames.all (fun f => maySendIn s.role p.ptype f)

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  simp only [maySendPacket, MaySendPacket, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => (maySendIn_iff _ _ _).mp (h2 f hf)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => (maySendIn_iff _ _ _).mpr (h2 f hf)⟩

/-! ## 7. The component -/

@[reducible] def component : Component where
  State := State
  Event := Event
  Effect := Effect
  Step := Step
  outcomes := outcomes
  outcomes_iff := outcomes_iff
  outcomes_ne := outcomes_ne
  Inv := Inv
  step_inv := step_inv
  MaySend := MaySend
  maySend := maySend
  maySend_iff := maySend_iff
  MaySendPacket := MaySendPacket
  maySendPacket := maySendPacket
  maySendPacket_iff := maySendPacket_iff

/-! ## 8. Named theorems -/

/-- §12.4, line 4900: "Note that all frames can appear in 1-RTT packets." -/
theorem allowedIn_oneRtt (f : Frame) : allowedIn f .oneRtt = true := by
  cases f <;> simp [allowedIn, pkts]

/-- §12.4, line 4731: "Version Negotiation, Stateless Reset, and Retry packets
    do not contain frames." -/
theorem allowedIn_retry (f : Frame) : allowedIn f .retry = false := by
  cases f <;> simp [allowedIn, pkts]

theorem allowedIn_versionNegotiation (f : Frame) : allowedIn f .versionNegotiation = false := by
  cases f <;> simp [allowedIn, pkts]

/-! ### (a) The legality table agrees with the prose of §12.5

§12.5 speaks of packet number *spaces*; Table 3 of packet *types*.  0-RTT and
1-RTT packets share the application data space (§12.3, line 4670), so a frame
may appear in a space when it may appear in some packet type of that space. -/

/-- A frame may appear in packet number space `sp`. -/
def allowedInSpace (f : Frame) : PnSpace → Bool
  | .initial => allowedIn f .initial
  | .handshake => allowedIn f .handshake
  | .appData => allowedIn f .zeroRtt || allowedIn f .oneRtt

theorem allowedInSpace_iff (f : Frame) (sp : PnSpace) :
    allowedInSpace f sp = true ↔ ∃ pt, pt.space = some sp ∧ allowedIn f pt = true := by
  constructor
  · intro h
    cases sp
    · exact ⟨.initial, rfl, h⟩
    · exact ⟨.handshake, rfl, h⟩
    · simp only [allowedInSpace, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨.zeroRtt, rfl, h⟩
      · exact ⟨.oneRtt, rfl, h⟩
  · rintro ⟨pt, hpt, h⟩
    cases sp <;> cases pt <;> simp_all [allowedInSpace, PacketType.space]

/-- The five frame types §12.5 singles out before "All other frame types". -/
def coreFrame : Frame → Bool
  | .padding _ | .ping | .crypto .. | .connectionClose .. | .ack .. => true
  | _ => false

/-- §12.5, line 4961: "PADDING, PING, and CRYPTO frames MAY appear in any
    packet number space." -/
theorem padding_any_space (n : Nat) (sp : PnSpace) : allowedInSpace (.padding n) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

theorem ping_any_space (sp : PnSpace) : allowedInSpace .ping sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

theorem crypto_any_space (off : Nat) (d : ByteArray) (sp : PnSpace) :
    allowedInSpace (.crypto off d) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

/-- §12.5, line 4964: "CONNECTION_CLOSE frames signaling errors at the QUIC
    layer (type 0x1c) MAY appear in any packet number space." -/
theorem connectionClose_transport_any_space (e ft : Nat) (r : ByteArray) (sp : PnSpace) :
    allowedInSpace (.connectionClose e (some ft) r) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts, ccPkts]

/-- §12.5, line 4965: "CONNECTION_CLOSE frames signaling application errors
    (type 0x1d) MUST only appear in the application data packet number
    space." -/
theorem connectionClose_application_appData (e : Nat) (r : ByteArray) (sp : PnSpace) :
    allowedInSpace (.connectionClose e none r) sp = true ↔ sp = .appData := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts, ccPkts]

/-- §12.5, line 4969: "ACK frames MAY appear in any packet number space". -/
theorem ack_any_space (la d fi : Nat) (rs : Array AckRange) (ec : Option Ecn) (sp : PnSpace) :
    allowedInSpace (.ack la d fi rs ec) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

/-- §12.5, line 4971: "However, as noted below, 0-RTT packets cannot contain
    ACK frames." -/
theorem ack_not_in_zeroRtt (la d fi : Nat) (rs : Array AckRange) (ec : Option Ecn) :
    allowedIn (.ack la d fi rs ec) .zeroRtt = false := by
  simp [allowedIn, pkts]

/-- §12.5, line 4973: "All other frame types MUST only be sent in the
    application data packet number space." -/
theorem other_frames_appData_only (f : Frame) (h : coreFrame f = false) (sp : PnSpace) :
    allowedInSpace f sp = true ↔ sp = .appData := by
  have hp : pkts f = [PacketType.zeroRtt, PacketType.oneRtt] ∨ pkts f = [PacketType.oneRtt] := by
    cases f <;> simp_all [coreFrame, pkts]
  rcases hp with hp | hp <;> cases sp <;> simp [allowedInSpace, allowedIn, hp]

/-- §12.5, line 4976 as a send-side rule: none of the six frames listed there
    may go into a 0-RTT packet — including ACK, so this component alone is
    correct about ACK-in-0-RTT and does not depend on `Ack`. -/
theorem no_forbidden_frame_in_zeroRtt {role : Role} {f : Frame}
    (h : forbiddenIn0Rtt f = true) : ¬ MaySendIn role .zeroRtt f := by
  rintro ⟨-, -, h3⟩
  rw [h3 rfl] at h
  exact Bool.noConfusion h

/-- The same at packet level: a 0-RTT packet we send contains none of them. -/
theorem no_forbidden_frame_in_zeroRtt_packet {s : State} {p : OutPacket}
    (hz : p.ptype = .zeroRtt) (h : MaySendPacket s p) {f : Frame} (hf : f ∈ p.frames) :
    forbiddenIn0Rtt f = false := (h.2 f hf).2.2 hz

/-! ### (d) PADDING, ACK and CONNECTION_CLOSE are exactly the non-ack-eliciting
frames (Table 3, `N` marking). -/

theorem not_ackEliciting_iff (f : Frame) :
    ackEliciting f = false ↔
      (∃ n, f = .padding n)
      ∨ (∃ la d fi rs ec, f = .ack la d fi rs ec)
      ∨ (∃ e ft r, f = .connectionClose e ft r) := by
  cases f <;> simp [ackEliciting]

/-- Consequently a packet is ack-eliciting exactly when it holds a frame that
    is none of those three (§13.2, line 5048: "only ack-eliciting packets cause
    an ACK frame to be sent within the maximum ack delay"). -/
theorem packetAckEliciting_iff (fs : List Frame) :
    packetAckEliciting fs = true ↔ ∃ f ∈ fs, ackEliciting f = true := by
  simp [packetAckEliciting]

/-! ### Receive-side soundness -/

/-- §12.4, line 4742: a packet containing no frames is a connection error of
    type PROTOCOL_VIOLATION, and nothing else is permitted for it. -/
theorem empty_packet_is_violation (s : State) (pt : PacketType) (o : Out) :
    Step s (.recvPacketFrames pt []) o ↔ o = .error .protocolViolation := by
  rw [← outcomes_iff]; simp [outcomes]

/-- A frame is only ever delivered from a packet type Table 3 permits. -/
theorem delivered_frame_allowed {s s' : State} {pt : PacketType} {f : Frame}
    {fx : List Effect} (h : Step s (.recvFrame pt f) (.ok s' fx)) :
    allowedIn f pt = true := by
  cases h with
  | frameOk h =>
    simp only [mustReject, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at h
    exact h.1

/-- The role never changes. -/
theorem role_const {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s'.role = s.role := by
  cases h <;> rfl

/-- Send/receive agreement: anything we may send, the peer must not reject on
    packet-type or role grounds.  (The peer may still exercise the §12.5
    0-RTT `MAY`; see `mayReject`.) -/
theorem maySendIn_not_mustReject {role : Role} {pt : PacketType} {f : Frame}
    (h : MaySendIn role pt f) : mustReject role.peer pt f = false := by
  obtain ⟨h1, h2, -⟩ := h
  simp only [mustReject, h1, Bool.not_true, Bool.false_or, decide_eq_false_iff_not]
  intro hs
  have h3 := h2 _ hs
  cases hr : role <;> rw [hr] at h3 <;> simp [Role.peer] at h3

/-- §12.4, line 4740, on the send side: a packet we send is never empty, so the
    peer's `Step.packetEmpty` never fires on it. -/
theorem maySendPacket_frames_ne_nil {s : State} {p : OutPacket} (h : MaySendPacket s p) :
    p.frames ≠ [] := h.1

/-- …and none of its frames makes the peer raise PROTOCOL_VIOLATION on
    packet-type or role grounds. -/
theorem maySendPacket_not_mustReject {s : State} {p : OutPacket} (h : MaySendPacket s p) :
    p.frames.any (mustReject s.role.peer p.ptype) = false := by
  simp only [List.any_eq_false]
  intro f hf
  simp [maySendIn_not_mustReject (h.2 f hf)]

/-! ## 9. Examples (scenarios from the text) -/

private def cli : State := { role := .client }
private def srv : State := { role := .server }

-- §12.4, line 4742: a packet with no frames is a PROTOCOL_VIOLATION.
example : component.step srv (.recvPacketFrames .initial []) = .error .protocolViolation := by decide

-- §12.5: a STREAM frame in an Initial packet is a PROTOCOL_VIOLATION …
example : component.step srv (.recvFrame .initial (.stream 0 0 false ByteArray.empty))
    = .error .protocolViolation := by decide
-- … while CRYPTO in an Initial packet is fine.
example : component.step srv (.recvFrame .initial (.crypto 0 ByteArray.empty))
    = .ok srv [.deliver (.crypto 0 ByteArray.empty)] := by decide

-- §19.7, line 7597: a server that receives NEW_TOKEN must close with
-- PROTOCOL_VIOLATION; a client that receives one must not.
example : component.step srv (.recvFrame .oneRtt (.newToken ByteArray.empty))
    = .error .protocolViolation := by decide
example : component.step cli (.recvFrame .oneRtt (.newToken ByteArray.empty))
    = .ok cli [.deliver (.newToken ByteArray.empty)] := by decide

-- §19.20, line 8207: same for HANDSHAKE_DONE.
example : component.step srv (.recvFrame .oneRtt .handshakeDone) = .error .protocolViolation := by
  decide
example : component.step cli (.recvFrame .oneRtt .handshakeDone) = .ok cli [.deliver .handshakeDone] := by
  decide

-- §12.5, line 4978: RETIRE_CONNECTION_ID in a 0-RTT packet — Table 3 permits
-- it (__01) but §12.5 lets the server reject it.  Both outcomes are accepted.
example : component.accepts srv (.recvFrame .zeroRtt (.retireConnectionId 0))
    (.ok srv [.deliver (.retireConnectionId 0)]) = true := by decide
example : component.accepts srv (.recvFrame .zeroRtt (.retireConnectionId 0))
    (.error .protocolViolation) = true := by decide

-- §12.4, line 4897: CONNECTION_CLOSE 0x1d (application) is not permitted in a
-- Handshake packet, 0x1c is.
example : component.step cli (.recvFrame .handshake (.connectionClose 0 none ByteArray.empty))
    = .error .protocolViolation := by decide
example : component.accepts cli (.recvFrame .handshake (.connectionClose 0 (some 0) ByteArray.empty))
    (.ok cli [.deliver (.connectionClose 0 (some 0) ByteArray.empty)]) = true := by decide

-- Send side (§12.4, line 4740 and Table 3): a client's 0-RTT packet may carry
-- STREAM but not ACK, and a client never sends NEW_TOKEN.
example : component.maySendPacket cli ⟨.zeroRtt, [.stream 0 0 false ByteArray.empty]⟩ = true := by
  decide
example : component.maySendPacket cli ⟨.zeroRtt, [.ack 0 0 0 #[] none]⟩ = false := by decide
example : component.maySendPacket cli ⟨.oneRtt, [.newToken ByteArray.empty]⟩ = false := by decide
example : component.maySendPacket srv ⟨.oneRtt, [.newToken ByteArray.empty]⟩ = true := by decide
-- §12.4, line 4740: a packet we send must contain at least one frame.
example : component.maySendPacket srv ⟨.oneRtt, []⟩ = false := by decide
example : component.maySendPacket srv ⟨.oneRtt, [.ping]⟩ = true := by decide
-- one illegal frame among legal ones is enough to refuse the packet
example : component.maySendPacket srv ⟨.initial, [.crypto 0 ByteArray.empty, .ping]⟩ = true := by
  decide
example : component.maySendPacket srv
    ⟨.initial, [.crypto 0 ByteArray.empty, .stream 0 0 false ByteArray.empty]⟩ = false := by decide
-- line 4731: Retry and Version Negotiation packets carry no frames at all
example : component.maySendPacket srv ⟨.retry, [.ping]⟩ = false := by decide
example : component.maySendPacket srv ⟨.versionNegotiation, [.ping]⟩ = false := by decide

-- Table 3 markings: a packet of PADDING only is not ack-eliciting, is in
-- flight (§13.2.7) and can probe a new path (§9.1).
example : packetAckEliciting [.padding 3] = false := by decide
example : packetInFlight [.padding 3] = true := by decide
example : packetProbing [.padding 3, .pathChallenge ByteArray.empty] = true := by decide
example : packetProbing [.padding 3, .ping] = false := by decide
-- a packet of ACK only is neither ack-eliciting nor in flight
example : packetAckEliciting [.ack 0 0 0 #[] none] = false := by decide
example : packetInFlight [.ack 0 0 0 #[] none] = false := by decide

-- following an implementation we cannot see inside
example : component.track srv (.recvFrame .oneRtt .ping) (.ok [.deliver .ping]) = some srv := by
  rfl

/-! ## 10. Coverage and notes

Assigned range: lines 4634–4988.  §13.1/§13.2 (lines 5018–5324) are covered in
`Spec/Ack.lean`.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §12.3 (4685) | "Subsequent packets sent in the same packet number space MUST increase the packet number by at least one." | `Ack.maySendPacketNumber` |
| §12.3 (4692) | "A QUIC endpoint MUST NOT reuse a packet number within the same packet number space in one connection." | `Ack.maySendPacketNumber` |
| §12.3 (4693) | packet number reaches 2^62-1 ⇒ MUST close without CONNECTION_CLOSE | `Ack.maySendPacketNumber` bounds the number; the close itself is out of scope: WP6 Termination |
| §12.3 (4709) | "A receiver MUST discard a newly unprotected packet unless it is certain that it has not processed another packet with the same packet number from the same packet number space." | `Ack.Step.duplicate` |
| §12.3 (4711) | "Duplicate suppression MUST happen after removing packet protection" | out of scope: packet protection (WP11 / QUIC-TLS); the `Ack` events are by construction post-decryption |
| §12.3 (4659) | "Version Negotiation (Section 17.2.1) and Retry (Section 17.2.5) packets do not include a packet number." | `Spec.PacketType.space` (WP0 Core) is `none` for both, so no `Ack` instance tracks them; `pkts` puts no frame in them either |
| §12.4 (4740) | "The payload of a packet that contains frames MUST contain at least one frame" | receive: `Step.packetEmpty`, `empty_packet_is_violation`; send: `MaySendPacket`, `maySendPacket_frames_ne_nil` |
| §12.4 (4742) | "An endpoint MUST treat receipt of a packet containing no frames as a connection error of type PROTOCOL_VIOLATION." | `Step.packetEmpty` |
| §12.4 (4743) | "Frames always fit within a single QUIC packet and cannot span multiple packets." | structural, nothing to check: `Frame.decodeFrames` parses each frame out of one packet payload and `Event.recvPacketFrames` carries exactly one packet's frames, so no `Frame` value can straddle two packets |
| §12.4 (4824–4862) | Table 3 | `pkts`, `allowedIn`, `ackEliciting`, `inFlight`, `probing`, `flowControlled` |
| §12.4 (4897) | "ih: Only a CONNECTION_CLOSE frame of type 0x1c can appear in Initial or Handshake packets." | `pkts` (`connectionClose _ (some _) _` vs `none`) |
| §12.4 (4900) | "Note that all frames can appear in 1-RTT packets." | `allowedIn_oneRtt` |
| §12.4 (4901) | "An endpoint MUST treat receipt of a frame in a packet type that is not permitted as a connection error of type PROTOCOL_VIOLATION." | receive: `Step.frameForbidden`, `Step.packetForbidden`; send: `MaySendIn` / `MaySendPacket`, `maySendPacket_not_mustReject` |
| §12.4 (4909–4921) | N / C / P / F markings | `ackEliciting`, `inFlight`, `probing`, `flowControlled` and the `packet*` liftings |
| §12.4 (4933) | "An endpoint MUST treat the receipt of a frame of unknown type as a connection error of type FRAME_ENCODING_ERROR." | out of scope here: the decoder (`Frame.decodeFrame`, `Err.unknownFrameType`) already rejects unknown types, so no `Frame` value reaches this component |
| §12.4 (4936) | "All frames are idempotent in this version of QUIC." | not a testable MUST; the per-frame components are idempotent by construction |
| §12.4 (4942) | "a frame type MUST use the shortest possible encoding" | out of scope here: `Frame.frameBody` / `Err.nonMinimalFrameType` |
| §12.4 (4950) | MAY treat a non-minimal frame type as PROTOCOL_VIOLATION | out of scope here: decoder, see above |
| §12.5 (4961) | "PADDING, PING, and CRYPTO frames MAY appear in any packet number space." | `padding_any_space`, `ping_any_space`, `crypto_any_space` |
| §12.5 (4964) | CONNECTION_CLOSE 0x1c MAY appear in any packet number space | `connectionClose_transport_any_space` |
| §12.5 (4965) | "CONNECTION_CLOSE frames signaling application errors (type 0x1d) MUST only appear in the application data packet number space." | `connectionClose_application_appData` |
| §12.5 (4969) | "ACK frames MAY appear in any packet number space, but can only acknowledge packets that appeared in that packet number space." | `ack_any_space`; the second half is `Ack.MaySend` / `Ack.maySend_ack_sound` |
| §12.5 (4971) | "0-RTT packets cannot contain ACK frames" | `ack_not_in_zeroRtt` |
| §12.5 (4973) | "All other frame types MUST only be sent in the application data packet number space." | `other_frames_appData_only` |
| §12.5 (4976) | ACK, CRYPTO, HANDSHAKE_DONE, NEW_TOKEN, PATH_RESPONSE, RETIRE_CONNECTION_ID cannot be sent in 0-RTT | `forbiddenIn0Rtt`, `no_forbidden_frame_in_zeroRtt`, `no_forbidden_frame_in_zeroRtt_packet` |
| §12.5 (4978) | "A server MAY treat receipt of these frames in 0-RTT packets as a connection error of type PROTOCOL_VIOLATION." | `Step.frameZeroRttMay`, `Step.packetZeroRttMay` |
| §19.7 (7597) | "Clients MUST NOT send NEW_TOKEN frames.  A server MUST treat receipt of a NEW_TOKEN frame as a connection error of type PROTOCOL_VIOLATION." | `senderOf`, `mustReject`, `MaySendIn` / `MaySendPacket` |
| §19.20 (8207) | "A HANDSHAKE_DONE frame can only be sent by the server. … A server MUST treat receipt of a HANDSHAKE_DONE frame as a connection error of type PROTOCOL_VIOLATION." | `senderOf`, `mustReject`, `MaySendIn` / `MaySendPacket` |
| §19.20 (8207) | "Servers MUST NOT send a HANDSHAKE_DONE frame before completing the handshake." | out of scope: needs handshake state (WP11) |

NOTES

1. **§12.5 line 4978's MAY against §12.4 line 4901's MUST — all six frames.**
   Line 4976 lists six frames that "it is not possible to send … in 0-RTT
   packets", and line 4978 says a server **MAY** treat receipt of them in a
   0-RTT packet as PROTOCOL_VIOLATION.  Line 4901 says an endpoint **MUST**
   treat a frame in a packet type Table 3 does not permit as PROTOCOL_VIOLATION.
   For five of the six the two sentences disagree about whether the error is
   optional, and the draft does not resolve it.  Reading chosen throughout:
   **Table 3 plus the MUST of line 4901 wins wherever they apply; line 4978
   only adds an option where Table 3 is silent.**  Frame by frame:

   | frame | Table 3 "Pkts" | 0-RTT permitted by Table 3? | which sentence wins | outcomes for receipt in 0-RTT |
   |---|---|---|---|---|
   | ACK | `IH_1` | no | L4901 MUST | `[.error .protocolViolation]` only |
   | CRYPTO | `IH_1` | no | L4901 MUST | `[.error .protocolViolation]` only |
   | HANDSHAKE_DONE | `___1` | no | L4901 MUST | `[.error .protocolViolation]` only |
   | NEW_TOKEN | `___1` | no | L4901 MUST | `[.error .protocolViolation]` only |
   | PATH_RESPONSE | `___1` | no | L4901 MUST | `[.error .protocolViolation]` only |
   | RETIRE_CONNECTION_ID | `__01` | **yes** | L4978 MAY | `[.ok …, .error .protocolViolation]` |

   So for the first five the model is *stricter* than line 4978 read on its
   own: it does not permit accepting them.  That is deliberate — a MAY cannot
   licence ignoring a MUST — but WP13 must expect a mismatch if ngtcp2 accepts
   any of the five in a 0-RTT packet, and should triage it here rather than
   patching `Step`.  On the send side all six are refused uniformly
   (`forbiddenIn0Rtt`, `no_forbidden_frame_in_zeroRtt`), which both sentences
   agree on.

   A third sentence pulls the other way and is *not* followed: line 4961 says
   "PADDING, PING, and CRYPTO frames MAY appear in any packet number space",
   and 0-RTT lives in the application data space, yet Table 3 gives CRYPTO
   `IH_1`.  `other_frames_appData_only` and `crypto_any_space` are stated over
   *spaces*, where both hold (CRYPTO reaches the application data space through
   1-RTT); the packet-type refusal of CRYPTO in 0-RTT comes from Table 3 alone.

   Line 4978 grants the discretion to "a server"; `mayReject` does not test the
   role, because only a server ever receives a 0-RTT packet (§17.2.3), so the
   branch is unreachable for a client.

2. **`C` marking and CONNECTION_CLOSE.**  Table 3 marks only ACK with `C`, so
   `inFlight (.connectionClose …) = true` here, i.e. a packet carrying only
   CONNECTION_CLOSE counts toward bytes in flight.  [QUIC-RECOVERY] §2 defines
   in-flight packets as those that are ack-eliciting or contain PADDING, which
   would make such a packet *not* in flight.  Table 3 is the text in the
   assigned range, so Table 3 is what is encoded; congestion control is out of
   scope anyway (RFC 9002).

3. **DATAGRAM (RFC 9221).**  `Frame` carries a `datagram` constructor that
   Table 3 of draft-34 does not mention.  It is given `__01`, ack-eliciting, in
   flight, non-probing and not flow controlled — which is RFC 9221 §5's own
   table.  Flagged because it is outside the assigned text.

   The five Table 3 functions (`pkts`, `ackEliciting`, `inFlight`, `probing`,
   `flowControlled`) list **every** `Frame` constructor explicitly rather than
   ending in a `_ =>` catch-all, so adding a frame type to `Frame.lean` breaks
   the build here and forces a decision for each column instead of silently
   inheriting `__01` / ack-eliciting / in-flight / non-probing / unmetered.
   `senderOf`, `forbiddenIn0Rtt` and `coreFrame` keep catch-alls on purpose:
   each encodes a short closed list quoted from §19.7, §19.20 or §12.5, and a
   frame absent from that list genuinely takes the default.

4. **Retry and Version Negotiation.**  These packets carry no frames at all
   (line 4731), so every frame is `allowedIn … = false` for them and a
   `recvFrame` event with `pt = .retry` yields PROTOCOL_VIOLATION.  In a real
   endpoint no frame is ever parsed out of such a packet, so the branch is
   unreachable from `decodePacket`; it is kept so that `allowedIn` is total
   over `PacketType`.

5. **Packet-level vs frame-level events.**  `recvPacketFrames` decides §12.4's
   "at least one frame" rule and the packet-type legality of the whole payload;
   the frames it accepts are then emitted as `deliver` effects for the owning
   components.  `recvFrame` is the same rule for a single frame, for use by
   WP12 when it walks a payload frame by frame.  Neither event models frame
   *semantics*; each `deliver` effect is the hand-off point.

6. **"MUST treat as a connection error" is `.error`, not `.drop`.**  Following
   the template, a connection error is `Outcome.error`; `.drop` is reserved for
   discarding a packet (see `Ack.Step.duplicate`).

7. **`Inv` is trivial.**  This component accumulates nothing.  `role_const`
   states the property that would otherwise be the invariant; it cannot be
   phrased as `Inv : State → Prop` because `Inv` has no access to the initial
   state.

8. **No `assembling` in the state, and `MaySend` is `True`.**  An earlier
   version carried the packet type being assembled in `State` so that
   `Component.MaySend : State → Frame → Prop` could see it.  Every send-side
   rule here is really about a frame *in a packet of a given type*, so all of
   them now live in `Component.MaySendPacket`, which is handed the real
   `OutPacket.ptype`; `MaySendIn role pt f` is the per-frame core they share.
   `MaySend` is `True` so that it does not repeat `MaySendPacket` (BRIEF) and
   components still compose by conjunction.  Two things follow: the packet type
   is no longer duplicated between this component and `Ack`, and this component
   alone is now correct about ACK-in-0-RTT
   (`no_forbidden_frame_in_zeroRtt`) instead of relying on the conjunction with
   `Ack.MaySend`.

9. **There are no SHOULD sentences in lines 4634–4988**, so the BRIEF's
   SHOULD rule has nothing to place here; every §13.2 SHOULD is in `Spec/Ack.lean`.
-/

end Quic.Spec.FrameRules
