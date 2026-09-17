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

/-! ## 0. Table 3 (§12.4, lines 4771–4816)

Four total functions on `Frame`, one per column of Table 3 that carries
normative content: "Pkts", and the N / C / P / F characters of "Spec".
They are total by construction: Lean's exhaustiveness check is the proof that
every frame type has a row. -/

/-- §12.4, line 4838: "ih: Only a CONNECTION_CLOSE frame of type 0x1c can
    appear in Initial or Handshake packets."  In `Frame`, `frameType = none` is
    the application variant 0x1d and `some _` is the transport variant 0x1c. -/
def ccPkts : Option Nat → List PacketType
  | some _ => [.initial, .handshake, .zeroRtt, .oneRtt]              -- 0x1c: ih01
  | none => [.zeroRtt, .oneRtt]                                      -- 0x1d: __01

/-- Table 3, "Pkts" column, line 4826: "The "Pkts" column in Table 3 lists the
    types of packets that each frame type could appear in".  `I` = Initial,
    `H` = Handshake, `0` = 0-RTT, `1` = 1-RTT.  Retry and Version Negotiation
    packets carry no frames at all (§12.4, line 4731), so they appear in no
    row. -/
def pkts : Frame → List PacketType
  | .padding _ => [.initial, .handshake, .zeroRtt, .oneRtt]          -- IH01
  | .ping => [.initial, .handshake, .zeroRtt, .oneRtt]               -- IH01
  | .ack .. => [.initial, .handshake, .oneRtt]                       -- IH_1
  | .crypto .. => [.initial, .handshake, .oneRtt]                    -- IH_1
  | .newToken _ => [.oneRtt]                                         -- ___1
  | .pathResponse _ => [.oneRtt]                                     -- ___1
  | .handshakeDone => [.oneRtt]                                      -- ___1
  | .connectionClose _ ft _ => ccPkts ft                             -- ih01
  -- every remaining row of Table 3 is __01; DATAGRAM (RFC 9221) likewise
  | _ => [.zeroRtt, .oneRtt]

@[simp] theorem mem_ccPkts_oneRtt (ft : Option Nat) : PacketType.oneRtt ∈ ccPkts ft := by
  cases ft <;> simp [ccPkts]

@[simp] theorem not_mem_ccPkts_retry (ft : Option Nat) : PacketType.retry ∉ ccPkts ft := by
  cases ft <;> simp [ccPkts]

@[simp] theorem not_mem_ccPkts_vn (ft : Option Nat) :
    PacketType.versionNegotiation ∉ ccPkts ft := by
  cases ft <;> simp [ccPkts]

/-- May a frame of this shape appear in a packet of this type? -/
def allowedIn (f : Frame) (pt : PacketType) : Bool := decide (pt ∈ pkts f)

/-- Table 3, "Spec" column, character `N`, line 4845: "Packets containing only
    frames with this marking are not ack-eliciting".  So a *frame* is
    ack-eliciting exactly when it is not marked `N`: PADDING (NP), ACK (NC) and
    CONNECTION_CLOSE (N) are the marked ones. -/
def ackEliciting : Frame → Bool
  | .padding _ | .ack .. | .connectionClose .. => false
  | _ => true

/-- Table 3, "Spec" column, character `C`, line 4848: "Packets containing only
    frames with this marking do not count toward bytes in flight for congestion
    control purposes".  ACK is the only row marked `C`. -/
def inFlight : Frame → Bool
  | .ack .. => false
  | _ => true

/-- Table 3, "Spec" column, character `P`, line 4852: "Packets containing only
    frames with this marking can be used to probe new network paths during
    connection migration".  §9.1: "PATH_CHALLENGE, PATH_RESPONSE,
    NEW_CONNECTION_ID, and PADDING frames are "probing frames", and all other
    frames are "non-probing frames"." -/
def probing : Frame → Bool
  | .padding _ | .newConnectionId .. | .pathChallenge _ | .pathResponse _ => true
  | _ => false

/-- Table 3, "Spec" column, character `F`, line 4856: "The content of frames
    with this marking are flow controlled".  STREAM is the only row marked `F`.
    (RFC 9221 §5: DATAGRAM frames are explicitly *not* flow controlled.) -/
def flowControlled : Frame → Bool
  | .stream .. => true
  | _ => false

/-! ### Packet-level readings of the same four characters

Each `Spec` character is stated about a *packet* ("packets containing only
frames with this marking …"), so each frame-level function above lifts to the
payload of a packet. -/

/-- A packet is ack-eliciting unless every frame in it is marked `N`. -/
def packetAckEliciting (fs : List Frame) : Bool := fs.any ackEliciting

/-- A packet counts toward bytes in flight unless every frame in it is
    marked `C`.  §13.2.7, line 5299: "Packets containing PADDING frames are
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

* §19.7, line 7596: "Clients MUST NOT send NEW_TOKEN frames.  A server MUST
  treat receipt of a NEW_TOKEN frame as a connection error of type
  PROTOCOL_VIOLATION."
* §19.20, line 8206: "A HANDSHAKE_DONE frame can only be sent by the server.
  … A server MUST treat receipt of a HANDSHAKE_DONE frame as a connection
  error of type PROTOCOL_VIOLATION." -/
def senderOf : Frame → Option Role
  | .newToken _ => some .server
  | .handshakeDone => some .server
  | _ => none

/-- §12.5, line 4977: "Note that it is not possible to send the following
    frames in 0-RTT packets for various reasons: ACK, CRYPTO, HANDSHAKE_DONE,
    NEW_TOKEN, PATH_RESPONSE, and RETIRE_CONNECTION_ID." -/
def forbiddenIn0Rtt : Frame → Bool
  | .ack .. | .crypto .. | .handshakeDone | .newToken _ | .pathResponse _
  | .retireConnectionId _ => true
  | _ => false

/-- The MUST-level reasons for a receiver in role `receiver` to reject frame
    `f` arriving in a packet of type `pt`.

* §12.4, line 4841: "An endpoint MUST treat receipt of a frame in a packet type
  that is not permitted as a connection error of type PROTOCOL_VIOLATION."
* §19.7 / §19.20: a frame only our own role is allowed to send cannot have been
  legitimately sent by the peer. -/
def mustReject (receiver : Role) (pt : PacketType) (f : Frame) : Bool :=
  !allowedIn f pt || decide (senderOf f = some receiver)

/-- §12.5, line 4980: "A server MAY treat receipt of these frames in 0-RTT
    packets as a connection error of type PROTOCOL_VIOLATION."  Of the six
    frames listed there, only RETIRE_CONNECTION_ID is permitted in 0-RTT by
    Table 3, so only it reaches this discretionary rule. -/
def mayReject (pt : PacketType) (f : Frame) : Bool :=
  decide (pt = .zeroRtt) && forbiddenIn0Rtt f && allowedIn f .zeroRtt

/-! ## 1. State, events, effects -/

/-- The endpoint's own role, and the type of the packet it is currently
    assembling.  The packet type is state rather than an argument because
    `Component.MaySend` is `State → Frame → Prop`; `Event.beginPacket` sets
    it. -/
structure State where
  role : Role
  /-- The packet type currently being assembled, for `MaySend`. -/
  assembling : PacketType
  deriving DecidableEq, Repr

inductive Event where
  /-- Frame `f` arrived in a packet of type `pt` (sent by our peer). -/
  | recvFrame (pt : PacketType) (f : Frame)
  /-- The whole frame sequence of a received packet of type `pt`, before the
      frames are handed out one by one.  This event decides §12.4's
      "at least one frame" rule. -/
  | recvPacketFrames (pt : PacketType) (fs : List Frame)
  /-- We start assembling a packet of type `pt`. -/
  | beginPacket (pt : PacketType)
  deriving DecidableEq

inductive Effect where
  /-- The frame is legal in this packet type; hand it to the component that
      owns its semantics. -/
  | deliver (f : Frame)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §12.4, line 4841: "An endpoint MUST treat receipt of a frame in a packet
      type that is not permitted as a connection error of type
      PROTOCOL_VIOLATION." (together with §19.7 and §19.20). -/
  | frameForbidden {s pt f} (h : mustReject s.role pt f = true) :
      Step s (.recvFrame pt f) (.error .protocolViolation)
  /-- An otherwise legal frame is delivered to its owning component. -/
  | frameOk {s pt f} (h : mustReject s.role pt f = false) :
      Step s (.recvFrame pt f) (.ok s [.deliver f])
  /-- §12.5, line 4980: "A server MAY treat receipt of these frames in 0-RTT
      packets as a connection error of type PROTOCOL_VIOLATION." -/
  | frameZeroRttMay {s pt f} (h : mustReject s.role pt f = false)
      (h2 : mayReject pt f = true) :
      Step s (.recvFrame pt f) (.error .protocolViolation)
  /-- §12.4, line 4741: "The payload of a packet that contains frames MUST
      contain at least one frame … An endpoint MUST treat receipt of a packet
      containing no frames as a connection error of type
      PROTOCOL_VIOLATION." -/
  | packetEmpty {s pt} : Step s (.recvPacketFrames pt []) (.error .protocolViolation)
  /-- §12.4, line 4841, applied to a whole payload. -/
  | packetForbidden {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = true) :
      Step s (.recvPacketFrames pt fs) (.error .protocolViolation)
  /-- Every frame is legal: all of them are delivered, in order. -/
  | packetOk {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false) :
      Step s (.recvPacketFrames pt fs) (.ok s (fs.map .deliver))
  /-- §12.5, line 4980, applied to a whole payload. -/
  | packetZeroRttMay {s pt fs} (h0 : fs ≠ []) (h : fs.any (mustReject s.role pt) = false)
      (h2 : fs.any (mayReject pt) = true) :
      Step s (.recvPacketFrames pt fs) (.error .protocolViolation)
  /-- Bookkeeping for `MaySend`: the packet under construction. -/
  | begin {s pt} : Step s (.beginPacket pt) (.ok { s with assembling := pt } [])

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
  | .beginPacket pt => [.ok { s with assembling := pt } []]

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
    | beginPacket pt =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .begin
  · intro h
    cases h with
    | frameForbidden h => simp [outcomes, h]
    | frameOk h => exact mem_outcomes_frameOk h
    | frameZeroRttMay h h2 => simp [outcomes, h, h2]
    | packetEmpty => simp [outcomes]
    | packetForbidden h0 h => exact mem_outcomes_packetForbidden h0 h
    | packetOk h0 h => exact mem_outcomes_packetOk h0 h
    | packetZeroRttMay h0 h h2 => exact mem_outcomes_packetMay h0 h h2
    | begin => simp [outcomes]

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

/-- What we may put into the packet we are assembling:

* §12.4, line 4841 / Table 3: only frames the packet type permits;
* §19.7, line 7596: "Clients MUST NOT send NEW_TOKEN frames";
  §19.20, line 8206: "A HANDSHAKE_DONE frame can only be sent by the server";
* §12.5, line 4977: none of ACK, CRYPTO, HANDSHAKE_DONE, NEW_TOKEN,
  PATH_RESPONSE, RETIRE_CONNECTION_ID in a 0-RTT packet. -/
def MaySend (s : State) (f : Frame) : Prop :=
  allowedIn f s.assembling = true
  ∧ (∀ r, senderOf f = some r → r = s.role)
  ∧ (s.assembling = .zeroRtt → forbiddenIn0Rtt f = false)

def maySend (s : State) (f : Frame) : Bool :=
  allowedIn f s.assembling
  && (match senderOf f with | none => true | some r => decide (r = s.role))
  && (if s.assembling = .zeroRtt then !forbiddenIn0Rtt f else true)

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp only [maySend, MaySend, Bool.and_eq_true]
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
    · by_cases hz : s.assembling = .zeroRtt
      · simp [hz, h3 hz]
      · simp [hz]

/-! ## 7. The component -/

def component : Component where
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

/-! ## 8. Named theorems -/

/-- §12.4, line 4840: "Note that all frames can appear in 1-RTT packets." -/
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
1-RTT packets share the application data space (§12.3, line 4664), so a frame
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

/-- §12.5, line 4956: "PADDING, PING, and CRYPTO frames MAY appear in any
    packet number space." -/
theorem padding_any_space (n : Nat) (sp : PnSpace) : allowedInSpace (.padding n) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

theorem ping_any_space (sp : PnSpace) : allowedInSpace .ping sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

theorem crypto_any_space (off : Nat) (d : ByteArray) (sp : PnSpace) :
    allowedInSpace (.crypto off d) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

/-- §12.5, line 4959: "CONNECTION_CLOSE frames signaling errors at the QUIC
    layer (type 0x1c) MAY appear in any packet number space." -/
theorem connectionClose_transport_any_space (e ft : Nat) (r : ByteArray) (sp : PnSpace) :
    allowedInSpace (.connectionClose e (some ft) r) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts, ccPkts]

/-- §12.5, line 4961: "CONNECTION_CLOSE frames signaling application errors
    (type 0x1d) MUST only appear in the application data packet number
    space." -/
theorem connectionClose_application_appData (e : Nat) (r : ByteArray) (sp : PnSpace) :
    allowedInSpace (.connectionClose e none r) sp = true ↔ sp = .appData := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts, ccPkts]

/-- §12.5, line 4964: "ACK frames MAY appear in any packet number space". -/
theorem ack_any_space (la d fi : Nat) (rs : Array AckRange) (ec : Option Ecn) (sp : PnSpace) :
    allowedInSpace (.ack la d fi rs ec) sp = true := by
  cases sp <;> simp [allowedInSpace, allowedIn, pkts]

/-- §12.5, line 4966: "However, as noted below, 0-RTT packets cannot contain
    ACK frames." -/
theorem ack_not_in_zeroRtt (la d fi : Nat) (rs : Array AckRange) (ec : Option Ecn) :
    allowedIn (.ack la d fi rs ec) .zeroRtt = false := by
  simp [allowedIn, pkts]

/-- §12.5, line 4968: "All other frame types MUST only be sent in the
    application data packet number space." -/
theorem other_frames_appData_only (f : Frame) (h : coreFrame f = false) (sp : PnSpace) :
    allowedInSpace f sp = true ↔ sp = .appData := by
  have hp : pkts f = [PacketType.zeroRtt, PacketType.oneRtt] ∨ pkts f = [PacketType.oneRtt] := by
    cases f <;> simp_all [coreFrame, pkts]
  rcases hp with hp | hp <;> cases sp <;> simp [allowedInSpace, allowedIn, hp]

/-- §12.5, line 4977 as a send-side rule: none of the six frames listed there
    may go into a 0-RTT packet. -/
theorem no_forbidden_frame_in_zeroRtt {s : State} {f : Frame}
    (h : forbiddenIn0Rtt f = true) (hz : s.assembling = .zeroRtt) : ¬ MaySend s f := by
  rintro ⟨-, -, h3⟩
  rw [h3 hz] at h
  exact Bool.noConfusion h

/-! ### (d) PADDING, ACK and CONNECTION_CLOSE are exactly the non-ack-eliciting
frames (Table 3, `N` marking). -/

theorem not_ackEliciting_iff (f : Frame) :
    ackEliciting f = false ↔
      (∃ n, f = .padding n)
      ∨ (∃ la d fi rs ec, f = .ack la d fi rs ec)
      ∨ (∃ e ft r, f = .connectionClose e ft r) := by
  cases f <;> simp [ackEliciting]

/-- Consequently a packet is ack-eliciting exactly when it holds a frame that
    is none of those three (§13.2, line 5044: "only ack-eliciting packets cause
    an ACK frame to be sent within the maximum ack delay"). -/
theorem packetAckEliciting_iff (fs : List Frame) :
    packetAckEliciting fs = true ↔ ∃ f ∈ fs, ackEliciting f = true := by
  simp [packetAckEliciting]

/-! ### Receive-side soundness -/

/-- §12.4, line 4743: a packet containing no frames is a connection error of
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
theorem maySend_not_mustReject {s : State} {f : Frame} (h : MaySend s f) :
    mustReject s.role.peer s.assembling f = false := by
  obtain ⟨h1, h2, -⟩ := h
  simp only [mustReject, h1, Bool.not_true, Bool.false_or, decide_eq_false_iff_not]
  intro hs
  have h3 := h2 _ hs
  cases hr : s.role <;> rw [hr] at h3 <;> simp [Role.peer] at h3

/-! ## 9. Examples (scenarios from the text) -/

private def cli : State := { role := .client, assembling := .oneRtt }
private def srv : State := { role := .server, assembling := .oneRtt }

-- §12.4, line 4743: a packet with no frames is a PROTOCOL_VIOLATION.
example : component.step srv (.recvPacketFrames .initial []) = .error .protocolViolation := by decide

-- §12.5: a STREAM frame in an Initial packet is a PROTOCOL_VIOLATION …
example : component.step srv (.recvFrame .initial (.stream 0 0 false ByteArray.empty))
    = .error .protocolViolation := by decide
-- … while CRYPTO in an Initial packet is fine.
example : component.step srv (.recvFrame .initial (.crypto 0 ByteArray.empty))
    = .ok srv [.deliver (.crypto 0 ByteArray.empty)] := by decide

-- §19.7, line 7596: a server that receives NEW_TOKEN must close with
-- PROTOCOL_VIOLATION; a client that receives one must not.
example : component.step srv (.recvFrame .oneRtt (.newToken ByteArray.empty))
    = .error .protocolViolation := by decide
example : component.step cli (.recvFrame .oneRtt (.newToken ByteArray.empty))
    = .ok cli [.deliver (.newToken ByteArray.empty)] := by decide

-- §19.20, line 8206: same for HANDSHAKE_DONE.
example : component.step srv (.recvFrame .oneRtt .handshakeDone) = .error .protocolViolation := by
  decide
example : component.step cli (.recvFrame .oneRtt .handshakeDone) = .ok cli [.deliver .handshakeDone] := by
  decide

-- §12.5, line 4980: RETIRE_CONNECTION_ID in a 0-RTT packet — Table 3 permits
-- it (__01) but §12.5 lets the server reject it.  Both outcomes are accepted.
example : component.accepts srv (.recvFrame .zeroRtt (.retireConnectionId 0))
    (.ok srv [.deliver (.retireConnectionId 0)]) = true := by decide
example : component.accepts srv (.recvFrame .zeroRtt (.retireConnectionId 0))
    (.error .protocolViolation) = true := by decide

-- §12.4, line 4838: CONNECTION_CLOSE 0x1d (application) is not permitted in a
-- Handshake packet, 0x1c is.
example : component.step cli (.recvFrame .handshake (.connectionClose 0 none ByteArray.empty))
    = .error .protocolViolation := by decide
example : component.accepts cli (.recvFrame .handshake (.connectionClose 0 (some 0) ByteArray.empty))
    (.ok cli [.deliver (.connectionClose 0 (some 0) ByteArray.empty)]) = true := by decide

-- Send side: a client assembling a 0-RTT packet may send STREAM but not ACK,
-- and never NEW_TOKEN.
example : component.maySend { role := .client, assembling := .zeroRtt }
    (.stream 0 0 false ByteArray.empty) = true := by decide
example : component.maySend { role := .client, assembling := .zeroRtt }
    (.ack 0 0 0 #[] none) = false := by decide
example : component.maySend cli (.newToken ByteArray.empty) = false := by decide
example : component.maySend srv (.newToken ByteArray.empty) = true := by decide

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
| §12.3 (4676) | "Subsequent packets sent in the same packet number space MUST increase the packet number by at least one." | `Ack.maySendPacketNumber` |
| §12.3 (4681) | "A QUIC endpoint MUST NOT reuse a packet number within the same packet number space in one connection." | `Ack.maySendPacketNumber` |
| §12.3 (4683) | packet number reaches 2^62-1 ⇒ MUST close without CONNECTION_CLOSE | `Ack.maySendPacketNumber` bounds the number; the close itself is out of scope: WP6 Termination |
| §12.3 (4694) | "A receiver MUST discard a newly unprotected packet unless it is certain that it has not processed another packet with the same packet number from the same packet number space." | `Ack.Step.duplicate` |
| §12.3 (4697) | "Duplicate suppression MUST happen after removing packet protection" | out of scope: packet protection (WP11 / QUIC-TLS); the `Ack` events are by construction post-decryption |
| §12.4 (4741) | "The payload of a packet that contains frames MUST contain at least one frame" | `Step.packetEmpty`, `empty_packet_is_violation` |
| §12.4 (4743) | "An endpoint MUST treat receipt of a packet containing no frames as a connection error of type PROTOCOL_VIOLATION." | `Step.packetEmpty` |
| §12.4 (4771–4816) | Table 3 | `pkts`, `allowedIn`, `ackEliciting`, `inFlight`, `probing`, `flowControlled` |
| §12.4 (4838) | "ih: Only a CONNECTION_CLOSE frame of type 0x1c can appear in Initial or Handshake packets." | `pkts` (`connectionClose _ (some _) _` vs `none`) |
| §12.4 (4840) | "Note that all frames can appear in 1-RTT packets." | `allowedIn_oneRtt` |
| §12.4 (4841) | "An endpoint MUST treat receipt of a frame in a packet type that is not permitted as a connection error of type PROTOCOL_VIOLATION." | `Step.frameForbidden`, `Step.packetForbidden` |
| §12.4 (4845–4857) | N / C / P / F markings | `ackEliciting`, `inFlight`, `probing`, `flowControlled` and the `packet*` liftings |
| §12.4 (4863) | "An endpoint MUST treat the receipt of a frame of unknown type as a connection error of type FRAME_ENCODING_ERROR." | out of scope here: the decoder (`Frame.decodeFrame`, `Err.unknownFrameType`) already rejects unknown types, so no `Frame` value reaches this component |
| §12.4 (4866) | "All frames are idempotent in this version of QUIC." | not a testable MUST; the per-frame components are idempotent by construction |
| §12.4 (4872) | "a frame type MUST use the shortest possible encoding" | out of scope here: `Frame.frameBody` / `Err.nonMinimalFrameType` |
| §12.4 (4880) | MAY treat a non-minimal frame type as PROTOCOL_VIOLATION | out of scope here: decoder, see above |
| §12.5 (4956) | "PADDING, PING, and CRYPTO frames MAY appear in any packet number space." | `padding_any_space`, `ping_any_space`, `crypto_any_space` |
| §12.5 (4959) | CONNECTION_CLOSE 0x1c MAY appear in any packet number space | `connectionClose_transport_any_space` |
| §12.5 (4961) | CONNECTION_CLOSE 0x1d "MUST only appear in the application data packet number space" | `connectionClose_application_appData` |
| §12.5 (4964) | "ACK frames MAY appear in any packet number space, but can only acknowledge packets that appeared in that packet number space." | `ack_any_space`; the second half is `Ack.MaySend` / `Ack.maySend_ack_sound` |
| §12.5 (4966) | "0-RTT packets cannot contain ACK frames" | `ack_not_in_zeroRtt` |
| §12.5 (4968) | "All other frame types MUST only be sent in the application data packet number space." | `other_frames_appData_only` |
| §12.5 (4977) | ACK, CRYPTO, HANDSHAKE_DONE, NEW_TOKEN, PATH_RESPONSE, RETIRE_CONNECTION_ID cannot be sent in 0-RTT | `forbiddenIn0Rtt`, `no_forbidden_frame_in_zeroRtt` |
| §12.5 (4980) | "A server MAY treat receipt of these frames in 0-RTT packets as a connection error of type PROTOCOL_VIOLATION." | `Step.frameZeroRttMay`, `Step.packetZeroRttMay` |
| §19.7 (7596) | "Clients MUST NOT send NEW_TOKEN frames.  A server MUST treat receipt of a NEW_TOKEN frame as a connection error of type PROTOCOL_VIOLATION." | `senderOf`, `mustReject`, `MaySend` |
| §19.20 (8206) | "A HANDSHAKE_DONE frame can only be sent by the server. … A server MUST treat receipt of a HANDSHAKE_DONE frame as a connection error of type PROTOCOL_VIOLATION." | `senderOf`, `mustReject`, `MaySend` |
| §19.20 (8207) | "Servers MUST NOT send a HANDSHAKE_DONE frame before completing the handshake." | out of scope: needs handshake state (WP11) |

NOTES

1. **Table 3 vs §12.5 for RETIRE_CONNECTION_ID.**  Table 3 gives
   RETIRE_CONNECTION_ID the "Pkts" value `__01`, i.e. 0-RTT is permitted, while
   the note at line 4977 says it is "not possible to send" it in a 0-RTT packet
   and line 4980 makes rejecting it a `MAY`.  Reading chosen: Table 3 governs
   the MUST (`mustReject` does not fire), the note governs the send side
   (`MaySend` is false) and supplies the discretionary receive error
   (`mayReject`).  RETIRE_CONNECTION_ID is the only frame where the two
   columns disagree; for the other five frames of the note, Table 3 already
   excludes 0-RTT, so `mustReject` fires and `mayReject` is redundant — hence
   the `allowedIn f .zeroRtt` conjunct in `mayReject`.

2. **`C` marking and CONNECTION_CLOSE.**  Table 3 marks only ACK with `C`, so
   `inFlight (.connectionClose …) = true` here, i.e. a packet carrying only
   CONNECTION_CLOSE counts toward bytes in flight.  [QUIC-RECOVERY] §2 defines
   in-flight packets as those that are ack-eliciting or contain PADDING, which
   would make such a packet *not* in flight.  Table 3 is the text in the
   assigned range, so Table 3 is what is encoded; congestion control is out of
   scope anyway (RFC 9002).

3. **DATAGRAM (RFC 9221).**  `Frame` carries a `datagram` constructor that
   Table 3 of draft-34 does not mention.  It falls into the `__01` catch-all of
   `pkts` and is ack-eliciting, in flight, non-probing and not flow controlled
   — which is RFC 9221 §5's own table.  Flagged because it is outside the
   assigned text.

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
-/

end Quic.Spec.FrameRules
