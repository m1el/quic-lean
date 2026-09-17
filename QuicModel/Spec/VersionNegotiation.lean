import QuicModel.Spec.DatagramSize
import QuicModel.Packet

/-
  WP7b: version negotiation — §5.2 (matching packets to connections, lines
  1835–1984), §6 (lines 2044–2156) and the version rules of §15 (lines
  5920–5958).

  Two components, one per role:

  * `Server` decides the fate of a datagram that arrives with some version,
    given the versions the server supports: deliver it, answer it with a Version
    Negotiation packet, or drop it.  A Version Negotiation packet is not a
    frame, so `Component.MaySend` is `True` here and the send-side rule is the
    packet-level predicate `Server.MaySendVn`.
  * `Client` handles a Version Negotiation packet that arrives in response to
    its connection attempt.

  The version-independent fields of an incoming datagram are not re-parsed:
  `Server.eventOfDatagram` gets them from `Quic.versionCid` (`QuicModel/Packet.lean`),
  and the echo property of the Version Negotiation the server builds is stated
  against that function.

  Both files follow the ten-part order of `Spec/Template.lean`.
-/
namespace Quic.Spec.VersionNeg

open Quic.Spec.DatagramSize (smallestMaxDatagramSize)

/-! ## 0. Versions (§15, lines 5920–5958) -/

/-- §15, line 5924: "The version 0x00000000 is reserved to represent version
    negotiation." -/
def versionNegotiationVersion : Nat := 0x00000000

/-- §15, line 5947: "Versions that follow the pattern 0x?a?a?a?a are reserved
    for use in forcing version negotiation to be exercised.  That is, any
    version number where the low four bits of all bytes is 1010 (in binary)." -/
def isReservedVersion (v : Nat) : Bool := (v &&& 0x0f0f0f0f) == 0x0a0a0a0a

/-- Named theorem (e), first half. -/
theorem isReservedVersion_iff (v : Nat) :
    isReservedVersion v = true ↔ v &&& 0x0f0f0f0f = 0x0a0a0a0a := by
  simp [isReservedVersion]

/-- Named theorem (e), second half: §15, line 5953 — "Reserved version numbers
    will never represent a real protocol", so none of the versions this model
    supports (`QuicModel/Packet.lean`: v1 and v2) is reserved. -/
theorem reserved_not_supported (v : Nat) (h : isSupportedVersion v = true) :
    isReservedVersion v = false := by
  simp only [isSupportedVersion, versionV1, versionV2, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> simp [isReservedVersion]

/-- Version 0 is not a reserved version: it is the Version Negotiation marker. -/
theorem versionNegotiation_not_reserved :
    isReservedVersion versionNegotiationVersion = false := by
  simp [isReservedVersion, versionNegotiationVersion]

/-! ## The server (§5.2.2, §6.1) -/

namespace Server

/-! ### 1. State, events, effects -/

/-- The contents of a Version Negotiation packet (§17.2.1, line 6237). -/
structure Vn where
  dcid : ByteArray
  scid : ByteArray
  /-- §17.2.1, line 6283: "The remainder of the Version Negotiation packet is a
      list of 32-bit versions that the server supports." -/
  versions : List Nat
  deriving DecidableEq

/-- The header those contents go in; `Quic.Header.versionNegotiation` is the
    wire form decoded by `QuicModel/Packet.lean`. -/
def Vn.header (vn : Vn) : Header := .versionNegotiation vn.dcid vn.scid

structure State where
  /-- The versions this server will accept for a new connection (§5.2.2). -/
  supported : List Nat
  /-- The version list it puts into a Version Negotiation packet: the versions
      it supports, possibly with reserved versions added (§6.3, line 2150:
      "Endpoints MAY add reserved versions to any field where unknown or
      unsupported versions are ignored"). -/
  advertised : List Nat
  /-- The length of the connection IDs this server issues, needed to read a
      short header (RFC 8999; `Quic.versionCid`). -/
  shortDcidLen : Nat
  deriving DecidableEq

inductive Event where
  /-- A UDP datagram of `size` bytes arrived.  `version` is `none` when the
      first packet has a short header (§5.2.2's "no version field") and
      `some v` for a long header.  `dcid`/`scid` are that packet's connection
      IDs.  These are exactly the version-independent fields RFC 8999 defines
      and `Quic.versionCid` extracts. -/
  | datagram (size : Nat) (version : Option Nat) (dcid scid : ByteArray)
  deriving DecidableEq

inductive Effect where
  /-- §5.2.2, line 1926: the datagram goes on to connection lookup, to be
      "matched to a connection using the connection ID".  Whether a connection
      exists — and what happens when none does — is WP12's `Endpoint`, so this
      component says only that version handling does not stop the datagram. -/
  | deliver
  /-- §6.1: answer with this Version Negotiation packet. -/
  | sendVersionNegotiation (vn : Vn)
  deriving DecidableEq

def Effect.isSendVn : Effect → Bool
  | .sendVersionNegotiation _ => true
  | .deliver => false

abbrev Out := Outcome State Effect

/-- RFC 8999 header form bit: true for a long header, which is the only form
    that carries a version field. -/
def isLongHeader (buf : ByteArray) : Bool := byteAt buf 0 &&& 0x80 != 0

/-- The event a received datagram gives rise to, computed with the existing
    `Quic.versionCid`.  `none` means the datagram is not even a well-formed
    RFC 8999 packet, and §5.2.2's "Servers MUST drop incoming packets under all
    other circumstances" applies without any state being consulted. -/
def eventOfDatagram (s : State) (buf : ByteArray) : Option Event :=
  match Quic.versionCid buf s.shortDcidLen with
  | .ok (vc, _) =>
      some (.datagram buf.size (if isLongHeader buf then some vc.version else none)
        vc.dcid vc.scid)
  | .error _ => none

/-- §17.2.1, lines 6260–6263: "The server MUST include the value from the Source
    Connection ID field of the packet it receives in the Destination Connection
    ID field.  The value for Source Connection ID MUST be copied from the
    Destination Connection ID of the received packet." -/
def mkVersionNegotiation (s : State) (dcid scid : ByteArray) : Vn :=
  { dcid := scid, scid := dcid, versions := s.advertised }

/-! ### 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §5.2.2, line 1926: "Packets with a supported version, or no version field,
      are matched to a connection using the connection ID ... These packets are
      processed using the selected connection."  A short header has no version
      field. -/
  | noVersionField {s n d c} : Step s (.datagram n none d c) (.ok s [.deliver])
  /-- Same sentence, the supported-version case. -/
  | supported {s n v d c} (h : v ∈ s.supported) :
      Step s (.datagram n (some v) d c) (.ok s [.deliver])
  /-- §6.1, line 2066: "An endpoint MUST NOT send a Version Negotiation packet
      in response to receiving a Version Negotiation packet."  A long header
      with version 0 is a Version Negotiation packet (§17.2.1, line 6228); a
      server never processes one, so §5.2.2 line 1946 — "Servers MUST drop
      incoming packets under all other circumstances" — applies. -/
  | recvVersionNegotiation {s n d c} (hs : versionNegotiationVersion ∉ s.supported) :
      Step s (.datagram n (some versionNegotiationVersion) d c) .drop
  /-- §5.2.2, line 1916: "Servers MUST drop smaller packets that specify
      unsupported versions" — smaller than what would initiate a new connection
      for a supported version, i.e. §14.1's 1200 bytes. -/
  | unsupportedTooSmall {s n v d c} (h : v ∉ s.supported) (h0 : v ≠ versionNegotiationVersion)
      (hn : n < smallestMaxDatagramSize) :
      Step s (.datagram n (some v) d c) .drop
  /-- §5.2.2, line 1911: "If a server receives a packet that indicates an
      unsupported version and if the packet is large enough to initiate a new
      connection for any supported version, the server SHOULD send a Version
      Negotiation packet as described in Section 6.1." -/
  | unsupportedSendVn {s n v d c} (h : v ∉ s.supported) (h0 : v ≠ versionNegotiationVersion)
      (hn : ¬ n < smallestMaxDatagramSize) :
      Step s (.datagram n (some v) d c)
        (.ok s [.sendVersionNegotiation (mkVersionNegotiation s d c)])
  /-- §5.2.2, line 1914: "A server MAY limit the number of packets to which it
      responds with a Version Negotiation packet" (§6.1, line 2083: "A server
      MAY limit the number of Version Negotiation packets it sends") — so
      staying silent is also permitted. -/
  | unsupportedSilent {s n v d c} (h : v ∉ s.supported) (h0 : v ≠ versionNegotiationVersion)
      (hn : ¬ n < smallestMaxDatagramSize) :
      Step s (.datagram n (some v) d c) .drop

/-! ### 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .datagram _ none _ _ => [.ok s [.deliver]]
  | .datagram n (some v) d c =>
    if v ∈ s.supported then [.ok s [.deliver]]
    else if v = versionNegotiationVersion then [.drop]
    else if n < smallestMaxDatagramSize then [.drop]
    else [.ok s [.sendVersionNegotiation (mkVersionNegotiation s d c)], .drop]

/-! ### 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | datagram n version d c =>
      cases version with
      | none => simp only [outcomes, List.mem_singleton] at h; subst h; exact .noVersionField
      | some v =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .supported ‹_›
        · split at h
          · simp only [List.mem_singleton] at h; subst h
            rename_i hns h0
            subst h0
            exact .recvVersionNegotiation hns
          · split at h
            · simp only [List.mem_singleton] at h; subst h
              exact .unsupportedTooSmall ‹_› ‹_› ‹_›
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h <;> subst h
              · exact .unsupportedSendVn ‹_› ‹_› ‹_›
              · exact .unsupportedSilent ‹_› ‹_› ‹_›
  · intro h
    cases h with
    | noVersionField => simp [outcomes]
    | supported h => simp [outcomes, h]
    | recvVersionNegotiation hs => simp [outcomes, hs]
    | unsupportedTooSmall h h0 hn => simp [outcomes, h, h0, hn]
    | unsupportedSendVn h h0 hn => simp [outcomes, h, h0, hn]
    | unsupportedSilent h h0 hn => simp [outcomes, h, h0, hn]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e with
  | datagram n version d c =>
    cases version <;> simp only [outcomes] <;> repeat' split
    all_goals simp

/-! ### 5. Invariant -/

/-- A server never "supports" the Version Negotiation marker (§15, line 5924)
    nor a reserved version (§15, line 5953: "Reserved version numbers will never
    represent a real protocol"), and every version it accepts appears in the
    list it advertises (§6.1, line 2065: "This includes a list of versions that
    the server will accept").  Nothing in this component changes the state, so
    the invariant is trivially preserved. -/
def Inv (s : State) : Prop :=
  versionNegotiationVersion ∉ s.supported ∧
  (∀ v ∈ s.supported, isReservedVersion v = false) ∧
  (∀ v ∈ s.supported, v ∈ s.advertised)

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h <;> exact hi

/-! ### 6. Send side

A Version Negotiation packet is not a frame, so the frame-level `MaySend` is
`True` and the real rule is the packet-level `MaySendVn`. -/

def MaySend (_ : State) (_ : Frame) : Prop := True
def maySend (_ : State) (_ : Frame) : Bool := true
theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-- When the server may emit the Version Negotiation packet `vn` in response to
    the datagram `e`: only for an unsupported, non-zero version in a datagram
    large enough to have started a connection (§5.2.2, §6.1), echoing both
    connection IDs and listing every version the server accepts (§17.2.1). -/
def MaySendVn (s : State) : Event → Vn → Prop
  | .datagram _ none _ _, _ => False
  | .datagram n (some v) d c, vn =>
      v ∉ s.supported ∧ v ≠ versionNegotiationVersion ∧
      smallestMaxDatagramSize ≤ n ∧
      vn.dcid = c ∧ vn.scid = d ∧ (∀ w ∈ s.supported, w ∈ vn.versions)

def maySendVn (s : State) : Event → Vn → Bool
  | .datagram _ none _ _, _ => false
  | .datagram n (some v) d c, vn =>
      !(decide (v ∈ s.supported)) && !(decide (v = versionNegotiationVersion)) &&
      decide (smallestMaxDatagramSize ≤ n) && decide (vn.dcid = c) && decide (vn.scid = d) &&
      s.supported.all (fun w => decide (w ∈ vn.versions))

theorem maySendVn_iff (s : State) (e : Event) (vn : Vn) :
    maySendVn s e vn = true ↔ MaySendVn s e vn := by
  cases e with
  | datagram n version d c =>
    cases version <;> simp [maySendVn, MaySendVn, List.all_eq_true, and_assoc]

/-! ### 7. The component -/

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

/-! ### 8. Named theorems -/

/-- Named theorem (d): every outcome for a datagram shorter than 1200 bytes
    whose version the server does not support is `.drop` (§5.2.2, line 1916:
    "Servers MUST drop smaller packets that specify unsupported versions"). -/
theorem small_unsupported_drop {s : State} {n v : Nat} {d c : ByteArray} {o : Out}
    (hv : v ∉ s.supported) (hn : n < smallestMaxDatagramSize)
    (h : Step s (.datagram n (some v) d c) o) : o = .drop := by
  cases h with
  | supported h => exact absurd h hv
  | recvVersionNegotiation => rfl
  | unsupportedTooSmall => rfl
  | unsupportedSendVn _ _ hn' => exact absurd hn hn'
  | unsupportedSilent _ _ hn' => exact absurd hn hn'

/-- §6.1, line 2066: "An endpoint MUST NOT send a Version Negotiation packet in
    response to receiving a Version Negotiation packet." -/
theorem no_vn_in_response_to_vn {s : State} {n : Nat} {d c : ByteArray} {o : Out}
    (hs : versionNegotiationVersion ∉ s.supported)
    (h : Step s (.datagram n (some versionNegotiationVersion) d c) o) : o = .drop := by
  cases h with
  | supported h => exact absurd h hs
  | recvVersionNegotiation => rfl
  | unsupportedTooSmall => rfl
  | unsupportedSendVn _ h0 => exact absurd rfl h0
  | unsupportedSilent _ h0 => exact absurd rfl h0

/-- Everything the spec permits the server to send is permitted by
    `MaySendVn`: `Step` and the send-side predicate agree. -/
theorem sendVn_maySendVn {s s' : State} {e : Event} {fx : List Effect} {vn : Vn}
    (hi : Inv s) (h : Step s e (.ok s' fx)) (hmem : Effect.sendVersionNegotiation vn ∈ fx) :
    MaySendVn s e vn := by
  cases h with
  | noVersionField => simp at hmem
  | supported => simp at hmem
  | unsupportedSendVn hv h0 hn =>
    simp only [List.mem_singleton, Effect.sendVersionNegotiation.injEq] at hmem
    subst hmem
    exact ⟨hv, h0, Nat.le_of_not_lt hn, rfl, rfl, hi.2.2⟩

/-- §17.2.1, line 6295: "A server MUST NOT send more than one Version
    Negotiation packet in response to a single UDP datagram." -/
theorem at_most_one_vn {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : (fx.filter Effect.isSendVn).length ≤ 1 := by
  cases h <;>
    first
      | simp [Effect.isSendVn]
      | (simp only [List.filter, Effect.isSendVn, List.length_cons, List.length_nil]; omega)

/-- Named theorem (c): the Version Negotiation packet the server builds for a
    datagram echoes the connection IDs that `Quic.versionCid` reads out of that
    datagram — its Source Connection ID becomes the VN's Destination Connection
    ID and vice versa (§17.2.1, lines 6260–6263). -/
theorem vn_echoes_versionCid {s : State} {buf : ByteArray} {e : Event} {s' : State}
    {fx : List Effect} {vn : Vn}
    (he : eventOfDatagram s buf = some e)
    (h : Step s e (.ok s' fx)) (hmem : Effect.sendVersionNegotiation vn ∈ fx) :
    ∃ vc r, Quic.versionCid buf s.shortDcidLen = Except.ok (vc, r) ∧
      vn.dcid = vc.scid ∧ vn.scid = vc.dcid ∧ vn.versions = s.advertised := by
  unfold eventOfDatagram at he
  split at he
  · rename_i vc r hvc
    obtain ⟨ver, vdcid, vscid⟩ := vc
    by_cases hl : isLongHeader buf = true
    · simp only [hl, Option.some.injEq] at he
      subst he
      cases h with
      | supported => simp at hmem
      | unsupportedSendVn _ _ _ =>
        simp only [List.mem_singleton, Effect.sendVersionNegotiation.injEq] at hmem
        subst hmem
        exact ⟨_, r, hvc, rfl, rfl, rfl⟩
    · simp only [Bool.not_eq_true] at hl
      simp only [hl, Option.some.injEq] at he
      subst he
      cases h with
      | noVersionField => simp at hmem
  · simp at he

/-- The version list of a Version Negotiation packet the server sends is exactly
    the list it advertises, which contains every version it accepts (§6.1, line
    2065) and may contain reserved versions for greasing (§6.3, line 2150). -/
theorem vn_lists_supported {s : State} {s' : State} {e : Event} {fx : List Effect} {vn : Vn}
    (hi : Inv s) (h : Step s e (.ok s' fx))
    (hmem : Effect.sendVersionNegotiation vn ∈ fx) :
    ∀ w ∈ s.supported, w ∈ vn.versions := by
  cases h with
  | noVersionField => simp at hmem
  | supported => simp at hmem
  | unsupportedSendVn _ _ _ =>
    simp only [List.mem_singleton, Effect.sendVersionNegotiation.injEq] at hmem
    subst hmem
    exact hi.2.2

/-- Named theorem (e), in the form the server's state needs it: no version the
    server accepts is a reserved version. -/
theorem supported_not_reserved {s : State} (hi : Inv s) {v : Nat} (h : v ∈ s.supported) :
    isReservedVersion v = false := hi.2.1 v h

/-! ### 9. Examples (scenarios from the text) -/

private def srv : State :=
  { supported := [versionV1], advertised := [versionV1, 0x0a0a0a0a], shortDcidLen := 8 }

-- §5.2.2: a supported version is delivered, whatever the datagram size.
example : component.step srv (.datagram 1200 (some versionV1) ⟨#[1]⟩ ⟨#[2]⟩) =
    .ok srv [.deliver] := by decide
example : component.step srv (.datagram 40 (some versionV1) ⟨#[1]⟩ ⟨#[2]⟩) =
    .ok srv [.deliver] := by decide
-- §5.2.2: a short header has no version field, so it is matched to a connection.
example : component.step srv (.datagram 40 none ⟨#[1]⟩ ByteArray.empty) =
    .ok srv [.deliver] := by decide
-- §5.2.2 / §6.1: an unsupported version in a full-size datagram is answered
-- with a Version Negotiation packet that echoes both connection IDs.
example : component.step srv (.datagram 1200 (some 0xff00001d) ⟨#[1,2,3]⟩ ⟨#[9]⟩) =
    .ok srv [.sendVersionNegotiation
      { dcid := ⟨#[9]⟩, scid := ⟨#[1,2,3]⟩, versions := [versionV1, 0x0a0a0a0a] }] := by decide
-- … but "A server MAY limit the number of packets to which it responds", so
-- silence is permitted too.
example : component.accepts srv (.datagram 1200 (some 0xff00001d) ⟨#[1,2,3]⟩ ⟨#[9]⟩)
    .drop = true := by decide
-- §5.2.2: "Servers MUST drop smaller packets that specify unsupported versions."
example : component.step srv (.datagram 1199 (some 0xff00001d) ⟨#[1,2,3]⟩ ⟨#[9]⟩) =
    .drop := by decide
example : component.accepts srv (.datagram 1199 (some 0xff00001d) ⟨#[1,2,3]⟩ ⟨#[9]⟩)
    (.ok srv [.sendVersionNegotiation
      { dcid := ⟨#[9]⟩, scid := ⟨#[1,2,3]⟩, versions := [versionV1, 0x0a0a0a0a] }]) =
    false := by decide
-- §6.3: a reserved version is treated like any other unsupported version.
example : component.step srv (.datagram 1200 (some 0x1a2a3a4a) ⟨#[7]⟩ ⟨#[8]⟩) =
    .ok srv [.sendVersionNegotiation
      { dcid := ⟨#[8]⟩, scid := ⟨#[7]⟩, versions := [versionV1, 0x0a0a0a0a] }] := by decide
-- §6.1: never a Version Negotiation packet in reply to one.
example : component.step srv (.datagram 1200 (some 0) ⟨#[1]⟩ ⟨#[2]⟩) = .drop := by decide
-- The event a real datagram produces, read out of `Quic.versionCid`: a long
-- header of version 1 with DCID 0x0102 and SCID 0x09.
example : eventOfDatagram srv ⟨#[0xc0, 0x00, 0x00, 0x00, 0x01, 2, 1, 2, 1, 9]⟩ =
    some (.datagram 10 (some versionV1) ⟨#[1,2]⟩ ⟨#[9]⟩) := by decide
-- A datagram `Quic.versionCid` rejects — here an unsupported version in a
-- datagram too small to answer — never becomes an event at all (§5.2.2:
-- "Servers MUST drop incoming packets under all other circumstances").
example : eventOfDatagram srv ⟨#[0xc0, 0xff, 0x00, 0x00, 0x1d, 2, 1, 2, 1, 9]⟩ = none := by decide
-- §17.2.1: the packet those contents go in is the header `QuicModel/Packet.lean`
-- decodes, with the connection IDs swapped.
example : (mkVersionNegotiation srv ⟨#[1,2,3]⟩ ⟨#[9]⟩).header =
    Header.versionNegotiation ⟨#[9]⟩ ⟨#[1,2,3]⟩ := rfl

end Server

/-! ## The client (§5.2.1, §6.2) -/

namespace Client

/-! ### 1. State, events, effects -/

structure State where
  /-- The Destination Connection ID the client put in the packets it sent. -/
  dcid : ByteArray
  /-- The Source Connection ID the client put in those packets. -/
  scid : ByteArray
  /-- §5.2.1, line 1898: the version the client "initially selected". -/
  chosen : Nat
  /-- §6.2, line 2100: whether the client "has received and successfully
      processed any other packet, including an earlier Version Negotiation
      packet". -/
  processedAny : Bool
  /-- §6.2: whether the current connection attempt has been abandoned. -/
  abandoned : Bool
  deriving DecidableEq

inductive Event where
  /-- A Version Negotiation packet arrived with these connection IDs and this
      list of versions (§17.2.1; `Quic.decodePacket` returns them as
      `Body.versions`). -/
  | recvVersionNegotiation (dcid scid : ByteArray) (versions : List Nat)
  /-- Any other packet arrived, carrying `version`.  `processedOk` is whether
      the rest of the stack processed it successfully — removing packet
      protection and so on — which is what §6.2 counts; it also covers §5.2.1's
      "The client MAY drop these packets, or MAY buffer them" for packets whose
      keys are not yet available. -/
  | recvOther (version : Nat) (processedOk : Bool)
  deriving DecidableEq

inductive Effect where
  /-- The packet is processed by the connection. -/
  | deliver
  /-- §6.2, line 2098: "MUST abandon the current connection attempt". -/
  | abandon
  /-- §6.2.1, line 2115 (draft-only): start a new connection attempt with this
      version from the list. -/
  | attemptVersion (v : Nat)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-- The state after acting on a Version Negotiation packet: the attempt is over,
    and the packet counts as "successfully processed" for the next one
    (§6.2, line 2100: "including an earlier Version Negotiation packet"). -/
def State.afterVn (s : State) : State := { s with processedAny := true, abandoned := true }

/-- §6.2.1, line 2136: "The new connection MUST use a new random Destination
    Connection ID different from the one it had previously sent."  The new
    attempt is a new instance of this component, so this is a side condition on
    how it is started rather than a transition here. -/
def MayStartNewAttempt (s : State) (newDcid : ByteArray) : Prop := newDcid ≠ s.dcid

/-- The versions of a Version Negotiation packet that a client of this draft may
    pick under §6.2.1: not the Version Negotiation marker, and not a reserved
    version, since those "will never represent a real protocol" (§15). -/
def usableVersions (vs : List Nat) : List Nat :=
  vs.filter (fun v => decide (v ≠ versionNegotiationVersion) && !isReservedVersion v)

/-! ### 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §5.2.1, line 1889: "Packets that do not match an existing connection ...
      are discarded."  Once the attempt has been abandoned there is no
      connection left to match. -/
  | afterAbandon {s e} (ha : s.abandoned = true) : Step s e .drop
  /-- §5.2.1, line 1898: "If a client receives a packet that uses a different
      version than it initially selected, it MUST discard that packet." -/
  | wrongVersion {s v ok} (ha : s.abandoned = false) (h : v ≠ s.chosen) :
      Step s (.recvOther v ok) .drop
  /-- §5.2.1, line 1893: "the client MAY drop these packets, or MAY buffer them
      in anticipation of later packets that allow it to compute the key" — a
      packet that is not successfully processed changes nothing. -/
  | notProcessed {s v} (ha : s.abandoned = false) (h : v = s.chosen) :
      Step s (.recvOther v false) .drop
  /-- A packet of the selected version that is processed successfully is what
      §6.2 line 2100 counts as "any other packet". -/
  | otherProcessed {s v} (ha : s.abandoned = false) (h : v = s.chosen) :
      Step s (.recvOther v true) (.ok { s with processedAny := true } [.deliver])
  /-- §6.2, line 2100: "A client MUST discard any Version Negotiation packet if
      it has received and successfully processed any other packet, including an
      earlier Version Negotiation packet." -/
  | vnAfterOther {s d c vs} (ha : s.abandoned = false) (hp : s.processedAny = true) :
      Step s (.recvVersionNegotiation d c vs) .drop
  /-- §6.2, line 2103: "A client MUST discard a Version Negotiation packet that
      lists the QUIC version selected by the client." -/
  | vnListsChosen {s d c vs} (ha : s.abandoned = false) (hp : s.processedAny = false)
      (h : s.chosen ∈ vs) : Step s (.recvVersionNegotiation d c vs) .drop
  /-- §6.2.1, line 2120: "The client MUST check that the Destination and Source
      Connection ID fields match the Source and Destination Connection ID fields
      in a packet that the client sent.  If this check fails, the packet MUST be
      discarded." -/
  | vnCidMismatch {s d c vs} (ha : s.abandoned = false) (hp : s.processedAny = false)
      (hc : s.chosen ∉ vs) (h : ¬ (d = s.scid ∧ c = s.dcid)) :
      Step s (.recvVersionNegotiation d c vs) .drop
  /-- §6.2, line 2098: "A client that supports only this version of QUIC MUST
      abandon the current connection attempt if it receives a Version
      Negotiation packet, with the following two exceptions." -/
  | vnAbandon {s d c vs} (ha : s.abandoned = false) (hp : s.processedAny = false)
      (hv : s.chosen ∉ vs) (hd : d = s.scid) (hs : c = s.dcid) :
      Step s (.recvVersionNegotiation d c vs) (.ok s.afterVn [.abandon])
  /-- §6.2.1, line 2115 (draft-only): "When a draft implementation receives a
      Version Negotiation packet, it MAY use it to attempt a new connection with
      one of the versions listed in the packet, instead of abandoning the
      current connection attempt". -/
  | vnRetry {s d c vs v} (ha : s.abandoned = false) (hp : s.processedAny = false)
      (hv : s.chosen ∉ vs) (hd : d = s.scid) (hs : c = s.dcid)
      (hmem : v ∈ usableVersions vs) :
      Step s (.recvVersionNegotiation d c vs) (.ok s.afterVn [.attemptVersion v])

/-! ### 3. Executable form -/

def outcomes (s : State) (e : Event) : List Out :=
  if s.abandoned then [.drop] else
  match e with
  | .recvOther v ok =>
    if v ≠ s.chosen then [.drop]
    else if ok then [.ok { s with processedAny := true } [.deliver]]
    else [.drop]
  | .recvVersionNegotiation d c vs =>
    if s.processedAny then [.drop]
    else if s.chosen ∈ vs then [.drop]
    else if ¬ (d = s.scid ∧ c = s.dcid) then [.drop]
    else (.ok s.afterVn [.abandon]) ::
      (usableVersions vs).map (fun v => .ok s.afterVn [.attemptVersion v])

/-! ### 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    simp only [outcomes] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; exact .afterAbandon ‹_›
    · rename_i hab
      have hab' : s.abandoned = false := by simpa using hab
      cases e with
      | recvOther v ok =>
        simp only at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .wrongVersion hab' ‹_›
        · rename_i hveq
          have hv : v = s.chosen := by simpa using hveq
          split at h
          · rename_i hok
            subst hok
            simp only [List.mem_singleton] at h; subst h
            exact .otherProcessed hab' hv
          · rename_i hok
            simp only [Bool.not_eq_true] at hok
            subst hok
            simp only [List.mem_singleton] at h; subst h
            exact .notProcessed hab' hv
      | recvVersionNegotiation d c vs =>
        simp only at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .vnAfterOther hab' ‹_›
        · rename_i hpr
          have hp : s.processedAny = false := by simpa using hpr
          split at h
          · simp only [List.mem_singleton] at h; subst h; exact .vnListsChosen hab' hp ‹_›
          · split at h
            · simp only [List.mem_singleton] at h; subst h
              exact .vnCidMismatch hab' hp ‹_› ‹_›
            · rename_i hcid
              have hcid' : d = s.scid ∧ c = s.dcid := by simpa using hcid
              simp only [List.mem_cons, List.mem_map] at h
              rcases h with h | ⟨v, hv, h⟩
              · subst h; exact .vnAbandon hab' hp ‹_› hcid'.1 hcid'.2
              · subst h; exact .vnRetry hab' hp ‹_› hcid'.1 hcid'.2 hv
  · intro h
    cases h with
    | afterAbandon ha => simp [outcomes, ha]
    | wrongVersion ha h => simp [outcomes, ha, h]
    | notProcessed ha h => simp [outcomes, ha, h]
    | otherProcessed ha h => simp [outcomes, ha, h]
    | vnAfterOther ha hp => simp [outcomes, ha, hp]
    | vnListsChosen ha hp h => simp [outcomes, ha, hp, h]
    | vnCidMismatch ha hp hc h => simp [outcomes, ha, hp, hc, h]
    | vnAbandon ha hp hv hd hs => simp [outcomes, ha, hp, hv, hd, hs]
    | vnRetry ha hp hv hd hs hmem =>
      simp only [outcomes, ha, hp, hv, hd, hs, Bool.false_eq_true, not_true_eq_false, and_self]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  simp only [outcomes]
  split
  · simp
  · cases e <;> repeat' split
    all_goals simp

/-! ### 5. Invariant -/

/-- Neither flag is ever cleared: a connection attempt that has processed a
    packet has processed one forever, and an abandoned attempt stays abandoned.
    (Stated as a relation between successive states by `flags_mono` below; `Inv`
    itself records the one structural fact, that an abandoned attempt has
    processed the Version Negotiation packet that abandoned it.) -/
def Inv (s : State) : Prop := s.abandoned = true → s.processedAny = true

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (_hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | otherProcessed => intro _; rfl
  | vnAbandon => intro _; rfl
  | vnRetry => intro _; rfl

/-! ### 6. Send side — this component governs no frame. -/

def MaySend (_ : State) (_ : Frame) : Prop := True
def maySend (_ : State) (_ : Frame) : Bool := true
theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-! ### 7. The component -/

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

/-! ### 8. Named theorems -/

/-- Acting on a Version Negotiation packet: a step that answers one with
    something other than silence. -/
def ActsOnVn : Event → List Effect → Prop
  | .recvVersionNegotiation .., fx => fx ≠ []
  | .recvOther .., _ => False

/-- Named theorem (a): a client never acts on a Version Negotiation packet that
    lists the version it chose — the packet is discarded (§6.2, line 2103). -/
theorem never_acts_on_own_version {s : State} {d c : ByteArray} {vs : List Nat} {o : Out}
    (h : s.chosen ∈ vs) (hs : Step s (.recvVersionNegotiation d c vs) o) : o = .drop := by
  cases hs with
  | afterAbandon => rfl
  | vnAfterOther => rfl
  | vnListsChosen => rfl
  | vnCidMismatch => rfl
  | vnAbandon _ _ hv => exact absurd h hv
  | vnRetry _ _ hv => exact absurd h hv

/-- Neither flag is ever cleared. -/
theorem flags_mono {s s' : State} {e : Event} {fx : List Effect} (h : Step s e (.ok s' fx)) :
    (s.processedAny = true → s'.processedAny = true) ∧
    (s.abandoned = true → s'.abandoned = true) := by
  cases h with
  | otherProcessed => exact ⟨fun _ => rfl, fun h => h⟩
  | vnAbandon => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | vnRetry => exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem processedAny_reachable {s₀ s : State} (h0 : s₀.processedAny = true)
    (h : component.Reachable s₀ s) : s.processedAny = true :=
  Component.Reachable.rec (motive := fun (x : State) _ => x.processedAny = true) h0
    (fun _ hs ih => (flags_mono hs).1 ih) h

/-- Acting on a Version Negotiation packet requires an untouched connection
    attempt and marks it as processed. -/
theorem acts_on_vn_marks {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (ha : ActsOnVn e fx) :
    s.processedAny = false ∧ s'.processedAny = true := by
  cases h with
  | otherProcessed => exact absurd ha (by simp [ActsOnVn])
  | vnAbandon _ hp => exact ⟨hp, rfl⟩
  | vnRetry _ hp => exact ⟨hp, rfl⟩

/-- Named theorem (b): a client acts on at most one Version Negotiation packet
    per connection attempt.  Once it has acted on one, every later step — with
    any number of steps in between — discards the next one (§6.2, line 2100). -/
theorem acts_on_vn_once {s₀ s₁ s₂ s₃ : State} {e₁ e₂ : Event} {fx₁ fx₂ : List Effect}
    (h₁ : Step s₀ e₁ (.ok s₁ fx₁)) (ha₁ : ActsOnVn e₁ fx₁)
    (hr : component.Reachable s₁ s₂)
    (h₂ : Step s₂ e₂ (.ok s₃ fx₂)) : ¬ ActsOnVn e₂ fx₂ := by
  intro ha₂
  have h1 : s₁.processedAny = true := (acts_on_vn_marks h₁ ha₁).2
  have h2 : s₂.processedAny = true := processedAny_reachable h1 hr
  have h3 : s₂.processedAny = false := (acts_on_vn_marks h₂ ha₂).1
  rw [h2] at h3
  exact Bool.noConfusion h3

/-- A client that acts on a Version Negotiation packet always ends the current
    connection attempt (§6.2, line 2098). -/
theorem acting_abandons {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (ha : ActsOnVn e fx) : s'.abandoned = true := by
  cases h with
  | otherProcessed => exact absurd ha (by simp [ActsOnVn])
  | vnAbandon => rfl
  | vnRetry => rfl

/-- §6.2.1: a version the client moves to was listed in the packet and is a
    version that can represent a real protocol (§15). -/
theorem attempted_version_listed {s s' : State} {d c : ByteArray} {vs : List Nat}
    {fx : List Effect} {v : Nat}
    (h : Step s (.recvVersionNegotiation d c vs) (.ok s' fx))
    (hmem : Effect.attemptVersion v ∈ fx) :
    v ∈ vs ∧ v ≠ versionNegotiationVersion ∧ isReservedVersion v = false := by
  cases h with
  | vnAbandon => simp at hmem
  | vnRetry _ _ _ _ _ hm =>
    simp only [List.mem_singleton, Effect.attemptVersion.injEq] at hmem
    subst hmem
    simp only [usableVersions, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hm
    exact ⟨hm.1, hm.2.1, hm.2.2⟩

/-! ### 9. Examples (scenarios from the text) -/

private def cli : State :=
  { dcid := ⟨#[1,2,3,4]⟩, scid := ⟨#[9,9]⟩, chosen := versionV1,
    processedAny := false, abandoned := false }

-- §6.2: a Version Negotiation packet that echoes both connection IDs and does
-- not list the chosen version abandons the connection attempt.
example : component.step cli (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d]) =
    .ok cli.afterVn [.abandon] := by decide
-- §6.2.1 (draft-only): trying one of the listed versions instead is permitted.
example : component.accepts cli (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d])
    (.ok cli.afterVn [.attemptVersion 0xff00001d]) = true := by decide
-- … but not a reserved version, which never represents a real protocol (§15).
example : component.accepts cli (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [0x1a2a3a4a])
    (.ok cli.afterVn [.attemptVersion 0x1a2a3a4a]) = false := by decide
-- §6.2: "MUST discard a Version Negotiation packet that lists the QUIC version
-- selected by the client."
example : component.step cli
    (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [versionV1, 0xff00001d]) = .drop := by decide
-- §6.2.1: "The client MUST check that the Destination and Source Connection ID
-- fields match the Source and Destination Connection ID fields in a packet that
-- the client sent."
example : component.step cli (.recvVersionNegotiation ⟨#[7,7]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d]) =
    .drop := by decide
-- §6.2: "MUST discard any Version Negotiation packet if it has received and
-- successfully processed any other packet".
example : component.step { cli with processedAny := true }
    (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d]) = .drop := by decide
-- … and processing a server packet is what sets that flag.
example : component.step cli (.recvOther versionV1 true) =
    .ok { cli with processedAny := true } [.deliver] := by decide
-- §5.2.1: "If a client receives a packet that uses a different version than it
-- initially selected, it MUST discard that packet."
example : component.step cli (.recvOther versionV2 true) = .drop := by decide
-- … and a packet it cannot yet decrypt leaves the flag clear, so a later
-- Version Negotiation packet is still acted upon.
example : component.step cli (.recvOther versionV1 false) = .drop := by decide
-- Following an implementation from the outside: the abandon is observable.
example : component.track cli (.recvVersionNegotiation ⟨#[9,9]⟩ ⟨#[1,2,3,4]⟩ [0xff00001d])
    (.ok [.abandon]) = some { cli with processedAny := true, abandoned := true } := by decide
-- Once abandoned, nothing is processed any more (§5.2.1).
example : component.step cli.afterVn (.recvOther versionV1 true) = .drop := by decide

end Client

/-! ## 10. Coverage and notes

Assigned ranges: lines 1835–1984 (§5.2), 2044–2156 (§6), 5920–5958 (§15).
(§14, lines 5640–5919, is covered by `Spec/DatagramSize.lean`.)

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §5.2 (1853) | associate a packet with an existing connection by DCID | out of scope: the connection table is WP12 `Endpoint`; §5.2's routing MUSTs about CIDs are WP4 `ConnIds` |
| §5.2 (1867) | endpoints can send a Stateless Reset for unattributable packets | out of scope: WP6 `Termination` |
| §5.2 (1872) | packets inconsistent with the connection state are discarded, e.g. a different version | `Client.Step.wrongVersion` (client side); server side is `Server.Step.supported`'s complement |
| §5.2 (1878) | invalid Initial/Retry/VN MAY be discarded; otherwise a connection error or full revert | `Client.Step.notProcessed`, `Server.Step.unsupportedSilent`; Retry is WP5 |
| §5.2.1 (1889) | packets that do not match an existing connection are discarded | `Client.Step.afterAbandon` |
| §5.2.1 (1893) | MAY drop or buffer packets whose keys are not yet available | `Client.Step.notProcessed` (`processedOk = false`) |
| §5.2.1 (1898) | a client MUST discard a packet of a version other than the one it selected | `Client.Step.wrongVersion` |
| §5.2.2 (1911) | unsupported version + large enough → SHOULD send Version Negotiation | `Server.Step.unsupportedSendVn` |
| §5.2.2 (1914) | a server MAY limit the number of packets it responds to | `Server.Step.unsupportedSilent` |
| §5.2.2 (1916) | servers MUST drop smaller packets with unsupported versions | `Server.Step.unsupportedTooSmall`, theorem `small_unsupported_drop` |
| §5.2.2 (1923) | servers SHOULD respond with VN provided the datagram is long enough | same as line 1911 |
| §5.2.2 (1926) | supported version or no version field → match to a connection | `Server.Step.supported`, `Server.Step.noVersionField` |
| §5.2.2 (1932) | a conforming Initial commits the server to the client's version | out of scope: WP11 `Handshake` |
| §5.2.2 (1936) | refusing a connection SHOULD send CONNECTION_CLOSE(CONNECTION_REFUSED) | out of scope: WP6 `Termination` |
| §5.2.2 (1940) | 0-RTT MAY be buffered; servers SHOULD ignore client Handshake packets | out of scope: WP11 `Handshake` |
| §5.2.2 (1946) | servers MUST drop incoming packets under all other circumstances | `Server.eventOfDatagram = none` (unparseable), `Server.Step.recvVersionNegotiation` |
| §5.2.3 (1948–1983) | load-balancer advice; stateless reset oracle | out of scope: deployment advice; stateless reset is WP6 |
| §6 (2051) | clients SHOULD size the first datagram to the largest minimum of all versions they support | `DatagramSize.MaySendDatagram` (1200 for this version); the multi-version SHOULD is advice, see NOTES |
| §6.1 (2063) | the server responds with a Version Negotiation packet listing versions it accepts | `Server.mkVersionNegotiation`, `Server.MaySendVn`, theorem `vn_lists_supported` |
| §6.1 (2066) | MUST NOT send a VN in response to a VN | `Server.Step.recvVersionNegotiation`, theorem `no_vn_in_response_to_vn` |
| §6.1 (2083) | a server MAY limit the number of VN packets it sends | `Server.Step.unsupportedSilent` |
| §6.2 (2098) | a client MUST abandon the attempt on receiving a VN | `Client.Step.vnAbandon`, theorem `acting_abandons` |
| §6.2 (2100) | MUST discard a VN if any other packet was received and successfully processed | `Client.Step.vnAfterOther`, theorem `acts_on_vn_once` |
| §6.2 (2103) | MUST discard a VN that lists the version the client selected | `Client.Step.vnListsChosen`, theorem `never_acts_on_own_version` |
| §6.2.1 (2115) | a draft implementation MAY try a version from the list instead | `Client.Step.vnRetry` |
| §6.2.1 (2120) | the client MUST check the echoed connection IDs; otherwise discard | `Client.Step.vnCidMismatch` |
| §6.2.1 (2136) | the new connection MUST use a new random DCID | `Client.MayStartNewAttempt` |
| §6.2.1 (2141) | MUST NOT be used outside of draft implementations | see NOTES |
| §6.3 (2147) | 0x?a?a?a?a versions are reserved | `isReservedVersion`, theorem `isReservedVersion_iff` |
| §6.3 (2150) | endpoints MAY add reserved versions to fields where unknown versions are ignored | `Server.State.advertised` may differ from `supported` |
| §6.3 (2154) | endpoints MAY send packets with a reserved version | the server treats them like any other unsupported version (example in §9) |
| §15 (5924) | version 0x00000000 is reserved to represent version negotiation | `versionNegotiationVersion`, `Server.Step.recvVersionNegotiation` |
| §15 (5944) | versions with the top 16 bits cleared are reserved for IETF consensus documents | not normative for an endpoint: no MUST/MAY for either role |
| §15 (5947) | 0x?a?a?a?a is reserved; a client or server MAY advertise support for them | `isReservedVersion`, `Server.State.advertised` |
| §15 (5953) | reserved versions never represent a real protocol | `Server.Inv` (never in `supported`), `Client.usableVersions`, theorems `reserved_not_supported`, `supported_not_reserved` |
| §17.2.1 (6260) | the server MUST echo SCID→DCID and DCID→SCID | `Server.mkVersionNegotiation`, theorem `vn_echoes_versionCid` |
| §17.2.1 (6295) | a server MUST NOT send more than one VN per UDP datagram | theorem `at_most_one_vn` |

NOTES

- **Where the datagram's fields come from.**  `Server.Event.datagram` carries the
  RFC 8999 version-independent fields, not the raw bytes, and
  `Server.eventOfDatagram` produces it from the existing `Quic.versionCid`.  The
  parser is therefore not duplicated, and a datagram `versionCid` rejects never
  becomes an event at all — which is §5.2.2's "Servers MUST drop incoming
  packets under all other circumstances".  Note that `versionCid` itself already
  makes the §5.2.2 routing decision for the fixed version set of
  `Quic.isSupportedVersion` (v1 and v2); this component repeats the decision
  against `State.supported`, so a server that supports some other set is
  modelled correctly and the two agree when `supported = [v1, v2]`.
- **"Large enough to initiate a new connection for any supported version".**
  Read as ≥ 1200 bytes, the value §14.1 fixes for this version
  (`DatagramSize.smallestMaxDatagramSize`).  A server supporting a future
  version with a larger minimum would use that instead; the model has one
  version family, so one constant.  §6 line 2051's matching client-side advice
  ("sized to the largest of the minimum datagram sizes from all versions they
  support") is a SHOULD about versions this model does not know, so it is not
  encoded.
- **Version 0 is never "supported".**  A long header with version 0 is a Version
  Negotiation packet, so `Server.Step.recvVersionNegotiation` takes precedence
  over `Server.Step.supported`; both carry the hypothesis that makes them
  disjoint, and `Server.Inv` rules the bad case out.  A *short* header also has
  no version field, so `Event.version = none` is used for it rather than
  `some 0`; `Quic.versionCid` reports version 0 for both, which is why
  `eventOfDatagram` looks at the header form bit.
- **§6.2 versus §6.2.1.**  §6.2 says a client "MUST abandon the current
  connection attempt"; §6.2.1, which the RFC editor was asked to delete before
  publication, says a draft implementation "MAY use it to attempt a new
  connection with one of the versions listed in the packet, instead of
  abandoning the current connection attempt".  Both are encoded
  (`vnAbandon`, `vnRetry`), with `vnAbandon` preferred so that `component.step`
  is the RFC 9000 behaviour.  The reading taken is that even under §6.2.1 the
  *current* attempt is over — the new attempt is a new connection with a new
  DCID (`MayStartNewAttempt`), hence a new instance of this component — so both
  alternatives set `abandoned`.  An implementation of RFC 9000 rather than
  draft-34 will never take `vnRetry`; it is permitted, not recommended, and the
  differential harness should not be surprised by ngtcp2 abandoning.
  §6.2.1's "MUST NOT be used outside of draft implementations" cannot be
  expressed as a transition rule: it is a condition on the implementation, not
  on a state.
- **Reserved versions in `vnRetry`.**  §6.2.1 says the client "selects an
  acceptable protocol version from the list".  A reserved version "will never
  represent a real protocol" (§15), and version 0 is the negotiation marker, so
  `usableVersions` filters both out.  This is the one place the text is silent
  and a choice was made; the effect is only to forbid an outcome that no sane
  implementation produces.
- **After abandoning.**  `Client.Step.afterAbandon` drops everything once the
  attempt is abandoned, on the strength of §5.2.1 line 1889 ("Packets that do
  not match an existing connection ... are discarded"): the abandoned attempt no
  longer exists.  Without this rule `Step` would let a client keep processing
  packets for a connection it gave up on.
- **What "acting on a Version Negotiation packet" means** (`Client.ActsOnVn`):
  an outcome with a non-empty effect list for a `recvVersionNegotiation` event.
  Named theorem (b) then holds for any number of intervening steps, because
  `processedAny` is monotone (`flags_mono`, `processedAny_reachable`).
- **`MaySend` and Version Negotiation.**  A Version Negotiation packet is not a
  frame, so `Component.MaySend` is `True` for both roles and the send-side rule
  is `Server.MaySendVn : State → Event → Vn → Prop`: the packet is permitted
  only as a response to a specific datagram, which is exactly what §6.1 and
  §17.2.1 say.  `sendVn_maySendVn` proves that everything `Step` permits the
  server to send satisfies it, given `Inv` — the invariant is what says the
  advertised list contains every supported version, which `MaySendVn` demands.
- **`Effect.deliver` is not "accept".**  For the server it means only that
  version handling does not stop the datagram: §5.2.2's connection lookup, and
  what a server does when no connection matches (a Stateless Reset, WP6, or a
  drop), are WP12's.  So this component never produces `.drop` for a supported
  version, and composition with the connection table may still drop it.
-/

end Quic.Spec.VersionNeg
