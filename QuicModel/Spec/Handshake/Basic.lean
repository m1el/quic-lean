import QuicModel.Spec.Handshake.Crypto
import QuicModel.Spec.TransportParams
import QuicModel.Spec.ConnIds.Common

/-!
  WP11 "Handshake", part 2: the transport side of the cryptographic handshake.

  §7 (lines 2157–2505), §7.5 (2696–2723), §17.2.2 and §17.2.2.1 (6300–6409),
  §17.2.3 and §17.2.4 (6410–6556), §19.6 (7509–7564), §19.20 (8193–8211).

  TLS is an opaque event source and sink, in the spirit of `Protection` in
  `QuicModel/Packet.lean`: it announces keys, hands over bytes to send, hands
  over the peer's (authenticated) transport parameter bytes, reports the fate of
  0-RTT, reports completion, and raises alerts.  The only thing that goes back
  into it is CRYPTO data, in order, per encryption level.  Nothing here knows
  what any of those bytes mean.

  File order follows `Spec/Template.lean`; the named theorems, the examples and
  the coverage table are in `Spec/Handshake.lean`.
-/
namespace Quic.Spec.Handshake

open Quic.Spec.Ack (Rng)
open Quic.Spec.ConnIds (Cid)

/-- WP1's decoded parameter record (`Spec/TransportParams/Wire.lean`).  The
    abbreviation is needed because `TransportParams` is also the name of the
    namespace WP1 lives in, which wins inside this one. -/
abbrev Params := Quic.Spec.TransportParams.TransportParams

/-! ## 0. Encryption levels and keys -/

/-- §7, line 2199: "The CRYPTO frame can be sent in different packet number
    spaces"; RFC 9001 calls the four key sets encryption levels. -/
inductive Level where | initial | zeroRtt | handshake | oneRtt
  deriving DecidableEq, Repr

/-- The three levels that carry a CRYPTO stream.  §19.6, line 7512: a CRYPTO
    frame "can be sent in all packet types except 0-RTT"; line 7541: "each
    encryption level is treated as a separate CRYPTO stream of data". -/
inductive CryptoLevel where | initial | handshake | oneRtt
  deriving DecidableEq, Repr

def CryptoLevel.level : CryptoLevel → Level
  | .initial => .initial
  | .handshake => .handshake
  | .oneRtt => .oneRtt

/-- The level whose keys protect a packet type.  Retry (§17.2.5) and Version
    Negotiation (§17.2.1) packets carry no level key. -/
def levelOf : PacketType → Option Level
  | .initial => some .initial
  | .zeroRtt => some .zeroRtt
  | .handshake => some .handshake
  | .oneRtt => some .oneRtt
  | .retry | .versionNegotiation => none

/-- The CRYPTO stream a packet type's payload belongs to. -/
def cryptoLevelOf : PacketType → Option CryptoLevel
  | .initial => some .initial
  | .handshake => some .handshake
  | .oneRtt => some .oneRtt
  | .zeroRtt | .retry | .versionNegotiation => none

inductive KeyDir where | read | write
  deriving DecidableEq, Repr

/-- §17.2.2.1, line 6403: "Initial packet protection keys are discarded".
    Discarding is final: the transport never asks for a key back. -/
inductive KeyState where | absent | present | discarded
  deriving DecidableEq, Repr

/-- One direction's four key sets. -/
structure Keys where
  initial : KeyState := .absent
  zeroRtt : KeyState := .absent
  handshake : KeyState := .absent
  oneRtt : KeyState := .absent
  deriving DecidableEq, Repr

namespace Keys
def get : Keys → Level → KeyState
  | k, .initial => k.initial
  | k, .zeroRtt => k.zeroRtt
  | k, .handshake => k.handshake
  | k, .oneRtt => k.oneRtt

def set : Keys → Level → KeyState → Keys
  | k, .initial, v => { k with initial := v }
  | k, .zeroRtt, v => { k with zeroRtt := v }
  | k, .handshake, v => { k with handshake := v }
  | k, .oneRtt, v => { k with oneRtt := v }

theorem get_set (k : Keys) (l l' : Level) (v : KeyState) :
    (k.set l v).get l' = if l' = l then v else k.get l' := by
  cases l <;> cases l' <;> simp [get, set]
end Keys

/-- The CRYPTO streams, one per level that has one. -/
structure Streams where
  initial : Crypto := {}
  handshake : Crypto := {}
  oneRtt : Crypto := {}
  deriving DecidableEq, Repr

namespace Streams
def get : Streams → CryptoLevel → Crypto
  | st, .initial => st.initial
  | st, .handshake => st.handshake
  | st, .oneRtt => st.oneRtt

def set : Streams → CryptoLevel → Crypto → Streams
  | st, .initial, c => { st with initial := c }
  | st, .handshake, c => { st with handshake := c }
  | st, .oneRtt, c => { st with oneRtt := c }

theorem get_set (st : Streams) (l l' : CryptoLevel) (c : Crypto) :
    (st.set l c).get l' = if l' = l then c else st.get l' := by
  cases l <;> cases l' <;> simp [get, set]
end Streams

/-- §17.2.3, line 6417: "As part of the TLS handshake, the server can accept or
    reject this early data." -/
inductive ZeroRtt where | notOffered | offered | accepted | rejected
  deriving DecidableEq, Repr

/-! ## 1. State, events, effects -/

structure State where
  /-- Our own role. -/
  role : Role
  /-- §7.5, line 2703: "Implementations MUST support buffering at least 4096
      bytes of data received in out-of-order CRYPTO frames.  Endpoints MAY
      choose to allow more data to be buffered during the handshake."  The
      invariant keeps this at 4096 or more. -/
  bufLimit : Nat := 4096
  /-- Keys for reading the peer's packets. -/
  read : Keys := {}
  /-- Keys for protecting our own packets. -/
  write : Keys := {}
  /-- The CRYPTO stream of each level. -/
  streams : Streams := {}
  /-- The TLS handshake has completed (RFC 9001 §4.1.1). -/
  complete : Bool := false
  /-- The handshake is confirmed (RFC 9001 §4.1.2, referenced at line 3281:
      "before the handshake is confirmed, as defined in section 4.1.2 of
      [QUIC-TLS]"): at the server when the handshake completes, at the client
      when a HANDSHAKE_DONE frame arrives (§19.20, line 8195). -/
  confirmed : Bool := false
  /-- What TLS said about 0-RTT. -/
  zeroRtt : ZeroRtt := .notOffered
  /-- §17.2.3, line 6476: "A client MUST NOT send 0-RTT packets once it starts
      processing 1-RTT packets from the server." -/
  processed1Rtt : Bool := false
  /-- §7.2, line 2357: the value we put in the Source Connection ID field of the
      first Initial packet we sent; §7.3, line 2399 requires it to be reported
      in `initial_source_connection_id`. -/
  localScid : Cid := []
  /-- §7.2, line 2333: the value we currently put in the Destination Connection
      ID field of the long-header packets we send.  A server has none until it
      has seen the client's first Initial. -/
  dcidSent : Option Cid := none
  /-- §7.3, line 2402: "the Destination Connection ID field from the first
      Initial packet it received from the client"; for a client, the value it
      chose for its own first Initial. -/
  originalDcid : Option Cid := none
  /-- The Source Connection ID of the peer's first Initial packet. -/
  peerScid : Option Cid := none
  /-- §7.3, line 2414: "the Source Connection ID field from the Retry packet",
      if there was a Retry. -/
  retryScid : Option Cid := none
  /-- A Retry happened in this connection (received, for a client; sent, for a
      server). -/
  retrySeen : Bool := false
  /-- An Initial packet from the peer has been processed (§7.2, line 2371: "Once
      a client has received a valid Initial packet from the server"). -/
  sawPeerInitial : Bool := false
  /-- How many times `dcidSent` has been set in response to a packet from the
      peer; §7.2, lines 2368 and 2376 bound it. -/
  dcidChanges : Nat := 0
  /-- The peer's transport parameters, once WP1 has accepted them and the §7.3
      checks have passed. -/
  peerParams : Option Params := none
  deriving DecidableEq

/-- A client at the start of a connection attempt: it has chosen its own Source
    Connection ID and the unpredictable Destination Connection ID of §7.2 line
    2337, and Initial keys are derived from the latter (RFC 9001 §5.2), so they
    exist in both directions from the outset. -/
def initClient (scid dcid : Cid) (bufLimit : Nat := 4096) : State :=
  { role := .client, bufLimit, localScid := scid,
    dcidSent := some dcid, originalDcid := some dcid,
    read := { initial := .present }, write := { initial := .present } }

/-- A server before the client's first Initial has arrived. -/
def initServer (scid : Cid) (bufLimit : Nat := 4096) : State :=
  { role := .server, bufLimit, localScid := scid,
    read := { initial := .present }, write := { initial := .present } }

namespace State

def stream (s : State) (l : CryptoLevel) : Crypto := s.streams.get l

def setStream (s : State) (l : CryptoLevel) (c : Crypto) : State :=
  { s with streams := s.streams.set l c }

/-- §17.2.2.1, line 6403: keys are discarded in both directions at once. -/
def discardKeys (s : State) (l : Level) : State :=
  { s with read := s.read.set l .discarded, write := s.write.set l .discarded }

def keysGone (s : State) (l : Level) : Bool :=
  (s.read.get l == .discarded) && (s.write.get l == .discarded)

/-- TLS announces a key.  A discarded key never comes back. -/
def provideKey (s : State) : KeyDir → Level → State
  | .read, l => if s.read.get l = .discarded then s else { s with read := s.read.set l .present }
  | .write, l => if s.write.get l = .discarded then s else { s with write := s.write.set l .present }

/-- The key state a packet of this type needs to be read; an unprotected packet
    type is always readable. -/
def readKeyFor (s : State) (pt : PacketType) : KeyState :=
  match levelOf pt with
  | none => .present
  | some l => s.read.get l

/-- §7.2, line 2333: "each endpoint sets the Destination Connection ID field in
    subsequent packets it sends to the value of the Source Connection ID field
    that it received." -/
def adoptScid (s : State) (scid : Cid) : State :=
  { s with dcidSent := some scid, peerScid := some scid, sawPeerInitial := true,
           dcidChanges := s.dcidChanges + 1 }

/-- §17.2.3, line 6476: a 1-RTT packet from the server has been processed. -/
def sawOneRtt (s : State) : State := { s with processed1Rtt := true }

/-- §7.2, line 2365: a client's response to a Retry — the same change of
    Destination Connection ID, but the Retry carries no peer Initial. -/
def adoptRetryScid (s : State) (scid : Cid) : State :=
  { s with dcidSent := some scid, retryScid := some scid, retrySeen := true,
           dcidChanges := s.dcidChanges + 1 }

end State

inductive Event where
  /-- TLS has the keys of `lvl` in direction `dir`. -/
  | tlsKeys (dir : KeyDir) (lvl : Level)
  /-- TLS discards the keys of `lvl`.  The transport draft states only the
      Initial case (§17.2.2.1), which this component drives itself; the other
      discards are RFC 9001 §4.9's and enter through this event. -/
  | tlsDiscardKeys (lvl : Level)
  /-- TLS hands over `len` further bytes of handshake data to send at `lvl`. -/
  | tlsSend (lvl : CryptoLevel) (len : Nat)
  /-- TLS delivers the peer's `quic_transport_parameters` extension, which it
      has authenticated (§7, line 2192; §7.3, line 2421). -/
  | tlsPeerParams (encoded : ByteArray)
  /-- TLS reports that 0-RTT was accepted or rejected (§17.2.3, line 6417). -/
  | tlsZeroRtt (accepted : Bool)
  /-- TLS reports handshake completion. -/
  | tlsComplete
  /-- TLS raises an alert; §19.6's carrier maps it to CRYPTO_ERROR 0x100+alert
      (§20.1, line 8339). -/
  | tlsAlert (alert : UInt8)
  /-- A packet that arrived and whose protection **was successfully removed**:
      its type and its two connection ID fields (§17.2).  Short-header packets
      have no Source Connection ID; the field is ignored for them.

      The "successfully" is load-bearing and is a contract on whoever fires the
      event (WP12): every rule below is conditioned on the packet having been
      processed, not merely seen.  §7.2, line 2332 says "After processing the first
      Initial packet, each endpoint sets the Destination Connection ID field in
      subsequent packets it sends to the value of the Source Connection ID field
      that it received"; line 2371, "Once a client has received a valid Initial
      packet from the server"; §17.2.3, line 6476, "once it starts processing
      1-RTT packets from the server".  Each of those qualifiers is the contract.  A packet whose AEAD
      fails is not this event at all; it never reaches this component, and so it
      changes nothing.

      This is a **hard requirement on the endpoint that fires the event**, not a
      stylistic note: with the read keys present every §7.2 arm below is a
      singleton, so a `recvHeader` synthesised from a packet whose protection
      has not been removed would make a forged packet *mandate* a connection ID
      change or a key discard.  See NOTE 10 and its examples. -/
  | recvHeader (pt : PacketType) (dcid scid : Cid)
  /-- A CRYPTO frame at `lvl` carrying the byte range `[off, off + len)`. -/
  | recvCrypto (lvl : CryptoLevel) (off len : Nat)
  /-- A HANDSHAKE_DONE frame arrived (§19.20). -/
  | recvHandshakeDone
  /-- We have sent a packet of this type. -/
  | sentPacket (pt : PacketType)
  /-- We (a server) sent a Retry packet with this Source Connection ID.  Whether
      to send one at all is WP5's (§8.1.2); only the §7.3 consequence is here. -/
  | sentRetry (scid : Cid)
  /-- We put a CRYPTO frame carrying `[off, off + len)` of `lvl` on the wire.
      §17.2.2, line 6376: "The first packet sent by a client always includes a
      CRYPTO frame that contains the start or all of the first cryptographic
      handshake message.  The first CRYPTO frame sent always begins at an offset
      of 0"; this event is what lets `MaySendPacket` know whether a frame is the
      first one at its level. -/
  | sentCrypto (lvl : CryptoLevel) (off len : Nat)
  deriving DecidableEq

inductive Effect where
  /-- Hand `[off, off + len)` of `lvl`'s CRYPTO stream to TLS.  §7, line 2167:
      "QUIC provides reliable, ordered delivery of the cryptographic handshake
      data", so these are always contiguous and in order. -/
  | deliverCrypto (lvl : CryptoLevel) (off len : Nat)
  /-- The keys of `lvl` are gone (§17.2.2.1). -/
  | keysDiscarded (lvl : Level)
  /-- §7.5, line 2716: this level's CRYPTO stream is now being discarded — "that
      CRYPTO frame and all CRYPTO frames received in the future".  The effect is
      what tells `Component.track` apart the two outcomes the sentence permits
      besides closing the connection (see NOTE 16). -/
  | cryptoDiscarding (lvl : CryptoLevel)
  /-- The peer's transport parameters passed both WP1's checks and §7.3's. -/
  | peerParams (tp : Params)
  | handshakeComplete
  | handshakeConfirmed
  /-- §7.2: the Destination Connection ID we send has changed. -/
  | dcidChanged (cid : Cid)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ### §19.6's offset limit -/

/-- §19.6, line 7545: "The largest offset delivered on a stream - the sum of the
    offset and data length - cannot exceed 2^62-1." -/
def maxCryptoOffset : Nat := 2 ^ 62 - 1

/-! ### §7.2's connection-ID rules, as outcomes

One arm per sentence; `HdrStep` below has one constructor per arm. -/

def cidOutcomes (s : State) (pt : PacketType) (dcid scid : Cid) : List Out :=
  match s.role, pt with
  -- §7.2, line 2365: "Upon first receiving an Initial or Retry packet from the
  -- server, the client uses the Source Connection ID supplied by the server as
  -- the Destination Connection ID for subsequent packets".
  | .client, .initial =>
    if s.sawPeerInitial then
      -- line 2371: "Once a client has received a valid Initial packet from the
      -- server, it MUST discard any subsequent packet it receives on that
      -- connection with a different Source Connection ID."
      if s.peerScid = some scid then [.ok s []] else [.drop]
    else [.ok (s.adoptScid scid) [.dcidChanged scid]]
  | .client, .retry =>
    -- line 2376: "A client MUST change the Destination Connection ID it uses
    -- for sending packets in response to only the first received Initial or
    -- Retry packet."  §17.2.5.2, line 6621 makes a later Retry a discard (WP5).
    if s.sawPeerInitial || s.retrySeen then [.drop]
    else [.ok (s.adoptRetryScid scid) [.dcidChanged scid]]
  | .client, .handshake =>
    -- line 2371 again: a different Source Connection ID after the server's
    -- first Initial MUST be discarded.
    if s.sawPeerInitial && s.peerScid ≠ some scid then [.drop] else [.ok s []]
  -- §17.2.3, line 6476: 1-RTT packets from the server end 0-RTT sending.
  | .client, .oneRtt => [.ok s.sawOneRtt []]
  -- A client never has 0-RTT read keys: §17.2.3, line 6415, a 0-RTT packet
  -- carries early data "from the client to the server".
  | .client, .zeroRtt => [.drop]
  -- WP7 owns Version Negotiation.
  | .client, .versionNegotiation => [.ok s []]
  -- §7.2, line 2378: "A server MUST set the Destination Connection ID it uses
  -- for sending packets based on the first received Initial packet", and
  -- §7.3, line 2402 records that packet's Destination Connection ID.
  | .server, .initial =>
    if s.sawPeerInitial then
      -- line 2382: "if subsequent Initial packets include a different Source
      -- Connection ID, they MUST be discarded."
      if s.peerScid = some scid then [.ok s []] else [.drop]
    else [.ok { (s.adoptScid scid) with originalDcid := some dcid } [.dcidChanged scid]]
  -- §17.2.2.1, line 6399: "A server stops sending and processing Initial
  -- packets when it receives its first Handshake packet."
  | .server, .handshake =>
    if s.read.get .initial = .discarded then [.ok s []]
    else [.ok (s.discardKeys .initial) [.keysDiscarded .initial]]
  -- §17.2.3: 0-RTT and 1-RTT packets carry no rule of this section.
  | .server, .zeroRtt => [.ok s []]
  | .server, .oneRtt => [.ok s []]
  -- §17.2.5.2 addresses clients only; a server ignores a Retry (WP5).
  | .server, .retry => [.drop]
  | .server, .versionNegotiation => [.ok s []]

def headerOutcomes (s : State) (pt : PacketType) (dcid scid : Cid) : List Out :=
  match s.readKeyFor pt with
  | .discarded => [.drop]
  | .absent => [.ok s [], .drop]
  | .present => cidOutcomes s pt dcid scid

/-! ### §7.3's checks on the peer's parameters -/

/-- §7.3 compares a transport parameter (a byte string) with a connection ID
    recorded from a packet header (a `Cid`, i.e. a `List UInt8`).  The comparison
    is made in `ByteArray`, the representation WP1 uses, because that is the one
    the kernel can evaluate. -/
def optCid (c : Option Cid) : Option ByteArray := c.map bytes

/-- §7.3, line 2428: "An endpoint MUST treat absence of the
    initial_source_connection_id transport parameter from either endpoint or
    absence of the original_destination_connection_id transport parameter from
    the server as a connection error of type TRANSPORT_PARAMETER_ERROR." -/
def missingCid (s : State) (tp : Params) : Bool :=
  tp.initialSourceConnectionId.isNone ||
    ((s.role == .client) && tp.originalDestinationConnectionId.isNone)

/-- §7.3, line 2433: the three situations an endpoint "MUST treat … as a
    connection error of type TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION":
    a missing `retry_source_connection_id` after a Retry, a present one without
    a Retry, and any mismatch with the connection ID fields of the Initial
    packets sent and received.  For a peer that is a client the last two
    parameters must be absent, which WP1's `Valid` has already enforced. -/
def cidMismatch (s : State) (tp : Params) : Bool :=
  !decide (tp.initialSourceConnectionId = optCid s.peerScid) ||
    ((s.role == .client) &&
      (!decide (tp.originalDestinationConnectionId = optCid s.originalDcid) ||
        !decide (tp.retrySourceConnectionId = optCid s.retryScid)))

/-- What §7.3 does with a parameter set WP1 has already accepted. -/
def authOutcomes (s : State) (tps : TransportParams.State) : List Out :=
  match tps.peer with
  | none => [.ok s []]
  | some tp =>
    if missingCid s tp then [.error .transportParameterError]
    else if cidMismatch s tp then
      [.error .transportParameterError, .error .protocolViolation]
    else [.ok { s with peerParams := some tp } [.peerParams tp]]

/-- WP1 first, then §7.3: the bytes are decoded and checked by
    `TransportParams.component`, whose error outcomes pass straight through. -/
def paramOutcomes (s : State) (b : ByteArray) : List Out :=
  (TransportParams.outcomes ⟨s.role, s.peerParams⟩ (.recvParams b)).flatMap fun o =>
    match o with
    | .error e => [.error e]
    | .drop => [.drop]
    | .ok tps _ => authOutcomes s tps

/-! ### Receiving a CRYPTO frame -/

/-- The effect of a receive that advanced the delivered prefix. -/
def deliverFx (lvl : CryptoLevel) (c c' : Crypto) : List Effect :=
  if c.delivered < c'.delivered then
    [.deliverCrypto lvl c.delivered (c'.delivered - c.delivered)]
  else []

def cryptoOutcomes (s : State) (lvl : CryptoLevel) (off len : Nat) : List Out :=
  -- §17.2.2.1, line 6407: "Any data in CRYPTO frames is discarded … when
  -- Initial keys are discarded"; §17.2.4, line 6546 says the same of Handshake.
  if s.read.get lvl.level = .discarded then [.drop]
  -- §19.6, line 7545: FRAME_ENCODING_ERROR or CRYPTO_BUFFER_EXCEEDED.
  else if maxCryptoOffset < off + len then
    [.error .frameEncodingError, .error .cryptoBufferExceeded]
  -- §7.5, line 2716: "all CRYPTO frames received in the future", acknowledged
  -- but not delivered (line 2719).  The same sentence's other alternative --
  -- line 2716 again, "or it MAY close the connection with a
  -- CRYPTO_BUFFER_EXCEEDED error code" -- is offered per frame, so electing to
  -- discard on one frame does not forfeit it on the next (NOTE 18).
  else if (s.stream lvl).discarding then [.ok s [], .error .cryptoBufferExceeded]
  else if s.bufLimit < bufferedBytes ((s.stream lvl).recv off len).buf then
    -- Three outcomes are permitted past the limit, and buffering anyway is one
    -- of them at every point in the connection: §7.5, line 2707, "An endpoint's
    -- buffer size does not need to remain constant during the life of the
    -- connection", so an endpoint that enlarges its buffer is simply not the
    -- endpoint the next two sentences are about.  Line 2711 names that outcome
    -- explicitly during the handshake: "it can expand its buffer temporarily to
    -- complete the handshake."
    if s.complete then
      -- §7.5, line 2716: "it MAY discard that CRYPTO frame and all CRYPTO
      -- frames received in the future, or it MAY close the connection with a
      -- CRYPTO_BUFFER_EXCEEDED error code.  Packets containing discarded CRYPTO
      -- frames MUST be acknowledged" — hence `.ok`, not `.drop`.
      [.ok (s.setStream lvl { s.stream lvl with discarding := true })
           [.cryptoDiscarding lvl],
       .ok (s.setStream lvl ((s.stream lvl).recv off len))
           (deliverFx lvl (s.stream lvl) ((s.stream lvl).recv off len)),
       .error .cryptoBufferExceeded]
    else
      -- §7.5, line 2713: "If an endpoint does not expand its buffer, it MUST
      -- close the connection with a CRYPTO_BUFFER_EXCEEDED error code."
      [.ok (s.setStream lvl ((s.stream lvl).recv off len))
           (deliverFx lvl (s.stream lvl) ((s.stream lvl).recv off len)),
       .error .cryptoBufferExceeded]
  else
    [.ok (s.setStream lvl ((s.stream lvl).recv off len))
         (deliverFx lvl (s.stream lvl) ((s.stream lvl).recv off len))]

/-! ## 2. The specification -/

/-- §7.2 and the key-availability rules, for one received packet header. -/
inductive HdrStep : State → PacketType → Cid → Cid → Out → Prop
  /-- §17.2.2.1, line 6398: an endpoint "stops … processing Initial packets"
      once their keys are discarded; RFC 9001 §4.9 generalises it. -/
  | keysDiscarded {s pt d c} (h : s.readKeyFor pt = .discarded) : HdrStep s pt d c .drop
  /-- §5.2.1, line 1895: "The client MAY drop these packets, or MAY buffer them
      in anticipation of later packets that allow it to compute the key"; §12.2,
      line 4622 says the same for either endpoint.  Buffering. -/
  | keysAbsentBuffer {s pt d c} (h : s.readKeyFor pt = .absent) : HdrStep s pt d c (.ok s [])
  /-- Same sentence: dropping. -/
  | keysAbsentDrop {s pt d c} (h : s.readKeyFor pt = .absent) : HdrStep s pt d c .drop
  /-- §7.2, line 2365: "Upon first receiving an Initial or Retry packet from the
      server, the client uses the Source Connection ID supplied by the server as
      the Destination Connection ID for subsequent packets". -/
  | cliInitialFirst {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .client)
      (hs : s.sawPeerInitial = false) :
      HdrStep s .initial d c (.ok (s.adoptScid c) [.dcidChanged c])
  /-- §7.2, line 2371, satisfied: a further Initial with the same Source
      Connection ID (§17.2.2, line 6365: "A server MAY send multiple Initial
      packets"). -/
  | cliInitialSame {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .client)
      (hs : s.sawPeerInitial = true) (hc : s.peerScid = some c) :
      HdrStep s .initial d c (.ok s [])
  /-- §7.2, line 2371: "it MUST discard any subsequent packet it receives on
      that connection with a different Source Connection ID." -/
  | cliInitialOther {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .client)
      (hs : s.sawPeerInitial = true) (hc : s.peerScid ≠ some c) :
      HdrStep s .initial d c .drop
  /-- §7.2, line 2365 for a Retry, and §17.2.5.3, line 6652: "The client copies
      the Source Connection ID field from the Retry packet to the Destination
      Connection ID field". -/
  | cliRetryFirst {s d c} (hk : s.readKeyFor .retry = .present) (hr : s.role = .client)
      (hs : s.sawPeerInitial = false) (ht : s.retrySeen = false) :
      HdrStep s .retry d c (.ok (s.adoptRetryScid c) [.dcidChanged c])
  /-- §7.2, line 2376: "A client MUST change the Destination Connection ID it
      uses for sending packets in response to only the first received Initial or
      Retry packet"; §17.2.5.2, line 6622: "After the client has received and
      processed an Initial or Retry packet from the server, it MUST discard any
      subsequent Retry packets that it receives." -/
  | cliRetryLate {s d c} (hk : s.readKeyFor .retry = .present) (hr : s.role = .client)
      (h : s.sawPeerInitial = true ∨ s.retrySeen = true) :
      HdrStep s .retry d c .drop
  /-- §7.2, line 2371 applied to a Handshake packet. -/
  | cliHandshakeOther {s d c} (hk : s.readKeyFor .handshake = .present) (hr : s.role = .client)
      (hs : s.sawPeerInitial = true) (hc : s.peerScid ≠ some c) :
      HdrStep s .handshake d c .drop
  /-- Otherwise a Handshake packet carries no §7.2 rule. -/
  | cliHandshakeOk {s d c} (hk : s.readKeyFor .handshake = .present) (hr : s.role = .client)
      (h : s.sawPeerInitial = false ∨ s.peerScid = some c) :
      HdrStep s .handshake d c (.ok s [])
  /-- §17.2.3, line 6476: "A client MUST NOT send 0-RTT packets once it starts
      processing 1-RTT packets from the server." -/
  | cliOneRtt {s d c} (hk : s.readKeyFor .oneRtt = .present) (hr : s.role = .client) :
      HdrStep s .oneRtt d c (.ok s.sawOneRtt [])
  /-- A client is never the recipient of a 0-RTT packet (§17.2.3, line 6415: a
      0-RTT packet carries early data "from the client to the server as part of
      the first flight"), so this arm is unreachable: nothing gives a client
      0-RTT *read* keys.  `.drop` is a convention for a state the text does not
      describe, not a rule read out of it (NOTE 19). -/
  | cliZeroRtt {s d c} (hk : s.readKeyFor .zeroRtt = .present) (hr : s.role = .client) :
      HdrStep s .zeroRtt d c .drop
  /-- Version Negotiation is WP7's (§6). -/
  | cliVn {s d c} (hr : s.role = .client) : HdrStep s .versionNegotiation d c (.ok s [])
  /-- §7.2, line 2378: "A server MUST set the Destination Connection ID it uses
      for sending packets based on the first received Initial packet"; §7.3,
      line 2402 keeps that packet's Destination Connection ID for
      `original_destination_connection_id`. -/
  | srvInitialFirst {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .server)
      (hs : s.sawPeerInitial = false) :
      HdrStep s .initial d c (.ok { (s.adoptScid c) with originalDcid := some d }
                                 [.dcidChanged c])
  /-- A further Initial with the same Source Connection ID. -/
  | srvInitialSame {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .server)
      (hs : s.sawPeerInitial = true) (hc : s.peerScid = some c) :
      HdrStep s .initial d c (.ok s [])
  /-- §7.2, line 2382: "if subsequent Initial packets include a different Source
      Connection ID, they MUST be discarded." -/
  | srvInitialOther {s d c} (hk : s.readKeyFor .initial = .present) (hr : s.role = .server)
      (hs : s.sawPeerInitial = true) (hc : s.peerScid ≠ some c) :
      HdrStep s .initial d c .drop
  /-- §17.2.2.1, line 6399: "A server stops sending and processing Initial
      packets when it receives its first Handshake packet." -/
  | srvHandshakeDiscard {s d c} (hk : s.readKeyFor .handshake = .present) (hr : s.role = .server)
      (hd : s.read.get .initial ≠ .discarded) :
      HdrStep s .handshake d c (.ok (s.discardKeys .initial) [.keysDiscarded .initial])
  /-- Same sentence, once the keys are already gone. -/
  | srvHandshakeAgain {s d c} (hk : s.readKeyFor .handshake = .present) (hr : s.role = .server)
      (hd : s.read.get .initial = .discarded) :
      HdrStep s .handshake d c (.ok s [])
  /-- A 0-RTT or 1-RTT packet at a server carries no rule of this section;
      §5.2.2, line 1940 (WP5) governs 0-RTT buffering. -/
  | srvAppData {s pt d c} (hk : s.readKeyFor pt = .present) (hr : s.role = .server)
      (hp : pt = .zeroRtt ∨ pt = .oneRtt) : HdrStep s pt d c (.ok s [])
  /-- §17.2.5.2 addresses clients only, so a server ignores a Retry (WP5's
      `retryWrongRole`). -/
  | srvRetry {s d c} (hr : s.role = .server) : HdrStep s .retry d c .drop
  /-- Version Negotiation is WP7's. -/
  | srvVn {s d c} (hr : s.role = .server) : HdrStep s .versionNegotiation d c (.ok s [])

/-- §7.5 and §19.6, for one received CRYPTO frame. -/
inductive CryptoStep : State → CryptoLevel → Nat → Nat → Out → Prop
  /-- §17.2.2.1, line 6407: "Any data in CRYPTO frames is discarded - and no
      longer retransmitted - when Initial keys are discarded"; §17.2.4, line
      6546 repeats it for Handshake keys. -/
  | levelGone {s l o n} (h : s.read.get l.level = .discarded) : CryptoStep s l o n .drop
  /-- §19.6, line 7546: "Receipt of a frame that exceeds this limit MUST be
      treated as a connection error of type FRAME_ENCODING_ERROR or
      CRYPTO_BUFFER_EXCEEDED."  First alternative. -/
  | tooLargeEncoding {s l o n} (hk : s.read.get l.level ≠ .discarded)
      (h : maxCryptoOffset < o + n) : CryptoStep s l o n (.error .frameEncodingError)
  /-- Same sentence, second alternative. -/
  | tooLargeBuffer {s l o n} (hk : s.read.get l.level ≠ .discarded)
      (h : maxCryptoOffset < o + n) : CryptoStep s l o n (.error .cryptoBufferExceeded)
  /-- §7.5, line 2716: "…and all CRYPTO frames received in the future"; line
      2719: "Packets containing discarded CRYPTO frames MUST be acknowledged". -/
  | alreadyDiscarding {s l o n} (hk : s.read.get l.level ≠ .discarded)
      (h : o + n ≤ maxCryptoOffset) (hd : (s.stream l).discarding = true) :
      CryptoStep s l o n (.ok s [])
  /-- §7.5, line 2716, the other half of the same sentence: "or it MAY close the
      connection with a CRYPTO_BUFFER_EXCEEDED error code."  It is offered for
      each frame the endpoint cannot buffer, so an endpoint that has been
      discarding may still give up later (NOTE 18). -/
  | discardingClose {s l o n} (hk : s.read.get l.level ≠ .discarded)
      (h : o + n ≤ maxCryptoOffset) (hd : (s.stream l).discarding = true) :
      CryptoStep s l o n (.error .cryptoBufferExceeded)
  /-- §7, line 2167: "QUIC provides reliable, ordered delivery of the
      cryptographic handshake data" — in-order bytes go to TLS, the rest is
      buffered (§7.5, line 2698). -/
  | accept {s l o n} (hk : s.read.get l.level ≠ .discarded) (h : o + n ≤ maxCryptoOffset)
      (hd : (s.stream l).discarding = false)
      (hb : bufferedBytes ((s.stream l).recv o n).buf ≤ s.bufLimit) :
      CryptoStep s l o n (.ok (s.setStream l ((s.stream l).recv o n))
                             (deliverFx l (s.stream l) ((s.stream l).recv o n)))
  /-- §7.5, line 2711: "If an endpoint's buffer is exceeded during the
      handshake, it can expand its buffer temporarily to complete the
      handshake."  Not restricted to the handshake: line 2707, "An endpoint's
      buffer size does not need to remain constant during the life of the
      connection", so an endpoint that enlarges its buffer after completion is
      not "unable to buffer all data in a CRYPTO frame" (line 2716) either.
      See NOTE 15. -/
  | expand {s l o n} (hk : s.read.get l.level ≠ .discarded) (h : o + n ≤ maxCryptoOffset)
      (hd : (s.stream l).discarding = false)
      (hb : s.bufLimit < bufferedBytes ((s.stream l).recv o n).buf) :
      CryptoStep s l o n (.ok (s.setStream l ((s.stream l).recv o n))
                             (deliverFx l (s.stream l) ((s.stream l).recv o n)))
  /-- §7.5, line 2713: "If an endpoint does not expand its buffer, it MUST close
      the connection with a CRYPTO_BUFFER_EXCEEDED error code." -/
  | overflowClose {s l o n} (hk : s.read.get l.level ≠ .discarded) (h : o + n ≤ maxCryptoOffset)
      (hd : (s.stream l).discarding = false)
      (hb : s.bufLimit < bufferedBytes ((s.stream l).recv o n).buf) :
      CryptoStep s l o n (.error .cryptoBufferExceeded)
  /-- §7.5, line 2716: "Once the handshake completes, if an endpoint is unable to
      buffer all data in a CRYPTO frame, it MAY discard that CRYPTO frame and all
      CRYPTO frames received in the future". -/
  | overflowDiscard {s l o n} (hk : s.read.get l.level ≠ .discarded)
      (h : o + n ≤ maxCryptoOffset) (hd : (s.stream l).discarding = false)
      (hb : s.bufLimit < bufferedBytes ((s.stream l).recv o n).buf) (hc : s.complete = true) :
      CryptoStep s l o n (.ok (s.setStream l { s.stream l with discarding := true })
                             [.cryptoDiscarding l])

/-- WP1's decode and validity checks, then §7.3's connection-ID checks. -/
inductive ParamStep : State → ByteArray → Out → Prop
  /-- §7.4, line 2535 and §18: whatever `TransportParams.component` rejects is
      rejected here with the same code. -/
  | wp1Error {s b e} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b) (.error e)) :
      ParamStep s b (.error e)
  /-- `TransportParams.component` never discards, but if it did, so would we. -/
  | wp1Drop {s b} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b) .drop) :
      ParamStep s b .drop
  /-- §7.3, line 2428: "An endpoint MUST treat absence of the
      initial_source_connection_id transport parameter from either endpoint or
      absence of the original_destination_connection_id transport parameter from
      the server as a connection error of type TRANSPORT_PARAMETER_ERROR." -/
  | missing {s b tps fx tp} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b)
        (.ok tps fx)) (hp : tps.peer = some tp) (hm : missingCid s tp = true) :
      ParamStep s b (.error .transportParameterError)
  /-- §7.3, line 2433: "An endpoint MUST treat the following as a connection
      error of type TRANSPORT_PARAMETER_ERROR or PROTOCOL_VIOLATION: absence of
      the retry_source_connection_id … after receiving a Retry packet, presence
      … when no Retry packet was received, or a mismatch between values received
      from a peer in these transport parameters and the value sent in the
      corresponding Destination or Source Connection ID fields of Initial
      packets."  First alternative. -/
  | mismatchTpe {s b tps fx tp} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b)
        (.ok tps fx)) (hp : tps.peer = some tp) (hm : missingCid s tp = false)
      (hc : cidMismatch s tp = true) : ParamStep s b (.error .transportParameterError)
  /-- Same sentence, second alternative. -/
  | mismatchPv {s b tps fx tp} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b)
        (.ok tps fx)) (hp : tps.peer = some tp) (hm : missingCid s tp = false)
      (hc : cidMismatch s tp = true) : ParamStep s b (.error .protocolViolation)
  /-- §7.3, line 2421: "Endpoints MUST validate that received transport
      parameters match received Connection ID values."  They do. -/
  | accept {s b tps fx tp} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b)
        (.ok tps fx)) (hp : tps.peer = some tp) (hm : missingCid s tp = false)
      (hc : cidMismatch s tp = false) :
      ParamStep s b (.ok { s with peerParams := some tp } [.peerParams tp])
  /-- `TransportParams.component` always records the parameters it accepted;
      this arm is unreachable and exists only to make the two forms agree. -/
  | acceptNone {s b tps fx} (h : TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b)
        (.ok tps fx)) (hp : tps.peer = none) : ParamStep s b (.ok s [])

inductive Step : State → Event → Out → Prop
  /-- Keys arrive from TLS.  A discarded key never comes back (§17.2.2.1). -/
  | keys {s dir l} : Step s (.tlsKeys dir l) (.ok (s.provideKey dir l) [])
  /-- RFC 9001 §4.9's discards, which the transport draft refers to at line
      6403; the Initial case of §17.2.2.1 is driven by `sentPacket` and by a
      server's first Handshake packet instead. -/
  | discard {s l} (h : s.keysGone l = false) :
      Step s (.tlsDiscardKeys l) (.ok (s.discardKeys l) [.keysDiscarded l])
  /-- Discarding twice changes nothing. -/
  | discardAgain {s l} (h : s.keysGone l = true) : Step s (.tlsDiscardKeys l) (.ok s [])
  /-- §19.6: TLS produces the bytes; the transport carries them. -/
  | send {s l n} :
      Step s (.tlsSend l n) (.ok (s.setStream l { s.stream l with handed := (s.stream l).handed + n }) [])
  /-- §7.4 and §7.3, composed: `TransportParams.component` then `ParamStep`. -/
  | params {s b o} (h : ParamStep s b o) : Step s (.tlsPeerParams b) o
  /-- §17.2.3, line 6417: the server accepted the early data. -/
  | zeroRttAccepted {s} : Step s (.tlsZeroRtt true) (.ok { s with zeroRtt := .accepted } [])
  /-- §17.2.3, line 6417: it rejected it, and the 0-RTT keys go with it
      (RFC 9001 §4.9.3). -/
  | zeroRttRejected {s} :
      Step s (.tlsZeroRtt false)
        (.ok { (s.discardKeys .zeroRtt) with zeroRtt := .rejected } [.keysDiscarded .zeroRtt])
  /-- A server's handshake is confirmed as soon as it completes (RFC 9001
      §4.1.2, referred to at line 3281); §19.20, line 8207: "Servers MUST NOT
      send a HANDSHAKE_DONE frame before completing the handshake." -/
  | completeServer {s} (hc : s.complete = false) (hr : s.role = .server) :
      Step s .tlsComplete (.ok { s with complete := true, confirmed := true }
                              [.handshakeComplete, .handshakeConfirmed])
  /-- A client's handshake is confirmed only by HANDSHAKE_DONE. -/
  | completeClient {s} (hc : s.complete = false) (hr : s.role = .client) :
      Step s .tlsComplete (.ok { s with complete := true } [.handshakeComplete])
  /-- Completion is reported once. -/
  | completeAgain {s} (hc : s.complete = true) : Step s .tlsComplete (.ok s [])
  /-- §20.1, line 8339: "CRYPTO_ERROR … the cryptographic handshake failed"; the
      1 byte of a TLS alert is added to 0x100. -/
  | alert {s a} : Step s (.tlsAlert a) (.error (.cryptoError a))
  | header {s pt d c o} (h : HdrStep s pt d c o) : Step s (.recvHeader pt d c) o
  | crypto {s l off len o} (h : CryptoStep s l off len o) : Step s (.recvCrypto l off len) o
  /-- §19.20, line 8195: "The server uses a HANDSHAKE_DONE frame … to signal
      confirmation of the handshake to the client." -/
  | doneClient {s} (hr : s.role = .client) (hc : s.complete = true) :
      Step s .recvHandshakeDone (.ok { s with confirmed := true } [.handshakeConfirmed])
  /-- The frame cannot legitimately precede the client's own completion (§19.20,
      line 8207); the text gives the *receiver* no rule, so ignoring it is
      permitted and it has no effect here. -/
  | doneEarly {s} (hr : s.role = .client) (hc : s.complete = false) :
      Step s .recvHandshakeDone (.ok s [])
  /-- The other outcome the silence leaves open.  A HANDSHAKE_DONE frame before
      the client's handshake completes means the peer broke §19.20, line 8207
      ("Servers MUST NOT send a HANDSHAKE_DONE frame before completing the
      handshake"), and §11.1, line 4446: "Errors that result in the connection
      being unusable, such as an obvious violation of protocol semantics … MUST
      be signaled using a CONNECTION_CLOSE frame"; §11, line 4434: "an endpoint
      MAY use any applicable error code when it detects an error condition; a
      generic error code (such as PROTOCOL_VIOLATION or INTERNAL_ERROR) can
      always be used".  Closing is therefore permitted, and so is ignoring:
      neither is mandated (NOTE 7). -/
  | doneEarlyClose {s} (hr : s.role = .client) (hc : s.complete = false) :
      Step s .recvHandshakeDone (.error .protocolViolation)
  /-- §19.20, line 8208: "A server MUST treat receipt of a HANDSHAKE_DONE frame
      as a connection error of type PROTOCOL_VIOLATION" — WP3's `mustReject`
      already rejects it, so this component adds nothing. -/
  | doneServer {s} (hr : s.role = .server) : Step s .recvHandshakeDone (.ok s [])
  /-- §17.2.2.1, line 6398: "A client stops both sending and processing Initial
      packets when it sends its first Handshake packet." -/
  | sentHandshake {s} (hr : s.role = .client) (hd : s.write.get .initial ≠ .discarded) :
      Step s (.sentPacket .handshake) (.ok (s.discardKeys .initial) [.keysDiscarded .initial])
  /-- Any other packet we send, and any Handshake packet after the first. -/
  | sentOther {s pt} (h : s.role ≠ .client ∨ pt ≠ .handshake ∨ s.write.get .initial = .discarded) :
      Step s (.sentPacket pt) (.ok s [])
  /-- §7.3, line 2414: "If it sends a Retry packet, a server also includes the
      Source Connection ID field from the Retry packet in the
      retry_source_connection_id transport parameter." -/
  | sentRetry {s c} (hr : s.role = .server) :
      Step s (.sentRetry c) (.ok { s with retryScid := some c, retrySeen := true } [])
  /-- A client does not send Retry packets (§17.2.5). -/
  | sentRetryClient {s c} (hr : s.role = .client) : Step s (.sentRetry c) (.ok s [])
  /-- §17.2.2, line 6378: record how far we have sent, so that "the first CRYPTO
      frame sent always begins at an offset of 0" is checkable.  Frames are
      retransmitted out of order after loss (§13.3), so the mark only ever moves
      forward. -/
  | sentCrypto {s l o n} :
      Step s (.sentCrypto l o n)
        (.ok (s.setStream l { s.stream l with
                sentNext := Nat.max (s.stream l).sentNext (o + n) }) [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .tlsKeys dir l => [.ok (s.provideKey dir l) []]
  | .tlsDiscardKeys l =>
    if s.keysGone l then [.ok s []] else [.ok (s.discardKeys l) [.keysDiscarded l]]
  | .tlsSend l n =>
    [.ok (s.setStream l { s.stream l with handed := (s.stream l).handed + n }) []]
  | .tlsPeerParams b => paramOutcomes s b
  | .tlsZeroRtt accepted =>
    if accepted then [.ok { s with zeroRtt := .accepted } []]
    else [.ok { (s.discardKeys .zeroRtt) with zeroRtt := .rejected } [.keysDiscarded .zeroRtt]]
  | .tlsComplete =>
    if s.complete then [.ok s []]
    else match s.role with
      | .server =>
        [.ok { s with complete := true, confirmed := true }
             [.handshakeComplete, .handshakeConfirmed]]
      | .client => [.ok { s with complete := true } [.handshakeComplete]]
  | .tlsAlert a => [.error (.cryptoError a)]
  | .recvHeader pt d c => headerOutcomes s pt d c
  | .recvCrypto l off len => cryptoOutcomes s l off len
  | .recvHandshakeDone =>
    match s.role with
    | .server => [.ok s []]
    | .client =>
      if s.complete then [.ok { s with confirmed := true } [.handshakeConfirmed]]
      else [.ok s [], .error .protocolViolation]
  | .sentPacket pt =>
    if s.role = .client ∧ pt = .handshake ∧ s.write.get .initial ≠ .discarded then
      [.ok (s.discardKeys .initial) [.keysDiscarded .initial]]
    else [.ok s []]
  | .sentRetry c =>
    match s.role with
    | .server => [.ok { s with retryScid := some c, retrySeen := true } []]
    | .client => [.ok s []]
  | .sentCrypto l o n =>
    [.ok (s.setStream l { s.stream l with
            sentNext := Nat.max (s.stream l).sentNext (o + n) }) []]

end Quic.Spec.Handshake
