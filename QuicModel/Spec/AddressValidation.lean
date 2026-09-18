import QuicModel.Spec.Core

/-
  WP5a: §8 / §8.1 address validation — the anti-amplification limit, address
  validation tokens (opaque), and the client's handling of a Retry packet
  (§17.2.5.2, §17.2.5.3).

  Text: draft-ietf-quic-transport-34 lines 2724–3068 and 6557–6697.
  Path validation (§8.2) is the companion file `Spec/PathValidation.lean`.

  File order as in `Spec/Template.lean`.
-/
namespace Quic.Spec.AddressValidation

/-! ## 1. State, events, effects

`Addr` is `Spec.Addr` — §8.2, line 3074: "an address is the two-tuple of IP
address and port".  An opaque handle; the model never inspects it. -/

/-- §8, line 2735: per-address anti-amplification accounting.

    `received` counts, per §8.1 line 2777, "all of the payload bytes received in
    datagrams that are uniquely attributed to a single connection", whether the
    packets in them were processed or discarded.  `sent` counts the UDP payload
    bytes sent to the address. -/
structure AddrState where
  validated : Bool := false
  received : Nat := 0
  sent : Nat := 0
  /-- §9.3, line 3378: "Receiving a packet from a new peer address containing a
      non-probing frame indicates that the peer has migrated to that address."
      Set when we first hear from an address the peer moved to, and only then;
      it decides whether the limit of §9.3.1 line 3431 binds a *client* towards
      this address.  See `State.limited` and NOTES 1. -/
  newPeerAddr : Bool := false
  deriving DecidableEq, Repr

/-- §8.1.1, line 2823: "A token sent in a NEW_TOKEN frame or a Retry packet MUST
    be constructed in a way that allows the server to identify how it was
    provided to a client."  The two provenances, which the server can always
    tell apart; the bytes themselves are never inspected by the model. -/
inductive TokenSource where
  | retry
  | newToken
  deriving DecidableEq, Repr

/-- The outcome of the server's (opaque) token check for a client Initial
    packet — §8.1.3, line 2987: "it MUST attempt to validate the token".

    `valid src addrUnchanged` additionally reports whether the token's record of
    the client address still matches the address the Initial arrived from
    (§8.1.4, lines 3046 and 3050).  How the check is performed, and the token's
    encryption and integrity protection (§8.1.4), are out of scope. -/
inductive TokenCheck where
  | absent
  | valid (src : TokenSource) (addrUnchanged : Bool)
  | invalid (src : TokenSource)
  deriving DecidableEq, Repr

/-- §8.1.3, line 2919: "Servers MAY discard any Initial packet that does not
    carry the expected token."  A valid token *is* the expected one; every other
    check result is not. -/
def TokenCheck.expected : TokenCheck → Bool
  | .valid _ _ => true
  | _ => false

/-- §8.1.2 / §8.1.3: the token a client repeats in its Initial packets, with the
    provenance that decides whether it may be carried to a later connection. -/
structure ClientToken where
  src : TokenSource
  bytes : ByteArray
  deriving DecidableEq

structure State where
  role : Role
  /-- Anti-amplification accounting, per peer address. -/
  addrs : Map Addr AddrState
  /-- §17.2.5.3, line 6656 (client): the token copied into every subsequent
      Initial packet, with where it came from. -/
  token : Option ClientToken
  /-- §17.2.5.2, line 6621 (client): Retry packets accepted in this connection
      attempt.  The invariant keeps it ≤ 1. -/
  retriesAccepted : Nat
  /-- §17.2.5.2, line 6622 (client): "After the client has received and
      processed an Initial or Retry packet from the server". -/
  sawServerPacket : Bool
  /-- §17.2.5.1, line 6601 (client): the Destination Connection ID of the
      Initial packets it sends.  Starts as the DCID of its first Initial and is
      replaced by the Source Connection ID of an accepted Retry. -/
  dcid : ByteArray
  /-- §8.1.3, line 2977 (client): tokens received in NEW_TOKEN frames, most
      recent first ("sending the most recent unused token is most likely to be
      effective", line 2981). -/
  newTokens : List ByteArray
  deriving DecidableEq

def init (role : Role) (dcid : ByteArray) : State :=
  { role, addrs := [], token := none, retriesAccepted := 0,
    sawServerPacket := false, dcid, newTokens := [] }

/-- What we know about `a`; an address never heard from is unvalidated with a
    zero budget. -/
def State.info (s : State) (a : Addr) : AddrState := (s.addrs.get? a).getD {}

def State.upd (s : State) (a : Addr) (f : AddrState → AddrState) : State :=
  { s with addrs := s.addrs.set a (f (s.info a)) }

/-- §8.1, line 2777 counts the bytes.  `newPath` is the caller's judgement that
    the datagram came from an address the peer has migrated to (§9.3, line
    3378); it is only believed while we have sent nothing there, since an
    address we have already written to is not new to us.  That restriction is
    what makes `State.limited` monotone, and hence `antiAmplification` true. -/
def State.addRecv (s : State) (a : Addr) (n : Nat) (newPath : Bool) : State :=
  s.upd a fun st =>
    { st with received := st.received + n,
              newPeerAddr := if st.sent = 0 then newPath else st.newPeerAddr }

def State.addSent (s : State) (a : Addr) (n : Nat) : State :=
  s.upd a fun st => { st with sent := st.sent + n }

def State.validate (s : State) (a : Addr) : State :=
  s.upd a fun st => { st with validated := true }

@[simp] theorem info_upd_self (s : State) (a : Addr) (f : AddrState → AddrState) :
    (s.upd a f).info a = f (s.info a) := by
  simp [State.info, State.upd]

theorem info_upd_ne (s : State) {a a' : Addr} (f : AddrState → AddrState) (h : a' ≠ a) :
    (s.upd a f).info a' = s.info a' := by
  simp [State.info, State.upd, Map.get?_set_of_ne _ _ h]

@[simp] theorem role_upd (s : State) (a : Addr) (f : AddrState → AddrState) :
    (s.upd a f).role = s.role := rfl

inductive Event where
  /-- §8.1, line 2777: `n` payload bytes arrived from `a` in a datagram uniquely
      attributed to this connection (processed or discarded — both count).
      `newPath` marks a datagram from an address the peer migrated to. -/
  | datagramRecv (a : Addr) (n : Nat) (newPath : Bool)
  /-- A UDP datagram of `n` payload bytes was sent to `a`. -/
  | datagramSent (a : Addr) (n : Nat)
  /-- §8.1, line 2757: "Once an endpoint has successfully processed a Handshake
      packet from the peer". -/
  | handshakeProcessed (a : Addr)
  /-- §8.1, line 2761: the peer used a connection ID we chose; `hasEntropy` says
      it "contains at least 64 bits of entropy". -/
  | peerUsedOurCid (a : Addr) (hasEntropy : Bool)
  /-- §8.2.3, line 3220: path validation to `a` succeeded (driven by
      `Spec/PathValidation.lean`). -/
  | pathValidated (a : Addr)
  /-- §8.1, line 2765 / §17.2.5.2, line 6622 (client): an Initial packet from
      the server was processed. -/
  | serverInitialProcessed (a : Addr)
  /-- §8.1.3, line 2987 (server): a client Initial arrived from `a`; `chk` is the
      result of the token check. -/
  | clientInitial (a : Addr) (chk : TokenCheck)
  /-- §17.2.5.2 (client): a Retry packet arrived carrying `token`, with Source
      Connection ID `scid`; `integrityOk` is the Retry Integrity Tag check of
      [QUIC-TLS] §5.8, an opaque boolean here. -/
  | recvRetry (token : ByteArray) (scid : ByteArray) (integrityOk : Bool)
  /-- §8.1.3 (client): a NEW_TOKEN frame arrived. -/
  | recvNewToken (token : ByteArray)
  deriving DecidableEq

inductive Effect where
  /-- §8: the address may now be sent to without the anti-amplification limit. -/
  | addressValidated (a : Addr)
  /-- §8.1.2, line 2830: the server requests address validation with a Retry. -/
  | sendRetry (a : Addr)
  /-- The server lets the cryptographic handshake proceed (§8.1.3, line 2994). -/
  | handshakeProceeds (a : Addr)
  /-- §17.2.5.3, line 6656: this token is copied to all subsequent Initials. -/
  | useToken (token : ByteArray)
  /-- §17.2.5.1, line 6601: this value is used as the Destination Connection ID
      of subsequent packets. -/
  | useDcid (cid : ByteArray)
  /-- §8.1.3: the client keeps the token for a future connection. -/
  | storeToken (token : ByteArray)
  deriving DecidableEq

abbrev Out := Outcome State Effect

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §8.1, line 2777: "servers MUST count all of the payload bytes received in
      datagrams that are uniquely attributed to a single connection.  This
      includes datagrams that contain packets that are successfully processed
      and datagrams that contain packets that are all discarded." -/
  | recv {s a n b} : Step s (.datagramRecv a n b) (.ok (s.addRecv a n b) [])
  /-- Sending is accounted for; whether it was permitted is `MaySendTo`. -/
  | sent {s a n} : Step s (.datagramSent a n) (.ok (s.addSent a n) [])
  /-- §8.1, line 2757: "Once an endpoint has successfully processed a Handshake
      packet from the peer, it can consider the peer address to have been
      validated." -/
  | handshakeValidates {s a} :
      Step s (.handshakeProcessed a) (.ok (s.validate a) [.addressValidated a])
  /-- Same sentence, the other reading of "can": an endpoint is free not to. -/
  | handshakeNoValidate {s a} : Step s (.handshakeProcessed a) (.ok s [])
  /-- §8.1, line 2761: "an endpoint MAY consider the peer address validated if
      the peer uses a connection ID chosen by the endpoint and the connection ID
      contains at least 64 bits of entropy." -/
  | cidValidates {s a} : Step s (.peerUsedOurCid a true) (.ok (s.validate a) [.addressValidated a])
  /-- Same sentence: the MAY may be declined. -/
  | cidNoValidate {s a} (b : Bool) : Step s (.peerUsedOurCid a b) (.ok s [])
  /-- §8.2.3, line 3220: after successful path validation "the endpoint can now
      send more than three times the amount of data that has been received." -/
  | pathValidates {s a} :
      Step s (.pathValidated a) (.ok (s.validate a) [.addressValidated a])
  /-- §8.1, line 2765: "For the client, the value of the Destination Connection
      ID field in its first Initial packet allows it to validate the server
      address as a part of successfully processing any packet."  Processing the
      server's Initial also arms the Retry-discard rule of §17.2.5.2. -/
  | serverInitial {s a} (h : s.role ≠ .server) :
      Step s (.serverInitialProcessed a)
        (.ok { (s.validate a) with sawServerPacket := true } [.addressValidated a])
  /-- A server has no client role to play here. -/
  | serverInitialWrongRole {s a} (h : s.role = .server) :
      Step s (.serverInitialProcessed a) .drop
  /-- A client does not receive client Initial packets. -/
  | initialWrongRole {s a chk} (h : s.role = .client) : Step s (.clientInitial a chk) .drop
  /-- §8.1.3, line 2987: "it MUST attempt to validate the token, unless it has
      already completed address validation." -/
  | initialValidated {s a chk} (h : s.role ≠ .client) (hv : (s.info a).validated = true) :
      Step s (.clientInitial a chk) (.ok s [.handshakeProceeds a])
  /-- §8.1.3, line 2919: "Servers MAY discard any Initial packet that does not
      carry the expected token" — including one arriving from an address that is
      already validated. -/
  | initialValidatedDiscard {s a chk} (h : s.role ≠ .client) (hv : (s.info a).validated = true)
      (hx : chk.expected = false) : Step s (.clientInitial a chk) .drop
  /-- §8.1.2, line 2830: "Upon receiving the client's Initial packet, the server
      can request address validation by sending a Retry packet containing a
      token." -/
  | initialAbsentRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a .absent) (.ok s [.sendRetry a])
  /-- Same sentence, the other choice: proceed with the client unvalidated (and
      keep to the anti-amplification limit, line 2773). -/
  | initialAbsentProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a .absent) (.ok s [.handshakeProceeds a])
  /-- §8.1.3, line 2919: "Servers MAY discard any Initial packet that does not
      carry the expected token" — an Initial with no token at all. -/
  | initialAbsentDiscard {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a .absent) .drop
  /-- §8.1.3, line 2994: "If the validation succeeds, the server SHOULD then
      allow the handshake to proceed", and the address is validated. -/
  | initialValidRetryProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .retry true))
        (.ok (s.validate a) [.addressValidated a, .handshakeProceeds a])
  /-- §8.1.2, line 2836: "In response to processing an Initial containing a token
      that was provided in a Retry packet, a server cannot send another Retry
      packet; it can only refuse the connection or permit it to proceed." -/
  | initialValidRetryRefuse {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .retry true)) (.error .connectionRefused)
  /-- §8.1.4, line 3054: "If the client IP address has changed, the server MUST
      adhere to the anti-amplification limit" — the handshake proceeds but the
      address is *not* validated. -/
  | initialValidRetryMovedProceed {s a}
      (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .retry false)) (.ok s [.handshakeProceeds a])
  /-- §8.1.2, line 2836, refusal branch, for a moved client. -/
  | initialValidRetryMovedRefuse {s a}
      (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .retry false)) (.error .connectionRefused)
  /-- §8.1.3, line 2994: validation succeeded with a NEW_TOKEN token from the
      same address. -/
  | initialValidNewProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .newToken true))
        (.ok (s.validate a) [.addressValidated a, .handshakeProceeds a])
  /-- §8.1.4, line 3052: "Servers can use tokens from NEW_TOKEN in deciding not
      to send a Retry packet" — so a Retry remains a permitted choice; unlike the
      Retry-token case of line 2836, nothing forbids it. -/
  | initialValidNewRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .newToken true))
        (.ok (s.validate a) [.addressValidated a, .sendRetry a])
  /-- §8.1.4, line 3054: NEW_TOKEN token valid but the client IP has changed —
      the handshake may proceed, the anti-amplification limit still applies. -/
  | initialValidNewMovedProceed {s a}
      (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .newToken false)) (.ok s [.handshakeProceeds a])
  /-- Same, choosing to send a Retry instead (line 3052). -/
  | initialValidNewMovedRetry {s a}
      (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.valid .newToken false)) (.ok s [.sendRetry a])
  /-- §8.1.2, line 2876: "Instead, the server SHOULD immediately close
      (Section 10.2) the connection with an INVALID_TOKEN error." -/
  | initialInvalidRetryClose {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) (.error .invalidToken)
  /-- §8.1.2, line 2873: "The server can discard such a packet and allow the
      client to time out to detect handshake failure, but that could impose a
      significant latency penalty on the client." -/
  | initialInvalidRetryDiscard {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) .drop
  /-- §8.1.3, line 2989: "If the token is invalid then the server SHOULD proceed
      as if the client did not have a validated address, including potentially
      sending a Retry." — written for a token of either provenance, so it is open
      to an invalid Retry token too; see NOTES 9. -/
  | initialInvalidRetryProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) (.ok s [.handshakeProceeds a])
  /-- Same sentence, "including potentially sending a Retry". -/
  | initialInvalidRetryRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) (.ok s [.sendRetry a])
  /-- §8.1.3, line 2989: "If the token is invalid then the server SHOULD proceed
      as if the client did not have a validated address, including potentially
      sending a Retry." -/
  | initialInvalidNewRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .newToken)) (.ok s [.sendRetry a])
  /-- Same sentence, without the Retry. -/
  | initialInvalidNewProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .newToken)) (.ok s [.handshakeProceeds a])
  /-- §8.1.3, line 2919: "Servers MAY discard any Initial packet that does not
      carry the expected token." -/
  | initialInvalidNewDiscard {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .newToken)) .drop
  /-- A server ignores a Retry packet (§17.2.5.2 addresses clients only). -/
  | retryWrongRole {s t c b} (h : s.role = .server) : Step s (.recvRetry t c b) .drop
  /-- §17.2.5.2, line 6621: "A client MUST accept and process at most one Retry
      packet for each connection attempt.  After the client has received and
      processed an Initial or Retry packet from the server, it MUST discard any
      subsequent Retry packets that it receives." -/
  | retryLate {s t c b} (h : s.role ≠ .server) (hp : s.sawServerPacket = true) :
      Step s (.recvRetry t c b) .drop
  /-- §17.2.5.2, line 6630: "A client MUST discard a Retry packet with a
      zero-length Retry Token field." -/
  | retryEmptyToken {s t c b} (h : s.role ≠ .server) (hp : s.sawServerPacket = false)
      (ht : t.size = 0) : Step s (.recvRetry t c b) .drop
  /-- §17.2.5.2, line 6626: "Clients MUST discard Retry packets that have a Retry
      Integrity Tag that cannot be validated." -/
  | retryBadTag {s t c} (h : s.role ≠ .server) (hp : s.sawServerPacket = false)
      (ht : t.size ≠ 0) : Step s (.recvRetry t c false) .drop
  /-- §17.2.5.1, line 6598: "A client MUST discard a Retry packet that contains a
      Source Connection ID field that is identical to the Destination Connection
      ID field of its Initial packet." -/
  | retrySameCid {s t c} (h : s.role ≠ .server) (hp : s.sawServerPacket = false)
      (ht : t.size ≠ 0) (hc : c = s.dcid) : Step s (.recvRetry t c true) .drop
  /-- §17.2.5.2, line 6633 ("The client responds to a Retry packet with an
      Initial packet that includes the provided Retry Token") and §17.2.5.1,
      line 6601: the client sets the Token field of subsequent Initials to the
      token and their Destination Connection ID to the Retry's Source
      Connection ID. -/
  | retryAccept {s t c} (h : s.role ≠ .server) (hp : s.sawServerPacket = false)
      (ht : t.size ≠ 0) (hc : c ≠ s.dcid) :
      Step s (.recvRetry t c true)
        (.ok { s with token := some ⟨.retry, t⟩, retriesAccepted := s.retriesAccepted + 1,
                      sawServerPacket := true, dcid := c }
             [.useToken t, .useDcid c])
  /-- A server receiving NEW_TOKEN is §19.7's rule (WP3), not modelled here. -/
  | newTokenWrongRole {s t} (h : s.role = .server) : Step s (.recvNewToken t) .drop
  /-- §8.1.3, line 2905: "The server uses the NEW_TOKEN frame (Section 19.7) to
      provide the client with an address validation token that can be used to
      validate future connections." -/
  | newTokenStore {s t} (h : s.role ≠ .server) :
      Step s (.recvNewToken t) (.ok { s with newTokens := t :: s.newTokens } [.storeToken t])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .datagramRecv a n b => [.ok (s.addRecv a n b) []]
  | .datagramSent a n => [.ok (s.addSent a n) []]
  | .handshakeProcessed a => [.ok (s.validate a) [.addressValidated a], .ok s []]
  | .peerUsedOurCid a b =>
      if b = true then [.ok (s.validate a) [.addressValidated a], .ok s []] else [.ok s []]
  | .pathValidated a => [.ok (s.validate a) [.addressValidated a]]
  | .serverInitialProcessed a =>
      if s.role = .server then [.drop]
      else [.ok { (s.validate a) with sawServerPacket := true } [.addressValidated a]]
  | .clientInitial a chk =>
      if s.role = .client then [.drop]
      else if (s.info a).validated = true then
        (if chk.expected = true then [.ok s [.handshakeProceeds a]]
         else [.ok s [.handshakeProceeds a], .drop])
      else match chk with
        | .absent => [.ok s [.sendRetry a], .ok s [.handshakeProceeds a], .drop]
        | .valid .retry true =>
            [.ok (s.validate a) [.addressValidated a, .handshakeProceeds a],
             .error .connectionRefused]
        | .valid .retry false => [.ok s [.handshakeProceeds a], .error .connectionRefused]
        | .valid .newToken true =>
            [.ok (s.validate a) [.addressValidated a, .handshakeProceeds a],
             .ok (s.validate a) [.addressValidated a, .sendRetry a]]
        | .valid .newToken false => [.ok s [.handshakeProceeds a], .ok s [.sendRetry a]]
        | .invalid .retry =>
            [.error .invalidToken, .drop, .ok s [.handshakeProceeds a], .ok s [.sendRetry a]]
        | .invalid .newToken => [.ok s [.sendRetry a], .ok s [.handshakeProceeds a], .drop]
  | .recvRetry t c b =>
      if s.role = .server then [.drop]
      else if s.sawServerPacket = true then [.drop]
      else if t.size = 0 then [.drop]
      else if b = false then [.drop]
      else if c = s.dcid then [.drop]
      else [.ok { s with token := some ⟨.retry, t⟩, retriesAccepted := s.retriesAccepted + 1,
                         sawServerPacket := true, dcid := c }
              [.useToken t, .useDcid c]]
  | .recvNewToken t =>
      if s.role = .server then [.drop]
      else [.ok { s with newTokens := t :: s.newTokens } [.storeToken t]]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | datagramRecv a n b => simp only [outcomes, List.mem_singleton] at h; subst h; exact .recv
    | datagramSent a n => simp only [outcomes, List.mem_singleton] at h; subst h; exact .sent
    | handshakeProcessed a =>
        simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .handshakeValidates
        · exact .handshakeNoValidate
    | peerUsedOurCid a b =>
        simp only [outcomes] at h
        split at h
        · subst ‹b = true›
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          · exact .cidValidates
          · exact .cidNoValidate _
        · simp only [List.mem_singleton] at h; subst h; exact .cidNoValidate _
    | pathValidated a => simp only [outcomes, List.mem_singleton] at h; subst h; exact .pathValidates
    | serverInitialProcessed a =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .serverInitialWrongRole ‹_›
        · simp only [List.mem_singleton] at h; subst h; exact .serverInitial ‹_›
    | clientInitial a chk =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .initialWrongRole ‹_›
        · split at h
          · split at h
            · simp only [List.mem_singleton] at h; subst h; exact .initialValidated ‹_› ‹_›
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with rfl | rfl
              · exact .initialValidated ‹_› ‹_›
              · exact .initialValidatedDiscard ‹_› ‹_›
                  (by simpa using ‹¬ (chk.expected = true)›)
          · have hv : (s.info a).validated = false := by
              simpa using ‹¬ ((s.info a).validated = true)›
            match chk with
            | .absent =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl | rfl
                · exact .initialAbsentRetry ‹_› hv
                · exact .initialAbsentProceed ‹_› hv
                · exact .initialAbsentDiscard ‹_› hv
            | .valid .retry true =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                · exact .initialValidRetryProceed ‹_› hv
                · exact .initialValidRetryRefuse ‹_› hv
            | .valid .retry false =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                · exact .initialValidRetryMovedProceed ‹_› hv
                · exact .initialValidRetryMovedRefuse ‹_› hv
            | .valid .newToken true =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                · exact .initialValidNewProceed ‹_› hv
                · exact .initialValidNewRetry ‹_› hv
            | .valid .newToken false =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                · exact .initialValidNewMovedProceed ‹_› hv
                · exact .initialValidNewMovedRetry ‹_› hv
            | .invalid .retry =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl | rfl | rfl
                · exact .initialInvalidRetryClose ‹_› hv
                · exact .initialInvalidRetryDiscard ‹_› hv
                · exact .initialInvalidRetryProceed ‹_› hv
                · exact .initialInvalidRetryRetry ‹_› hv
            | .invalid .newToken =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl | rfl
                · exact .initialInvalidNewRetry ‹_› hv
                · exact .initialInvalidNewProceed ‹_› hv
                · exact .initialInvalidNewDiscard ‹_› hv
    | recvRetry t c b =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .retryWrongRole ‹_›
        · split at h
          · simp only [List.mem_singleton] at h; subst h; exact .retryLate ‹_› ‹_›
          · have hp : s.sawServerPacket = false := by simpa using ‹¬ (s.sawServerPacket = true)›
            split at h
            · simp only [List.mem_singleton] at h; subst h; exact .retryEmptyToken ‹_› hp ‹_›
            · split at h
              · simp only [List.mem_singleton] at h; subst h
                subst ‹b = false›
                exact .retryBadTag ‹_› hp ‹_›
              · have hb : b = true := by simpa using ‹¬ (b = false)›
                subst hb
                split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact .retrySameCid ‹_› hp ‹_› ‹_›
                · simp only [List.mem_singleton] at h; subst h
                  exact .retryAccept ‹_› hp ‹_› ‹_›
    | recvNewToken t =>
        simp only [outcomes] at h
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .newTokenWrongRole ‹_›
        · simp only [List.mem_singleton] at h; subst h; exact .newTokenStore ‹_›
  · intro h
    cases h with
    | recv => simp [outcomes]
    | sent => simp [outcomes]
    | handshakeValidates => simp [outcomes]
    | handshakeNoValidate => simp [outcomes]
    | cidValidates => simp [outcomes]
    | cidNoValidate b => cases b <;> simp [outcomes]
    | pathValidates => simp [outcomes]
    | serverInitial h => simp [outcomes, h]
    | serverInitialWrongRole h => simp [outcomes, h]
    | initialWrongRole h => simp [outcomes, h]
    | initialValidated h hv =>
      simp only [outcomes, h, hv, reduceIte]
      split <;> simp
    | initialValidatedDiscard h hv hx => simp [outcomes, h, hv, hx]
    | initialAbsentRetry h hv => simp [outcomes, h, hv]
    | initialAbsentProceed h hv => simp [outcomes, h, hv]
    | initialAbsentDiscard h hv => simp [outcomes, h, hv]
    | initialValidRetryProceed h hv => simp [outcomes, h, hv]
    | initialValidRetryRefuse h hv => simp [outcomes, h, hv]
    | initialValidRetryMovedProceed h hv => simp [outcomes, h, hv]
    | initialValidRetryMovedRefuse h hv => simp [outcomes, h, hv]
    | initialValidNewProceed h hv => simp [outcomes, h, hv]
    | initialValidNewRetry h hv => simp [outcomes, h, hv]
    | initialValidNewMovedProceed h hv => simp [outcomes, h, hv]
    | initialValidNewMovedRetry h hv => simp [outcomes, h, hv]
    | initialInvalidRetryClose h hv => simp [outcomes, h, hv]
    | initialInvalidRetryDiscard h hv => simp [outcomes, h, hv]
    | initialInvalidRetryProceed h hv => simp [outcomes, h, hv]
    | initialInvalidRetryRetry h hv => simp [outcomes, h, hv]
    | initialInvalidNewRetry h hv => simp [outcomes, h, hv]
    | initialInvalidNewProceed h hv => simp [outcomes, h, hv]
    | initialInvalidNewDiscard h hv => simp [outcomes, h, hv]
    | retryWrongRole h => simp [outcomes, h]
    | retryLate h hp => simp [outcomes, h, hp]
    | retryEmptyToken h hp ht => simp [outcomes, h, hp, ht]
    | retryBadTag h hp ht => simp [outcomes, h, hp, ht]
    | retrySameCid h hp ht hc => simp [outcomes, h, hp, ht, hc]
    | retryAccept h hp ht hc => simp [outcomes, h, hp, ht, hc]
    | newTokenWrongRole h => simp [outcomes, h]
    | newTokenStore h => simp [outcomes, h]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- §17.2.5.2, line 6621: at most one Retry is accepted per connection attempt,
    and accepting one arms the discard rule for every later Retry. -/
def Inv (s : State) : Prop :=
  s.retriesAccepted ≤ 1 ∧ (s.retriesAccepted = 1 → s.sawServerPacket = true)

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨h1, h2⟩ := hi
  cases h with
  | recv => exact ⟨h1, h2⟩
  | sent => exact ⟨h1, h2⟩
  | handshakeValidates => exact ⟨h1, h2⟩
  | handshakeNoValidate => exact ⟨h1, h2⟩
  | cidValidates => exact ⟨h1, h2⟩
  | cidNoValidate => exact ⟨h1, h2⟩
  | pathValidates => exact ⟨h1, h2⟩
  | serverInitial => exact ⟨h1, fun _ => rfl⟩
  | initialValidated => exact ⟨h1, h2⟩
  | initialAbsentRetry => exact ⟨h1, h2⟩
  | initialAbsentProceed => exact ⟨h1, h2⟩
  | initialValidRetryProceed => exact ⟨h1, h2⟩
  | initialValidRetryMovedProceed => exact ⟨h1, h2⟩
  | initialValidNewProceed => exact ⟨h1, h2⟩
  | initialValidNewRetry => exact ⟨h1, h2⟩
  | initialValidNewMovedProceed => exact ⟨h1, h2⟩
  | initialValidNewMovedRetry => exact ⟨h1, h2⟩
  | initialInvalidRetryProceed => exact ⟨h1, h2⟩
  | initialInvalidRetryRetry => exact ⟨h1, h2⟩
  | initialInvalidNewRetry => exact ⟨h1, h2⟩
  | initialInvalidNewProceed => exact ⟨h1, h2⟩
  | retryAccept _ hp _ _ =>
    have hz : s.retriesAccepted = 0 := by
      rcases Nat.eq_zero_or_pos s.retriesAccepted with h0 | h0
      · exact h0
      · have he : s.retriesAccepted = 1 := by omega
        simp [h2 he] at hp
    refine ⟨?_, fun _ => rfl⟩
    show s.retriesAccepted + 1 ≤ 1
    omega
  | newTokenStore => exact ⟨h1, h2⟩

/-! ## 6. Send side

No individual frame is governed by this component, so `MaySend` is `True`
everywhere; the real rule is about whole datagrams and is exported through the
component's `MaySendDatagram` field. -/

/-- Whom the anti-amplification limit binds.

    §8, line 2735: "after receiving packets from an address that is not yet
    validated, an endpoint MUST limit the amount of data it sends to the
    unvalidated address to three times the amount of data received from that
    address."  §8.1, line 2773: "Prior to validating the client address, servers
    MUST NOT send more than three times as many bytes as the number of bytes
    they have received."  §9.3.1, line 3431: "Until a peer's address is deemed
    valid, an endpoint limits the amount of data it sends to that address."

    And whom it does *not* bind — §8.1, line 2818: "Clients are only constrained
    by the congestion controller."  §21.1.1.1, line 8462: "The anti-amplification
    limit does not apply to clients when establishing a new connection or when
    initiating connection migration."

    So: a server is bound towards every client address it has not validated; a
    client only towards an address the peer migrated to (`newPeerAddr`) and that
    it has not validated.  See NOTES 1. -/
def State.limited (s : State) (a : Addr) : Prop :=
  (s.info a).validated = false ∧ (s.role = .server ∨ (s.info a).newPeerAddr = true)

def State.limitedB (s : State) (a : Addr) : Bool :=
  !(s.info a).validated && (decide (s.role = .server) || (s.info a).newPeerAddr)

theorem limitedB_iff (s : State) (a : Addr) : s.limitedB a = true ↔ s.limited a := by
  simp [State.limitedB, State.limited]

instance instDecidableLimited (s : State) (a : Addr) : Decidable (s.limited a) :=
  decidable_of_iff _ (limitedB_iff s a)

/-- May a datagram of `nBytes` go to `a`? -/
def MaySendTo (s : State) (a : Addr) (nBytes : Nat) : Prop :=
  ¬ s.limited a ∨ (s.info a).sent + nBytes ≤ 3 * (s.info a).received

def maySendTo (s : State) (a : Addr) (nBytes : Nat) : Bool :=
  !s.limitedB a || decide ((s.info a).sent + nBytes ≤ 3 * (s.info a).received)

theorem maySendTo_iff (s : State) (a : Addr) (n : Nat) :
    maySendTo s a n = true ↔ MaySendTo s a n := by
  unfold maySendTo MaySendTo
  rw [← limitedB_iff]
  by_cases hb : s.limitedB a = true
  · rw [hb]; simp
  · have hb' : s.limitedB a = false := by simpa using hb
    rw [hb']; simp

instance instDecidableMaySendTo (s : State) (a : Addr) (n : Nat) : Decidable (MaySendTo s a n) :=
  decidable_of_iff _ (maySendTo_iff s a n)

/-- No frame is governed by this component on its own. -/
def MaySend (_ : State) : Frame → Prop := fun _ => True

def maySend (_ : State) : Frame → Bool := fun _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

/-! ### The Retry a server sends (§17.2.5.1)

A Retry packet carries no frames, and the fields these rules constrain are
connection IDs, which `Spec.OutPacket` does not carry — so they are exported as
free-standing decidable predicates for WP12 rather than as `MaySendPacket`. -/

/-- The connection IDs in play when a server answers a client Initial with a
    Retry: the client's Initial header, and the Retry the server proposes. -/
structure RetryHeader where
  clientDcid : ByteArray
  clientScid : ByteArray
  retryDcid : ByteArray
  retryScid : ByteArray
  deriving DecidableEq

/-- §17.2.5.1, line 6592: "The server populates the Destination Connection ID
    with the connection ID that the client included in the Source Connection ID
    of the Initial packet."  §17.2.5.1, line 6597: "This value MUST NOT be equal
    to the Destination Connection ID field of the packet sent by the client." -/
def MaySendRetry (h : RetryHeader) : Prop :=
  h.retryDcid = h.clientScid ∧ h.retryScid ≠ h.clientDcid

def maySendRetry (h : RetryHeader) : Bool :=
  decide (h.retryDcid = h.clientScid) && !decide (h.retryScid = h.clientDcid)

theorem maySendRetry_iff (h : RetryHeader) : maySendRetry h = true ↔ MaySendRetry h := by
  simp [maySendRetry, MaySendRetry]

/-- §17.2.5.1, line 6615: "A server MUST NOT send more than one Retry packet in
    response to a single UDP datagram."  A received datagram may coalesce several
    Initial packets, so this constrains the effects produced while processing one
    whole received datagram, not one sent datagram: WP12 conjoins it over the
    concatenated effect lists of the packets in the datagram it just read. -/
def AtMostOneRetry (fx : List Effect) : Prop :=
  (fx.filter (fun f => match f with | .sendRetry _ => true | _ => false)).length ≤ 1

def atMostOneRetry (fx : List Effect) : Bool :=
  decide ((fx.filter (fun f => match f with | .sendRetry _ => true | _ => false)).length ≤ 1)

theorem atMostOneRetry_iff (fx : List Effect) : atMostOneRetry fx = true ↔ AtMostOneRetry fx := by
  simp [atMostOneRetry, AtMostOneRetry]

/-! ### Recommended (the SHOULDs that pick one of the permitted outcomes) -/

/-- Advice only: every outcome of `Step` conforms, and `step_recommended` shows
    the model's preferred outcome is the recommended one.  The three SHOULDs of
    §8.1 that constrain an outcome this component models are quoted inline; the
    remaining SHOULDs in range are marked `advice, not checkable here` in the
    coverage table, with the reason. -/
def Recommended (s : State) (e : Event) (o : Out) : Prop :=
  match e with
  | .clientInitial a chk =>
      s.role = .client ∨ (s.info a).validated = true ∨
        (match chk with
         -- §8.1.2, line 2876: "Instead, the server SHOULD immediately close
         -- (Section 10.2) the connection with an INVALID_TOKEN error."
         | .invalid .retry => o = .error .invalidToken
         -- §8.1.3, line 2989: "the server SHOULD proceed as if the client did
         -- not have a validated address, including potentially sending a Retry."
         | .invalid .newToken => o = .ok s [.sendRetry a] ∨ o = .ok s [.handshakeProceeds a]
         -- §8.1.3, line 2994: "If the validation succeeds, the server SHOULD
         -- then allow the handshake to proceed."
         | .valid _ true => o = .ok (s.validate a) [.addressValidated a, .handshakeProceeds a]
         | .valid _ false => o = .ok s [.handshakeProceeds a]
         | .absent => True)
  | _ => True

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
  MaySendDatagram := fun s d => MaySendTo s d.dest d.size
  maySendDatagram := fun s d => maySendTo s d.dest d.size
  maySendDatagram_iff := fun s d => maySendTo_iff s d.dest d.size

/-- The preferred outcome is the recommended one, wherever the text recommends
    one. -/
theorem step_recommended (s : State) (e : Event) : Recommended s e (component.step s e) := by
  cases e with
  | datagramRecv => trivial
  | datagramSent => trivial
  | handshakeProcessed => trivial
  | peerUsedOurCid => trivial
  | pathValidated => trivial
  | serverInitialProcessed => trivial
  | recvRetry => trivial
  | recvNewToken => trivial
  | clientInitial a chk =>
    simp only [Recommended]
    by_cases hr : s.role = .client
    · exact Or.inl hr
    by_cases hv : (s.info a).validated = true
    · exact Or.inr (Or.inl hv)
    refine Or.inr (Or.inr ?_)
    have hv' : (s.info a).validated = false := by simpa using hv
    cases chk with
    | absent => trivial
    | valid src b => cases src <;> cases b <;> simp [Component.step, outcomes, hr, hv']
    | invalid src => cases src <;> simp [Component.step, outcomes, hr, hv']

/-! ## 8. Named theorems -/

/-- The anti-amplification property: every address the limit binds (`limited`)
    has been sent at most three times what was received from it. -/
def AntiAmp (s : State) : Prop :=
  ∀ a, s.limited a → (s.info a).sent ≤ 3 * (s.info a).received

theorem AntiAmp.congr {s s' : State} (ha : s'.addrs = s.addrs) (hr : s'.role = s.role)
    (hi : AntiAmp s) : AntiAmp s' := by
  intro a hl
  obtain ⟨h1, h2⟩ := hl
  simp only [State.info, ha] at h1 h2 ⊢
  rw [hr] at h2
  exact hi a ⟨h1, h2⟩

theorem antiAmp_addRecv {s : State} {a : Addr} {n : Nat} {b : Bool} (hi : AntiAmp s) :
    AntiAmp (s.addRecv a n b) := by
  intro a' hl
  by_cases hEq : a' = a
  · subst hEq
    obtain ⟨hval, hrole⟩ := hl
    simp only [State.addRecv, info_upd_self, role_upd] at hval hrole ⊢
    by_cases hs : (s.info a').sent = 0
    · omega
    · simp only [hs, reduceIte] at hrole
      have := hi a' ⟨hval, hrole⟩
      omega
  · simp only [State.limited, State.addRecv, info_upd_ne _ _ hEq, role_upd] at hl ⊢
    exact hi a' hl

theorem antiAmp_validate {s : State} {a : Addr} (hi : AntiAmp s) : AntiAmp (s.validate a) := by
  intro a' hl
  by_cases hEq : a' = a
  · subst hEq
    obtain ⟨hval, _⟩ := hl
    simp [State.validate, info_upd_self] at hval
  · simp only [State.limited, State.validate, info_upd_ne _ _ hEq, role_upd] at hl ⊢
    exact hi a' hl

theorem antiAmp_addSent {s : State} {a : Addr} {n : Nat}
    (hi : AntiAmp s) (hm : MaySendTo s a n) : AntiAmp (s.addSent a n) := by
  intro a' hl
  by_cases hEq : a' = a
  · subst hEq
    simp only [State.limited, State.addSent, info_upd_self, role_upd] at hl
    simp only [State.addSent, info_upd_self]
    rcases hm with hm | hm
    · exact absurd hl hm
    · exact hm
  · simp only [State.limited, State.addSent, info_upd_ne _ _ hEq, role_upd] at hl ⊢
    exact hi a' hl

/-- The side condition on a self-generated event: a datagram is only sent when
    `MaySendTo` permits it.  Every other event is an input. -/
def EventOk (s : State) : Event → Prop
  | .datagramSent a n => MaySendTo s a n
  | _ => True

/-- States reachable from `s₀` by permitted steps, where every datagram we sent
    was one we were allowed to send. -/
inductive ReachableOk (s₀ : State) : State → Prop
  | refl : ReachableOk s₀ s₀
  | step {s s' e fx} : ReachableOk s₀ s → EventOk s e → Step s e (.ok s' fx) → ReachableOk s₀ s'

/-- **(a)** In every reachable state, an address the anti-amplification limit
    binds has been sent at most three times as many bytes as were received from
    it — provided every datagram sent satisfied `maySendTo`.
    §8, line 2735; §8.1, line 2773; §9.3.1, line 3431. -/
theorem antiAmplification {s₀ s : State} (h0 : AntiAmp s₀) (h : ReachableOk s₀ s) : AntiAmp s := by
  induction h with
  | refl => exact h0
  | @step s1 s2 e fx _ hok hstep ih =>
    cases hstep with
    | recv => exact antiAmp_addRecv ih
    | sent => exact antiAmp_addSent ih hok
    | handshakeValidates => exact antiAmp_validate ih
    | handshakeNoValidate => exact ih
    | cidValidates => exact antiAmp_validate ih
    | cidNoValidate => exact ih
    | pathValidates => exact antiAmp_validate ih
    | serverInitial => exact AntiAmp.congr rfl rfl (antiAmp_validate ih)
    | initialValidated => exact ih
    | initialAbsentRetry => exact ih
    | initialAbsentProceed => exact ih
    | initialValidRetryProceed => exact antiAmp_validate ih
    | initialValidRetryMovedProceed => exact ih
    | initialValidNewProceed => exact antiAmp_validate ih
    | initialValidNewRetry => exact antiAmp_validate ih
    | initialValidNewMovedProceed => exact ih
    | initialValidNewMovedRetry => exact ih
    | initialInvalidRetryProceed => exact ih
    | initialInvalidRetryRetry => exact ih
    | initialInvalidNewRetry => exact ih
    | initialInvalidNewProceed => exact ih
    | retryAccept => exact AntiAmp.congr rfl rfl ih
    | newTokenStore => exact AntiAmp.congr rfl rfl ih

/-- The empty state satisfies it, so the theorem applies from connection start. -/
theorem antiAmp_init (r : Role) (d : ByteArray) : AntiAmp (init r d) := by
  intro a _; simp [State.info, init, Map.get?]

/-- **(b)** Address validation is permanent: no step ever unvalidates an
    address. -/
theorem validated_persists {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (a : Addr) (hv : (s.info a).validated = true) :
    (s'.info a).validated = true := by
  have hval : ∀ b : Addr, ((s.validate b).info a).validated = true := by
    intro b
    by_cases hEq : a = b
    · subst hEq; rw [State.validate, info_upd_self]
    · rw [State.validate, info_upd_ne _ _ hEq]; exact hv
  have hrecv : ∀ (b : Addr) (n : Nat) (p : Bool), ((s.addRecv b n p).info a).validated = true := by
    intro b n p
    by_cases hEq : a = b
    · subst hEq; rw [State.addRecv, info_upd_self]; exact hv
    · rw [State.addRecv, info_upd_ne _ _ hEq]; exact hv
  have hsent : ∀ (b : Addr) (n : Nat), ((s.addSent b n).info a).validated = true := by
    intro b n
    by_cases hEq : a = b
    · subst hEq; rw [State.addSent, info_upd_self]; exact hv
    · rw [State.addSent, info_upd_ne _ _ hEq]; exact hv
  cases h with
  | recv => exact hrecv _ _ _
  | sent => exact hsent _ _
  | handshakeValidates => exact hval _
  | handshakeNoValidate => exact hv
  | cidValidates => exact hval _
  | cidNoValidate => exact hv
  | pathValidates => exact hval _
  | serverInitial => exact hval _
  | initialValidated => exact hv
  | initialAbsentRetry => exact hv
  | initialAbsentProceed => exact hv
  | initialValidRetryProceed => exact hval _
  | initialValidRetryMovedProceed => exact hv
  | initialValidNewProceed => exact hval _
  | initialValidNewRetry => exact hval _
  | initialValidNewMovedProceed => exact hv
  | initialValidNewMovedRetry => exact hv
  | initialInvalidRetryProceed => exact hv
  | initialInvalidRetryRetry => exact hv
  | initialInvalidNewRetry => exact hv
  | initialInvalidNewProceed => exact hv
  | retryAccept => exact hv
  | newTokenStore => exact hv

/-- **(d)** A client accepts at most one Retry packet per connection attempt.
    §17.2.5.2, line 6621. -/
theorem atMostOneRetryAccepted {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    s.retriesAccepted ≤ 1 :=
  (component.inv_of_reachable h0 h).1

theorem inv_init (r : Role) (d : ByteArray) : Inv (init r d) := ⟨by simp [init], by simp [init]⟩

/-- The sharper form of (d): once a Retry has been accepted (or any Initial from
    the server processed), every further Retry is discarded — the only permitted
    outcome is `drop`. -/
theorem retry_discarded_after {s : State} (hp : s.sawServerPacket = true) (h : s.role ≠ .server)
    (t c : ByteArray) (b : Bool) : outcomes s (.recvRetry t c b) = [.drop] := by
  simp [outcomes, hp, show s.role ≠ .server from h]

/-- An accepted Retry sets the token and the DCID that subsequent Initial
    packets must use (§17.2.5.3, line 6651). -/
theorem retry_effects {s s' : State} {t c : ByteArray} {fx : List Effect}
    (h : Step s (.recvRetry t c true) (.ok s' fx)) :
    s'.token = some ⟨.retry, t⟩ ∧ s'.dcid = c ∧ fx = [.useToken t, .useDcid c] := by
  cases h with
  | retryAccept => exact ⟨rfl, rfl, rfl⟩

/-! ## 9. Examples (scenarios from the text)

The first blocks are the review's probes P5.1–P5.4b with the corrected values. -/

private def a1 : Addr := ⟨1⟩
private def c0 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
private def c1 : ByteArray := ⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩
private def tok : ByteArray := ⟨#[7, 7, 7, 7]⟩
private def sv : State := (init .server c0).addRecv a1 1200 false
private def svV : State := sv.validate a1
private def cl : State := init .client c0

-- P5.1 (AV-1, fixed): a brand-new client may send its 1200-byte Initial, and
-- anything else — §8.1 line 2818, §21.1.1.1 line 8462.
example : maySendTo (init .client c0) a1 1200 = true := by decide
example : maySendTo (init .client c0) a1 1 = true := by decide
example : maySendTo (init .client c0) a1 1000000 = true := by decide
-- A client that has heard from the server on the original path is still free …
example : maySendTo ((init .client c0).addRecv a1 10 false) a1 100000 = true := by decide
-- … but towards an address the *peer* migrated to it is bound (§9.3.1, 3431).
example : maySendTo ((init .client c0).addRecv a1 100 true) a1 300 = true := by decide
example : maySendTo ((init .client c0).addRecv a1 100 true) a1 301 = false := by decide
-- and the limit lifts once that address is validated.
example : maySendTo (((init .client c0).addRecv a1 100 true).validate a1) a1 99999 = true := by
  decide
-- A server is bound towards an unvalidated client address, as before.
example : maySendTo sv a1 3600 = true := by decide
example : maySendTo sv a1 3601 = false := by decide
example : maySendTo (init .server c0) a1 1 = false := by decide
example : maySendTo svV a1 100000 = true := by decide
-- The budget is cumulative across datagrams.
example : maySendTo (sv.addSent a1 3600) a1 1 = false := by decide
-- The same rule through the component's datagram field.
example : component.maySendDatagram sv { size := 3600, packets := [], dest := a1 } = true := by
  decide
example : component.maySendDatagram sv { size := 3601, packets := [], dest := a1 } = false := by
  decide
example : component.maySendDatagram (init .client c0)
    { size := 1200, packets := [], dest := a1 } = true := by decide

-- P5.2 (AV-2, fixed): a validated server MAY discard an Initial that does not
-- carry the expected token (§8.1.3, line 2919) …
example : component.outcomes svV (.clientInitial a1 .absent)
    = [.ok svV [.handshakeProceeds a1], .drop] := by decide
example : component.accepts svV (.clientInitial a1 .absent) .drop = true := by decide
example : component.accepts svV (.clientInitial a1 (.invalid .newToken)) .drop = true := by decide
-- … but a valid token *is* the expected one, so there is nothing to discard.
example : component.outcomes svV (.clientInitial a1 (.valid .newToken true))
    = [.ok svV [.handshakeProceeds a1]] := by decide

-- P5.3 (AV-2, fixed): an unvalidated server may discard a token-less Initial.
example : component.accepts sv (.clientInitial a1 .absent) .drop = true := by decide
example : component.accepts sv (.clientInitial a1 (.invalid .newToken)) .drop = true := by decide

-- P5.4 (AV-3, fixed): an invalid Retry token — INVALID_TOKEN is preferred
-- (§8.1.2, line 2876), and "proceed as unvalidated" (§8.1.3, line 2989) is
-- permitted too.
example : component.outcomes sv (.clientInitial a1 (.invalid .retry))
    = [.error .invalidToken, .drop, .ok sv [.handshakeProceeds a1], .ok sv [.sendRetry a1]] := by
  decide
example : component.accepts sv (.clientInitial a1 (.invalid .retry))
    (.ok sv [.handshakeProceeds a1]) = true := by decide

-- P5.4b (AV-4): CONNECTION_REFUSED stays in the two places §8 itself names it;
-- the general right to refuse (§5.2.2, line 1936) is the endpoint's, see NOTES 5.
example : component.accepts sv (.clientInitial a1 .absent) (.error .connectionRefused)
    = false := by decide
example : component.accepts sv (.clientInitial a1 (.valid .retry true))
    (.error .connectionRefused) = true := by decide

-- Figure 9 (line 2895): Initial without a token → the server sends a Retry …
example : component.step sv (.clientInitial a1 .absent) = .ok sv [.sendRetry a1] := by decide
-- §8.1.3, line 2994: Initial+Token with a valid Retry token → validated, proceed.
example : component.step sv (.clientInitial a1 (.valid .retry true)) =
    .ok svV [.addressValidated a1, .handshakeProceeds a1] := by decide
-- §8.1.2, line 2836: a second Retry is not an option there.
example : component.accepts sv (.clientInitial a1 (.valid .retry true)) (.ok sv [.sendRetry a1])
    = false := by decide
-- §8.1.4, line 3054: a valid NEW_TOKEN token from a changed address does not
-- validate the address.
example : component.step sv (.clientInitial a1 (.valid .newToken false)) =
    .ok sv [.handshakeProceeds a1] := by decide

-- §17.2.5.2, line 6633: the client accepts the Retry and uses token and new DCID.
example : component.step cl (.recvRetry tok c1 true) =
    .ok { cl with token := some ⟨.retry, tok⟩, retriesAccepted := 1, sawServerPacket := true,
                  dcid := c1 }
         [.useToken tok, .useDcid c1] := by decide
-- … and discards a second one (line 6621).
example : component.step ((component.step cl (.recvRetry tok c1 true)).next cl)
    (.recvRetry tok c1 true) = .drop := by decide
-- §17.2.5.2, line 6630: zero-length token → discard.
example : component.step cl (.recvRetry ByteArray.empty c1 true) = .drop := by decide
-- §17.2.5.2, line 6626: bad integrity tag → discard.
example : component.step cl (.recvRetry tok c1 false) = .drop := by decide
-- §17.2.5.1, line 6598: SCID equal to our Initial's DCID → discard.
example : component.step cl (.recvRetry tok c0 true) = .drop := by decide
-- §8.1.3: a NEW_TOKEN frame is stored for a future connection.
example : component.step cl (.recvNewToken tok) =
    .ok { cl with newTokens := [tok] } [.storeToken tok] := by decide

-- AV-5: §17.2.5.1, lines 6592 and 6597 — the Retry a server sends.
example : maySendRetry { clientDcid := c0, clientScid := c1, retryDcid := c1, retryScid := tok }
    = true := by decide
example : maySendRetry { clientDcid := c0, clientScid := c1, retryDcid := c1, retryScid := c0 }
    = false := by decide   -- SCID equal to the client's Initial DCID
example : maySendRetry { clientDcid := c0, clientScid := c1, retryDcid := c0, retryScid := tok }
    = false := by decide   -- DCID is not the client's SCID
-- §17.2.5.1, line 6615: at most one Retry per received UDP datagram.
example : atMostOneRetry [.sendRetry a1] = true := by decide
example : atMostOneRetry [.sendRetry a1, .handshakeProceeds a1, .sendRetry ⟨2⟩] = false := by decide

-- Following a server we cannot see inside: it answered with a Retry, so it did
-- not validate the address.
example : component.track sv (.clientInitial a1 (.invalid .newToken)) (.ok [.sendRetry a1]) =
    some sv := by rfl

/-! ## 10. Coverage and notes

Every normative sentence in lines 2724–3068 and 6557–6697.  Line numbers are the
line the quoted sentence starts on.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §8 (2735) | MUST limit data sent to an unvalidated address to 3× data received | `State.limited`, `MaySendTo`, `antiAmplification` |
| §8.1 (2757) | successfully processed Handshake packet ⇒ peer address can be considered validated | `Step.handshakeValidates` / `.handshakeNoValidate` |
| §8.1 (2761) | MAY consider validated if the peer uses a CID we chose with ≥ 64 bits of entropy | `Step.cidValidates` / `.cidNoValidate` |
| §8.1 (2765) | the client validates the server address by processing any packet | `Step.serverInitial` |
| §8.1 (2773) | servers MUST NOT send more than 3× the bytes received prior to validation | `State.limited`, `MaySendTo` |
| §8.1 (2777) | servers MUST count all payload bytes of datagrams uniquely attributed to the connection, processed or discarded | `Step.recv` (the caller supplies `n`) |
| §8.1 (2783) | clients MUST pad Initial datagrams to ≥ 1200 bytes | out of scope: WP7 DatagramSize |
| §8.1 (2795) | clients MUST send a packet on a PTO | out of scope: loss recovery (RFC 9002) |
| §8.1 (2805) | that packet MUST be an Initial in a ≥ 1200-byte datagram, else a Handshake packet | out of scope: WP7 DatagramSize / RFC 9002 |
| §8.1 (2818) | "Clients are only constrained by the congestion controller." | `State.limited`'s role clause; probes P5.1 |
| §8.1.1 (2823) | a token MUST be constructed so the server can identify how it was provided | `TokenSource`, carried on `TokenCheck`; construction itself out of scope |
| §8.1.2 (2830) | the server can request address validation by sending a Retry | `Step.initialAbsentRetry` |
| §8.1.2 (2832) | the token MUST be repeated by the client in all Initials after the Retry | `Effect.useToken`, `State.token`; see NOTES 4 |
| §8.1.2 (2836) | after a Retry token, the server can only refuse or proceed — no second Retry | `Step.initialValidRetry{Proceed,Refuse}`; no `sendRetry` outcome exists |
| §8.1.2 (2873) | the server can discard an Initial with an invalid Retry token | `Step.initialInvalidRetryDiscard` |
| §8.1.2 (2876) | SHOULD immediately close (Section 10.2) with INVALID_TOKEN | SHOULD → `Recommended`; `Step.initialInvalidRetryClose`, the preferred outcome |
| §8.1.3 (2899) | a server MAY provide tokens for later connections with NEW_TOKEN | `Step.newTokenStore` |
| §8.1.3 (2917) | the client MUST include the token in all Initials unless a Retry replaces it | `State.token` / `Effect.useToken`; see NOTES 4 |
| §8.1.3 (2918) | the client MUST NOT use a Retry token for future connections | `ClientToken.src`; see NOTES 4 |
| §8.1.3 (2919) | servers MAY discard an Initial that does not carry the expected token | `Step.initialAbsentDiscard`, `.initialValidatedDiscard`, `.initialInvalidNewDiscard`, `.initialInvalidRetryDiscard` |
| §8.1.3 (2923) | a token SHOULD have an expiration time | SHOULD → advice, not checkable here: token construction is opaque (`TokenCheck`) |
| §8.1.3 (2930) | a NEW_TOKEN token MUST NOT include linkable information | out of scope: token construction |
| §8.1.3 (2934) | a server MUST ensure every NEW_TOKEN frame it sends is unique across clients | out of scope: token construction; no cross-connection state here |
| §8.1.3 (2936) | information distinguishing Retry from NEW_TOKEN tokens MAY be visible to others | out of scope: token construction |
| §8.1.3 (2946) | a client with an applicable unused token SHOULD include it in its Initial | SHOULD → advice, not checkable here: token *selection* is policy over `State.newTokens`, and the Token field is a packet header, not a frame (NOTES 4) |
| §8.1.3 (2950) | a client MUST NOT include a token not applicable to the server | out of scope: no server identity in this model (NOTES 5) |
| §8.1.3 (2954) | a client MAY use a token from any previous connection to that server | out of scope: same reason |
| §8.1.3 (2960) | a Retry token MUST be used immediately and cannot be used in later attempts | `ClientToken.src`; see NOTES 4 |
| §8.1.3 (2973) | a client SHOULD NOT reuse a NEW_TOKEN token for different connection attempts | SHOULD → advice, not checkable here: the component models one connection attempt, so reuse across attempts is not observable in its state |
| §8.1.3 (2987) | on an Initial with a token the server MUST attempt validation unless already validated | `Step.initialValidated` (the exception) plus the `chk` cases |
| §8.1.3 (2989) | invalid token ⇒ SHOULD proceed as if unvalidated, possibly with a Retry | SHOULD → `Recommended`; `Step.initialInvalid{Retry,New}{Proceed,Retry}` |
| §8.1.3 (2994) | validation succeeds ⇒ SHOULD allow the handshake to proceed | SHOULD → `Recommended`; `Step.initialValid{Retry,New}Proceed` preferred |
| §8.1.3 (3013) | clients MAY use tokens from one connection for any attempt using the same version | out of scope: token selection policy, no version state here |
| §8.1.4 (3031) | an address validation token MUST be difficult to guess | out of scope: token construction |
| §8.1.4 (3037) | the token MUST be covered by integrity protection | out of scope: token construction |
| §8.1.4 (3046) | Retry tokens SHOULD let the server verify the source IP and port | SHOULD → advice, not checkable here: token construction; its *effect* is the `addrUnchanged` flag of `TokenCheck.valid` |
| §8.1.4 (3050) | NEW_TOKEN tokens MUST let the server verify the client IP | out of scope: token construction; effect is `addrUnchanged` |
| §8.1.4 (3054) | if the client IP changed the server MUST adhere to the anti-amplification limit | `Step.initialValid*Moved*` do not validate the address |
| §8.1.4 (3060) | servers MUST ensure replay of tokens is prevented or limited | out of scope: server token store (opaque `TokenCheck`) |
| §8.1.4 (3061) | servers SHOULD accept Retry tokens only for a short time | SHOULD → advice, not checkable here: no clock and no server token store |
| §8.1.4 (3064) | NEW_TOKEN tokens SHOULD NOT be accepted multiple times | SHOULD → advice, not checkable here: same reason |
| §8.1.4 (3066) | tokens MAY include extra information to narrow applicability or reuse | out of scope: token construction |
| §17.2.5 (6579) | a client MUST ignore the bits of the Unused field | out of scope: header decoding (`QuicModel/Packet.lean`); no bit of it reaches `Event` |
| §17.2.5.1 (6592) | the Retry DCID is the client's Initial SCID | `MaySendRetry` |
| §17.2.5.1 (6597) | the Retry SCID MUST NOT equal the client's Initial DCID (**server send**) | `MaySendRetry` |
| §17.2.5.1 (6598) | a client MUST discard a Retry whose SCID equals its Initial's DCID (**client receive**) | `Step.retrySameCid` |
| §17.2.5.1 (6601) | the client MUST use the Retry SCID as the DCID of subsequent packets | `Step.retryAccept`, `Effect.useDcid` |
| §17.2.5.1 (6613) | a server MAY send Retry packets in response to Initial and 0-RTT packets | `Effect.sendRetry` for the Initial case; 0-RTT is out of scope (WP11 Handshake) |
| §17.2.5.1 (6615) | a server MUST NOT send more than one Retry per received UDP datagram | `AtMostOneRetry` / `atMostOneRetry`, exported for WP12 |
| §17.2.5.2 (6621) | a client MUST accept and process at most one Retry per connection attempt | `Inv`, `atMostOneRetryAccepted` |
| §17.2.5.2 (6622) | after an Initial or Retry from the server, discard later Retries | `Step.retryLate`, `retry_discarded_after` |
| §17.2.5.2 (6626) | discard Retries whose Retry Integrity Tag cannot be validated | `Step.retryBadTag` (the tag check is the opaque `integrityOk`) |
| §17.2.5.2 (6630) | a client MUST discard a Retry with a zero-length Retry Token | `Step.retryEmptyToken` |
| §17.2.5.2 (6633) | the client responds with an Initial carrying the Retry Token | `Step.retryAccept`, `Effect.useToken` |
| §17.2.5.2 (6641) | the client MUST NOT change its Source Connection ID | out of scope: WP4 ConnIds |
| §17.2.5.2 (6646) | a Retry has no packet number and cannot be acknowledged | out of scope: WP3 FrameRules / ACK generation |
| §17.2.5.3 (6651) | subsequent Initials carry the Retry's CID and token | `Effect.useDcid`, `Effect.useToken` |
| §17.2.5.3 (6671) | the client MUST use the same cryptographic handshake message | out of scope: WP11 Handshake |
| §17.2.5.3 (6673) | a server MAY treat a different handshake message as an error or discard it | out of scope: WP11 Handshake |
| §17.2.5.3 (6679) | a client MAY attempt 0-RTT after a Retry | out of scope: WP11 Handshake |
| §17.2.5.3 (6682) | the client MUST NOT reset the packet number after a Retry | out of scope: WP3 / WP11 |
| §17.2.5.3 (6691) | a server MAY abort the connection if it detects a reset packet number | out of scope: WP3 / WP11 |
| §17.2.5.3 (6694) | Retry CIDs are copied to transport parameters and validated | out of scope: WP1 TransportParams, §7.3 |
| §8.2 (3070–3271) | path validation | `Spec/PathValidation.lean` |

Sentences from outside the assigned range that this file relies on, listed so a
reviewer can check the import: §9.3 line 3378 (a packet from a new peer address
means the peer migrated) and §9.3.1 line 3431 (an endpoint limits what it sends
to an unvalidated peer address) justify `AddrState.newPeerAddr`; §21.1.1.1 line
8462 (the limit does not apply to clients establishing a connection or
initiating migration) is the authority for the client exemption.  §9 as a whole
is WP10 Migration's.

NOTES

1. **Whom the limit binds (review AV-1).**  The first version applied the 3×
   budget to every unvalidated address of either role, which made a fresh
   client's very first Initial illegal: nothing had been received, so the budget
   was zero.  §8.1 line 2818 and §21.1.1.1 line 8462 are explicit that a client
   establishing a connection or initiating migration is exempt, and §8's own
   sentence binds an endpoint only "after receiving packets from" the address.
   `State.limited` now binds a server towards any unvalidated client address, and
   a client only towards an address the *peer* moved to.  `newPeerAddr` is set
   from the receive event and only while nothing has been sent to that address —
   an address we have already written to is not new to us — which keeps `limited`
   monotone (it can only stop holding, via validation) and hence keeps
   `antiAmplification` true.  Consequence worth knowing: a server that has
   received nothing from an address still has budget 0 there, which is the
   conservative reading of line 2735.

2. **"can consider … validated" (line 2757) and the MAY of line 2761** are
   encoded as *two* outcomes each: validating (preferred) and not validating.
   A conforming implementation that is more conservative is therefore accepted.

3. **Address-validating events are not exclusive.**  `Step.pathValidated` is the
   hook for `PathValidation`: §8.2.3 line 3220 says a validated path lifts the
   anti-amplification limit.  Composing the two components (WP12) means firing
   this event on `PathValidation.Effect.pathValidated`.

4. **Token use on the send side is an effect, not a `MaySend` clause.**  The
   token of §8.1.2/§8.1.3 travels in the Token field of the Initial *packet*
   header, not in a frame, and neither `Frame` nor `Spec.OutPacket` carries it.
   The obligations "MUST be repeated in all Initial packets" (lines 2832 and
   2917) and "MUST NOT use a Retry token for future connections" (line 2918) are
   therefore recorded in `State.token` (with its `ClientToken.src`) and announced
   with `Effect.useToken`; the packet-level check belongs to WP12, which can
   state it as `pkt.token = (s.token.map ClientToken.bytes).getD ByteArray.empty`
   for Initial packets.  Likewise `Effect.useDcid` records line 6601's DCID
   obligation, whose enforcement is a packet-header property.

5. **This component must not veto a refusal (review AV-4).**  §5.2.2 line 1936
   gives a server an unconditional right to refuse a new connection with
   CONNECTION_REFUSED, and §8 neither grants nor removes it.  `Step` here names
   `.error .connectionRefused` only in the two places §8.1.2 line 2836 itself
   names it ("it can only refuse the connection or permit it to proceed").
   **WP12 must therefore not read `AddressValidation.accepts = false` as a veto
   of a connection-level refusal**: the endpoint's merge for connection errors
   has to be a union over components, not an intersection.  Adding
   `.error .connectionRefused` to every branch here would instead make this
   component the owner of a rule from §5.2.2, outside its range.

6. **One Retry per received datagram (line 6615)** constrains the effects
   produced while processing one *received* datagram, which may coalesce several
   Initial packets; it is not a property of a datagram we send, so it is exported
   as `AtMostOneRetry` over an effect list rather than as a `MaySendDatagram`
   clause.  `MaySendRetry` covers the header rules of lines 6592 and 6597, which
   `Spec.OutPacket` cannot express because it carries no connection IDs.

7. **Ambiguity: may a server still send a Retry after a *valid* NEW_TOKEN
   token?**  Line 2994 says it SHOULD allow the handshake to proceed, and line
   2836's prohibition is explicitly restricted to tokens "provided in a Retry
   packet"; line 3052 ("Servers can use tokens from NEW_TOKEN in deciding not to
   send a Retry packet") presupposes that sending one is still a choice.  The
   reading encoded here: permitted, but not preferred
   (`Step.initialValidNewRetry`).

8. **Ambiguity: does a valid token always validate the address?**  §8.1.4 line
   3054 makes the anti-amplification limit apply whenever the client IP has
   changed, even with a valid NEW_TOKEN token.  The reading encoded here extends
   that to Retry tokens as well (the `addrUnchanged` flag gates address
   validation for both sources), which is the conservative choice; a server
   whose Retry tokens do verify the address pair — line 3046's SHOULD — never
   sees `valid .retry false`.

9. **Ambiguity: does line 2989 reach an invalid *Retry* token (review AV-3)?**
   Line 2989 is written for "the token", without restricting its provenance,
   while lines 2871–2876 discuss the invalid-Retry-token case and recommend
   INVALID_TOKEN.  Reading encoded: INVALID_TOKEN stays the preferred and the
   `Recommended` outcome, and proceeding-as-unvalidated — with or without a
   Retry — is additionally permitted.  The Retry alternative is odd in practice,
   since line 2871 observes the client "will not accept another Retry token",
   but that is an observation, not a prohibition.

10. **`.drop` vs `.ok s []`.**  Following the Template, `.drop` is used for
    discarding a whole packet (an Initial or a Retry), which is what every
    discard rule in this range is about.  Events that do not apply to the
    endpoint's role also yield `.drop`.

11. **Sends are recorded, not policed, by `Step`.**  `Step.sent` accepts any
    `datagramSent`, because the model must be able to describe an implementation
    that oversends in order to reject it.  The prohibition lives in `MaySendTo`
    (and so in the component's `MaySendDatagram`), and theorem
    `antiAmplification` carries it as the `EventOk` side condition of
    `ReachableOk`.

12. **§10.2.1 lines 3993 and 4008** (a closing endpoint that has discarded keys
    must limit itself to 3× what it received; an endpoint in the closing state
    must either discard packets from an unvalidated address or apply that limit)
    are outside this file's range and belong to WP6 Termination.  They can be
    expressed with the machinery here — `State.limited` and `MaySendTo` are
    already per-address — if the lead wants one owner for the 3× rule.
-/

end Quic.Spec.AddressValidation
