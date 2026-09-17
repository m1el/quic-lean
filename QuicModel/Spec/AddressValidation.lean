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

/-! ## 1. State, events, effects -/

/-- A peer transport address — §8.2, line 3075: "an address is the two-tuple of
    IP address and port".  An opaque handle: the model never inspects it.
    Equality of handles means equality of the two-tuple. -/
structure Addr where
  id : Nat
  deriving DecidableEq, Repr

/-- §8, line 2736: per-address anti-amplification accounting.

    `received` counts, per line 2777, "all of the payload bytes received in
    datagrams that are uniquely attributed to a single connection", whether the
    packets in them were processed or discarded.  `sent` counts the UDP payload
    bytes sent to the address. -/
structure AddrState where
  validated : Bool := false
  received : Nat := 0
  sent : Nat := 0
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
    (§8.1.4, lines 3046–3055).  How the check is performed, and the token's
    encryption and integrity protection (§8.1.4), are out of scope. -/
inductive TokenCheck where
  | absent
  | valid (src : TokenSource) (addrUnchanged : Bool)
  | invalid (src : TokenSource)
  deriving DecidableEq, Repr

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
      effective", line 2982). -/
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

def State.addRecv (s : State) (a : Addr) (n : Nat) : State :=
  s.upd a fun st => { st with received := st.received + n }

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

inductive Event where
  /-- §8.1, line 2777: `n` payload bytes arrived from `a` in a datagram uniquely
      attributed to this connection (processed or discarded — both count). -/
  | datagramRecv (a : Addr) (n : Nat)
  /-- A UDP datagram of `n` payload bytes was sent to `a`. -/
  | datagramSent (a : Addr) (n : Nat)
  /-- §8.1, line 2757: "Once an endpoint has successfully processed a Handshake
      packet from the peer". -/
  | handshakeProcessed (a : Addr)
  /-- §8.1, line 2761: the peer used a connection ID we chose; `hasEntropy` says
      it "contains at least 64 bits of entropy". -/
  | peerUsedOurCid (a : Addr) (hasEntropy : Bool)
  /-- §8.2.3, line 3219: path validation to `a` succeeded (driven by
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
  | recv {s a n} : Step s (.datagramRecv a n) (.ok (s.addRecv a n) [])
  /-- Sending is accounted for; whether it was permitted is `MaySendDatagram`. -/
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
  /-- §8.2.3, line 3219: after successful path validation "the endpoint can now
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
  /-- §8.1.2, line 2830: "Upon receiving the client's Initial packet, the server
      can request address validation by sending a Retry packet containing a
      token." -/
  | initialAbsentRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a .absent) (.ok s [.sendRetry a])
  /-- Same sentence, the other choice: proceed with the client unvalidated (and
      keep to the anti-amplification limit, line 2773). -/
  | initialAbsentProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a .absent) (.ok s [.handshakeProceeds a])
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
  /-- §8.1.2, line 2875: "the server SHOULD immediately close the connection with
      an INVALID_TOKEN error." -/
  | initialInvalidRetryClose {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) (.error .invalidToken)
  /-- §8.1.2, line 2873: "The server can discard such a packet and allow the
      client to time out to detect handshake failure". -/
  | initialInvalidRetryDiscard {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .retry)) .drop
  /-- §8.1.3, line 2989: "If the token is invalid then the server SHOULD proceed
      as if the client did not have a validated address, including potentially
      sending a Retry." -/
  | initialInvalidNewRetry {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .newToken)) (.ok s [.sendRetry a])
  /-- Same sentence, without the Retry. -/
  | initialInvalidNewProceed {s a} (h : s.role ≠ .client) (hv : (s.info a).validated = false) :
      Step s (.clientInitial a (.invalid .newToken)) (.ok s [.handshakeProceeds a])
  /-- §8.1.3, line 2920: "Servers MAY discard any Initial packet that does not
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
  /-- §17.2.5.2, lines 6633–6641: the client accepts the Retry, sets the Token
      field of subsequent Initials to the token and their Destination Connection
      ID to the Retry's Source Connection ID. -/
  | retryAccept {s t c} (h : s.role ≠ .server) (hp : s.sawServerPacket = false)
      (ht : t.size ≠ 0) (hc : c ≠ s.dcid) :
      Step s (.recvRetry t c true)
        (.ok { s with token := some ⟨.retry, t⟩, retriesAccepted := s.retriesAccepted + 1,
                      sawServerPacket := true, dcid := c }
             [.useToken t, .useDcid c])
  /-- A server receiving NEW_TOKEN is §19.7's rule (WP3), not modelled here. -/
  | newTokenWrongRole {s t} (h : s.role = .server) : Step s (.recvNewToken t) .drop
  /-- §8.1.3, line 2905: "The server uses the NEW_TOKEN frame to provide the
      client with an address validation token that can be used to validate
      future connections." -/
  | newTokenStore {s t} (h : s.role ≠ .server) :
      Step s (.recvNewToken t) (.ok { s with newTokens := t :: s.newTokens } [.storeToken t])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .datagramRecv a n => [.ok (s.addRecv a n) []]
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
      else if (s.info a).validated = true then [.ok s [.handshakeProceeds a]]
      else match chk with
        | .absent => [.ok s [.sendRetry a], .ok s [.handshakeProceeds a]]
        | .valid .retry true =>
            [.ok (s.validate a) [.addressValidated a, .handshakeProceeds a],
             .error .connectionRefused]
        | .valid .retry false => [.ok s [.handshakeProceeds a], .error .connectionRefused]
        | .valid .newToken true =>
            [.ok (s.validate a) [.addressValidated a, .handshakeProceeds a],
             .ok (s.validate a) [.addressValidated a, .sendRetry a]]
        | .valid .newToken false => [.ok s [.handshakeProceeds a], .ok s [.sendRetry a]]
        | .invalid .retry => [.error .invalidToken, .drop]
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
    | datagramRecv a n => simp only [outcomes, List.mem_singleton] at h; subst h; exact .recv
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
          · simp only [List.mem_singleton] at h; subst h; exact .initialValidated ‹_› ‹_›
          · have hv : (s.info a).validated = false := by
              simpa using ‹¬ ((s.info a).validated = true)›
            match chk with
            | .absent =>
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with rfl | rfl
                · exact .initialAbsentRetry ‹_› hv
                · exact .initialAbsentProceed ‹_› hv
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
                rcases h with rfl | rfl
                · exact .initialInvalidRetryClose ‹_› hv
                · exact .initialInvalidRetryDiscard ‹_› hv
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
    | initialValidated h hv => simp [outcomes, h, hv]
    | initialAbsentRetry h hv => simp [outcomes, h, hv]
    | initialAbsentProceed h hv => simp [outcomes, h, hv]
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

The rule this component enforces is about whole datagrams, not frames, so
`MaySend` is `True` everywhere and the real predicate is `MaySendDatagram`. -/

/-- §8, line 2736: "after receiving packets from an address that is not yet
    validated, an endpoint MUST limit the amount of data it sends to the
    unvalidated address to three times the amount of data received from that
    address"; §8.1, line 2773: "Prior to validating the client address, servers
    MUST NOT send more than three times as many bytes as the number of bytes
    they have received." -/
def MaySendDatagram (s : State) (a : Addr) (nBytes : Nat) : Prop :=
  (s.info a).validated = true ∨ (s.info a).sent + nBytes ≤ 3 * (s.info a).received

def maySendDatagram (s : State) (a : Addr) (nBytes : Nat) : Bool :=
  (s.info a).validated || decide ((s.info a).sent + nBytes ≤ 3 * (s.info a).received)

theorem maySendDatagram_iff (s : State) (a : Addr) (n : Nat) :
    maySendDatagram s a n = true ↔ MaySendDatagram s a n := by
  simp [maySendDatagram, MaySendDatagram]

instance instDecidableMaySendDatagram (s : State) (a : Addr) (n : Nat) :
    Decidable (MaySendDatagram s a n) :=
  decidable_of_iff _ (maySendDatagram_iff s a n)

/-- No frame is governed by this component on its own. -/
def MaySend (_ : State) : Frame → Prop := fun _ => True

def maySend (_ : State) : Frame → Bool := fun _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  simp [maySend, MaySend]

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

/-! ## 8. Named theorems -/

/-- The anti-amplification property, as a predicate on states. -/
def AntiAmp (s : State) : Prop :=
  ∀ a, (s.info a).validated = false → (s.info a).sent ≤ 3 * (s.info a).received

theorem AntiAmp.congr {s s' : State} (h : s'.addrs = s.addrs) (hi : AntiAmp s) : AntiAmp s' := by
  intro a; simp only [State.info, h]; exact hi a

theorem antiAmp_addRecv {s : State} {a : Addr} {n : Nat} (hi : AntiAmp s) :
    AntiAmp (s.addRecv a n) := by
  intro a' hv
  by_cases hEq : a' = a
  · subst hEq
    simp only [State.addRecv, info_upd_self] at hv ⊢
    have := hi a' hv
    omega
  · rw [State.addRecv, info_upd_ne _ _ hEq] at hv ⊢
    exact hi a' hv

theorem antiAmp_validate {s : State} {a : Addr} (hi : AntiAmp s) : AntiAmp (s.validate a) := by
  intro a' hv
  by_cases hEq : a' = a
  · subst hEq; simp only [State.validate, info_upd_self] at hv; exact absurd hv (by simp)
  · rw [State.validate, info_upd_ne _ _ hEq] at hv ⊢
    exact hi a' hv

theorem antiAmp_addSent {s : State} {a : Addr} {n : Nat}
    (hi : AntiAmp s) (hm : MaySendDatagram s a n) : AntiAmp (s.addSent a n) := by
  intro a' hv
  by_cases hEq : a' = a
  · subst hEq
    simp only [State.addSent, info_upd_self] at hv ⊢
    rcases hm with hm | hm
    · exact absurd hm (by simp [hv])
    · exact hm
  · rw [State.addSent, info_upd_ne _ _ hEq] at hv ⊢
    exact hi a' hv

/-- The side condition on a self-generated event: a datagram is only sent when
    `MaySendDatagram` permits it.  Every other event is an input. -/
def EventOk (s : State) : Event → Prop
  | .datagramSent a n => MaySendDatagram s a n
  | _ => True

/-- States reachable from `s₀` by permitted steps, where every datagram we sent
    was one we were allowed to send. -/
inductive ReachableOk (s₀ : State) : State → Prop
  | refl : ReachableOk s₀ s₀
  | step {s s' e fx} : ReachableOk s₀ s → EventOk s e → Step s e (.ok s' fx) → ReachableOk s₀ s'

/-- **(a)** In every reachable state, an address that is not yet validated has
    been sent at most three times as many bytes as were received from it —
    provided every datagram sent satisfied `maySendDatagram`.
    §8, lines 2733–2739; §8.1, line 2773. -/
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
    | serverInitial => exact AntiAmp.congr rfl (antiAmp_validate ih)
    | initialValidated => exact ih
    | initialAbsentRetry => exact ih
    | initialAbsentProceed => exact ih
    | initialValidRetryProceed => exact antiAmp_validate ih
    | initialValidRetryMovedProceed => exact ih
    | initialValidNewProceed => exact antiAmp_validate ih
    | initialValidNewRetry => exact antiAmp_validate ih
    | initialValidNewMovedProceed => exact ih
    | initialValidNewMovedRetry => exact ih
    | initialInvalidNewRetry => exact ih
    | initialInvalidNewProceed => exact ih
    | retryAccept => exact AntiAmp.congr rfl ih
    | newTokenStore => exact AntiAmp.congr rfl ih

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
  have hrecv : ∀ (b : Addr) (n : Nat), ((s.addRecv b n).info a).validated = true := by
    intro b n
    by_cases hEq : a = b
    · subst hEq; rw [State.addRecv, info_upd_self]; exact hv
    · rw [State.addRecv, info_upd_ne _ _ hEq]; exact hv
  have hsent : ∀ (b : Addr) (n : Nat), ((s.addSent b n).info a).validated = true := by
    intro b n
    by_cases hEq : a = b
    · subst hEq; rw [State.addSent, info_upd_self]; exact hv
    · rw [State.addSent, info_upd_ne _ _ hEq]; exact hv
  cases h with
  | recv => exact hrecv _ _
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
  | initialInvalidNewRetry => exact hv
  | initialInvalidNewProceed => exact hv
  | retryAccept => exact hv
  | newTokenStore => exact hv

/-- **(d)** A client accepts at most one Retry packet per connection attempt.
    §17.2.5.2, line 6621. -/
theorem atMostOneRetry {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
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
    packets must use (§17.2.5.3, lines 6651–6657). -/
theorem retry_effects {s s' : State} {t c : ByteArray} {fx : List Effect}
    (h : Step s (.recvRetry t c true) (.ok s' fx)) :
    s'.token = some ⟨.retry, t⟩ ∧ s'.dcid = c ∧ fx = [.useToken t, .useDcid c] := by
  cases h with
  | retryAccept => exact ⟨rfl, rfl, rfl⟩

/-! ## 9. Examples (scenarios from the text) -/

private def ca : Addr := ⟨1⟩
private def sv : State := (init .server ByteArray.empty).addRecv ca 1200
private def tok : ByteArray := ⟨#[7, 7, 7, 7]⟩
private def cid0 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩
private def cid1 : ByteArray := ⟨#[9, 9, 9, 9, 9, 9, 9, 9]⟩
private def cl : State := init .client cid0

-- §8.1, line 2773: after a 1200-byte client Initial the server may send 3600
-- bytes and no more.
example : maySendDatagram sv ca 3600 = true := by decide
example : maySendDatagram sv ca 3601 = false := by decide
-- A server that has heard nothing from an address may send nothing to it.
example : maySendDatagram (init .server ByteArray.empty) ca 1 = false := by decide
-- §8.1, line 2757: a Handshake packet validates the address; then the limit is
-- gone.
example : maySendDatagram ((component.step sv (.handshakeProcessed ca)).next sv) ca 100000 = true := by
  decide

-- Figure 9 (line 2883): Initial without a token → the server sends a Retry …
example : component.step sv (.clientInitial ca .absent) = .ok sv [.sendRetry ca] := by decide
-- … but proceeding unvalidated is also permitted …
example : component.accepts sv (.clientInitial ca .absent) (.ok sv [.handshakeProceeds ca]) = true := by
  decide
-- … and closing with INVALID_TOKEN is not.
example : component.accepts sv (.clientInitial ca .absent) (.error .invalidToken) = false := by decide

-- §8.1.3, line 2994: Initial+Token with a valid Retry token → validated, proceed.
example : component.step sv (.clientInitial ca (.valid .retry true)) =
    .ok (sv.validate ca) [.addressValidated ca, .handshakeProceeds ca] := by decide
-- §8.1.2, line 2836: a second Retry is not an option there …
example : component.accepts sv (.clientInitial ca (.valid .retry true)) (.ok sv [.sendRetry ca])
    = false := by decide
-- … though refusing the connection is.
example : component.accepts sv (.clientInitial ca (.valid .retry true))
    (.error .connectionRefused) = true := by decide

-- §8.1.2, line 2875: an invalid Retry token → INVALID_TOKEN, or discard.
example : component.step sv (.clientInitial ca (.invalid .retry)) = .error .invalidToken := by decide
example : component.accepts sv (.clientInitial ca (.invalid .retry)) .drop = true := by decide
-- §8.1.3, line 2989: an invalid NEW_TOKEN token → treat as unvalidated instead.
example : component.step sv (.clientInitial ca (.invalid .newToken)) = .ok sv [.sendRetry ca] := by
  decide
-- §8.1.4, line 3054: a valid NEW_TOKEN token from a changed address does not
-- validate the address.
example : component.step sv (.clientInitial ca (.valid .newToken false)) =
    .ok sv [.handshakeProceeds ca] := by decide

-- §17.2.5.2, line 6633: the client accepts the Retry and uses token and new DCID.
example : component.step cl (.recvRetry tok cid1 true) =
    .ok { cl with token := some ⟨.retry, tok⟩, retriesAccepted := 1, sawServerPacket := true,
                  dcid := cid1 }
         [.useToken tok, .useDcid cid1] := by decide
-- … and discards a second one (line 6621).
example : component.step ((component.step cl (.recvRetry tok cid1 true)).next cl)
    (.recvRetry tok cid1 true) = .drop := by decide
-- §17.2.5.2, line 6630: zero-length token → discard.
example : component.step cl (.recvRetry ByteArray.empty cid1 true) = .drop := by decide
-- §17.2.5.2, line 6626: bad integrity tag → discard.
example : component.step cl (.recvRetry tok cid1 false) = .drop := by decide
-- §17.2.5.1, line 6598: SCID equal to our Initial's DCID → discard.
example : component.step cl (.recvRetry tok cid0 true) = .drop := by decide
-- §8.1.3: a NEW_TOKEN frame is stored for a future connection.
example : component.step cl (.recvNewToken tok) =
    .ok { cl with newTokens := [tok] } [.storeToken tok] := by decide

-- Following a server we cannot see inside: it answered with a Retry, so it did
-- not validate the address.
example : component.track sv (.clientInitial ca (.invalid .newToken)) (.ok [.sendRetry ca]) =
    some sv := by rfl

/-! ## 10. Coverage and notes

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §8 (2736) | after receiving packets from an unvalidated address an endpoint MUST limit data sent to 3× data received | `MaySendDatagram`, `antiAmplification` |
| §8.1 (2757) | successfully processed Handshake packet ⇒ peer address can be considered validated | `Step.handshakeValidates` / `.handshakeNoValidate` |
| §8.1 (2761) | MAY consider validated if the peer uses a CID we chose with ≥ 64 bits of entropy | `Step.cidValidates` / `.cidNoValidate` |
| §8.1 (2765) | the client validates the server address by processing any packet | `Step.serverInitial` |
| §8.1 (2773) | servers MUST NOT send more than 3× the bytes received prior to validation | `MaySendDatagram`, `antiAmplification` |
| §8.1 (2777) | servers MUST count all payload bytes of datagrams uniquely attributed to the connection, processed or discarded | `Step.recv` (the caller supplies `n`) |
| §8.1 (2783) | clients MUST pad Initial datagrams to ≥ 1200 bytes | out of scope: WP7 VersionAndSize |
| §8.1 (2795) | clients MUST send a packet on a PTO | out of scope: loss recovery (RFC 9002) |
| §8.1.1 (2823) | a token MUST be constructed so the server can identify how it was provided | `TokenSource`, carried on `TokenCheck`; construction itself out of scope |
| §8.1.2 (2830) | the server can request address validation by sending a Retry | `Step.initialAbsentRetry` |
| §8.1.2 (2832) | the token MUST be repeated by the client in all Initials after the Retry | `Effect.useToken`, `State.token`; see NOTES 4 |
| §8.1.2 (2836) | after a Retry token, the server can only refuse or proceed — no second Retry | `Step.initialValidRetry{Proceed,Refuse}`; no `sendRetry` outcome exists |
| §8.1.2 (2873) | the server can discard an Initial with an invalid Retry token | `Step.initialInvalidRetryDiscard` |
| §8.1.2 (2875) | the server SHOULD immediately close with INVALID_TOKEN | `Step.initialInvalidRetryClose` (preferred outcome) |
| §8.1.3 (2899) | a server MAY provide tokens for later connections with NEW_TOKEN | `Step.newTokenStore` |
| §8.1.3 (2917) | the client MUST include the token in all Initials unless a Retry replaces it | `State.token` / `Effect.useToken`; see NOTES 4 |
| §8.1.3 (2918) | the client MUST NOT use a Retry token for future connections | `ClientToken.src`; see NOTES 4 |
| §8.1.3 (2920) | servers MAY discard an Initial that does not carry the expected token | `Step.initialInvalidNewDiscard` |
| §8.1.3 (2924) | a token SHOULD have an expiration time | out of scope: token construction |
| §8.1.3 (2930) | a NEW_TOKEN token MUST NOT be linkable; MUST be unique across clients | out of scope: token construction |
| §8.1.3 (2950) | a client MUST NOT include a token not applicable to the server | out of scope: no server identity in this model (NOTES 5) |
| §8.1.3 (2961) | a Retry token MUST be used immediately and not in later attempts | `ClientToken.src`; see NOTES 4 |
| §8.1.3 (2973) | a client SHOULD NOT reuse a NEW_TOKEN token | `Recommended`, NOTES 5 |
| §8.1.3 (2987) | on an Initial with a token the server MUST attempt validation unless already validated | `Step.initialValidated` (the exception) plus the `chk` cases |
| §8.1.3 (2989) | invalid token ⇒ SHOULD proceed as if unvalidated, possibly with a Retry | `Step.initialInvalidNew{Retry,Proceed}` |
| §8.1.3 (2994) | validation succeeds ⇒ SHOULD allow the handshake to proceed | `Step.initialValid{Retry,New}Proceed` (preferred) |
| §8.1.4 (3031) | a token MUST be difficult to guess; MUST be integrity protected | out of scope: token construction (opaque `TokenCheck`) |
| §8.1.4 (3046) | Retry tokens SHOULD let the server verify the source IP and port | `TokenCheck.valid _ addrUnchanged` |
| §8.1.4 (3050) | NEW_TOKEN tokens MUST let the server verify the client IP | `TokenCheck.valid _ addrUnchanged` |
| §8.1.4 (3054) | if the client IP changed the server MUST adhere to the anti-amplification limit | `Step.initialValid*Moved*` do not validate the address |
| §8.1.4 (3060) | servers MUST prevent or limit token replay | out of scope: server token store, opaque `TokenCheck` |
| §17.2.5.1 (6597) | the Retry SCID MUST NOT equal the client's Initial DCID; a client MUST discard such a Retry | `Step.retrySameCid` |
| §17.2.5.1 (6601) | the client MUST use the Retry SCID as the DCID of subsequent packets | `Step.retryAccept`, `Effect.useDcid` |
| §17.2.5.1 (6616) | a server MUST NOT send more than one Retry per UDP datagram | see NOTES 6 |
| §17.2.5.2 (6621) | a client MUST accept at most one Retry per connection attempt | `Inv`, `atMostOneRetry` |
| §17.2.5.2 (6622) | after an Initial or Retry from the server, discard later Retries | `Step.retryLate`, `retry_discarded_after` |
| §17.2.5.2 (6626) | discard Retries whose Retry Integrity Tag does not validate | `Step.retryBadTag` (tag check is the opaque `integrityOk`) |
| §17.2.5.2 (6630) | a client MUST discard a Retry with a zero-length Retry Token | `Step.retryEmptyToken` |
| §17.2.5.2 (6641) | the client MUST NOT change its Source Connection ID | out of scope: WP4 ConnIds |
| §17.2.5.2 (6646) | a Retry has no packet number and cannot be acknowledged | out of scope: WP3 FrameRules / ACK generation |
| §17.2.5.3 (6651) | subsequent Initials carry the Retry's CID and token | `Effect.useDcid`, `Effect.useToken` |
| §17.2.5.3 (6671) | the client MUST reuse the same cryptographic handshake message | out of scope: WP11 Handshake |
| §17.2.5.3 (6682) | the client MUST NOT reset packet numbers after a Retry | out of scope: WP3 / WP11 |
| §17.2.5.3 (6694) | Retry CIDs are copied to transport parameters and validated | out of scope: WP1 TransportParams, §7.3 |
| §8.2 (3070–3271) | path validation | `Spec/PathValidation.lean` |

NOTES

1. **Who the limit binds.**  §8's opening sentence is written for "an endpoint",
   while §8.1 repeats it for servers.  `MaySendDatagram` is role-independent: it
   is the §8 rule, which §9.3 also applies to either endpoint on an unvalidated
   path.  A client normally validates the server address with the first packet
   it processes (`Step.serverInitial`), so the limit rarely binds it.

2. **"can consider … validated" (line 2757) and the MAY of line 2761** are
   encoded as *two* outcomes each: validating (preferred) and not validating.
   A conforming implementation that is more conservative is therefore accepted.

3. **Address-validating events are not exclusive.**  `Step.pathValidated` is the
   hook for `PathValidation`: §8.2.3 line 3219 says a validated path lifts the
   anti-amplification limit.  Composing the two components (WP12) means firing
   this event on `PathValidation.Effect.pathValidated`.

4. **Token use on the send side is an effect, not a `MaySend` clause.**  The
   token of §8.1.2/§8.1.3 travels in the Token field of the Initial *packet*
   header, not in a frame, and `Component.MaySend` is per `Frame`.  The
   obligations "MUST be repeated in all Initial packets" and "MUST NOT use a
   Retry token for future connections" are therefore recorded in `State.token`
   (with its `ClientToken.src`) and announced with `Effect.useToken`; the
   packet-level check belongs to WP12 Endpoint, which can state it as
   `pkt.token = (s.token.map ClientToken.bytes).getD ByteArray.empty` for Initial
   packets.  Likewise `Effect.useDcid` records §17.2.5.1's DCID obligation, whose
   enforcement is a packet-header property.

5. **Token selection policy is out of scope.**  Which stored NEW_TOKEN token a
   client offers (lines 2944–2985, 3013–3017), and the SHOULD NOT against
   reusing one, are policy over `State.newTokens`; they constrain nothing the
   receiver can observe in one connection, so they appear in `Recommended`-style
   prose here rather than in `Step`.  No server identity is modelled, so
   "applicable to the server" (line 2950) cannot be stated.

6. **One Retry per datagram (line 6616)** is a property of a whole datagram,
   which may coalesce several Initial packets.  This component sees one packet
   per `clientInitial` event and emits at most one `Effect.sendRetry` per event,
   so the datagram-level rule is WP12's to enforce over the effect list of a
   whole datagram.

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

9. **`.drop` vs `.ok s []`.**  Following the Template, `.drop` is used for
   discarding a whole packet (an Initial or a Retry), which is what every
   discard rule in this range is about.  Events that do not apply to the
   endpoint's role also yield `.drop`.

10. **Sends are recorded, not policed, by `Step`.**  `Step.sent` accepts any
    `datagramSent`, because the model must be able to describe an implementation
    that oversends in order to reject it.  The prohibition lives in
    `MaySendDatagram`, and theorem `antiAmplification` carries it as the
    `EventOk` side condition of `ReachableOk`.
-/

end Quic.Spec.AddressValidation
