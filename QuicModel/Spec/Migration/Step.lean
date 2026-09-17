import QuicModel.Spec.Migration.Basic

/-!
  WP10 "Migration", parts 2–5: the specification, its executable form, the
  proof that they agree, and the invariant.
-/
namespace Quic.Spec.Migration

/-! ## 1d. The remaining case analyses

As with `recvCase`, each event's guard chain is one total function, so that
`Step` and `outcomes` name the same branches. -/

namespace State

/-- §9.6.1, line 3707 (client) and §9.6.2, line 3730 (server): the conditions
    under which an endpoint starts using the server's preferred address.  The
    server's extra condition is line 3730's "has received a non-probing packet
    with a new largest packet number on its preferred address"; the switch is
    gated on `handshakeConfirmed` because moving the server's own sending
    address is itself initiating migration (§9, line 3280) — see NOTES 4. -/
def preferredSwitchReady (s : State) (p : Path) : Bool :=
  s.handshakeConfirmed && s.isPreferredPath p && decide (p ≠ s.active) &&
    (match s.role with
     | .client => true
     | .server => (s.infoOf p).sawNonProbing && decide ((s.infoOf p).largestPn = s.largestPn))

/-- §8.2.1: a path validation is started on `p`.  §9, line 3287: a client that
    starts validating the preferred address has "acted on a preferred_address
    transport parameter". -/
def startProbe (s : State) (p : Path) : State :=
  { (s.markValidating p) with preferredActedOn := s.preferredActedOn || s.isPreferredPath p }

/-- §8.2.3: `p` is now validated; if it is the path we are already sending on it
    becomes the last validated peer address of §9.3.2, line 3452. -/
def succStay (s : State) (p : Path) : State :=
  { (s.markValidated p) with lastValidated := if p = s.active then some p else s.lastValidated }

def succSwitch (s : State) (p : Path) : State := (s.succStay p).switchTo p

def succSwitchFx (s : State) (p : Path) : List Effect :=
  Effect.switchPath p :: (if s.otherValidating p then [Effect.abandonValidation s.active] else [])

/-- §9.5, line 3600: start transmitting on `p` with the connection ID whose
    sequence number is `n`. -/
def useCid (s : State) (p : Path) (n : Nat) : State :=
  { s with dcidOn := s.dcidOn.set p n, tx := ⟨p, n⟩ }

end State

inductive SuccCase where
  | gone | stay | mustSwitch | maySwitch
  deriving DecidableEq, Repr

def succCase (s : State) (p : Path) : SuccCase :=
  if s.discarded then .gone
  else if !s.preferredSwitchReady p then .stay
  else if decide (s.role = .client) && s.otherValidating p then .mustSwitch
  else .maySwitch

inductive FailCase where
  | gone | revert | noPath | otherPath | otherPathNoneLeft
  deriving DecidableEq, Repr

def failCase (s : State) (p : Path) : FailCase :=
  if s.discarded then .gone
  else if decide (p = s.active) && !s.isValidated p then
    (match s.lastValidated with
     | some q => if decide (q = p) then .noPath else .revert
     | none => .noPath)
  else if (s.markFailed p).hasValidatedPath then .otherPath
  else .otherPathNoneLeft

inductive MigCase where
  | gone | tooEarly | banned | validateFirst | already | fresh
  deriving DecidableEq, Repr

def migCase (s : State) (p : Path) : MigCase :=
  if s.discarded then .gone
  else if !s.handshakeConfirmed then .tooEarly
  else if s.sendBanned p then .banned
  else if s.isPreferredPath p && !s.isValidated p then .validateFirst
  else if s.isValidated p then .already
  else .fresh

inductive ProbeCase where
  | gone | banned | probe
  deriving DecidableEq, Repr

def probeCase (s : State) (p : Path) : ProbeCase :=
  if s.discarded then .gone
  else if s.sendBanned p then .banned
  else .probe

inductive CidCase where
  | gone | zeroLen | localReuse | rebind | peerReuse | fresh
  deriving DecidableEq, Repr

def cidCase (s : State) (p : Path) (n : Nat) : CidCase :=
  if s.discarded then .gone
  else if s.peerZeroLen then .zeroLen
  else if s.reusedAcrossLocal p n then .localReuse
  else if s.reusedAcrossPeer p n then (if s.rebindKeepsCid p n then .rebind else .peerReuse)
  else .fresh

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §9.3.2, line 3461: "MUST close the connection silently by discarding all
      connection state.  This results in new packets on the connection being
      handled generically." -/
  | recvGone {s p pn pr d} (hc : recvCase s p pn pr = .gone) :
      Step s (.recvPacket p pn pr d) .drop
  /-- §9, line 3325: "If a client receives packets from an unknown server
      address, the client MUST discard these packets." -/
  | recvUnknownServer {s p pn pr d} (hc : recvCase s p pn pr = .unknownServer) :
      Step s (.recvPacket p pn pr d) .drop
  /-- §9.6, line 3680: "If a client receives packets from a new server address
      when the client has not initiated a migration to that address, the client
      SHOULD discard these packets."  The recommended outcome. -/
  | recvUnsolicitedDrop {s p pn pr d} (hc : recvCase s p pn pr = .unsolicited) :
      Step s (.recvPacket p pn pr d) .drop
  /-- Same sentence: a SHOULD, so processing the packet is still conforming. -/
  | recvUnsolicitedKeep {s p pn pr d} (hc : recvCase s p pn pr = .unsolicited) :
      Step s (.recvPacket p pn pr d) (.ok (s.observe p pn pr d) (s.observeFx p))
  /-- §9.1, line 3340 ("A packet containing only probing frames is a 'probing
      packet'"), §9.3, line 3387 ("only … in response to the highest-numbered
      non-probing packet"), and §9, line 3312 ("MUST perform path validation …
      if it detects any change to a peer's address, unless it has previously
      validated that address"): the packet is taken in, the sending path does
      not move. -/
  | recvQuiet {s p pn pr d} (hc : recvCase s p pn pr = .quiet) :
      Step s (.recvPacket p pn pr d) (.ok (s.observe p pn pr d) (s.observeFx p))
  /-- §9, line 3289: "the endpoint MUST either drop the incoming packets on that
      path without generating a stateless reset or proceed with path validation
      and allow the peer to migrate."  First alternative. -/
  | recvBannedDrop {s p pn pr d} (hc : recvCase s p pn pr = .banned) :
      Step s (.recvPacket p pn pr d) .drop
  /-- Same sentence, second alternative. -/
  | recvBannedMigrate {s p pn pr d} (hc : recvCase s p pn pr = .banned) :
      Step s (.recvPacket p pn pr d) (.ok (s.permit p pn pr d) (s.permitFx p))
  /-- §9.3, line 3382: "If the recipient permits the migration, it MUST send
      subsequent packets to the new peer address and MUST initiate path
      validation (Section 8.2) … if validation is not already underway", and
      §9.3.3, line 3498: "In response to an apparent migration, endpoints MUST
      validate the previously active path using a PATH_CHALLENGE frame." -/
  | recvMigrate {s p pn pr d} (hc : recvCase s p pn pr = .migrate) :
      Step s (.recvPacket p pn pr d) (.ok (s.permit p pn pr d) (s.permitFx p))
  /-- Same sentence: "if the recipient permits" — it need not.  §9, line 3312's
      path validation is still required. -/
  | recvRefuse {s p pn pr d} (hc : recvCase s p pn pr = .migrate) :
      Step s (.recvPacket p pn pr d) (.ok (s.observe p pn pr d) (s.observeFx p))
  /-- Nothing reaches a connection whose state has been discarded. -/
  | succGone {s p} (hc : succCase s p = .gone) : Step s (.validationSucceeded p) .drop
  /-- §8.2.3: the path is validated; §9.3.2, line 3452's "last validated peer
      address" is updated when it is the path in use. -/
  | succStay {s p} (hc : succCase s p = .stay) :
      Step s (.validationSucceeded p) (.ok (s.succStay p) [])
  /-- §9.6.3, line 3757: "If path validation of the server's preferred address
      succeeds, the client MUST abandon validation of the original address and
      migrate to using the server's preferred address." -/
  | succMustSwitch {s p} (hc : succCase s p = .mustSwitch) :
      Step s (.validationSucceeded p) (.ok (s.succSwitch p) (s.succSwitchFx p))
  /-- §9.6.1, line 3707: "As soon as path validation succeeds, the client SHOULD
      begin sending all future packets to the new server address using the new
      connection ID and discontinue use of the old server address"; §9.6.2, line
      3730 for the server.  The recommended outcome. -/
  | succSwitch {s p} (hc : succCase s p = .maySwitch) :
      Step s (.validationSucceeded p) (.ok (s.succSwitch p) (s.succSwitchFx p))
  /-- Same sentences: a SHOULD, so staying is conforming. -/
  | succKeep {s p} (hc : succCase s p = .maySwitch) :
      Step s (.validationSucceeded p) (.ok (s.succStay p) [])
  | failGone {s p} (hc : failCase s p = .gone) : Step s (.validationFailed p) .drop
  /-- §9.3.2, line 3452: "an endpoint MUST revert to using the last validated
      peer address when validation of a new peer address fails." -/
  | failRevert {s p} (hc : failCase s p = .revert) :
      Step s (.validationFailed p)
        (.ok ((s.markFailed p).revertTo (s.lastValidated.getD s.active))
             [.switchPath (s.lastValidated.getD s.active)])
  /-- §9.3.2, line 3460: "If an endpoint has no state about the last validated
      peer address, it MUST close the connection silently by discarding all
      connection state." -/
  | failNoPath {s p} (hc : failCase s p = .noPath) :
      Step s (.validationFailed p)
        (.ok { (s.markFailed p) with discarded := true } [.discardState])
  /-- §9.1, line 3333: "Failure of path validation simply means that the new
      path is not usable for this connection.  Failure to validate a path does
      not cause the connection to end unless there are no valid alternative
      paths available." -/
  | failOther {s p} (hc : failCase s p = .otherPath) :
      Step s (.validationFailed p) (.ok (s.markFailed p) [])
  /-- Same sentence, when no alternative is left — the connection may still
      continue (§9, line 3318: "An endpoint capable of connection migration MAY
      wait for a new path to become available before discarding connection
      state"). -/
  | failOtherWait {s p} (hc : failCase s p = .otherPathNoneLeft) :
      Step s (.validationFailed p) (.ok (s.markFailed p) [])
  /-- §9, line 3316: "When an endpoint has no validated path on which to send
      packets, it MAY discard connection state." -/
  | failOtherGiveUp {s p} (hc : failCase s p = .otherPathNoneLeft) :
      Step s (.validationFailed p)
        (.ok { (s.markFailed p) with discarded := true } [.discardState])
  | migGone {s p} (hc : migCase s p = .gone) : Step s (.requestMigrate p) .drop
  /-- §9, line 3280: "An endpoint MUST NOT initiate connection migration before
      the handshake is confirmed, as defined in section 4.1.2 of [QUIC-TLS]." -/
  | migTooEarly {s p} (hc : migCase s p = .tooEarly) : Step s (.requestMigrate p) .drop
  /-- §9, line 3284: "an endpoint also MUST NOT send packets (including probing
      packets; see Section 9.1) from a different local address to the address
      the peer used during the handshake, unless the endpoint has acted on a
      preferred_address transport parameter from the peer." -/
  | migBanned {s p} (hc : migCase s p = .banned) : Step s (.requestMigrate p) .drop
  /-- §9.6.2, line 3715: "A client that migrates to a preferred address MUST
      validate the address it chooses before migrating." -/
  | migValidateFirst {s p} (hc : migCase s p = .validateFirst) :
      Step s (.requestMigrate p) (.ok (s.startProbe p) [.startValidation p])
  /-- §9.3, line 3394: "An endpoint MAY skip validation of a peer address if
      that address has been seen recently"; §9, line 3313: "unless it has
      previously validated that address." -/
  | migAlready {s p} (hc : migCase s p = .already) :
      Step s (.requestMigrate p) (.ok (s.switchTo p) [.switchPath p])
  /-- §9.2, lines 3345 and 3365: "An endpoint can migrate a connection to a new
      local address by sending packets containing non-probing frames from that
      address … To establish reachability on the new path, an endpoint initiates
      path validation (Section 8.2) on the new path." -/
  | migFresh {s p} (hc : migCase s p = .fresh) :
      Step s (.requestMigrate p) (.ok ((s.startProbe p).switchTo p)
        [.startValidation p, .switchPath p])
  /-- §9.2, line 3366: "An endpoint MAY defer path validation until after a peer
      sends the next non-probing frame to its new address." -/
  | migDefer {s p} (hc : migCase s p = .fresh) :
      Step s (.requestMigrate p) (.ok (s.switchTo p) [.switchPath p])
  | probeGone {s p} (hc : probeCase s p = .gone) : Step s (.requestProbe p) .drop
  /-- §9, line 3285: the ban of line 3284 covers probing packets too. -/
  | probeBanned {s p} (hc : probeCase s p = .banned) : Step s (.requestProbe p) .drop
  /-- §9.1, line 3331: "An endpoint MAY probe for peer reachability from a new
      local address using path validation (Section 8.2) prior to migrating the
      connection to the new local address." -/
  | probeStart {s p} (hc : probeCase s p = .probe) :
      Step s (.requestProbe p) (.ok (s.startProbe p) [.startValidation p])
  /-- §9, line 3281: the handshake is confirmed. -/
  | confirmed {s} : Step s .handshakeConfirmed (.ok { s with handshakeConfirmed := true } [])
  /-- §18.2, line 7066: "This transport parameter is only sent by a server." -/
  | preferredWrongRole {s a} (h : s.role = .server) : Step s (.learnPreferredAddress a) .drop
  /-- §9.6.1, line 3686: "A server conveys a preferred address by including the
      preferred_address transport parameter in the TLS handshake." -/
  | preferredLearn {s a} (h : s.role ≠ .server) :
      Step s (.learnPreferredAddress a) (.ok { s with preferredPeer := some a } [])
  | cidGone {s p n} (hc : cidCase s p n = .gone) : Step s (.beginSendOn p n) .drop
  /-- §9.5, line 3630: with zero-length connection IDs there is no sequence
      number to keep apart, so lines 3603 and 3608 have no content; the text's
      answer is the SHOULD NOT of line 3630, which is `Recommended`. -/
  | cidZeroLen {s p n} (hc : cidCase s p n = .zeroLen) :
      Step s (.beginSendOn p n) (.ok { s with tx := ⟨p, n⟩ } [])
  /-- §9.5, line 3603: "An endpoint MUST NOT reuse a connection ID when sending
      from more than one local address". -/
  | cidLocalReuse {s p n} (hc : cidCase s p n = .localReuse) : Step s (.beginSendOn p n) .drop
  /-- §9.5, line 3608: "Similarly, an endpoint MUST NOT reuse a connection ID
      when sending to more than one destination address." -/
  | cidPeerReuse {s p n} (hc : cidCase s p n = .peerReuse) : Step s (.beginSendOn p n) .drop
  /-- §9.5, line 3611: "… in which case it MAY continue to use the current
      connection ID with the new remote address while still sending from the
      same local address." -/
  | cidRebindKeep {s p n} (hc : cidCase s p n = .rebind) :
      Step s (.beginSendOn p n) (.ok (s.useCid p n) [])
  /-- Same sentence: a MAY, so switching to a fresh connection ID instead (and
      therefore not transmitting with this one) is equally conforming. -/
  | cidRebindRefuse {s p n} (hc : cidCase s p n = .rebind) : Step s (.beginSendOn p n) .drop
  /-- §9.5, line 3600: "At any time, endpoints MAY change the Destination
      Connection ID they transmit with to a value that has not been used on
      another path." -/
  | cidFresh {s p n} (hc : cidCase s p n = .fresh) :
      Step s (.beginSendOn p n) (.ok (s.useCid p n) [])

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvPacket p pn pr d =>
    match recvCase s p pn pr with
    | .gone => [.drop]
    | .unknownServer => [.drop]
    | .unsolicited => [.drop, .ok (s.observe p pn pr d) (s.observeFx p)]
    | .quiet => [.ok (s.observe p pn pr d) (s.observeFx p)]
    | .banned => [.drop, .ok (s.permit p pn pr d) (s.permitFx p)]
    | .migrate => [.ok (s.permit p pn pr d) (s.permitFx p),
                   .ok (s.observe p pn pr d) (s.observeFx p)]
  | .validationSucceeded p =>
    match succCase s p with
    | .gone => [.drop]
    | .stay => [.ok (s.succStay p) []]
    | .mustSwitch => [.ok (s.succSwitch p) (s.succSwitchFx p)]
    | .maySwitch => [.ok (s.succSwitch p) (s.succSwitchFx p), .ok (s.succStay p) []]
  | .validationFailed p =>
    match failCase s p with
    | .gone => [.drop]
    | .revert => [.ok ((s.markFailed p).revertTo (s.lastValidated.getD s.active))
                    [.switchPath (s.lastValidated.getD s.active)]]
    | .noPath => [.ok { (s.markFailed p) with discarded := true } [.discardState]]
    | .otherPath => [.ok (s.markFailed p) []]
    | .otherPathNoneLeft => [.ok (s.markFailed p) [],
                             .ok { (s.markFailed p) with discarded := true } [.discardState]]
  | .requestMigrate p =>
    match migCase s p with
    | .gone => [.drop]
    | .tooEarly => [.drop]
    | .banned => [.drop]
    | .validateFirst => [.ok (s.startProbe p) [.startValidation p]]
    | .already => [.ok (s.switchTo p) [.switchPath p]]
    | .fresh => [.ok ((s.startProbe p).switchTo p) [.startValidation p, .switchPath p],
                 .ok (s.switchTo p) [.switchPath p]]
  | .requestProbe p =>
    match probeCase s p with
    | .gone => [.drop]
    | .banned => [.drop]
    | .probe => [.ok (s.startProbe p) [.startValidation p]]
  | .handshakeConfirmed => [.ok { s with handshakeConfirmed := true } []]
  | .learnPreferredAddress a =>
    if s.role = .server then [.drop] else [.ok { s with preferredPeer := some a } []]
  | .beginSendOn p n =>
    match cidCase s p n with
    | .gone => [.drop]
    | .zeroLen => [.ok { s with tx := ⟨p, n⟩ } []]
    | .localReuse => [.drop]
    | .peerReuse => [.drop]
    | .rebind => [.ok (s.useCid p n) [], .drop]
    | .fresh => [.ok (s.useCid p n) []]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvPacket p pn pr d =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .recvGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .recvUnknownServer hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .recvUnsolicitedDrop hc
        · exact .recvUnsolicitedKeep hc
      · simp only [List.mem_singleton] at h; subst h; exact .recvQuiet hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .recvBannedDrop hc
        · exact .recvBannedMigrate hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .recvMigrate hc
        · exact .recvRefuse hc
    | validationSucceeded p =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .succGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .succStay hc
      · simp only [List.mem_singleton] at h; subst h; exact .succMustSwitch hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .succSwitch hc
        · exact .succKeep hc
    | validationFailed p =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .failGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .failRevert hc
      · simp only [List.mem_singleton] at h; subst h; exact .failNoPath hc
      · simp only [List.mem_singleton] at h; subst h; exact .failOther hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .failOtherWait hc
        · exact .failOtherGiveUp hc
    | requestMigrate p =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .migGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .migTooEarly hc
      · simp only [List.mem_singleton] at h; subst h; exact .migBanned hc
      · simp only [List.mem_singleton] at h; subst h; exact .migValidateFirst hc
      · simp only [List.mem_singleton] at h; subst h; exact .migAlready hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .migFresh hc
        · exact .migDefer hc
    | requestProbe p =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .probeGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .probeBanned hc
      · simp only [List.mem_singleton] at h; subst h; exact .probeStart hc
    | handshakeConfirmed =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .confirmed
    | learnPreferredAddress a =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .preferredWrongRole hc
      · simp only [List.mem_singleton] at h; subst h; exact .preferredLearn hc
    | beginSendOn p n =>
      simp only [outcomes] at h
      split at h <;> rename_i hc
      · simp only [List.mem_singleton] at h; subst h; exact .cidGone hc
      · simp only [List.mem_singleton] at h; subst h; exact .cidZeroLen hc
      · simp only [List.mem_singleton] at h; subst h; exact .cidLocalReuse hc
      · simp only [List.mem_singleton] at h; subst h; exact .cidPeerReuse hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact .cidRebindKeep hc
        · exact .cidRebindRefuse hc
      · simp only [List.mem_singleton] at h; subst h; exact .cidFresh hc
  · intro h
    cases h with
    | recvGone hc => simp [outcomes, hc]
    | recvUnknownServer hc => simp [outcomes, hc]
    | recvUnsolicitedDrop hc => simp [outcomes, hc]
    | recvUnsolicitedKeep hc => simp [outcomes, hc]
    | recvQuiet hc => simp [outcomes, hc]
    | recvBannedDrop hc => simp [outcomes, hc]
    | recvBannedMigrate hc => simp [outcomes, hc]
    | recvMigrate hc => simp [outcomes, hc]
    | recvRefuse hc => simp [outcomes, hc]
    | succGone hc => simp [outcomes, hc]
    | succStay hc => simp [outcomes, hc]
    | succMustSwitch hc => simp [outcomes, hc]
    | succSwitch hc => simp [outcomes, hc]
    | succKeep hc => simp [outcomes, hc]
    | failGone hc => simp [outcomes, hc]
    | failRevert hc => simp [outcomes, hc]
    | failNoPath hc => simp [outcomes, hc]
    | failOther hc => simp [outcomes, hc]
    | failOtherWait hc => simp [outcomes, hc]
    | failOtherGiveUp hc => simp [outcomes, hc]
    | migGone hc => simp [outcomes, hc]
    | migTooEarly hc => simp [outcomes, hc]
    | migBanned hc => simp [outcomes, hc]
    | migValidateFirst hc => simp [outcomes, hc]
    | migAlready hc => simp [outcomes, hc]
    | migFresh hc => simp [outcomes, hc]
    | migDefer hc => simp [outcomes, hc]
    | probeGone hc => simp [outcomes, hc]
    | probeBanned hc => simp [outcomes, hc]
    | probeStart hc => simp [outcomes, hc]
    | confirmed => simp [outcomes]
    | preferredWrongRole h => simp [outcomes, h]
    | preferredLearn h => simp [outcomes, h]
    | cidGone hc => simp [outcomes, hc]
    | cidZeroLen hc => simp [outcomes, hc]
    | cidLocalReuse hc => simp [outcomes, hc]
    | cidPeerReuse hc => simp [outcomes, hc]
    | cidRebindKeep hc => simp [outcomes, hc]
    | cidRebindRefuse hc => simp [outcomes, hc]
    | cidFresh hc => simp [outcomes, hc]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant

Two facts a reachable state never loses:

* the "last validated peer address" of §9.3.2, line 3452 really is validated,
  which is what makes reverting to it meaningful (theorem `revert_is_validated`);
* §9.5, line 3603: a connection ID in use as a Destination Connection ID is in
  use from one local address only.  Line 3608's companion rule is *not* part of
  the invariant: the MAY of line 3611 breaks it, see `cid_reuse_counterexample`. -/

def InvLastValidated (s : State) : Prop :=
  ∀ q, s.lastValidated = some q → s.statusOf q = .validated

def InvOneLocalAddrPerCid (s : State) : Prop :=
  ∀ e₁ ∈ s.dcidOn, ∀ e₂ ∈ s.dcidOn, e₁.2 = e₂.2 → e₁.1.loc = e₂.1.loc

def Inv (s : State) : Prop := InvLastValidated s ∧ InvOneLocalAddrPerCid s


/-! ### Projection lemmas

Every state update in this component either leaves `paths` alone or rewrites one
entry without touching its `status`, and only `beginSendOn` touches `dcidOn`. -/

namespace State

theorem statusOf_of_set (s t : State) (p q : Path) (f : PathInfo → PathInfo)
    (hp : t.paths = s.paths.set p (f (s.infoOf p)))
    (hf : (f (s.infoOf p)).status = (s.infoOf p).status) :
    t.statusOf q = s.statusOf q := by
  show ((t.paths.get? q).getD {}).status = ((s.paths.get? q).getD {}).status
  rw [hp]
  by_cases h : q = p
  · subst h; rw [Map.get?_set_self]; exact hf
  · rw [Map.get?_set_of_ne _ _ h]

theorem statusOf_setInfo_ne (s : State) (p q : Path) (f : PathInfo → PathInfo) (h : q ≠ p) :
    (s.setInfo p f).statusOf q = s.statusOf q := by
  show (((s.paths.set p (f (s.infoOf p))).get? q).getD {}).status = _
  rw [Map.get?_set_of_ne _ _ h]
  rfl

theorem statusOf_setInfo_self (s : State) (p : Path) (f : PathInfo → PathInfo) :
    (s.setInfo p f).statusOf p = (f (s.infoOf p)).status := by
  show (((s.paths.set p (f (s.infoOf p))).get? p).getD {}).status = _
  rw [Map.get?_set_self]
  rfl

theorem statusOf_setInfo (s : State) (p q : Path) (f : PathInfo → PathInfo)
    (hf : (f (s.infoOf p)).status = (s.infoOf p).status) :
    (s.setInfo p f).statusOf q = s.statusOf q := by
  by_cases h : q = p
  · subst h; rw [statusOf_setInfo_self]; exact hf
  · exact statusOf_setInfo_ne s p q f h

@[simp] theorem statusOf_markValidating (s : State) (p q : Path) :
    (s.markValidating p).statusOf q = s.statusOf q :=
  statusOf_setInfo s p q (fun i => { i with validating := true }) rfl

@[simp] theorem statusOf_recordRecv (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).statusOf q = s.statusOf q :=
  statusOf_of_set s _ p q
    (fun i => { i with largestPn := Nat.max i.largestPn pn,
                       sawNonProbing := i.sawNonProbing || !pr }) rfl rfl

@[simp] theorem statusOf_markValidated_self (s : State) (p : Path) :
    (s.markValidated p).statusOf p = .validated := by
  rw [markValidated, statusOf_setInfo_self]

theorem statusOf_markValidated_ne (s : State) {p q : Path} (h : q ≠ p) :
    (s.markValidated p).statusOf q = s.statusOf q :=
  statusOf_setInfo_ne s p q _ h

theorem statusOf_markFailed_of_validated (s : State) (p : Path) {q : Path}
    (hq : s.statusOf q = .validated) : (s.markFailed p).statusOf q = .validated := by
  unfold markFailed
  split
  · rw [statusOf_setInfo s p q (fun i => { i with validating := false }) rfl]; exact hq
  · rename_i hv
    by_cases h : q = p
    · subst h
      have : s.isValidated q = true := by simp [isValidated, hq]
      exact absurd this hv
    · rw [statusOf_setInfo_ne s p q _ h]; exact hq

@[simp] theorem statusOf_switchTo (s : State) (p q : Path) :
    (s.switchTo p).statusOf q = s.statusOf q := rfl

@[simp] theorem statusOf_revertTo (s : State) (p q : Path) :
    (s.revertTo p).statusOf q = s.statusOf q := rfl

@[simp] theorem statusOf_startProbe (s : State) (p q : Path) :
    (s.startProbe p).statusOf q = s.statusOf q :=
  statusOf_of_set s _ p q (fun i => { i with validating := true }) rfl rfl

@[simp] theorem statusOf_observe (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).statusOf q = s.statusOf q := by
  unfold observe; split <;> simp

@[simp] theorem statusOf_permit (s : State) (p q : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).statusOf q = s.statusOf q := by
  unfold permit; split <;> simp

theorem statusOf_succStay_ne (s : State) {p q : Path} (h : q ≠ p) :
    (s.succStay p).statusOf q = s.statusOf q := statusOf_markValidated_ne (s := s) h

theorem statusOf_succStay_self (s : State) (p : Path) :
    (s.succStay p).statusOf p = .validated := statusOf_markValidated_self s p

@[simp] theorem lastValidated_markValidating (s : State) (p : Path) :
    (s.markValidating p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_markValidated (s : State) (p : Path) :
    (s.markValidated p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_markFailed (s : State) (p : Path) :
    (s.markFailed p).lastValidated = s.lastValidated := by unfold markFailed; split <;> rfl

@[simp] theorem lastValidated_startProbe (s : State) (p : Path) :
    (s.startProbe p).lastValidated = s.lastValidated := rfl

@[simp] theorem lastValidated_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).lastValidated = s.lastValidated := by unfold observe; split <;> rfl

@[simp] theorem lastValidated_revertTo (s : State) (p : Path) :
    (s.revertTo p).lastValidated = s.lastValidated := rfl

@[simp] theorem dcidOn_setInfo (s : State) (p : Path) (f : PathInfo → PathInfo) :
    (s.setInfo p f).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markValidating (s : State) (p : Path) :
    (s.markValidating p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markValidated (s : State) (p : Path) :
    (s.markValidated p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_markFailed (s : State) (p : Path) :
    (s.markFailed p).dcidOn = s.dcidOn := by unfold markFailed; split <;> rfl

@[simp] theorem dcidOn_recordRecv (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.recordRecv p pn pr d).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_switchTo (s : State) (p : Path) : (s.switchTo p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_revertTo (s : State) (p : Path) : (s.revertTo p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_observe (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.observe p pn pr d).dcidOn = s.dcidOn := by unfold observe; split <;> rfl

@[simp] theorem dcidOn_permit (s : State) (p : Path) (pn : Nat) (pr : Bool) (d : Nat) :
    (s.permit p pn pr d).dcidOn = s.dcidOn := by unfold permit; split <;> rfl

@[simp] theorem dcidOn_startProbe (s : State) (p : Path) : (s.startProbe p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_succStay (s : State) (p : Path) : (s.succStay p).dcidOn = s.dcidOn := rfl

@[simp] theorem dcidOn_succSwitch (s : State) (p : Path) :
    (s.succSwitch p).dcidOn = s.dcidOn := rfl

end State

/-! ### Preservation -/

theorem invOneLocal_congr {s t : State} (hi : InvOneLocalAddrPerCid s) (h : t.dcidOn = s.dcidOn) :
    InvOneLocalAddrPerCid t := by
  intro e₁ h₁ e₂ h₂ h12
  rw [h] at h₁ h₂
  exact hi e₁ h₁ e₂ h₂ h12

theorem invLast_congr {s t : State} (hi : InvLastValidated s)
    (hl : t.lastValidated = s.lastValidated) (hs : ∀ q, t.statusOf q = s.statusOf q) :
    InvLastValidated t := by
  intro q hq
  rw [hs q]
  exact hi q (hl ▸ hq)

/-- Switching the sending path keeps the invariant: the path we leave is
    recorded as "last validated" only when it is in fact validated. -/
theorem invLast_switchTo (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.switchTo p) := by
  intro q hq
  rw [State.statusOf_switchTo]
  simp only [State.switchTo] at hq
  split at hq
  · rename_i hv
    rcases Option.some.inj hq with rfl
    simpa [State.isValidated] using hv
  · exact ht q hq

theorem invLast_revertTo (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.revertTo p) := fun q hq => ht q hq

theorem invLast_discard (t : State) (ht : InvLastValidated t) :
    InvLastValidated { t with discarded := true } := fun q hq => ht q hq

theorem invLast_markFailed (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.markFailed p) := by
  intro q hq
  exact State.statusOf_markFailed_of_validated _ _ (ht q (by simpa using hq))

theorem invLast_succStay (t : State) (p : Path) (ht : InvLastValidated t) :
    InvLastValidated (t.succStay p) := by
  intro q hq
  simp only [State.succStay] at hq
  by_cases hqp : q = p
  · subst hqp; exact State.statusOf_succStay_self t q
  · rw [State.statusOf_succStay_ne _ hqp]
    split at hq
    · exact absurd (Option.some.inj hq).symm hqp
    · exact ht q hq

/-- `Map.set` never invents an entry: what comes out was already there, or is
    the one just written. -/
theorem mem_set_weak {κ ν : Type} [DecidableEq κ] (m : Map κ ν) (k : κ) (v : ν) (e : κ × ν)
    (h : e ∈ m.set k v) : e = (k, v) ∨ e ∈ m := by
  induction m with
  | nil => simp only [Map.set, List.mem_singleton] at h; exact Or.inl h
  | cons x xs ih =>
    rw [Map.set] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- §9.5, line 3603 is exactly what keeps `InvOneLocalAddrPerCid` true. -/
theorem invOneLocal_useCid {s : State} {p : Path} {n : Nat}
    (hi : InvOneLocalAddrPerCid s) (hr : s.reusedAcrossLocal p n = false) :
    InvOneLocalAddrPerCid (s.useCid p n) := by
  have key : ∀ e ∈ s.dcidOn, e.2 = n → e.1.loc = p.loc := by
    intro e he h2
    cases hl : decide (e.1.loc = p.loc) with
    | true => exact of_decide_eq_true hl
    | false =>
      have hne : e.1.loc ≠ p.loc := of_decide_eq_false hl
      have hcon : s.reusedAcrossLocal p n = true := by
        simp only [State.reusedAcrossLocal, List.any_eq_true]
        exact ⟨e, he, by simp [h2, hne]⟩
      rw [hr] at hcon
      exact Bool.noConfusion hcon
  intro e₁ h₁ e₂ h₂ h12
  simp only [State.useCid] at h₁ h₂
  rcases mem_set_weak _ _ _ _ h₁ with rfl | h₁ <;> rcases mem_set_weak _ _ _ _ h₂ with rfl | h₂
  · rfl
  · exact (key e₂ h₂ (by simpa using h12.symm)).symm
  · exact key e₁ h₁ (by simpa using h12)
  · exact hi e₁ h₁ e₂ h₂ h12

theorem reusedAcrossLocal_false_of_cidCase {s : State} {p : Path} {n : Nat}
    (h : cidCase s p n = .rebind ∨ cidCase s p n = .fresh) :
    s.reusedAcrossLocal p n = false := by
  unfold cidCase at h
  split at h
  · rcases h with h | h <;> simp at h
  · split at h
    · rcases h with h | h <;> simp at h
    · split at h
      · rcases h with h | h <;> simp at h
      · rename_i hx
        cases hb : s.reusedAcrossLocal p n
        · rfl
        · exact absurd hb hx

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hA, hB⟩ := hi
  cases h with
  | recvUnsolicitedKeep hc | recvQuiet hc | recvRefuse hc =>
    exact ⟨invLast_congr hA (by simp) (by simp), invOneLocal_congr hB (by simp)⟩
  | recvBannedMigrate hc | recvMigrate hc =>
    refine ⟨?_, invOneLocal_congr hB (by simp)⟩
    unfold State.permit
    refine invLast_switchTo _ _ (invLast_congr hA ?_ ?_)
    · split <;> rfl
    · intro q; split <;> simp
  | succStay hc | succKeep hc => exact ⟨invLast_succStay _ _ hA, invOneLocal_congr hB (by simp)⟩
  | succMustSwitch hc | succSwitch hc =>
    exact ⟨invLast_switchTo _ _ (invLast_succStay _ _ hA), invOneLocal_congr hB (by simp)⟩
  | failRevert hc =>
    exact ⟨invLast_revertTo _ _ (invLast_markFailed _ _ hA), invOneLocal_congr hB (by simp)⟩
  | failNoPath hc | failOtherGiveUp hc =>
    exact ⟨invLast_discard _ (invLast_markFailed _ _ hA), invOneLocal_congr hB (by simp)⟩
  | failOther hc | failOtherWait hc =>
    exact ⟨invLast_markFailed _ _ hA, invOneLocal_congr hB (by simp)⟩
  | migValidateFirst hc | probeStart hc =>
    exact ⟨invLast_congr hA (by simp) (by simp), invOneLocal_congr hB (by simp)⟩
  | migAlready hc | migDefer hc =>
    exact ⟨invLast_switchTo _ _ hA, invOneLocal_congr hB (by simp)⟩
  | migFresh hc =>
    exact ⟨invLast_switchTo _ _ (invLast_congr hA (by simp) (by simp)),
           invOneLocal_congr hB (by simp)⟩
  | confirmed => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl⟩
  | preferredLearn h => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl⟩
  | cidZeroLen hc => exact ⟨invLast_congr hA rfl (fun _ => rfl), invOneLocal_congr hB rfl⟩
  | cidRebindKeep hc =>
    exact ⟨invLast_congr hA rfl (fun _ => rfl),
           invOneLocal_useCid hB (reusedAcrossLocal_false_of_cidCase (Or.inl hc))⟩
  | cidFresh hc =>
    exact ⟨invLast_congr hA rfl (fun _ => rfl),
           invOneLocal_useCid hB (reusedAcrossLocal_false_of_cidCase (Or.inr hc))⟩

end Quic.Spec.Migration
