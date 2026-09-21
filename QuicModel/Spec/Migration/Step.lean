import QuicModel.Spec.Migration.Basic

/-!
  WP10 "Migration", parts 2–4: the specification, its executable form, and the
  proof that they agree.
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
    sequence number is `n`.  `dcidOn` says what is in use now and is
    overwritten; `recordCidUse` adds to the history lines 3603 and 3608 are
    about, which is never overwritten. -/
def useCid (s : State) (p : Path) (n : Nat) : State :=
  { (s.recordCidUse p n) with dcidOn := s.dcidOn.set p n }

end State

inductive SuccCase where
  | gone | stay | mustSwitch | maySwitch
  deriving DecidableEq, Repr

@[noinline]
def succCase (s : State) (p : Path) : SuccCase :=
  if s.discarded then .gone
  else if !s.preferredSwitchReady p then .stay
  else if decide (s.role = .client) && s.otherValidating p then .mustSwitch
  else .maySwitch

inductive FailCase where
  | gone | revert | noPath | otherPath | otherPathNoneLeft
  deriving DecidableEq, Repr

@[noinline]
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

@[noinline]
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

@[noinline]
def probeCase (s : State) (p : Path) : ProbeCase :=
  if s.discarded then .gone
  else if s.sendBanned p then .banned
  else .probe

inductive CidCase where
  | gone | zeroLen | localReuse | rebind | peerReuse | fresh
  deriving DecidableEq, Repr

@[noinline]
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
  /-- §9.6, line 3679: "If a client receives packets from a new server address
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
      continue (§9, line 3317: "An endpoint capable of connection migration MAY
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
      that address has been seen recently"; §9, line 3314: "unless it has
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
  /-- §18.2, line 7067: "This transport parameter is only sent by a server." -/
  | preferredWrongRole {s a} (h : s.role = .server) : Step s (.learnPreferredAddress a) .drop
  /-- §9.6.1, line 3686: "A server conveys a preferred address by including the
      preferred_address transport parameter in the TLS handshake." -/
  | preferredLearn {s a} (h : s.role ≠ .server) :
      Step s (.learnPreferredAddress a) (.ok { s with preferredPeer := some a } [])
  | cidGone {s p n} (hc : cidCase s p n = .gone) : Step s (.beginSendOn p n) .drop
  /-- §9.5, line 3630: with zero-length connection IDs there is no sequence
      number to keep apart, so lines 3603 and 3608 have no content and there is
      no use to record; the text's answer is the SHOULD NOT of line 3630, which
      is `RecommendedMigration`. -/
  | cidZeroLen {s p n} (hc : cidCase s p n = .zeroLen) :
      Step s (.beginSendOn p n) (.ok s [])
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
  /-- Bookkeeping, not a rule of §9: one of the peer's connection IDs, as WP4
      `ConnIds` learned it.  §9.5 speaks of sequence numbers and
      `Spec.OutDatagram` carries bytes, so `MaySendDatagram` needs the
      dictionary between them (NOTES 16). -/
  | peerCidLearn {s seq cid} :
      Step s (.learnPeerCid seq cid) (.ok (s.recordPeerCid seq cid) [])

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
  | .learnPeerCid seq cid => [.ok (s.recordPeerCid seq cid) []]
  | .beginSendOn p n =>
    match cidCase s p n with
    | .gone => [.drop]
    | .zeroLen => [.ok s []]
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
    | learnPeerCid seq cid =>
      simp only [outcomes, List.mem_singleton] at h; subst h; exact .peerCidLearn
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
    | peerCidLearn => simp [outcomes]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

end Quic.Spec.Migration
