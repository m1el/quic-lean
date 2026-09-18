import QuicModel.Spec.Migration.Theorems

/-!
  WP10 "Migration": §9 Connection Migration, lines 3272–3812 of
  `spec/draft-ietf-quic-transport-34.txt`.

  One `Component` — `Quic.Spec.Migration.component` — over an abstract `Path`
  (a local address and a peer address, both opaque).  It answers one question:
  *which path does the connection use, and which connection ID on it?*

  * `Migration/Basic.lean`     parts 1–1c: state, events, effects, `recvCase`
  * `Migration/Step.lean`      parts 2–4: `Step`, `outcomes`, `outcomes_iff`
  * `Migration/Inv.lean`       part 5: `Inv` and `step_inv`
  * `Migration/Send.lean`      parts 6–7: `MaySendPacket`, `Recommended`, the component
  * `Migration/Theorems.lean`  parts 8–9: named theorems and worked scenarios

  What it is joined to: `PathValidation` (WP5b) drives `validationSucceeded` /
  `validationFailed` and consumes `Effect.startValidation`;
  `AddressValidation` (WP5a) owns the anti-amplification budget that
  `MaySendDatagramOn` refers to; `ConnIds` (WP4) owns the connection IDs whose
  sequence numbers appear in `dcidOn` / `scidOn`; `FrameRules` (WP3) decides
  which packets are probing packets.
-/

/-!
## 10. Coverage of lines 3272–3812

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §9 (3280) | "An endpoint MUST NOT initiate connection migration before the handshake is confirmed" | `Step.migTooEarly`, `MaySendPacket` clause 2, `no_migration_before_confirmed`, `maySendPacket_unconfirmed`, `active_loc_stable_from_init`; NOTES 4, 5 |
| §9 (3284) | peer sent `disable_active_migration` ⇒ MUST NOT send packets (including probing packets) from a different local address to the peer's handshake address, unless it acted on `preferred_address` | `State.sendBanned`, `MaySendPacket` clause 3, `Step.migBanned`, `Step.probeBanned`, `disableMigration_blocks`, `sendBanned_iff` |
| §9 (3289) | "the endpoint MUST either drop the incoming packets on that path without generating a stateless reset or proceed with path validation and allow the peer to migrate" | `RecvCase.banned`, `Step.recvBannedDrop`, `Step.recvBannedMigrate`; NOTES 2 |
| §9 (3312) | "An endpoint MUST perform path validation … if it detects any change to a peer's address, unless it has previously validated that address" | `State.mustValidate`, `Effect.startValidation` from `observe`/`permit`; NOTES 9 |
| §9 (3316) | "When an endpoint has no validated path on which to send packets, it MAY discard connection state" | `Step.failOtherGiveUp` |
| §9 (3318) | "An endpoint capable of connection migration MAY wait for a new path to become available" | `Step.failOtherWait` |
| §9 (3321) | migration limited to new client addresses except §9.6; clients initiate all migrations | the shape of the model: only `recvPacket` changes `active.peer`, only `requestMigrate` changes `active.loc`; NOTES 3 |
| §9 (3323) | "Servers do not send non-probing packets … toward a client address until they see a non-probing packet from that address" | `MaySendPacket` clause 4 via `State.sawNonProbingFrom`; NOTES 8 |
| §9 (3325) | "If a client receives packets from an unknown server address, the client MUST discard these packets" | `RecvCase.unknownServer`, `Step.recvUnknownServer`; NOTES 6 |
| §9.1 (3331) | "An endpoint MAY probe for peer reachability from a new local address using path validation … prior to migrating" | `Step.probeStart` |
| §9.1 (3333) | failure of path validation does not end the connection "unless there are no valid alternative paths available" | `Step.failOther`, `Step.failOtherWait`, `Step.failOtherGiveUp` |
| §9.1 (3338) | definition of probing frames and probing packets | `FrameRules.probing` / `FrameRules.packetProbing` (WP3); the `probingOnly` field of `Event.recvPacket` |
| §9.2 (3345) | "An endpoint can migrate a connection to a new local address by sending packets containing non-probing frames from that address" | `Step.migFresh`, `MaySendPacket` clause 2 |
| §9.2 (3348) | a migrating endpoint can send without first validating the peer's address | `migCase` places no validation precondition on the *peer* address |
| §9.2 (3365) | "an endpoint initiates path validation … on the new path" | `Effect.startValidation` in `Step.migFresh` |
| §9.2 (3366) | "An endpoint MAY defer path validation until after a peer sends the next non-probing frame to its new address" | `Step.migDefer` |
| §9.2 (3370) | the endpoint resets its congestion controller and RTT estimate | out of scope: RFC 9002 state |
| §9.2 (3374) | the endpoint validates ECN capability (§13.4) | out of scope: ECN is not modelled |
| §9.3 (3379) | "Receiving a packet from a new peer address containing a non-probing frame indicates that the peer has migrated to that address" | `RecvCase.migrate` |
| §9.3 (3382) | "If the recipient permits the migration, it MUST send subsequent packets to the new peer address and MUST initiate path validation … if validation is not already underway" | `Step.recvMigrate`, `State.permit`, `State.permitFx`; the "if" is `Step.recvRefuse` |
| §9.3 (3387) | "An endpoint only changes the address to which it sends packets in response to the highest-numbered non-probing packet" | `State.isHighest`, `RecvCase.quiet`, `probing_never_migrates` |
| §9.3 (3392) | "An endpoint MAY send data to an unvalidated peer address, but it MUST protect against potential attacks as described in Section 9.3.1 and Section 9.3.2" | `MaySendDatagramOn` (WP5's budget) and `revert_or_close`; NOTES 10 |
| §9.3 (3394) | "An endpoint MAY skip validation of a peer address if that address has been seen recently" | the `!isValidated` guard of `State.mustValidate` |
| §9.3 (3401) | "an endpoint can abandon any path validation for other addresses" | not encoded: a MAY about `PathValidation`'s state, which WP5 owns; `Effect.abandonValidation` exists for the one case §9.6.3 makes a MUST |
| §9.3 (3407) | "the server SHOULD send new address validation tokens … to the client" | `RecommendedNewTokens`; the token itself is WP5's |
| §9.3.1 (3429) | an endpoint is required to validate a peer's new address | `State.mustValidate` |
| §9.3.1 (3431) | "Until a peer's address is deemed valid, an endpoint limits the amount of data it sends to that address; see Section 8" | `AddressValidation.MaySendTo`, referenced by `MaySendDatagramOn`; not duplicated |
| §9.3.1 (3436) | "If an endpoint skips validation of a peer address …, it does not need to limit its sending rate" | already in WP5's predicate: a validated address has no budget |
| §9.3.2 (3451) | "an endpoint MUST revert to using the last validated peer address when validation of a new peer address fails" | `Step.failRevert`, `revert_or_close`, `InvLastValidated` |
| §9.3.2 (3454) | higher-numbered packets from the legitimate address trigger another migration | `RecvCase.migrate` on `State.isHighest` |
| §9.3.2 (3460) | "If an endpoint has no state about the last validated peer address, it MUST close the connection silently by discarding all connection state" | `Step.failNoPath`, `Effect.discardState`, `State.discarded`, `discarded_sends_nothing`, `RecvCase.gone` |
| §9.3.2 (3463) | "an endpoint MAY send a stateless reset in response to any further incoming packets" | out of scope: WP6 Termination |
| §9.3.3 (3492) | "A non-probing packet received on the original path that increases the maximum received packet number will cause the endpoint to move back to that path" | `RecvCase.migrate` (the original path is just another path) |
| §9.3.3 (3498) | "In response to an apparent migration, endpoints MUST validate the previously active path using a PATH_CHALLENGE frame" | `Effect.validatePrevious` in `State.permitFx` |
| §9.3.3 (3505) | "An endpoint that receives a PATH_CHALLENGE on an active path SHOULD send a non-probing packet in response" | `RecommendedRespondToChallenge` |
| §9.3.3 (3517) | heuristics (recent packets on the old path, IPv6, duplicates, change of connection ID) | not encoded: advice with no normative keyword; `State.scidOn` records the connection-ID change an implementation would key on |
| §9.4 (3536) | "Packets sent on the old path MUST NOT contribute to congestion control or RTT estimation for the new path" | out of scope: RFC 9002 state |
| §9.4 (3539) | "an endpoint MUST immediately reset the congestion controller and round-trip time estimator for the new path" | out of scope: RFC 9002 state |
| §9.4 (3544) | "the endpoint MAY instead retain its congestion control state … for port-only changes" | out of scope: RFC 9002 state |
| §9.4 (3573) | the PATH_CHALLENGE timer "SHOULD be set as described in Section 6.2.1 … and MUST NOT be more aggressive" | out of scope: RFC 9002 state; the deadline is a parameter of `PathValidation` |
| §9.5 (3600) | "endpoints MAY change the Destination Connection ID they transmit with to a value that has not been used on another path" | `Step.cidFresh`, `Event.beginSendOn` |
| §9.5 (3603) | "An endpoint MUST NOT reuse a connection ID when sending from more than one local address" | `State.reusedAcrossLocal`, `Step.cidLocalReuse`, `MaySendPacket` clause 6, `InvOneLocalAddrPerCid`, `dcid_one_local_address` |
| §9.5 (3608) | "Similarly, an endpoint MUST NOT reuse a connection ID when sending to more than one destination address" | `State.reusedAcrossPeer`, `Step.cidPeerReuse`, `MaySendPacket` clause 6 |
| §9.5 (3611) | "… it MAY continue to use the current connection ID with the new remote address while still sending from the same local address" | `State.rebindKeepsCid`, `Step.cidRebindKeep` / `Step.cidRebindRefuse`; NOTES 7 |
| §9.5 (3615) | "These requirements regarding connection ID reuse apply only to the sending of packets" | `State.scidOn` is recorded and never constrained; NOTES 7 |
| §9.5 (3630) | "An endpoint SHOULD NOT initiate migration with a peer that has requested a zero-length connection ID" | `RecommendedMigration`; NOTES 8 |
| §9.5 (3649) | a client may switch connection ID, port or address after inactivity; "addresses SHOULD only be changed infrequently" | out of scope: the model has no notion of elapsed time between events |
| §9.5 (3659) | "endpoints SHOULD provide new connection IDs before peers migrate" | out of scope: WP4 `ConnIds.Local` |
| §9.6 (3678) | migrating to a new server address mid-connection is not supported | the state holds a single `preferredPeer`, and `knownServerAddr` admits no other server address |
| §9.6 (3680) | "If a client receives packets from a new server address when the client has not initiated a migration to that address, the client SHOULD discard these packets" | `RecvCase.unsolicited`, `Step.recvUnsolicitedDrop` / `Step.recvUnsolicitedKeep`, `Recommended`; NOTES 6 |
| §9.6.1 (3686) | "A server conveys a preferred address by including the preferred_address transport parameter in the TLS handshake" | `Event.learnPreferredAddress`, `Step.preferredLearn`, `Step.preferredWrongRole` |
| §9.6.1 (3689) | "Servers MAY communicate a preferred address of each address family" | out of scope: one preferred address per connection in the model; NOTES 11 |
| §9.6.1 (3701) | "Once the handshake is confirmed, the client SHOULD select one of the two addresses … and initiate path validation" | `Step.migValidateFirst`, gated by `migCase_confirmed` |
| §9.6.1 (3703) | "A client constructs packets using any previously unused active connection ID, taken from either the preferred_address transport parameter or a NEW_CONNECTION_ID frame" | `Event.beginSendOn` with §9.5's guards; `preferredAddressCidSeq = 1` (§5.1.1, line 1698) |
| §9.6.1 (3707) | "As soon as path validation succeeds, the client SHOULD begin sending all future packets to the new server address … and discontinue use of the old server address" | `Step.succSwitch` / `Step.succKeep`, `Recommended` |
| §9.6.1 (3710) | "If path validation fails, the client MUST continue sending all future packets to the server's original IP address" | `MaySendPacket` clause 5, `Step.failRevert` |
| §9.6.2 (3715) | "A client that migrates to a preferred address MUST validate the address it chooses before migrating" | `MigCase.validateFirst`, `Step.migValidateFirst` |
| §9.6.2 (3718) | the server answers a PATH_CHALLENGE at its preferred address | out of scope: WP5b `PathValidation.Step.challenge` |
| §9.6.2 (3721) | "The server MUST send non-probing packets from its original address until it receives a non-probing packet from the client at its preferred address and until the server has validated the new path" | `MaySendPacket` clause 4 |
| §9.6.2 (3726) | "The server MUST probe on the path toward the client from its preferred address" | the second disjunct of `State.mustValidate`; NOTES 9 |
| §9.6.2 (3730) | "Once the server has completed its path validation and has received a non-probing packet with a new largest packet number on its preferred address, the server begins sending non-probing packets … exclusively from its preferred IP address" | `State.preferredSwitchReady`, `Step.succSwitch`; NOTES 4 |
| §9.6.2 (3733) | "The server SHOULD drop newer packets for this connection that are received on the old IP address" | not encoded; NOTES 12 |
| §9.6.2 (3735) | "The server MAY continue to process delayed packets that are received on the old IP address" | `RecvCase.quiet` — a packet on the old path is processed and, being reordered, does not move the sending path |
| §9.6.2 (3740) | "A client MUST NOT use these for other connections" | out of scope: the model has one connection |
| §9.6.3 (3747) | "the client SHOULD perform path validation to both the original and preferred server address … concurrently" | not encoded: two `requestProbe` events are permitted and `State.otherValidating` records the situation |
| §9.6.3 (3757) | "If path validation of the server's preferred address succeeds, the client MUST abandon validation of the original address and migrate to using the server's preferred address" | `SuccCase.mustSwitch`, `Step.succMustSwitch`, `Effect.abandonValidation` |
| §9.6.3 (3760) | "If path validation of the server's preferred address fails but validation of the server's original address succeeds, the client MAY migrate to its new address and continue sending to the server's original address" | `Step.succSwitch` / `Step.succKeep` on the original address |
| §9.6.3 (3764) | "the server MUST protect against potential attacks as described in Section 9.3.1 and Section 9.3.2" | the same code path as §9.3: `State.mustValidate`, `Step.failRevert`, `MaySendDatagramOn` |
| §9.6.3 (3772) | "Servers SHOULD initiate path validation to the client's new address upon receiving a probe packet from a different address" | `State.mustValidate` makes it unconditional, which is what §9 line 3312 already requires |
| §9.6.3 (3776) | "A client that migrates to a new address SHOULD use a preferred address from the same address family for the server" | out of scope: addresses are opaque handles with no family |
| §9.6.3 (3779) | "the client MAY use this connection ID on any path" | `Event.beginSendOn` ties no sequence number to any path beyond §9.5's rules |
| §9.7 (3787) | "Endpoints that send data using IPv6 SHOULD apply an IPv6 flow label" | out of scope: below the transport; the model has no IP header |
| §9.7 (3791) | "The flow label generation MUST be designed to minimize the chances of linkability" | out of scope: below the transport |

## NOTES

1. **Two kinds of `Path`.**  `PathValidation.Path` is an opaque `⟨id⟩`; this
   component's `Path` is the pair of addresses §9 talks about, because §9.5's
   rules are about the local address and §9.3's about the peer address, and
   because the peer address has to be the key `AddressValidation` uses for the
   anti-amplification budget.  WP12 holds the bijection (one `PathValidation.Path`
   per `Migration.Path` it has seen) and keeps the two in sync at three points:
   `Migration.Effect.startValidation p` ⇒ `PathValidation.Event.startValidation`
   for the corresponding handle; `PathValidation.Effect.pathValidated` ⇒
   `Migration.Event.validationSucceeded`; `PathValidation.Effect.pathFailed` ⇒
   `Migration.Event.validationFailed`.  `PathInfo.status` and
   `PathInfo.validating` are exactly the part of `PathValidation.State` this
   component needs, mirrored rather than embedded; `State.markFailed` mirrors
   `PathValidation.State.markFailed` including its rule that a validated path
   stays validated (`PathValidation` NOTES 7), so the two never disagree.

2. **"If the peer violates this requirement" (line 3289).**  Two MUST NOTs
   precede it: line 3280 (do not initiate migration before the handshake is
   confirmed) and line 3284 (`disable_active_migration`).  The reading encoded
   is the narrow one — "this requirement" is line 3284's, the one in the same
   paragraph — so the two-alternative response (`RecvCase.banned`) applies only
   when we sent `disable_active_migration`.  Receiving an apparent migration
   before the handshake is confirmed is handled by the general rules instead:
   §9, line 3312 requires the path validation and §9.3, line 3382 leaves the
   switch to the recipient.  Under the broad reading the only change is that
   `recvCase` would return `.banned` when `!handshakeConfirmed` as well, which
   *removes* the `Step.recvRefuse` outcome; the narrow reading is therefore the
   more permissive one, and a differential run cannot be failed by it.

3. **A received packet never changes the local address we send from.**
   `recvCase` returns `.quiet` when the packet arrived at a local address other
   than the active path's, so `State.permit` only ever moves `active.peer`.  The
   one case where the local address does change on the receive side — a server
   taking up its preferred address — is §9.6.2's, and it happens on
   `validationSucceeded`, under line 3730's conditions, not on the packet that
   triggers it.  This is what makes `active_loc_stable_from_init` true.

4. **The preferred-address switch is gated on the handshake being confirmed.**
   §9.6.2, line 3730 does not repeat the condition, but moving the address a
   server sends from *is* initiating connection migration, which §9, line 3280
   forbids before the handshake is confirmed; §9.6.1, line 3701 says the same
   for the client ("Once the handshake is confirmed").  `preferredSwitchReady`
   therefore requires `handshakeConfirmed`.

5. **Named theorem (a) is false in its literal form.**  "The active path never
   changes to a new path before the handshake is confirmed" does not hold: a
   peer NAT rebinding during the handshake produces a packet from a new peer
   address, §9 line 3312 *requires* the endpoint to validate that address, and
   §9.3 line 3382 *permits* it to start sending there — nothing in §9 forbids
   following a migration it did not initiate.  The counterexample is
   `Step.recvMigrate` from a state with `handshakeConfirmed = false`.  What is
   proved instead, and is what line 3280 actually says:
   `no_migration_before_confirmed` (an endpoint-initiated migration is a no-op),
   `maySendPacket_unconfirmed` (no non-probing packet may leave from a new local
   address) and `active_loc_stable_from_init` (the *local* address of the active
   path never moves while the handshake is unconfirmed).

6. **MUST discard versus SHOULD discard for a packet from a server address.**
   §9, line 3325 says a client "MUST discard" packets "from an unknown server
   address"; §9.6, line 3680 says it "SHOULD discard" packets "from a new server
   address when the client has not initiated a migration to that address".  The
   reading encoded distinguishes the two by what the client knows: the preferred
   address it was told about in the handshake is *not* unknown, so a packet from
   it falls under the SHOULD (`RecvCase.unsolicited`, both outcomes permitted),
   and any other address falls under the MUST (`RecvCase.unknownServer`, only
   `drop`).  Without this split the two sentences contradict each other.

7. **Named theorem (c) per direction.**  For the *sending* direction the
   unrestricted statement — no connection ID sequence number in use on two
   different paths at once — is false, and the MAY of §9.5, line 3611 is the
   counterexample: `cliTwoPeers` in `Migration/Theorems.lean` has connection ID
   number 0 in use on `p00` and `p01`, two distinct paths, and `maySendPacket`
   permits it, exactly as the text allows after a NAT rebinding of the peer.
   What holds unconditionally is the local-address half, line 3603:
   `dcid_one_local_address` says two paths sharing a Destination Connection ID
   share a local address, in every reachable state.  For the *receiving*
   direction there is nothing to prove: line 3615 says "These requirements
   regarding connection ID reuse apply only to the sending of packets", so
   `scidOn` records which of our connection IDs the peer uses on which path
   (which §9.3.3, line 3521 suggests as an attack heuristic, and which
   `rebindKeepsCid` needs) without ever constraining it.

8. **Zero-length connection IDs.**  When the peer issued us zero-length
   connection IDs (`peerZeroLen`) our Destination Connection IDs carry no
   sequence number, so §9.5 lines 3603 and 3608 have nothing to bite on:
   `CidCase.zeroLen` records the send context without touching `dcidOn`, and
   clause 6 of `MaySendPacket` is satisfied outright.  The text's own answer to
   that situation is the SHOULD NOT of line 3630 (`RecommendedMigration`), not a
   prohibition.  Symmetrically, when *we* issued zero-length connection IDs
   (`ourZeroLen`) an incoming packet carries no sequence number we could record,
   so `recordRecv` leaves `scidOn` alone.  `dcid_one_local_address` is
   consequently a statement about the paths that appear in `dcidOn`, which is
   empty in the zero-length case.

9. **`mustValidate` is slightly stronger than any one sentence.**  It fires when
   the peer address is new and unvalidated (§9, line 3312) *or* when the packet
   arrived at a local address other than the one we send from and that path is
   unvalidated (§9.6.2, line 3726, the server probing from its preferred
   address).  Merging the two means a `startValidation` effect is produced in a
   case the text covers only for the server's preferred address; since the only
   way a client can receive at a second local address is to have migrated there
   itself, no other situation is reachable.

10. **Anti-amplification is referenced, not duplicated.**  §9.3, line 3392 and
    §9.3.1, line 3431 defer to §8, which is WP5's.  The `Component`'s
    `MaySendDatagram` field can only see this component's state, so the budget
    check is the free function `MaySendDatagramOn av s d`, taking WP5's state
    exactly as `PathValidation.MaySendDatagramOn` does (its NOTES 10).  WP12
    conjoins the two.  The `MaySendDatagram` field itself carries the rule that
    every packet coalesced in a datagram is bound by the path rules of the
    datagram it leaves in.

11. **One preferred address, not one per family.**  §9.6.1, line 3689 lets a
    server offer an IPv4 and an IPv6 preferred address.  Addresses here are
    opaque handles with no family, so the state holds a single
    `preferredPeer`/`preferredLocal`.  Modelling both would only duplicate every
    preferred-address rule; the choice between them (line 3701's "select one of
    the two addresses") is a policy decision the model does not constrain.

12. **§9.6.2, line 3733 is not encoded.**  "The server SHOULD drop newer packets
    for this connection that are received on the old IP address" would, taken as
    a `Recommended` outcome, contradict §9.3's handling of the same packet: a
    non-probing packet with a new largest packet number on the old path is
    exactly what §9.3.3, line 3492 says should pull the connection back.  The
    two sentences are reconciled only by "once the server has completed its path
    validation", i.e. after the server has finished migrating, and expressing
    that as a preference among permitted outcomes needs the server to know it
    will not be asked to migrate back.  The MAY of line 3735 *is* encoded
    (`RecvCase.quiet` processes the packet), so no conforming behaviour is
    rejected either way.

13. **`preferredActedOn` for both roles.**  §9, line 3287 ("unless the endpoint
    has acted on a preferred_address transport parameter from the peer") is a
    send-side condition for the client; §5.2.2, line 1979 ("after a client has
    acted on a preferred_address transport parameter") is the receive-side one
    for the server.  One flag serves both: the client sets it when it starts
    validating the preferred address (`State.startProbe`), the server when a
    packet from the client reaches its preferred address (`State.recordRecv`).
    "Acting on" the parameter is not defined in the text; starting the path
    validation §9.6.2 line 3715 requires is the earliest point at which the
    endpoint has committed to it.

14. **`Event.beginSendOn` is an event, not only a `MaySendPacket` rule.**
    §9.5's prohibitions are about *reuse*, so they need a record of which
    connection ID is in use where, and that record has to be updated by
    something.  A request the text forbids yields `.drop` — nothing is sent and
    nothing changes — the same convention `ConnIds` uses for `issueCid` (its
    NOTES 8).  `MaySendPacket` then re-checks the same condition on `State.tx`
    so that the send-side predicate is self-contained and WP12 does not have to
    trust the event ordering.

15. **Retransmission.**  `MaySend` is `True` for every frame, and
    `MaySendPacket`'s conditions are about the path and connection ID a packet
    leaves with rather than its contents, so re-sending a lost frame on a
    permitted path is always permitted (§12.4, line 4936; §13.3).
-/
