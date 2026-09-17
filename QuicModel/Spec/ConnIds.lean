import QuicModel.Spec.ConnIds.Remote
import QuicModel.Spec.ConnIds.Local

/-!
  WP4 "ConnIds": §5.1 Connection ID, §5.1.1 Issuing, §5.1.2 Consuming and
  Retiring (lines 1608–1834), §19.15 NEW_CONNECTION_ID and §19.16
  RETIRE_CONNECTION_ID (lines 7923–8058).

  One endpoint's view is two `Component`s over disjoint frames:

  * `ConnIds.Remote` — the connection IDs the peer issued to us.  It receives
    NEW_CONNECTION_ID and governs sending RETIRE_CONNECTION_ID.
  * `ConnIds.Local` — the connection IDs we issued to the peer.  It receives
    RETIRE_CONNECTION_ID and governs sending NEW_CONNECTION_ID.

  Each is `True` on the frame the other governs, so an endpoint's `MaySend` is
  their conjunction (WP12).  The coverage table for both is at the end of
  `ConnIds/Remote.lean`.
-/
namespace Quic.Spec.ConnIds

/-! ## The two halves govern disjoint frames -/

theorem remote_maySend_newCid (s : Remote.State) (seq rpt : Nat) (cid token : ByteArray) :
    Remote.MaySend s (.newConnectionId seq rpt cid token) := trivial

theorem local_maySend_retireCid (s : Local.State) (n : Nat) :
    Local.MaySend s (.retireConnectionId n) := trivial

/-! ## The zero-length rules are mirror images

§19.15 line 7970 forbids *sending* NEW_CONNECTION_ID when our own connection
IDs are zero-length (`Local.State.zeroLen`); line 7974 makes *receiving* one a
PROTOCOL_VIOLATION when the peer's connection IDs are zero-length
(`Remote.State.peerZeroLen`), because that is exactly the peer being in the
first situation.  §19.16 lines 8055–8058 are the same pair the other way round.
-/

example (s : Local.State) (h : s.zeroLen = true) (cid token : ByteArray) (seq rpt : Nat) :
    Local.maySend s (.newConnectionId seq rpt cid token) = false := by
  simp [Local.maySend, Local.canIssue, Local.isReNewCid, h]

example (s : Remote.State) (h : s.peerZeroLen = true) (n : Nat) :
    Remote.maySend s (.retireConnectionId n) = false := by
  simp [Remote.maySend, h]

/-! ## The MAY of §19.15 line 7985 and connection-ID uniqueness

Sequence numbers identify connection IDs uniquely in both sets, under either
alternative of the MAY (`Remote.seq_unique`, `Local.seq_unique`): the lenient
alternative keeps the entry it already has rather than overwriting it.

The converse is *not* true on the remote side.  If the endpoint takes the
lenient alternative when the peer reuses a connection ID under a second
sequence number, the same connection ID ends up recorded twice.  Here is the
counterexample. -/

section Counterexample

private def tok (b : UInt8) : ResetToken := List.replicate 16 b

private def c0 : Remote.State :=
  { entries := [⟨0, [1], tok 0⟩], retired := [], retirePriorTo := 0, limit := 4,
    peerZeroLen := false }

/-- The peer reuses connection ID `[1]` under sequence number 1. -/
private def c1 : Remote.State := { c0 with entries := c0.entries ++ [⟨1, [1], tok 0⟩] }

-- §19.15, line 7985 makes this a *permitted* outcome (the MAY is not taken) …
example : Remote.component.accepts c0 (.recvNewCid 1 0 [1] (tok 0)) (.ok c1 []) = true := by decide
-- … and so is rejecting the frame.
example : Remote.component.accepts c0 (.recvNewCid 1 0 [1] (tok 0))
    (.error .protocolViolation) = true := by decide
-- After the lenient step, one connection ID has two sequence numbers.
example : c1.entries.filter (fun e => decide (e.cid = [1])) = c1.entries := by decide
example : (seqs c1.entries).Nodup := by decide

end Counterexample

/-! ## NOTES: ambiguities in the text and the readings encoded

1. **Which side's zero length matters.**  §19.15 line 7974 says "An endpoint
   that is sending packets with a zero-length Destination Connection ID MUST
   treat receipt of a NEW_CONNECTION_ID frame as … PROTOCOL_VIOLATION".  The
   Destination Connection ID an endpoint *sends* is one its *peer* issued, so
   this is `Remote.State.peerZeroLen`, not a property of our own connection
   IDs — it is the exact mirror of line 7970's MUST NOT on the sender, which is
   about the sender's own (`Local.State.zeroLen`).  §19.16 line 8055 is read the
   same way: "provides a zero-length connection ID" is the issuer, so receiving
   RETIRE_CONNECTION_ID is checked against `Local.State.zeroLen` and sending one
   against `Remote.State.peerZeroLen`.

2. **Order of the receive-side checks.**  The text does not say which error wins
   when a NEW_CONNECTION_ID is both malformed and arrives at a zero-length-CID
   endpoint.  `Remote.outcomes` checks, in order: zero-length (PROTOCOL_
   VIOLATION), connection ID length (FRAME_ENCODING_ERROR), Retire Prior To >
   Sequence Number (FRAME_ENCODING_ERROR), the reuse MAY, then the limit.  Only
   the preferred outcome is affected: each check is a separate `Step`
   constructor with the earlier ones as hypotheses, so a differential run that
   sees a different one of these errors will still be inside `Step` only if the
   earlier guards do not hold.  If ngtcp2 turns out to prefer another order this
   is the first thing to relax.

3. **`entries` is never pruned.**  §5.1.2 line 1826 says "An endpoint MUST NOT
   forget a connection ID without retiring it", so the model keeps every entry
   forever and records retirement separately.  This also makes §19.15 line 8013
   ("unless it has already done so for that sequence number") and the repeat
   detection of line 7979 decidable from the state alone.  A real
   implementation may of course drop the bytes of a retired connection ID; that
   only weakens its ability to detect the line 7985 reuse, which is a MAY.

4. **A repeat with a different value is ignored, not overwritten.**  When the
   lenient alternative of line 7985 is taken and the sequence number is already
   known, `Remote.entriesAfter` keeps the existing entry.  The text does not say
   what to do; keeping the first is what makes `Remote.seq_unique` hold under
   both alternatives, and it matches "the endpoint MAY treat that receipt as a
   connection error" — an endpoint that does not treat it as an error should not
   let the peer rewrite history either.

5. **A newly received connection ID below Retire Prior To.**  `Remote.staleOf`
   runs over the entry list *after* insertion, so such a connection ID is added
   and retired in the same step, producing `stopUsing` and `queueRetire` for it.
   The alternative reading — never add it at all — would lose the record needed
   for "unless it has already done so for that sequence number".  The
   `stopUsing` effect for a connection ID that was never used is harmless.

6. **Effect order.**  §5.1.2 line 1811 requires retiring "before adding the
   newly provided connection ID", so retirement effects are emitted in entry
   order and the newly added connection ID, being appended, comes last.

7. **Retire Prior To is not required to increase on the send side.**  §19.15
   lines 7998–8001 say only that once a sender indicates a Retire Prior To
   value, "smaller values sent in subsequent NEW_CONNECTION_ID frames have no
   effect", and that "a receiver MUST ignore any Retire Prior To fields that do
   not increase the largest received Retire Prior To value".  That is a rule
   about the receiver, not a prohibition on the sender, so `Local.canIssue`
   places no condition on `rpt` beyond §19.15 line 7993's `rpt ≤ seq`, and
   `MaySend` does not restrict it: an endpoint may send an older value.
   `Local.State.sentRetirePriorTo` therefore tracks the *largest* value sent
   (`applyIssue` uses `Nat.max`), which is what the SHOULD NOT of §5.1.2 line
   1831 in `Local.Recommended` refers to and what keeps `Local.sent_rpt_mono`
   true.

8. **`issueCid` and `recvRetireCid`'s `dcidSeq`.**  "Issue a connection ID" is
   modelled as an event rather than only as `MaySend`, so that the sequence
   number counter and `sentRetirePriorTo` advance in the state; a request the
   text forbids yields `.drop` (nothing is sent, nothing changes) rather than an
   error, because no frame has been received.  §19.16 line 8050 needs to know
   which connection ID the carrying packet was addressed to, so that sequence
   number is part of the event; `none` covers the connection IDs of §5.1.1 line
   1704 that have no sequence number.

9. **Not modelled here.**  Choosing which remote connection ID to use on which
   path and the migration rules (WP10); stateless reset detection from the
   tokens, which are opaque bytes here (WP6); learning the initial connection
   IDs, `active_connection_id_limit` and `preferred_address` from the handshake
   (WP11) — all three are initial-state parameters; the minimum value of 2 for
   `active_connection_id_limit` (§18.2, WP1) is not enforced; the number of
   unacknowledged RETIRE_CONNECTION_ID frames (§5.1.2 line 1823) needs loss
   recovery state, which is RFC 9002 and out of scope.

10. **Retransmission and `MaySend`.**  §12.4 line 4936, "All frames are
    idempotent in this version of QUIC", means a NEW_CONNECTION_ID or
    RETIRE_CONNECTION_ID lost in flight is re-sent unchanged, at a point where
    the state has moved on.  Both `MaySend`s therefore have a second disjunct
    for an exact repeat: `Local.isReNewCid` accepts a frame whose sequence
    number, connection ID and stateless reset token match an entry we issued,
    carrying any `rpt ≤ seq`; `Remote.MaySend` accepts a RETIRE_CONNECTION_ID
    for a sequence number already retired.  That disjunct still carries the
    conditions that held of the original frame and cannot have changed since —
    not zero-length, legal field lengths — so it never admits a frame the text
    forbids outright.  `MaySend` consequently cannot tell a retransmission from
    a gratuitous duplicate; deciding whether the frame is really in flight needs
    loss recovery state (RFC 9002), which is out of scope.
-/

end Quic.Spec.ConnIds
