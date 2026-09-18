# Wave 1 review, group A — WP1 TransportParams, WP2 Stream, WP3 FrameRules/Ack, WP4 ConnIds

Reviewer: independent (did not write any of the reviewed Lean).
Worktree: `quic-lean-wt/review1a`, branch `review1a`, base `41d5579`.
`timeout 600 lake build` → clean, 67 jobs, no warnings.
Probe files: `out/probe_wp1.lean`, `out/probe_wp2{,b}.lean`,
`out/probe_wp3{,b,c}.lean`, `out/probe_wp4.lean`. All were run under
`timeout … lake env lean` and all exit 0, so every `example` quoted below is a
*true* statement about the model — the results are from runs, not from reading
the code. No Lean under `QuicModel/` was modified.

Method: the assigned text range was read and its normative sentences listed
before any Lean was opened; `Step`, `outcomes`, `MaySend`, `Recommended`, `Inv`
and the named theorems were then classified sentence by sentence; every quoted
sentence attached to an error-code rule was checked against
`spec/draft-ietf-quic-transport-34.txt` by line number.

---

## WP1 — TransportParams (§7.4, §7.4.1, §7.4.2 lines 2506–2695; §18 lines 6875–7154)

Files: `QuicModel/Spec/TransportParams.lean`, `TransportParams/{Wire,Validity,Order}.lean`.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| W1-1 | MEDIUM | §7.4 L2539–2542: "An endpoint MUST NOT send a parameter more than once in a given transport parameters extension.  An endpoint SHOULD treat receipt of duplicate transport parameters as a connection error of type TRANSPORT_PARAMETER_ERROR." | `TransportParams.lean` `Step.accept` / `outcomes` via `Wire.applyEntries` | The SHOULD is correctly an *alternative* (`Step.duplicate` preferred, `Step.accept` still permitted), but the accepting alternative is hard-wired to **the last copy wins**: `applyEntries` folds left to right. The text says nothing about which copy applies, so an implementation that keeps the **first** copy — the other obvious choice, and the one a "insert if absent" decoder produces — is rejected by `accepts`. `NOTES 2` admits this; it is still `Step` rejecting conforming behaviour. | Either add a `Step.acceptFirst` alternative built from a first-wins fold, or make the accepting alternative existential over "any choice function over the duplicate group". Cheapest faithful version: enumerate both folds in `outcomes` when `duplicated raw`. |
| W1-2 | MEDIUM | §7.4.1 L2640–2641: "The applicable subset of transport parameters that permit sending of application data SHOULD be set to non-zero values for 0-RTT."  §18.2 L7041: "This value SHOULD include the receiver's expected delays in alarms firing." | — (no `Recommended` anywhere in WP1) | Two SHOULDs in range are simply dropped. PLAN §1 says SHOULD-that-recommends "goes in a separate `Recommended` predicate"; WP1 defines none, so the coverage table's "advice only; not modelled" leaves a hole the rule was written to close. Low practical impact (both are advice to the *sender* of the parameters), but it is a missing rule in range. | Add `def Recommended : Role → TransportParams → Prop` with the two clauses, cite both lines, and point the coverage rows at it. |
| W1-3 | LOW | §18.2 L7128–7131: "If this transport parameter is absent, a default of 2 is assumed.  If an endpoint issues a zero-length connection ID, it will never send a NEW_CONNECTION_ID frame and therefore ignores the active_connection_id_limit value received from its peer." | `Validity.lean` `Valid` 5th conjunct | `Valid` rejects `active_connection_id_limit < 2` unconditionally, so an endpoint that issues zero-length connection IDs — which the text says "ignores the … value received from its peer" — has *no* accepting outcome (probe P3 shows `outcomes = [error]`). The unconditional MUST at L7125–7127 supports the model's reading, so this is a note rather than a defect, but the coverage table files L7131 as "out of scope: WP4 ConnIds" when the decision is actually taken here. | Keep the behaviour; move the L7131 row out of "out of scope" and record the reading in NOTES (the MUST at L7126 is unconditional and wins). |
| W1-4 | LOW | §7.4.1 L2607–2609: "the server MUST NOT reduce any limits **or alter any values that might be violated by the client with its 0-RTT data**.  **In particular**, …" | `Validity.lean` `ZeroRttCompatible` | Only the seven enumerated parameters are encoded. The leading clause is broader than the enumeration it introduces. Defensible (the enumeration is the operative part) but undeclared. | One NOTES line saying the broader clause is read as exhausted by the seven-item list. |
| W1-5 | LOW | citations throughout | `TransportParams.lean` coverage table, `Validity.lean` inline comments, `Wire.lean` header | A large fraction of the line numbers are wrong, several by 20–35 lines, several landing on blank lines or inside an unrelated parameter's text. This includes rules the brief says must be checked individually because they carry an error code. See the table below. | Re-derive the numbers mechanically (`grep -n` on the quoted substring). |

Wrong citations found (cited → actual; verified with `sed -n "<n>p"`):

| cited | claimed sentence | actual line | what is at the cited line |
|---|---|---|---|
| §7.4.2 L2664 (`Wire.lean` §"Interpreting the raw sequence", coverage row) | "An endpoint MUST ignore transport parameters that it does not support." | 2670 | "…server MAY treat use of updated transport parameters in 0-RTT as a" |
| §7.4.1 L2574 (`Validity.lean` `remembered` doc; coverage row) | "A client MUST NOT use remembered values for the following parameters…" | 2593 | blank line |
| §7.4.1 L2584 (`Validity.lean` `ZeroRttCompatible` doc; coverage row) | "If 0-RTT data is accepted by the server, the server MUST NOT reduce any limits…" | 2607 | "parameters established in the handshake.  Not all transport" |
| §7.4.1 L2612 (`Validity.lean` `zeroRttCompatibleStrict` doc; coverage row) | "A server MAY store and recover the previously sent values of the max_idle_timeout…" | 2645 | blank line |
| §7.4.1 L2566 / 2580 / 2606 / 2620 / 2623 (coverage rows) | five 0-RTT sentences | 2588 / 2600 / 2640 / 2653 / 2656 | blank lines and the `initial_max_streams_bidi` bullet |
| §18.2 L6952 (`Validity.lean` `Valid`, **error-code rule**) | "Values below 1200 are invalid." | 6964 | "by a client, but MAY be sent by a server.  A server that does not" (stateless_reset_token) |
| §18.2 L7018 (`Validity.lean` `Valid`, **error-code rule**) | "Values above 20 are invalid." | 7036 | "parameter is absent or zero, the peer cannot open bidirectional" |
| §18.2 L7028 (`Validity.lean` `Valid`, **error-code rule**) | "Values of 2^14 or greater are invalid." | 7045 | "unidirectional streams until a MAX_STREAMS frame is sent.  Setting" |
| §18.2 L7145 (`Validity.lean` `Valid`, **error-code rule**) | "A client MUST NOT include any server-only transport parameter…" | 7149 | "every stream of the corresponding type immediately after opening.  If" |
| §18.2 coverage rows 6940 / 6944 / 6959 / 7040 / 7051 / 7054 / 7062 | odcid / max_idle_timeout / stateless_reset_token / disable_active_migration / preferred_address-server-only / all-zero address MAY / Figure 22 | 6934 / 6939 / 6951 / 7047 / 7067 / 7068 / 7099 | the coverage rows for `stateless_reset_token` (6959) and `max_udp_payload_size` (6952) point into each other's paragraphs |

Correct, for the record: §7.4 L2536, L2539, L2540; §18.2 L7093, L7094, L7124; §4.6 L1537; §18.1 L6912.

### Probes (`out/probe_wp1.lean`, `lake env lean` exit 0 — every `example` below compiles)

W1-1, duplicates:

```lean
-- last copy accepted
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 20 }⟩
      [.paramsApplied { defaults with initialMaxData := 20 }]) = true := by decide
-- FIRST copy rejected
example : component.accepts cli (.recvParams (ext [(0x04, [0x0a]), (0x04, [0x14])]))
    (.ok ⟨.client, some { defaults with initialMaxData := 10 }⟩
      [.paramsApplied { defaults with initialMaxData := 10 }]) = false := by decide
```

W1-3, `active_connection_id_limit = 1` has exactly one permitted outcome:

```lean
example : component.outcomes cli (.recvParams (ext [(0x0e, [0x01])]))
    = [.error .transportParameterError] := by decide
```

### Checked and found correct

- Every §18.2 range rule at its boundary, by probe: `max_udp_payload_size` 1199/1200,
  `ack_delay_exponent` 20/21, `max_ack_delay` 2^14−1 / 2^14, `active_connection_id_limit`
  0/1/2, `initial_max_streams_{bidi,uni}` 2^60 / 2^60+1 (§4.6 L1537, code
  TRANSPORT_PARAMETER_ERROR — correct, not FRAME_ENCODING_ERROR).
- All four §18.2 defaults that are "otherwise stated" (65527, 3, 25, 2) and 0 for the rest.
- Server-only parameters (`0x00`, `0x02`, `0x0d`, `0x10`) rejected from a client, accepted
  from a server, for both role directions.
- §18.1 reserved identifiers: `IsReserved n := n % 31 = 27` is exactly `31*N+27` over `Nat`,
  `ofCode?_reserved` is proved, a *repeated* reserved identifier is not a duplicate (NOTES 1
  is the right reading given §7.4.2).
- Unknown non-reserved identifiers ignored (probe with id 0x1234).
- `disable_active_migration` with a non-empty value → TRANSPORT_PARAMETER_ERROR (NOTES 7);
  zero-length → flag set.
- Non-minimal varint accepted, trailing byte in a value rejected (NOTES 3 — consistent with
  §16's "Values do not need to be encoded on the minimum number of bytes").
- `preferred_address`: zero-length CID inside it → error; server with zero-length
  `initial_source_connection_id` providing one → error; absent iscid → vacuous (NOTES 5);
  a client sending it at all → error.
- CID lengths in the three §7.3 parameters are deliberately unbounded (NOTES 4); probed at 21
  and 200 bytes — accepted, which matches the text (no bound is stated in §18.2).
- `Step` is exhaustive over `decodeRaw` × `validate` × `duplicated` and `outcomes_ne` holds;
  the preferred outcome for duplicates is the error, which is what makes `step_perm` true.
- Named theorems say what they claim and are not vacuous: `step_encodeParams` (round trip,
  hypotheses `tp.WF` + `Valid role.peer tp` are both necessary), `step_ok_valid` (b — every
  accepted record satisfies `Valid`, and the effect list is exactly `[paramsApplied tp]`),
  `step_perm` (c — order independence of the *preferred* outcome, with the honest caveat in
  its own doc comment that the accepted record is order dependent under duplicates).
- `Inv` is `peer = none ∨ Valid` — trivially true of a realistic initial state.
- `MaySend ≡ True`: correct, this component governs no frame (§7.4: parameters travel in
  the TLS handshake). Composition by conjunction is unaffected.
- `remembered` resets exactly the seven parameters of §7.4.1 L2593–2598 and keeps everything
  else (L2600); `ZeroRttCompatible` covers exactly the seven bullets of L2613–2631;
  `zeroRttCompatibleStrict` covers exactly the three of L2645–2647.

### Modelling choices worth flagging for composition

- `State.peer` is overwritten by a second `recvParams` with no check (NOTES 8) — WP11 must
  guarantee the event fires once.
- "MUST be ignored" is `.ok s []` throughout (never `.drop`), consistent with the template.
- `duplicated` counts only *known* identifiers, so the duplicate check is not decidable from
  the raw byte sequence alone — WP12 must keep `Raw` around, not just the interpreted record.

---

## WP4 — ConnIds (§5.1 lines 1608–1834; §19.15–19.16 lines 7923–8058)

Files: `QuicModel/Spec/ConnIds.lean`, `ConnIds/{Common,Remote,Local}.lean`.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| W4-1 | HIGH | §5.1.1 L1721–1725: "An endpoint MUST NOT provide more connection IDs than the peer's limit.  An endpoint MAY send connection IDs that temporarily exceed a peer's limit if the NEW_CONNECTION_ID frame also requires the retirement of any excess, by including a sufficiently large value in the Retire Prior To field."  With §5.1.2 L1811–1814: "Upon receipt of an increased Retire Prior To field, the peer MUST stop using the corresponding connection IDs and retire them with RETIRE_CONNECTION_ID frames **before adding the newly provided connection ID** to the set of active connection IDs." | `Local.lean` `State.peerActiveAfter`, used by `canIssue` and hence by `Step.issueOk`/`issueRefused` **and `MaySend`** | `peerActiveAfter s rpt` counts `issued` entries with `rpt ≤ e.seq ∧ e.seq ∉ s.retired`, i.e. it credits **only the Retire Prior To of the frame being sent** and never `s.sentRetirePriorTo`. `s.retired` only fills in when the peer's RETIRE_CONNECTION_ID frames arrive, so in the whole window between our raising Retire Prior To and the peer's replies coming back, the model over-counts the peer's active set and refuses a NEW_CONNECTION_ID the text permits. Probe P4-A reaches such a state by two *model-permitted* issues and then gets `.drop` / `maySend = false` for a frame that leaves the peer at exactly its limit. This violates "`MaySend` is never stricter than the text". | `peerActiveAfter` should filter on `Nat.max s.sentRetirePriorTo rpt`, not `rpt`. (`sentRetirePriorTo` already exists and is already maintained as a running `Nat.max` by `applyIssue`; it is currently read only by `Recommended`.) |
| W4-2 | MEDIUM | §5.1.2 L1826–1829: "An endpoint MUST NOT forget a connection ID without retiring it, though it **MAY choose to treat having connection IDs in need of retirement that exceed this limit as a connection error of type CONNECTION_ID_LIMIT_ERROR**." | `Remote.lean` `Step` | The MAY has no constructor. A conforming peer that takes it closes with CONNECTION_ID_LIMIT_ERROR at a point where `Remote.Step` permits only `.ok` (probe P4-I). The coverage row calls the whole sentence "partly … out of scope (RFC 9002)", but only the *trigger* needs loss-recovery state; the permitted outcome does not. This is reachable in a differential run (a peer that walks Retire Prior To up fast). | Add `Step.retireBacklog` gated on a state field (count of queued-but-unacked retirements, or simply `s.retired.length > 2 * s.limit` as a decidable over-approximation) and record the approximation in NOTES; or state explicitly in NOTES that `accepts` will reject this legal behaviour and that WP13 must triage it. |
| W4-3 | MEDIUM | §5.1.1 L1753–1758: "An endpoint MAY limit the total number of connection IDs issued for each connection to avoid the risk of running out of connection IDs … An endpoint MAY also limit the issuance of connection IDs to reduce the amount of per-path state it maintains." | `Local.lean` `Step.issueRefused`; coverage row "§5.1.1 (1753) … `Step.issueRefused` allows refusing" | `issueRefused` carries `h : canIssue s cid token rpt = false`, so when `canIssue` holds, issuing is the **only** permitted outcome of the `issueCid` event (probe P4-B: `accepts … .drop = false`). The coverage table's claim that `issueRefused` encodes the MAY is therefore wrong. The defence — "not issuing is modelled by not raising the event" — is reasonable, but then the coverage row is mis-stated. | Either drop the hypothesis from `issueRefused` (making `.drop` always permitted for `issueCid`), or change the coverage row to "not modelled: declining to issue is modelled by the event not occurring" and say so in NOTES. |
| W4-4 | MEDIUM | §5.1.1 L1718–1719 "An endpoint SHOULD ensure that its peer has a sufficient number of available and unused connection IDs"; L1749–1750 "An endpoint SHOULD supply a new connection ID when the peer retires a connection ID." | `Local.lean` `Recommended`; coverage rows 1718 and 1749 | The coverage table maps L1718 to `Local.Recommended` and L1749 to `Local.Effect.cidRetiredByPeer`. `Recommended` contains **only** the §5.1.2 L1831 clause; neither SHOULD is in it. `cidRetiredByPeer` is an effect, not a recommendation — emitting it says nothing about supplying a replacement. | Add the two clauses to `Recommended` (`activeCount` below some threshold ⇒ issue; `n ∈ retired` freshly ⇒ issue) or correct the two rows to "advice, not modelled". |
| W4-5 | LOW | §19.15 Figure 39: "Stateless Reset Token (128)"; `Common.lean` defines `tokenLenOk` for it | `Remote.lean` `Step`, `Event.recvNewCid` | `tokenLenOk` is enforced on the **send** side (`Local.canIssue`, `isReNewCid`) but never on receipt, so `Remote` accepts `recvNewCid _ _ _ [1,2,3]` (probe P4-J). Harmless — the field is fixed-width so the packet parser cannot produce it — but `Event` then has states the wire cannot reach, which matters when WP12 builds events from decoded frames. | Either add `tokenLenOk token = true` as a hypothesis to the non-error constructors, or note in NOTES that `Event` is assumed to come from a successfully decoded frame. |
| W4-6 | LOW | §19.15 L7998–8001: "Once a sender indicates a Retire Prior To value, smaller values sent in subsequent NEW_CONNECTION_ID frames have no effect." | `Local.lean` `isReNewCid` | The retransmission disjunct accepts **any** `rpt ≤ seq` for an already-issued sequence number, so `maySend` calls a frame with a *different* Retire Prior To a "retransmission" (probe P4-C: both `rpt = 0` and `rpt = 1` accepted for the frame originally sent with `rpt = 0`). §12.4's idempotence argument covers the identical frame only. Not a rule violation — raising Retire Prior To is not forbidden — but it makes `MaySend` unable to distinguish a retransmission from a new Retire Prior To update, which is exactly what §5.1.2 L1831's SHOULD NOT is about. | Store the `rpt` actually sent in `Entry` (or a parallel list) and require equality in `isReNewCid`; the `canIssue` disjunct already covers genuinely new values. |
| W4-7 | LOW | §5.1.2 L1811–1812: "Upon receipt of an increased Retire Prior To field, the peer MUST stop using the corresponding connection IDs…" | `Remote.lean` `Effect.stopUsing` doc ("§19.15, line 8011") and `Step.ncidOk` doc ("line 8011") | Line 8011 is blank (it is inside the page break before page 143). The sentence is §5.1.2 **line 1811** — a digit transposition, and the section is wrong too. The same sentence is cited correctly as "§5.1.2, line 1811" in the examples section 20 lines later. | s/§19.15, line 8011/§5.1.2, line 1811/ in both places. |

Everything else in the range is cited correctly: §5.1 L1644; §5.1.1 L1703, 1709, 1712, 1721, 1722, 1743, 1766; §5.1.2 L1779, 1781, 1806, 1823, 1831; §19.15 L7959, 7966, 7970, 7974, 7979, 7985, 7993, 7998, 8013; §19.16 L8046, 8050, 8055; §12.4 L4936 — all verified line by line.

### Probes (`out/probe_wp4.lean`, `lake env lean` exit 0)

W4-1 — the whole chain is model-permitted, and the last step is the defect:

```lean
def sA : Local.State :=
  { nextSeq := 1, issued := [⟨0, [1], tok 0⟩], retired := [], peerLimit := 2,
    zeroLen := false, sentRetirePriorTo := 0 }
def sB : Local.State := (Local.component.step sA (.issueCid [2] (tok 2) 0)).next sA
def sC : Local.State := (Local.component.step sB (.issueCid [3] (tok 3) 2)).next sB

example : Local.component.step sA (.issueCid [2] (tok 2) 0) ≠ .drop := by decide
example : Local.component.step sB (.issueCid [3] (tok 3) 2) ≠ .drop := by decide
example : sC.issued = [⟨0, [1], tok 0⟩, ⟨1, [2], tok 2⟩, ⟨2, [3], tok 3⟩]
    ∧ sC.retired = [] ∧ sC.sentRetirePriorTo = 2 ∧ sC.nextSeq = 3 := by decide

-- we told the peer to retire everything below 2, so it holds exactly {seq 2}.
-- Issuing seq 3 with rpt 0 leaves it with two = its limit.  The model refuses:
example : Local.component.step sC (.issueCid [4] (tok 4) 0) = .drop := by decide
example : Local.component.maySend sC (.newConnectionId 3 0 (bs [4]) (bs (tok 4))) = false := by decide
-- what the model counted vs. what the text says the peer holds:
example : sC.peerActiveAfter 0 = 4 := by decide
example : (sC.issued.filter
    (fun e => decide (Nat.max sC.sentRetirePriorTo 0 ≤ e.seq ∧ e.seq ∉ sC.retired))).length + 1
      = 2 := by decide
-- re-sending the Retire Prior To we already sent gets through, so a sender that
-- keeps rpt monotone (ngtcp2 does) will not hit this in the differential run:
example : Local.component.step sC (.issueCid [4] (tok 4) 2) ≠ .drop := by decide
```

W4-2 — the L1826 MAY has no permitted outcome:

```lean
example : Remote.component.accepts r0 (.recvNewCid 2 2 [3] (tok 3))
    (.error .connectionIdLimitError) = false := by decide
```

W4-3 — declining to issue when `canIssue` holds is not permitted:

```lean
example : Local.component.outcomes sA (.issueCid [2] (tok 2) 0)
    = [.ok ((Local.applyIssue sA [2] (tok 2) 0).1) ((Local.applyIssue sA [2] (tok 2) 0).2)] := by decide
example : Local.component.accepts sA (.issueCid [2] (tok 2) 0) .drop = false := by decide
```

W4-5 / W4-6:

```lean
example : Remote.component.step r1 (.recvNewCid 7 0 [9] [1, 2, 3])
    ≠ .error .frameEncodingError := by decide            -- 3-byte reset token accepted
example : Local.component.maySend sB (.newConnectionId 1 0 (bs [2]) (bs (tok 2))) = true := by decide
example : Local.component.maySend sB (.newConnectionId 1 1 (bs [2]) (bs (tok 2))) = true := by decide
```

### Checked and found correct

- The zero-length mirror pair is read correctly and is the *non-obvious* reading:
  §19.15 L7970 (send) ↔ `Local.zeroLen`, L7974 (receive) ↔ `Remote.peerZeroLen`;
  §19.16 L8055 (send) ↔ `Remote.peerZeroLen`, L8056 (receive) ↔ `Local.zeroLen`.
  NOTES 1 gives the right justification ("the Destination Connection ID an endpoint
  *sends* is one its *peer* issued"). Probed in all four directions.
- §19.15 L7985 `conflicts` matches the sentence exactly — all three triggers (same CID with a
  different token, same CID with a different sequence number, same sequence number with
  different CIDs) and nothing more; both alternatives of the MAY are permitted and nothing
  else is (`accepts … .error .frameEncodingError = false`).
- §19.15 L7979 repeats: an exact repeat is `.ok s []` however many times, including after the
  entry has been retired by a Retire Prior To (probe P4-D, three copies).
- §19.15 L7998 `Nat.max` and `rpt_mono`: a smaller Retire Prior To leaves `retirePriorTo`
  where it was (probe P4-F).
- §19.15 L8013: a newly received connection ID below the standing Retire Prior To is added and
  retired in the same step, producing `stopUsing`+`queueRetire`; already-retired sequence
  numbers produce nothing ("unless it has already done so"). Both probed. NOTES 5's reading
  (add then retire, rather than never add) is the one that keeps L8013's "unless" decidable —
  correct call.
- §5.1.1 L1743 CONNECTION_ID_LIMIT_ERROR is the *only* outcome when the post-processing active
  count exceeds the limit, and the L1722 escape hatch works (same frame with a large enough
  Retire Prior To is accepted). Both probed at the boundary (`limit = 2`).
- §19.16 L8046 boundary: `n = nextSeq - 1` accepted, `n = nextSeq` → PROTOCOL_VIOLATION.
- §19.16 L8050 MAY: exactly two outcomes, error preferred.
- Retransmission (rule 3): `Remote.MaySend` accepts a RETIRE_CONNECTION_ID for an
  already-retired sequence number; `Local.isReNewCid` accepts a re-issued NEW_CONNECTION_ID
  whose sequence number is no longer `nextSeq`. Both probed.
- Both `MaySend`s are `True` on the frame the other half owns (`remote_maySend_newCid`,
  `local_maySend_retireCid`), so conjunction composes.
- Named theorem statements match their doc comments and are not vacuous:
  `Remote.active_le_limit` (a) with `limit_const` to pin down what "the limit" means;
  `{Remote,Local}.seq_unique` (b) — hypothesis is `Inv`, which holds of a realistic initial
  state (`entries = [seq 0]` or `[seq 0, seq 1]`, `activeCount ≤ limit` with limit ≥ 2);
  `retired_never_active` (c) is stated over `Reachable`, which is the right strength;
  `rpt_mono` / `sent_rpt_mono` (d); `Local.issue_seq_succ` pins §5.1.1 L1704's "MUST increase
  by 1"; `issue_respects_peer_limit` is real but is the statement W4-1 undermines.
- The `ConnIds.lean` counterexample section is honest and correct: under the lenient
  alternative of L7985 one connection ID can end up under two sequence numbers, and it says so.
- A peer that skips sequence numbers on receipt is accepted — correct, §5.1.1 L1704 is a
  send-side MUST with no receiver-side error code attached.

### Modelling choices worth flagging for composition

- `Remote.entries` and `Local.issued` only ever grow (NOTES 3). Justified by §5.1.2 L1826, but
  it makes both states unbounded; WP12/WP13 should not compare them structurally against an
  implementation that prunes.
- `Remote`'s `.drop` for a local `retireCid` of an unknown/already-retired sequence number is
  indistinguishable from `.ok s []` to the harness — fine, since it is a local event, but it
  means `trackSet` will never shrink on it.
- `Local.Event.recvRetireCid` carries `dcidSeq`, which WP12 must supply from the packet header;
  §19.16 L8050's *send-side* MUST NOT is correctly deferred to WP12 (the packet being
  assembled is not visible here).
- `Local.State.sentRetirePriorTo` is currently write-only outside `Recommended`; fixing W4-1
  gives it a second reader and makes the field earn its place.

---

## WP2 — Stream (§2, §3 lines 641–1292; §4.1 lines 1315–1385 stream-level; §4.4, §4.5 lines 1461–1526)

Files: `QuicModel/Spec/Stream.lean`, `Stream/{Send,Recv}.lean`.
Probes: `out/probe_wp2.lean`, `out/probe_wp2b.lean` (both re-run by the reviewer, exit 0).

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| W2-1 | HIGH | §4.1 L1368 "A receiver MUST close the connection with a FLOW_CONTROL_ERROR error if the sender violates the advertised connection or stream data limits." vs §4.5 L1517/L1520 "Once a final size for a stream is known, it cannot change.  If a RESET_STREAM or STREAM frame is received indicating a change in the final size for the stream, an endpoint SHOULD respond with a FINAL_SIZE_ERROR error" | `Stream/Recv.lean` `outcomes` for `.recvResetStream`, `Step.resetFlowControl` / `Step.resetFinalSize` | The `if`-chain tests flow control **before** final size, so a RESET_STREAM whose Final Size both exceeds the advertised stream credit and contradicts a known final size has **only** FLOW_CONTROL_ERROR permitted. The text gives no precedence (one MUST, one SHOULD, both applicable), and ngtcp2 — the implementation this is differentially tested against — returns FINAL_SIZE_ERROR for exactly this input: `conn_recv_reset_stream` checks `SHUT_RD`/`last_offset != final_size` (`lib/ngtcp2_conn.c:7889-7894`) *before* `rx.max_offset < final_size` (`:7906`). **Reviewer verified both the Lean probe and the ngtcp2 source.** This will fire as a false differential violation. | Emit `.error .finalSizeError` alongside `.error .flowControlError` in `outcomes` when `resetFinalSizeViolation s fs` also holds. The `.recvStream` path already matches ngtcp2's order (`:7596` before `:7601`), so only RESET_STREAM diverges. |
| W2-2 | HIGH | §13.3 L5393 "An endpoint **SHOULD** stop sending MAX_STREAM_DATA frames when the receiving part of the stream enters a \"Size Known\" or \"Reset Recvd\" state"; §13.3 L5390 "an updated value is sent when the packet containing the most recent MAX_STREAM_DATA frame for a stream is lost"; §3.1 L971 "The endpoint can safely ignore any MAX_STREAM_DATA frames it receives from its peer for a stream in this state." | `Stream/Recv.lean` `maySendMaxStreamData` (`:= s.phase.isRecv`), `Step.sendMaxStreamDataForbidden` | §3.3's "the receiver only sends MAX_STREAM_DATA in the Recv state" is descriptive and §13.3 restates it as a SHOULD; §3.1 L971 shows the text expects such frames to arrive after the FIN. The model makes it absolute: `maySend = false` and the `sentMaxStreamData` event `.drop`s, so the model will not follow an implementation that conformingly **retransmits a lost MAX_STREAM_DATA** after the peer's FIN arrived. Violates both "a SHOULD that recommends must not make `Step` reject the alternative" and "`MaySend` must accept an exact repeat". | Relax `maySendMaxStreamData`; move "only in Recv" into `Recommended`; keep `Step.sendMaxStreamData`'s `max` update available in every phase. |
| W2-3 | MEDIUM | §3.2 L1082 "In the \"Recv\" state, the endpoint receives STREAM and STREAM_DATA_BLOCKED frames"; §4.1 L1368's FLOW_CONTROL_ERROR MUST is not obviously inapplicable to STREAM_DATA_BLOCKED's Maximum Stream Data field | `Stream/Recv.lean` `Step.blocked` | Unconditionally `.ok s []` with no hypotheses: no bound on `limit` (not even 2^62−1) and no error alternative. ngtcp2's `conn_recv_stream_data_blocked` (`lib/ngtcp2_conn.c:8536-8595`) returns FLOW_CONTROL_ERROR when `rx.max_offset < max_stream_data` and FINAL_SIZE_ERROR when the stream is `SHUT_RD`, so `accepts` is `false` for the reference implementation. | Add the two error alternatives, or state in the coverage table that §19.13's handling belongs to WP3 and `Step.blocked` is deliberately permissive-only. Neither is currently said. |
| W2-4 | MEDIUM | §3.1 L971–973 "MAX_STREAM_DATA frames might be received until the peer receives the final stream offset.  The endpoint **can safely ignore** any MAX_STREAM_DATA frames it receives from its peer for a stream in this state." | `Stream/Send.lean` `Step.maxStreamDataIgnored` / `Step.maxStreamDataRaise` (guard `s.phase.beforeFin`) | "can safely ignore" is a permission; the model makes ignoring **mandatory** in `dataSent`/`resetSent`/`dataRecvd`/`resetRecvd`. An implementation that processes the frame (raising `maxData`, emitting `creditAvailable`) is conforming but rejected by `accepts`. The NOTES claim the two readings are indistinguishable — they are not, because `creditAvailable` is part of the observation. | Add `Step.maxStreamDataRaise` as a second permitted outcome whenever `s.maxData < v`, in any phase, keeping the ignoring outcome first so `component.step` is unchanged. |
| W2-5 | MEDIUM | §3.5 L1259–1261 "If any outstanding data is declared lost, the endpoint SHOULD send a RESET_STREAM frame instead of retransmitting the data."  §3.5 L1265–1267 "An endpoint that sends a STOP_SENDING frame MAY ignore the error code in any RESET_STREAM frames subsequently received for that stream." | `Stream/{Send,Recv}.lean` §10 coverage tables | Neither sentence has a coverage row, a `Step` constructor, a `Recommended` clause, or an out-of-scope declaration. (The first appears in Send.lean's NOTES prose but not in the table.) Rule 4 violation. | Add rows: L1259 → `Recommended` / "advice, not encoded"; L1265 → permissive, already satisfied (`Recv` never inspects a received RESET_STREAM's code). |
| W2-6 | MEDIUM | §13.3 L5359 "The content of a RESET_STREAM frame MUST NOT change when it is sent again." | `Stream/Send.lean` `maySendReset` (`_code` ignored) | Pins the Final Size but not the error code, so a retransmitted RESET_STREAM may carry a different application error code. §13.3 is outside WP2's assigned range — the lead should place this with WP3 or back here, but somebody must own it. | `maySendReset` should require `s.resetCode = none ∨ s.resetCode = some code` once the phase is `resetSent`. |
| W2-7 | MEDIUM | §3.5 L1243 "the transport SHOULD signal this by sending a STOP_SENDING frame"; §4.1 L1376 / L1382 "A sender SHOULD send a STREAM_DATA_BLOCKED or DATA_BLOCKED frame…" / "…SHOULD periodically send…" | `Stream/Recv.lean` `Recommended`; `Stream/Send.lean` and `Stream.lean` (none) | `Recommended` exists only in `Recv.lean` and covers only §4.5's two FINAL_SIZE_ERROR SHOULDs. The other SHOULD-that-recommends sentences in range are dropped as "advice, not encoded" rather than recorded. `Send.lean` and the composite have no `Recommended` at all, so the composite cannot express any recommendation. | Add a `Recommended` to `Send.lean` covering §4.1 L1376/L1382 and §3.5 L1259; lift both halves' into `Stream.lean`. |
| W2-8 | MEDIUM | §3.2 L1101–1103, L1135–1137: "Data Read" and "Reset Read" are terminal | `Stream.lean` `terminal_absorbing` (doc: "**(c) Terminal states absorb**, on both halves") | The two conjuncts have different strength: the send conjunct proves `ss' = ss`, the recv conjunct only `rs'.phase = rs.phase`. In `dataRead` a late STREAM frame below the final size still changes `ranges` and `highest` (probe P12). Deliberate (§3.5 L1250 accounting) and documented in `Recv.terminal_absorbing`, but `Stream.lean`'s doc claims more than the theorem gives — a named theorem weaker than advertised. | Reword: "the send half freezes entirely; the receive half's *phase* freezes while flow-control accounting continues (§3.5 L1250)". |
| W2-9 | LOW | §3.4 Note (*1) L1222–1224 "A stream is considered \"idle\" if it has not yet been created, or if the receiving part of the stream is in the \"Recv\" state **without yet having received any frames**." | `Stream.lean` `Recv.untouched`, `State.composite` | Wrong in both directions: (a) after *receiving* a STREAM_DATA_BLOCKED the stream is still `.idle`; (b) after *sending* a STOP_SENDING — no frame received — it is `.openStream`, because `untouched` tests `rs.stopSending.isNone`, which `sentStopSending` also sets. | Track "a frame has been received" with an explicit `Bool` set by the three receive events; drop `stopSending.isNone` from `untouched`. |
| W2-10 | LOW | many | all three files' doc comments and coverage tables | Systematic line-number drift, worst around −34 through §3.3. Cited → actual: §2.4 811/815/818 → **801/805/808**; §3 866/892 → **832/859**; §3.1 927→**940**, 944→**971**, 947→**975**, 949/973→**976/991**, 962→**979**, 968→**986**; §3.2 1062→**1082**, 1066→**1089**, 1071→**1095**, 1076→**1101**, 1081→**1105**, 1084→**1109**, 1090→**1127**, 1092→**1130**, 1096→**1135**; §3.3 1105/1112/1114/1116/1118/1120/1121/1123 → **1141/1146/1147/1150/1161/1153/1156/1157**; §3.4 1130/1133/1140 → **1166/1164/1168**; §3.5 1219→**1243**, 1246→**1250**, 1258→**1254**, 1266→**1263**, 1273→**1269**, 1284→**1273**; §4.1 1357→**1364**, 1359→**1368**, 1361→**1372**, 1370→**1376**; §4.4 1462/1466→**1467/1471**; §4.5 1516→**1517**, 1519→**1520**, 1521→**1522**. Three of the wrong ones are error-code rules: §4.1 1359 (FLOW_CONTROL_ERROR), §4.1 1361 (MUST ignore), §4.5 1519/1521 (FINAL_SIZE_ERROR). Correct as cited: §4.1 1330, 1349; §4.5 1479, 1486, 1489, 1493, 1496, 1499; and **every** §19 citation (7431, 7474, 7476, 7638, 7684, 7686, 7736, 7864). | Re-derive all §2–§4 numbers from the shipped draft; §19 is already right. |
| W2-11 | LOW | §2.2 L744–746 "QUIC makes no specific allowances for delivery of stream data out of order.  However, implementations MAY choose to offer the ability to deliver data out of order to a receiving application." | `Stream/Recv.lean` §10 coverage table | A MAY in range with no row. Harmless — `Step.read` permits reading only the contiguous prefix, the conservative reading — but undeclared. | Add a row: "out of scope: an API choice; `Step.read` models in-order delivery only". |

### Probes (`out/probe_wp2.lean`, `out/probe_wp2b.lean`; both compile, so every `example` is a true statement about the model)

W2-2 — the identical MAX_STREAM_DATA frame goes from permitted to forbidden purely because the peer's FIN arrived:

```lean
private def r0 : Recv.State := Recv.init ⟨1⟩ .client 100
private def rSize : Recv.State :=
  { r0 with phase := .sizeKnown, highest := 10, ranges := [(5, 10)], finalSize := some 10 }

example : Recv.component.maySend r0    (.maxStreamData 1 200) = true  := by decide
example : Recv.component.maySend rSize (.maxStreamData 1 200) = false := by decide
example : Recv.component.step rSize (.sentMaxStreamData 200) = .drop := by decide
example : Recv.component.accepts rSize (.sentMaxStreamData 200)
    (.ok { rSize with maxData := 200 } []) = false := by decide
```

W2-1 — `rSize` has `finalSize = 10`, `maxData = 100`; FINAL_SIZE_ERROR is not permitted:

```lean
example : Recv.component.accepts rSize (.recvResetStream 3 150)
    (.error .finalSizeError) = false := by decide      -- only FLOW_CONTROL_ERROR is permitted
example : Recv.component.step rSize (.recvStream 0 150 true) = .error .flowControlError := by decide
example : Recv.component.accepts rSize (.recvStream 0 (2 ^ 62) true)
    (.error .finalSizeError) = false := by decide
```

W2-4 — processing a MAX_STREAM_DATA after the FIN is rejected:

```lean
private def sSent : Send.State :=
  { s0 with phase := .dataSent, written := 5, finWritten := true, sent := 5, finalSize := some 5 }
example : Send.component.step sSent (.recvMaxStreamData 200) = .ok sSent [] := by decide
example : Send.component.accepts sSent (.recvMaxStreamData 200)
    (.ok { sSent with maxData := 200 } [.creditAvailable 200]) = false := by decide
```

W2-6, W2-3, W2-9, W2-12 respectively:

```lean
private def sR : Send.State := (Send.component.step s0 (.sentResetStream 7 0)).next s0
example : Send.component.maySend sR (.resetStream 0 7  0) = true := by decide
example : Send.component.maySend sR (.resetStream 0 99 0) = true := by decide  -- code changed

example : Recv.component.step r0 (.recvStreamDataBlocked 10000) = .ok r0 [] := by decide
example : Recv.component.accepts r0 (.recvStreamDataBlocked 10000)
    (.error .flowControlError) = false := by decide
example : Recv.component.accepts r0 (.recvStreamDataBlocked (2 ^ 62))
    (.error .frameEncodingError) = false := by decide

example : biC.composite = some .idle := by decide
example : ((component.step biC (.recv (.recvStreamDataBlocked 50))).next biC).composite
    = some .idle := by decide          -- a frame WAS received, still "idle"
example : ((component.step biC (.recv (.sentStopSending 3))).next biC).composite
    = some .openStream := by decide    -- no frame received, no longer "idle"
```

### Checked and found correct

- **§19 direction rules.** `Stream.Step.sendMissing` / `recvMissing` give STREAM_STATE_ERROR exactly for the receive-only/send-only cases of §19.4 L7431, §19.5 L7476, §19.8 L7638, §19.10 L7736, §19.13 L7864; all five citations verified; `hasSend`/`hasRecv` match Table 1 for all four stream types × both roles. Probed both directions.
- **§19.8 L7684–7686 boundary.** `maxOffset = 2^62 − 1`; `offset+len = 2^62−1` accepted, `2^62` errors with *both* FRAME_ENCODING_ERROR and FLOW_CONTROL_ERROR permitted — the "either code" sentence modelled correctly. Same for RESET_STREAM's Final Size.
- **§4.1 L1368 stream-credit boundary.** `offset+len = maxData` accepted, `maxData+1` is FLOW_CONTROL_ERROR with no non-error alternative (correct: MUST).
- **§4.5's SHOULDs are genuinely optional** — the best-handled SHOULD in the whole group. `Step.streamFinalSizeIgnored`/`resetFinalSizeIgnored` are available in *every* phase, the error stays first in `outcomes`, and `Recommended` + `step_recommended` + `error_permitted_of_not_recommended` state the relationship precisely.
- **§4.5 L1517 final-size immutability** — `finalSize_immutable` on both halves and the composite, non-vacuous, covers all `.ok` constructors; the extra "FIN below `highest`" disjunct in `finalSizeViolation` is a defensible reading and is documented.
- **§3.3 L1146/1147 send prohibitions** — `no_send_from_terminal`, `no_data_after_reset`: correct and non-vacuous; RESET_STREAM correctly stays sendable from "Reset Sent" with the final size pinned, so exact-repeat retransmission works for RESET_STREAM and for STREAM/STREAM_DATA_BLOCKED while `mayCarryData`.
- **§13.3 L5409** — `maySendBlocked`'s `limit = s.maxData` requirement *looks* like it breaks exact-repeat retransmission (a repeat is rejected) but is correct: §13.3 says these frames "always include the limit that is causing blocking at the time that they are transmitted". Not a finding.
- **Figures 2 and 3** — every arrow has an example; `Reaches` / `step_follows_diagram` are real closures of `Arrow` and non-vacuous. The optional arrows (Data Recvd ↔ Reset Recvd) are genuine alternative outcomes with distinguishable effects, so `track` still works.
- Duplicate and overlapping STREAM frames are idempotent (`insertRange`/`addRange`), probed including a three-event write/send/re-send sequence returning to the same state.
- `Inv` on both halves is satisfied by `init` for every role and direction and is not over-strong; `step_inv` covers all `.ok` constructors. `MaySend` is `True` for other streams' frames and for frame types the half does not govern, on both halves and the composite.

### Modelling choices worth flagging for composition

- `.drop` vs `.ok s []`: refused *application* calls are `.drop` (`writeRefused`/`endRefused`/`resetRefused`/`readRefused`/`readResetRefused`) and refused *transmission* events are `.drop` too, while "the frame is ignored" is `.ok s []`. WP13 must use `Obs.matchesLoosely`; note that `sendMaxStreamDataForbidden`/`sendStreamForbidden` being `.drop` means a spec-violating *send* is caught only by `maySend`, never by `Step`.
- Receive-side state keeps growing in a terminal phase (`highest`, `ranges`, `read`), so `Recv.State` equality is a poor proxy for "stream finished"; the composite's `simpleClosed`/`composite` read only phases.
- `Send.written` vs `Send.sent`: `maySendStream` requires `offset+len ≤ written`, so the harness must feed `appWrite` events before it can accept any STREAM frame ngtcp2 emits — a source of spurious `maySend = false` unless WP13 synthesises writes.
- Both halves carry `id` and `role` redundantly with the composite; `Stream.Inv` keeps the three copies in sync and WP9/WP12 must preserve that.

---

## WP3 — FrameRules / Ack (§12.3–12.5 lines 4634–4988; §13.1–13.2 lines 5018–5324)

Files: `QuicModel/Spec/FrameRules.lean`, `QuicModel/Spec/Ack.lean`.
Probes: `out/probe_wp3.lean`, `out/probe_wp3b.lean` (both re-run by the reviewer, exit 0).

This is the best-cited package of the four: every one of ~35 citations checked resolves to
the sentence quoted, and **Table 3 is reproduced exactly** — all 20 rows × 4 packet types
plus both CONNECTION_CLOSE variants confirmed by `decide`. The findings are about
permissiveness and the §13.2 timing definitions, not the legality table.

### Findings

| id | sev | text (§, line) | Lean | what is wrong | suggested fix |
|---|---|---|---|---|---|
| W3-1 | HIGH | §12.3 L4717–4719: "The data required for detecting duplicates **can be limited by maintaining a minimum packet number below which all packets are immediately dropped**." | `Ack.lean` `outcomes` / `Step.process` / `Step.duplicate` | For a packet number not in `received`, `outcomes` offers **only** `.ok (s.record …) [.processed …]`; `.drop` is not permitted. An implementation keeping a minimum packet number — explicitly sanctioned inside the assigned range — is rejected by `accepts` and empties `trackSet`. NOTE 3 mentions the divergence but states it in the *opposite* direction ("would accept a packet this model drops") and does not encode the permitted alternative. | Add `minPn : Nat` to `State` plus `Step.belowMinimum {s pn t ae} (h : pn < s.minPn) : Step s (.recvPacket pn t ae) .drop`, appending `.drop` to `outcomes` in that case. `processed_at_most_once` survives. Failing that, state in NOTE 3 that the model is deliberately *stricter* here so the harness special-cases it. |
| W3-2 | MEDIUM | §12.5 L4976–4980: "Note that it is not possible to send the following frames in 0-RTT packets…: ACK, CRYPTO, HANDSHAKE_DONE, NEW_TOKEN, PATH_RESPONSE, and RETIRE_CONNECTION_ID.  A server **MAY** treat receipt of these frames in 0-RTT packets as a connection error of type PROTOCOL_VIOLATION." | `FrameRules.lean` `mustReject`, `mayReject`, `outcomes` | For five of the six, Table 3 excludes 0-RTT so `mustReject` fires via §12.4 L4901–4903's MUST and the model permits **only** the error; RETIRE_CONNECTION_ID is `__01` in Table 3 so it gets both outcomes. The draft contradicts itself (L4901's MUST vs L4978's MAY, and L4961's "PADDING, PING, and CRYPTO frames MAY appear in any packet number space" — 0-RTT *is* the appData space). **Reviewer confirmed the contradiction is in the draft, not in the model**; the model's Table-3-plus-MUST reading is defensible but undeclared: NOTE 1 explains the RETIRE_CONNECTION_ID choice without saying the other five are stricter than L4978. | Extend NOTE 1 to say L4901–4903 + Table 3 are read as overriding L4978 for the five, and that WP13 must expect a mismatch if ngtcp2 accepts them. (Alternatively demote all six to `mayReject` for a uniform `[.ok …, .error …]`.) |
| W3-3 | MEDIUM | §13.2.1 L5075: "An endpoint MUST acknowledge all ack-eliciting Initial and Handshake packets immediately and all ack-eliciting 0-RTT and 1-RTT packets within its advertised max_ack_delay" | `Ack.lean` `ackDeadline`, `AcknowledgedInTime` | (a) The deadline is anchored to `s.largestTime` — arrival of the largest packet *of any kind* — so a later **non**-ack-eliciting packet pushes the deadline for an already-pending ack-eliciting packet arbitrarily far out (probe: 25100 µs → 925000 µs). (b) For Initial/Handshake the deadline is `s.largestTime` exactly, so `AcknowledgedInTime s sentAt` requires `sentAt ≤` the instant of arrival — unsatisfiable by any real endpoint. The named predicate is therefore vacuously unusable for two of the four spaces. | Track `oldestPendingAckElicitingTime : Option Time`, reset on `sentAck`, and anchor to it; express "immediately" for Initial/Handshake as a slack parameter or as "before any other packet is sent", not `≤ t`. |
| W3-4 | MEDIUM | §12.4 L4740: "The payload of a packet that contains frames MUST contain at least one frame" | `FrameRules.lean` `component` (no `MaySendPacket`) | Encoded receive-side only (`Step.packetEmpty`). `MaySendPacket` is left at the default `fun _ _ => True`, so the model lets *us* send a frameless packet. BRIEF: whole-packet rules belong in `MaySendPacket`. | `MaySendPacket s p := p.frames ≠ [] ∧ ∀ f ∈ p.frames, allowedIn f p.ptype`. The second conjunct matters because it sees the real `ptype` rather than the `assembling` shadow state. |
| W3-5 | MEDIUM | coverage-table completeness (rule 4) | `FrameRules` / `Ack` §10 tables | Six sentences in range have no row: §12.3 L4659 (VN/Retry carry no packet number); §12.4 L4744 ("Frames always fit within a single QUIC packet and cannot span multiple packets"); §13.2.1 L5128 (MAY wait for an ack-eliciting packet — only in a doc comment); §13.2.3 L5192 (SHOULD stop tracking acknowledged ACK Ranges) and L5201 (MAY limit ACK frame size further); §13.2.5 L5286 (SHOULD report measured delay above max_ack_delay). None is a MUST. | Add rows marked `Recommended` / permissive / out-of-scope. L5192 should point at NOTE 3, since the model never prunes. |
| W3-6 | MEDIUM | §13.2.1 L5064: "Every packet SHOULD be acknowledged at least once" | `Ack.lean` `Recommended` | Only the MUST half of L5064 is modelled (via `ackDeadline`). The SHOULD half — every packet, including non-ack-eliciting, eventually acknowledged — is absent from `Recommended` and not declared out of scope; the coverage row points only at `ackDeadline`/`AcknowledgedInTime`. | Add a `Recommended` clause / trace-level `EventuallyAcknowledged`, or declare it out of scope as a liveness property. |
| W3-7 | LOW | §13.2 L5052: "…SHOULD attempt to include an ACK frame **if one has not been sent recently**." | `Ack.lean` `Recommended.withOtherFrames` | The guard is `s.ackElicitingPending = true`, which is the guard of the *other* cited sentence (L5125). "not been sent recently" is a distinct time-based condition, nowhere represented. Harmless (outside `Step`) but two sentences are conflated under one clause. | Split into two clauses, or note the approximation. |
| W3-8 | LOW | §13.2.5 L5280: "An endpoint MUST NOT include delays that it does not control when populating the ACK Delay field" | `Ack.lean` `AckDelayOk` | `delay ≤ now − s.largestTime` is *necessary* (you cannot report more delay than has elapsed) but is not the stated requirement (only *intentional* delay). The model is looser; not recorded in NOTES. | Keep it; add a NOTE that it is a sound over-approximation because uncontrolled delay is unobservable in the model. |
| W3-9 | LOW | §12.3 L4693: "If the packet number for sending reaches 2^62 − 1, the sender MUST close the connection without sending … any further packets" | `Ack.lean` `maySendPacketNumber`, `maxPn` | `pn ≤ maxPn = 2^62−1` permits sending 2^62−1 itself. Whether "reaches" means that number is still usable or is already the stop point is ambiguous; the reading chosen is not in NOTES. | One NOTES line stating the reading. |

### Probes (`out/probe_wp3.lean`, `out/probe_wp3b.lean`)

W3-1 — a fresh packet may not be dropped:

```lean
example : Ack.component.outcomes a0 (.recvPacket 7 100 true)
    = [.ok (a0.record 7 100 true) [.processed 7 true]] := by decide
example : Ack.component.accepts a0 (.recvPacket 7 100 true) .drop = false := by decide
```

W3-2 — CRYPTO in 0-RTT has only the error outcome, RETIRE_CONNECTION_ID has both:

```lean
example : FrameRules.component.outcomes srv (.recvFrame .zeroRtt (.crypto 0 .empty))
    = [.error .protocolViolation] := by decide
example : FrameRules.component.accepts srv (.recvFrame .zeroRtt (.crypto 0 .empty))
    (.ok srv [.deliver (.crypto 0 .empty)]) = false := by decide
example : FrameRules.component.outcomes srv (.recvFrame .zeroRtt (.retireConnectionId 0))
    = [.ok srv [.deliver (.retireConnectionId 0)], .error .protocolViolation] := by decide
```

W3-3 — (a) a non-ack-eliciting packet moves the ACK deadline; (b) `AcknowledgedInTime` is
unsatisfiable for Initial/Handshake:

```lean
private def b0 : Ack.State := a0.record 5 100 true       -- ack-eliciting, t = 100
private def b1 : Ack.State := b0.record 6 900000 false   -- non-ack-eliciting, t = 900000
#eval Ack.ackDeadline b0   -- some 25100
#eval Ack.ackDeadline b1   -- some 925000

private def i1 : Ack.State := i0.record 0 1000 true      -- Initial space
example : Ack.ackDeadline i1 = some 1000 := by decide
example : ¬ Ack.AcknowledgedInTime i1 1001 := by
  intro h; have h2 : (1001 : Nat) ≤ 1000 := h 1000 (by decide); exact absurd h2 (by decide)
```

W3-4 — no packet-level send rule:

```lean
example : FrameRules.component.maySendPacket srv { ptype := .oneRtt, frames := [] } = true := by decide
example : FrameRules.component.maySendPacket srv
    { ptype := .initial, frames := [.stream 0 0 false .empty] } = true := by decide
```

### Checked and found correct

- **Table 3, exhaustively.** `pkts` matches all 20 rows across Initial / Handshake / 0-RTT /
  1-RTT, including `ACK = IH_1`, `CRYPTO = IH_1`, `NEW_TOKEN`/`PATH_RESPONSE`/`HANDSHAKE_DONE
  = ___1`, and the `CONNECTION_CLOSE` split `ih01` (0x1c, `frameType = some _`) vs `__01`
  (0x1d, `none`) — confirmed against `Frame.lean:47`. The `N`/`C`/`P`/`F` columns
  (`ackEliciting`, `inFlight`, `probing`, `flowControlled`) each match their marked rows;
  `probing` also agrees with §9.1's four-frame list.
- **Every citation checked resolves** — 4636, 4659, 4662, 4670, 4685, 4692, 4693, 4709, 4711,
  4731, 4740, 4742, 4886, 4897, 4901/4902, 4909, 4912, 4916, 4920, 4933, 4942, 4949, 4961,
  4964, 4966, 4969, 4971, 4973, 4976, 4978; 5020, 5026, 5030, 5047, 5048, 5052, 5064, 5075,
  5078, 5084, 5087, 5101, 5105, 5108, 5112, 5125, 5131, 5163, 5171, 5176, 5181, 5198, 5213,
  5218, 5223, 5271, 5280, 5282, 5293, 5298, 5307, 5311; plus the out-of-range 7236, 7300,
  7358, 7373, 7375, 7597, 8207. No misquote found — the only package for which that is true.
- **Error codes.** PROTOCOL_VIOLATION for frame-in-wrong-packet-type (L4902), empty payload
  (L4742), ack-of-unsent (L5030); FRAME_ENCODING_ERROR for a negative computed packet number
  (L7375). All four correct; `acked_isSome_iff_check` genuinely ties `acked` to the wire
  decoder's `Frame.check`.
- **§19.3.1 range arithmetic.** `acked`/`ackedAux` implement `smallest = largest − first`,
  `largest' = previous_smallest − gap − 2`, `smallest' = largest' − len`, with both underflow
  guards correctly placed. Boundaries probed: `acked 3 3 [] = some [⟨0,3⟩]`, `acked 3 5 [] =
  none`, `acked 2 0 [gap 0 len 0] = some [⟨2,2⟩,⟨0,0⟩]`, `acked 1 0 [gap 0 len 0] = none`.
- **SHOULDs are in `Recommended`, not `Step`.** §13.1 L5030 correctly offers both
  `.error .protocolViolation` and `.ok s []`. `Recommended` is satisfiable (`sendAckNow = true`
  discharges all three clauses) and constrains nothing in `Step`; `RecommendedAck` is
  equivalent to L5223 given that only received packets may be acknowledged.
- **Retransmission / idempotence (rule 3).** `FrameRules.MaySend` depends only on
  `(role, assembling)`, so repeats are trivially fine. `Ack.MaySend` depends on `received`,
  which `received_mono` proves only grows — an ACK accepted in `a1` is still accepted in `a2`
  after two more packets. An ACK spanning a gap in `received` is refused; the same packets as
  two proper ranges are accepted.
- **Named theorems say what they claim.** `maySend_ack_sound` is the promised "ACK never
  acknowledges an unreceived pn" and is non-vacuous; `processed_at_most_once` is a genuine
  reachability statement; `allowedIn_oneRtt`/`_retry`/`_versionNegotiation` are total over
  `Frame`; the six §12.5-agreement theorems collectively discharge "the legality table matches
  §12.5 prose", and `coreFrame` is exactly the five frame types §12.5 singles out.
- `Inv` is not too strong (the natural initial state `received = []`, `largest = none`
  satisfies it) and `step_inv` covers every `.ok` constructor. `Ranges.insert` merges adjacent
  ranges correctly and preserves `wf`; `mem_insert` is the exact soundness statement.
  `State.outOfOrder` implements both bullets of L5101 against the pre-insert state with the
  `pn = m+1` boundary correctly `false`.
- Out-of-scope claims are supported: unknown frame type (L4933) and non-minimal frame type
  (L4942/4949) really are rejected by the decoder (`Err.unknownFrameType`,
  `Err.nonMinimalFrameType`, `QuicModel/Frame.lean:136,141`).

### Modelling choices worth flagging for composition

- `Ack.Step.duplicate` gives `.drop` and `Step.process` gives `.ok _ [.processed …]`, so
  `Obs.matchesLoosely` does *not* conflate them at the model level — but ngtcp2 exposes no
  "processed" callback, so at harness level the distinction vanishes and they *do* collapse.
  WP13 must decide how to map it.
- `assembling` is duplicated in `FrameRules.State` and `Ack.State`. `Ack.MaySend` checks only
  `assembling.space = some s.space`, which passes for `space = .appData, assembling = .zeroRtt`;
  it is `FrameRules.MaySend` (Table 3: ACK is `IH_1`) that refuses. Composition by conjunction
  saves it, but **neither component is individually correct about ACK-in-0-RTT**, so WP12 must
  keep both.
- `received` and `largest` only grow, nothing is pruned — this is what makes
  `processed_at_most_once` unconditional and is the root of W3-1.
- `FrameRules` models `recvFrame` and `recvPacketFrames` as independent events with
  overlapping rules; WP12 must pick one and not double-report the same PROTOCOL_VIOLATION.
- `Recommended`, `AcknowledgedInTime`, `AtMostOneAckOnly`, `NoAckOfNonAckEliciting`,
  `NotAlwaysAckEliciting` and `AckDelayOk` are free-standing trace predicates, not `Component`
  fields — nothing proves or checks them. To bind anything they need a trace-level harness in
  WP12/WP13.

---

## Cross-package observations for the lead

1. **`Recommended` is used inconsistently.** WP3 `Ack` has one; WP4 `Local` has one covering a
   single sentence; WP2 has one only in `Recv`, covering two sentences; WP1 has none. Several
   SHOULD-that-recommends sentences in range (W1-2, W2-7, W3-6) are simply dropped with the
   coverage-table phrase "advice only; not modelled", which is not what PLAN §1 asks for. Worth
   one ruling from the lead: either `Recommended` is mandatory for in-range SHOULDs, or the
   coverage table gets an explicit `advice, not modelled` category and the PLAN is amended.
2. **Line citations.** WP3 is clean. WP1 and WP2 have systematic drift (WP2 up to −34 lines,
   WP1 up to −35), in both cases including rules that carry an error code. WP4 has one
   transposition (8011 for 1811). All of it is mechanically fixable from the quoted substrings;
   none of it changes a `Step`.
3. **Four places where `Step`/`MaySend` is stricter than the text** (W4-1, W2-1, W2-2, W3-1)
   and none where it is looser in a way that admits a forbidden outcome. That asymmetry is
   worth knowing before WP13: the differential run against ngtcp2 tests exactly the
   too-strict direction, so all four are likely to fire as false violations. W2-1 is the one
   with a confirmed ngtcp2 divergence today.
4. **Three MAYs with no representation in `Step`** (W4-2, W4-3, W3-2 × 5 frames) plus one
   permission read as a prohibition (W2-4). Same failure mode each time: an alternative the
   text permits was collapsed into the preferred outcome.
