import QuicModel.Spec.ConnIds.Common

/-!
  §5.1.1 "Issuing Connection IDs", the send side of §19.15 NEW_CONNECTION_ID and
  the receive side of §19.16 RETIRE_CONNECTION_ID: one endpoint's view of the
  connection IDs *it issued to its peer*, which the peer uses as Destination
  Connection IDs when it sends to us.

  File order is `Spec/Template.lean`'s ten parts.
-/
namespace Quic.Spec.ConnIds.Local

/-! ## 1. State, events, effects -/

/-- The connection IDs we have issued.

`issued` starts with the initial connection ID (sequence number 0, sent in the
Source Connection ID field during the handshake) and, if we sent the
`preferred_address` transport parameter, the one with sequence number 1; those
come from the handshake (WP11) and are parameters of the initial state.  The
connection ID a client picks for its first Destination Connection ID and any
connection ID from a Retry packet have no sequence number (§5.1.1, line 1704)
and are deliberately not represented here. -/
structure State where
  /-- §5.1.1, line 1703: "The sequence number on each newly issued connection ID
      MUST increase by 1"; this is the number the next one gets. -/
  nextSeq : Nat
  /-- Every connection ID we have issued, with its sequence number. -/
  issued : List Entry
  /-- Sequence numbers the peer has retired with RETIRE_CONNECTION_ID. -/
  retired : List Nat
  /-- The peer's `active_connection_id_limit` transport parameter (§5.1.1,
      line 1721: "An endpoint MUST NOT provide more connection IDs than the
      peer's limit"). -/
  peerLimit : Nat
  /-- §5.1.1, line 1766: "An endpoint that selects a zero-length connection ID
      during the handshake cannot issue a new connection ID." -/
  zeroLen : Bool
  /-- The largest Retire Prior To value we have sent. -/
  sentRetirePriorTo : Nat
  deriving DecidableEq, Repr

namespace State

/-- Connection IDs we issued that the peer has not retired: §5.1.1, line 1709,
    "it MUST accept packets that carry this connection ID for the duration of
    the connection or until its peer invalidates the connection ID via a
    RETIRE_CONNECTION_ID frame". -/
def active (s : State) : List Entry :=
  s.issued.filter (fun e => decide (e.seq ∉ s.retired))

def activeCount (s : State) : Nat := s.active.length

/-- How many connection IDs the peer would hold active after a
    NEW_CONNECTION_ID with this Retire Prior To value: everything at or above
    `rpt` that it has not already retired, plus the one being issued. -/
def peerActiveAfter (s : State) (rpt : Nat) : Nat :=
  (s.issued.filter (fun e => decide (rpt ≤ e.seq ∧ e.seq ∉ s.retired))).length + 1

end State

inductive Event where
  /-- A RETIRE_CONNECTION_ID frame arrived (§19.16).  `dcidSeq` is the sequence
      number of the connection ID the carrying packet was addressed to, which
      §19.16 line 8050 needs; `none` when that connection ID has no sequence
      number (§5.1.1, line 1704). -/
  | recvRetireCid (seq : Nat) (dcidSeq : Option Nat)
  /-- We decide to issue a connection ID (§5.1.1, line 1702), with this Retire
      Prior To value.  Driven by the application or by §5.1.1 line 1749 ("An
      endpoint SHOULD supply a new connection ID when the peer retires a
      connection ID"). -/
  | issueCid (cid : Cid) (token : ResetToken) (rpt : Nat)
  deriving DecidableEq, Repr

inductive Effect where
  /-- Send a NEW_CONNECTION_ID frame (§19.15). -/
  | sendNewCid (seq rpt : Nat) (cid : Cid) (token : ResetToken)
  /-- The peer retired this connection ID: stop accepting packets that carry it,
      and §5.1.1 line 1749, consider issuing a replacement. -/
  | cidRetiredByPeer (seq : Nat)
  deriving DecidableEq, Repr

abbrev Out := Outcome State Effect

/-! ## 1b. The two transitions, as total functions -/

/-- Recording the peer's retirement.  A retransmitted RETIRE_CONNECTION_ID for a
    sequence number already retired changes nothing. -/
def applyRetire (s : State) (n : Nat) : State × List Effect :=
  if n ∈ s.retired then (s, [])
  else ({ s with retired := s.retired ++ [n] }, [.cidRetiredByPeer n])

/-- Every condition §5.1.1 and §19.15 put on issuing a connection ID.  The frame
    we would emit is `NEW_CONNECTION_ID(nextSeq, rpt, cid, token)`. -/
def canIssue (s : State) (cid : Cid) (token : ResetToken) (rpt : Nat) : Bool :=
  -- §5.1.1, line 1766 / §19.15, line 7970: not while our connection IDs are
  -- zero-length.
  !s.zeroLen &&
  -- §19.15, line 7959 and 7966: 1..20 bytes of connection ID, 128 bits of token.
  cidLenOk cid && tokenLenOk token &&
  -- §19.15, line 7993: "The Retire Prior To field MUST be less than or equal to
  -- the Sequence Number field."
  decide (rpt ≤ s.nextSeq) &&
  -- §19.15, line 7998: smaller values have no effect; we never send one.
  decide (s.sentRetirePriorTo ≤ rpt) &&
  -- §5.1, line 1644: "the same connection ID MUST NOT be issued more than once
  -- on the same connection".
  !s.issued.any (fun e => decide (e.cid = cid)) &&
  -- §5.1.1, line 1721: "An endpoint MUST NOT provide more connection IDs than
  -- the peer's limit.  An endpoint MAY send connection IDs that temporarily
  -- exceed a peer's limit if the NEW_CONNECTION_ID frame also requires the
  -- retirement of any excess, by including a sufficiently large value in the
  -- Retire Prior To field."
  decide (s.peerActiveAfter rpt ≤ s.peerLimit)

/-- Issuing: §5.1.1, line 1703, "The sequence number on each newly issued
    connection ID MUST increase by 1". -/
def applyIssue (s : State) (cid : Cid) (token : ResetToken) (rpt : Nat) :
    State × List Effect :=
  ({ s with nextSeq := s.nextSeq + 1,
            issued := s.issued ++ [⟨s.nextSeq, cid, token⟩],
            sentRetirePriorTo := rpt },
   [.sendNewCid s.nextSeq rpt cid token])

/-! ## 2. The specification -/

inductive Step : State → Event → Out → Prop
  /-- §19.16, line 8055: "An endpoint that provides a zero-length connection ID
      MUST treat receipt of a RETIRE_CONNECTION_ID frame as a connection error
      of type PROTOCOL_VIOLATION." -/
  | retireZeroLen {s n d} (hz : s.zeroLen = true) :
      Step s (.recvRetireCid n d) (.error .protocolViolation)
  /-- §19.16, line 8046: "Receipt of a RETIRE_CONNECTION_ID frame containing a
      sequence number greater than any previously sent to the peer MUST be
      treated as a connection error of type PROTOCOL_VIOLATION." -/
  | retireUnknown {s n d} (hz : s.zeroLen = false) (h : n ≥ s.nextSeq) :
      Step s (.recvRetireCid n d) (.error .protocolViolation)
  /-- §19.16, line 8050: "The sequence number specified in a
      RETIRE_CONNECTION_ID frame MUST NOT refer to the Destination Connection ID
      field of the packet in which the frame is contained.  The peer MAY treat
      this as a connection error of type PROTOCOL_VIOLATION."
      First alternative of the MAY. -/
  | retireSelf {s n d} (hz : s.zeroLen = false) (hn : ¬ n ≥ s.nextSeq) (h : d = some n) :
      Step s (.recvRetireCid n d) (.error .protocolViolation)
  /-- The frame is processed.  Reached whether or not it names the packet's own
      Destination Connection ID — taking the second alternative of the MAY above
      means processing it as usual. -/
  | retireOk {s n d} (hz : s.zeroLen = false) (hn : ¬ n ≥ s.nextSeq) :
      Step s (.recvRetireCid n d) (.ok (applyRetire s n).1 (applyRetire s n).2)
  /-- Issuing a connection ID, when everything §5.1.1 requires holds. -/
  | issueOk {s cid token rpt} (h : canIssue s cid token rpt = true) :
      Step s (.issueCid cid token rpt)
        (.ok (applyIssue s cid token rpt).1 (applyIssue s cid token rpt).2)
  /-- A local request to issue a connection ID that the text forbids is simply
      not carried out; nothing is sent and nothing changes. -/
  | issueRefused {s cid token rpt} (h : canIssue s cid token rpt = false) :
      Step s (.issueCid cid token rpt) .drop

/-! ## 3. Executable form -/

def outcomes (s : State) : Event → List Out
  | .recvRetireCid n d =>
    if s.zeroLen then [.error .protocolViolation]
    else if n ≥ s.nextSeq then [.error .protocolViolation]
    else if d = some n then
      [.error .protocolViolation, .ok (applyRetire s n).1 (applyRetire s n).2]
    else [.ok (applyRetire s n).1 (applyRetire s n).2]
  | .issueCid cid token rpt =>
    if canIssue s cid token rpt then
      [.ok (applyIssue s cid token rpt).1 (applyIssue s cid token rpt).2]
    else [.drop]

/-! ## 4. The two forms agree -/

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  constructor
  · intro h
    cases e with
    | recvRetireCid n d =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h
        exact .retireZeroLen (by simp_all)
      · have hz : s.zeroLen = false := by simp_all
        split at h
        · simp only [List.mem_singleton] at h; subst h; exact .retireUnknown hz ‹_›
        · have hn : ¬ n ≥ s.nextSeq := ‹_›
          split at h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .retireSelf hz hn ‹_›
            · exact .retireOk hz hn
          · simp only [List.mem_singleton] at h; subst h
            exact .retireOk hz hn
    | issueCid cid token rpt =>
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .issueOk (by simp_all)
      · simp only [List.mem_singleton] at h; subst h; exact .issueRefused (by simp_all)
  · intro h
    cases h with
    | retireZeroLen hz => simp [outcomes, hz]
    | retireUnknown hz hg => simp [outcomes, hz, hg]
    | @retireSelf n d hz hn hd => simp [outcomes, hz, hn, hd]
    | @retireOk n d hz hn =>
      by_cases hd : d = some n <;> simp [outcomes, hz, hn, hd]
    | issueOk hc => simp [outcomes, hc]
    | issueRefused hc => simp [outcomes, hc]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e <;> simp only [outcomes] <;> repeat' split
  all_goals simp

/-! ## 5. Invariant -/

/-- Sequence numbers are unique and below the next one to be handed out. -/
def Inv (s : State) : Prop :=
  (seqs s.issued).Nodup ∧ ∀ e ∈ s.issued, e.seq < s.nextSeq

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hn, hb⟩ := hi
  cases h with
  | @retireOk n d _ _ =>
    unfold applyRetire
    split
    · exact ⟨hn, hb⟩
    · exact ⟨hn, hb⟩
  | @issueOk cid token rpt _ =>
    refine ⟨?_, ?_⟩
    · show (seqs (s.issued ++ [⟨s.nextSeq, cid, token⟩])).Nodup
      simp only [seqs_append, seqs_singleton]
      exact nodup_append_singleton hn (fun hm => by
        obtain ⟨e, he, hes⟩ := mem_seqs.mp hm
        exact absurd (hes ▸ hb e he) (Nat.lt_irrefl _))
    · intro e he
      show e.seq < s.nextSeq + 1
      rcases List.mem_append.mp he with he | he
      · exact Nat.lt_succ_of_lt (hb e he)
      · rw [List.mem_singleton.mp he]; exact Nat.lt_succ_self _

/-! ## 6. Send side

This component owns NEW_CONNECTION_ID (§19.15); RETIRE_CONNECTION_ID belongs to
the other half, so it is unconstrained here. -/

/-- A NEW_CONNECTION_ID may be sent exactly when it is the frame `canIssue`
    describes: the next sequence number, a fresh connection ID of legal length,
    a Retire Prior To that is at most the sequence number and never smaller than
    one already sent, and a result that keeps the peer inside its
    `active_connection_id_limit`. -/
def MaySend (s : State) : Frame → Prop
  | .newConnectionId seq rpt cid token =>
    seq = s.nextSeq ∧ canIssue s cid.data.toList token.data.toList rpt = true
  | _ => True

def maySend (s : State) : Frame → Bool
  | .newConnectionId seq rpt cid token =>
    decide (seq = s.nextSeq) && canIssue s cid.data.toList token.data.toList rpt
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;> simp [maySend, MaySend]

/-- SHOULD-level advice, kept out of `Step` so that ignoring it is never an
    error (§5.1.1, line 1718 and line 1749; §5.1.2, line 1831). -/
def Recommended (s : State) : Event → Prop
  | .recvRetireCid _ _ => True
  | .issueCid _ _ rpt =>
    -- §5.1.2, line 1831: "Endpoints SHOULD NOT issue updates of the Retire Prior
    -- To field before receiving RETIRE_CONNECTION_ID frames that retire all
    -- connection IDs indicated by the previous Retire Prior To value."
    rpt > s.sentRetirePriorTo → ∀ e ∈ s.issued, e.seq < s.sentRetirePriorTo → e.seq ∈ s.retired

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

/-- (b) A sequence number identifies at most one connection ID we issued. -/
theorem seq_unique {s : State} (hi : Inv s) {e₁ e₂ : Entry}
    (h1 : e₁ ∈ s.issued) (h2 : e₂ ∈ s.issued) (hs : e₁.seq = e₂.seq) : e₁ = e₂ :=
  entry_eq_of_seq_eq hi.1 h1 h2 hs

theorem inv_nodup_reachable {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s) :
    (seqs s.issued).Nodup :=
  (component.inv_of_reachable h0 h).1

/-- §5.1.1, line 1703: each newly issued connection ID's sequence number is one
    more than the last. -/
theorem issue_seq_succ {s s' : State} {cid token rpt} {fx : List Effect}
    (h : Step s (.issueCid cid token rpt) (.ok s' fx)) :
    s'.nextSeq = s.nextSeq + 1 ∧ fx = [.sendNewCid s.nextSeq rpt cid token] := by
  cases h with
  | issueOk _ => exact ⟨rfl, rfl⟩

/-- (c) Retirement is permanent: `retired` only ever grows. -/
theorem retired_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : ∀ n ∈ s.retired, n ∈ s'.retired := by
  cases h with
  | @retireOk n d _ _ =>
    intro m hm
    unfold applyRetire
    split
    · exact hm
    · exact List.mem_append_left _ hm
  | issueOk _ => exact fun m hm => hm

theorem retired_mono_reachable {s₀ s : State} (h : component.Reachable s₀ s) :
    ∀ n ∈ s₀.retired, n ∈ s.retired :=
  Component.Reachable.rec (motive := fun (t : State) _ => ∀ n ∈ s₀.retired, n ∈ t.retired)
    (fun _ hn => hn) (fun _ hs ih n hn => retired_mono hs n (ih n hn)) h

theorem not_active_of_retired {s : State} {n : Nat} (h : n ∈ s.retired) :
    ∀ e ∈ s.active, e.seq ≠ n := by
  intro e he heq
  simp only [State.active, List.mem_filter, decide_eq_true_eq] at he
  exact he.2 (heq ▸ h)

/-- (c), as a statement about runs: a connection ID the peer retired never
    becomes active again. -/
theorem retired_never_active {s₀ s : State} (h : component.Reachable s₀ s)
    {n : Nat} (hn : n ∈ s₀.retired) : ∀ e ∈ s.active, e.seq ≠ n :=
  not_active_of_retired (retired_mono_reachable h n hn)

/-- (d) The Retire Prior To value we have sent never decreases; `canIssue`
    refuses a smaller one. -/
theorem sent_rpt_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.sentRetirePriorTo ≤ s'.sentRetirePriorTo := by
  cases h with
  | @retireOk n d _ _ =>
    unfold applyRetire
    split
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  | @issueOk cid token rpt hc =>
    simp only [canIssue, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2

theorem sent_rpt_mono_reachable {s₀ s : State} (h : component.Reachable s₀ s) :
    s₀.sentRetirePriorTo ≤ s.sentRetirePriorTo :=
  Component.Reachable.rec
    (motive := fun (t : State) _ => s₀.sentRetirePriorTo ≤ t.sentRetirePriorTo)
    (Nat.le_refl _) (fun _ hs ih => Nat.le_trans ih (sent_rpt_mono hs)) h

/-- (a), send side: we never push the peer past its `active_connection_id_limit`
    (§5.1.1, line 1721). -/
theorem issue_respects_peer_limit {s : State} {cid token rpt}
    (h : canIssue s cid token rpt = true) : s.peerActiveAfter rpt ≤ s.peerLimit := by
  simp only [canIssue, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## 9. Examples (scenarios from the text) -/

section Examples

private def tok (b : UInt8) : ResetToken := List.replicate 16 b

/-- After the handshake: we sent one connection ID in the Source Connection ID
    field (sequence number 0) and no `preferred_address`; the peer advertised an
    `active_connection_id_limit` of 3. -/
private def s0 : State :=
  { nextSeq := 1, issued := [⟨0, [1], tok 0⟩], retired := [], peerLimit := 3,
    zeroLen := false, sentRetirePriorTo := 0 }

-- §5.1.1, line 1703: the next connection ID gets sequence number 1.
example : component.step s0 (.issueCid [2] (tok 2) 0) =
    .ok { s0 with nextSeq := 2, issued := s0.issued ++ [⟨1, [2], tok 2⟩] }
      [.sendNewCid 1 0 [2] (tok 2)] := by decide

-- §5.1.1, line 1721: "An endpoint MUST NOT provide more connection IDs than the
-- peer's limit."  With a limit of 1 and one already issued, a plain
-- NEW_CONNECTION_ID is refused …
private def s1 : State := { s0 with peerLimit := 1 }
example : component.step s1 (.issueCid [2] (tok 2) 0) = .drop := by decide
-- … but line 1722's escape hatch works: retiring the excess in the same frame.
private def s1after : State :=
  { s1 with nextSeq := 2, sentRetirePriorTo := 1,
            issued := s1.issued ++ [⟨1, [2], tok 2⟩] }
example : component.step s1 (.issueCid [2] (tok 2) 1) =
    .ok s1after [.sendNewCid 1 1 [2] (tok 2)] := by decide

-- §5.1, line 1644: "the same connection ID MUST NOT be issued more than once
-- on the same connection."
example : component.step s0 (.issueCid [1] (tok 7) 0) = .drop := by decide

-- §19.15, line 7959 and 7966: the length bounds on the two fields.
example : component.step s0 (.issueCid (List.replicate 21 3) (tok 2) 0) = .drop := by decide
example : component.step s0 (.issueCid [2] [2, 2] 0) = .drop := by decide

-- §5.1.1, line 1766: "An endpoint that selects a zero-length connection ID
-- during the handshake cannot issue a new connection ID."
example : component.step { s0 with zeroLen := true } (.issueCid [2] (tok 2) 0) = .drop := by decide

-- §19.16, line 8046: a sequence number we never sent.
example : component.step s0 (.recvRetireCid 1 none) = .error .protocolViolation := by decide

-- §19.16 ordinary receipt: the peer retires our initial connection ID while
-- sending on a different one.
example : component.step s0 (.recvRetireCid 0 (some 4)) =
    .ok { s0 with retired := [0] } [.cidRetiredByPeer 0] := by decide
-- A retransmission of the same frame changes nothing.
example : component.step { s0 with retired := [0] } (.recvRetireCid 0 (some 4)) =
    .ok { s0 with retired := [0] } [] := by decide

-- §19.16, line 8050: the frame retires the connection ID the packet was sent
-- to.  Both alternatives of the MAY are permitted …
example : component.accepts s0 (.recvRetireCid 0 (some 0)) (.error .protocolViolation) = true := by
  decide
example : component.accepts s0 (.recvRetireCid 0 (some 0))
    (.ok { s0 with retired := [0] } [.cidRetiredByPeer 0]) = true := by decide
-- … and the preferred one is to reject.
example : component.step s0 (.recvRetireCid 0 (some 0)) = .error .protocolViolation := by decide

-- §19.16, line 8055: we issue zero-length connection IDs.
example : component.step { s0 with zeroLen := true } (.recvRetireCid 0 none) =
    .error .protocolViolation := by decide

-- §19.15 send side.
private def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

example : component.maySend s0 (.newConnectionId 1 0 (bytes [2]) (bytes (tok 2))) = true := by
  decide
-- Wrong sequence number: §5.1.1, line 1703 requires an increase by exactly 1.
example : component.maySend s0 (.newConnectionId 2 0 (bytes [2]) (bytes (tok 2))) = false := by
  decide
-- §19.15, line 7993: Retire Prior To must not exceed the sequence number.
example : component.maySend s0 (.newConnectionId 1 2 (bytes [2]) (bytes (tok 2))) = false := by
  decide
-- Frames this component does not govern are unconstrained.
example : component.maySend s0 (.retireConnectionId 0) = true := by decide

-- Following an implementation whose state we cannot see.
example : component.track s0 (.recvRetireCid 0 none) (.ok [.cidRetiredByPeer 0]) =
    some { s0 with retired := [0] } := by decide

end Examples

/-! ## 10. Coverage and notes

The coverage table for both halves of WP4 is at the end of
`QuicModel/Spec/ConnIds/Remote.lean`; the rows naming `Local.*` are this file.
The notes are in `QuicModel/Spec/ConnIds.lean`.
-/

end Quic.Spec.ConnIds.Local
