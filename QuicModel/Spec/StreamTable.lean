import QuicModel.Spec.StreamTable.Inv

/-
  WP9 StreamTable, part 3 of 3: the send side, the `Component`, the named
  theorems, examples and the coverage table.

  Parts 1–4 are in `StreamTable/Defs.lean` and `StreamTable/Step.lean`, part 5
  in `StreamTable/Inv.lean`; together they follow the ten-part order of
  `Spec/Template.lean`, whose stream-count component this package supersedes.
-/
namespace Quic.Spec.StreamTable

/-! ## 6. Send side

Frames this component governs: the two connection-level limit frames, the two
connection/stream-count blocked frames, and — by conjunction with WP2's
per-stream `MaySend` — every frame that names a stream.

Two readings of the text are worth stating up front.

* **A smaller limit may be advertised.**  §4.1, line 1357: "Once a receiver
  advertises a limit for the connection or a stream, it is not an error to
  advertise a smaller limit, but the smaller limit has no effect", and §4.6,
  line 1559: "Once a receiver advertises a stream limit using the MAX_STREAMS
  frame, advertising a smaller limit has no effect.  A receiver MUST ignore any
  MAX_STREAMS frame that does not increase the stream limit."  Neither sentence
  forbids sending it, so `MaySend` does not require an increase — unlike
  `Spec/Template.lean`, which this file supersedes (see NOTES).
* **A blocked frame carries the limit in force.**  §13.3, line 5409: "These
  frames always include the limit that is causing blocking at the time that they
  are transmitted." -/

/-- §4.6, line 1553 with §4.1, line 1330: what the connection level adds to a
    stream's own `MaySend` for a frame that consumes send credit. -/
def sendCredit (s : State) (id : StreamId) (k : Nat) : Prop :=
  s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer

def sendCreditB (s : State) (id : StreamId) (k : Nat) : Bool :=
  decide (s.sentTotal + (k - sentHighest (s.get id)) ≤ s.maxDataPeer)

/-- A frame naming a stream may be sent only for a stream that exists, within
    the peer's stream limit (§4.6, line 1553), and if the stream itself permits
    it (WP2). -/
def streamMaySend (s : State) (id : StreamId) (f : Frame) : Prop :=
  s.has id = true ∧ s.withinPeerStreamLimit id = true ∧ Stream.MaySend (s.get id) f

def streamMaySendB (s : State) (id : StreamId) (f : Frame) : Bool :=
  s.has id && s.withinPeerStreamLimit id && Stream.maySend (s.get id) f

def MaySend (s : State) : Frame → Prop
  | .maxData v => v ≤ maxVarint
  | .maxStreams _ v => v ≤ maxStreamsLimit
  | .dataBlocked v => v = s.maxDataPeer
  | .streamsBlocked dir v => v ≤ maxStreamsLimit ∧ v = s.maxStreamsPeer.get dir
  | .stream id offset fin data =>
      streamMaySend s ⟨id⟩ (.stream id offset fin data) ∧
        sendCredit s ⟨id⟩ (offset + data.size)
  | .resetStream id code fs =>
      streamMaySend s ⟨id⟩ (.resetStream id code fs) ∧ sendCredit s ⟨id⟩ fs
  | .streamDataBlocked id v => streamMaySend s ⟨id⟩ (.streamDataBlocked id v)
  | .maxStreamData id v => streamMaySend s ⟨id⟩ (.maxStreamData id v)
  | .stopSending id code => streamMaySend s ⟨id⟩ (.stopSending id code)
  | _ => True

def maySend (s : State) : Frame → Bool
  | .maxData v => decide (v ≤ maxVarint)
  | .maxStreams _ v => decide (v ≤ maxStreamsLimit)
  | .dataBlocked v => decide (v = s.maxDataPeer)
  | .streamsBlocked dir v => decide (v ≤ maxStreamsLimit) && decide (v = s.maxStreamsPeer.get dir)
  | .stream id offset fin data =>
      streamMaySendB s ⟨id⟩ (.stream id offset fin data) && sendCreditB s ⟨id⟩ (offset + data.size)
  | .resetStream id code fs =>
      streamMaySendB s ⟨id⟩ (.resetStream id code fs) && sendCreditB s ⟨id⟩ fs
  | .streamDataBlocked id v => streamMaySendB s ⟨id⟩ (.streamDataBlocked id v)
  | .maxStreamData id v => streamMaySendB s ⟨id⟩ (.maxStreamData id v)
  | .stopSending id code => streamMaySendB s ⟨id⟩ (.stopSending id code)
  | _ => true

theorem streamMaySend_iff (s : State) (id : StreamId) (f : Frame) :
    streamMaySendB s id f = true ↔ streamMaySend s id f := by
  simp [streamMaySendB, streamMaySend, Stream.maySend_iff, and_assoc]

theorem sendCredit_iff (s : State) (id : StreamId) (k : Nat) :
    sendCreditB s id k = true ↔ sendCredit s id k := by
  simp [sendCreditB, sendCredit]

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f <;>
    simp [maySend, MaySend, streamMaySend_iff, sendCredit_iff]

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

/-! ### The SHOULDs that are about *when*, not *whether*

§4.1, line 1371 and §4.6, line 1569 recommend a blocked frame when actually
blocked; §4.2's autotuning advice and §4.3 are performance guidance with no
observable rule.  None of them restricts `MaySend`. -/

def Recommended (s : State) : Frame → Prop
  -- §4.1, line 1368: "If a sender has sent data up to the limit, it will be
  -- unable to send new data and is considered blocked."
  | .dataBlocked _ => s.sentTotal = s.maxDataPeer
  -- §4.6, line 1569: "An endpoint that is unable to open a new stream due to
  -- the peer's limits SHOULD send a STREAMS_BLOCKED frame."
  | .streamsBlocked dir _ => s.opened.get s.role dir = s.maxStreamsPeer.get dir
  | _ => True

/-! ## 8. Named theorems -/

/-! ### (a) Connection-level flow control -/

/-- **(a) Nothing beyond the connection-level credit we advertised is ever
    accounted for.**  §19.9, line 7710: "The sum of the final sizes on all
    streams — including streams in terminal states — MUST NOT exceed the value
    advertised by a receiver." -/
theorem recvTotal_le_advertised {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) : s.recvTotal ≤ s.maxDataLocal :=
  (component.inv_of_reachable h0 h).1

/-- **(a, send side) We never send beyond the peer's MAX_DATA.**  §4.1,
    line 1330: "Senders MUST NOT send data in excess of either limit."  Every
    `Step` that records a transmission checks `connSendBlocked` first, which is
    exactly the connection-level half of `MaySend`; a frame that fails it is
    never sent (`Step.existSendBlocked`), so the hypothesis "every send
    satisfied `MaySend`" is discharged by the model itself. -/
theorem sentTotal_le_peer {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) : s.sentTotal ≤ s.maxDataPeer :=
  (component.inv_of_reachable h0 h).2.1

/-- The link between the two halves of (a): the connection-level part of
    `MaySend` for a STREAM frame is exactly the check `Step` makes on the
    corresponding `sentStream` event. -/
theorem maySend_stream_iff_not_blocked (s : State) (id : StreamId) (offset : Nat)
    (fin : Bool) (data : ByteArray) :
    sendCredit s id (offset + data.size) ↔
      connSendBlocked s (s.get id) (.send (.sentStream offset data.size fin)) = false := by
  simp [sendCredit, connSendBlocked, sentEnd]

/-! ### (b) Stream-count limits -/

/-- **(b) The peer never opens more streams of a type than we advertised.**
    §4.6, line 1553: "An endpoint MUST terminate a connection with a
    STREAM_LIMIT_ERROR error if a peer opens more streams than was
    permitted." -/
theorem openedRemote_le_advertised {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (d : StreamDir) :
    s.opened.get s.role.peer d ≤ s.maxStreamsLocal.get d :=
  (component.inv_of_reachable h0 h).2.2.1 d

/-- **(b, our side) We never open more streams than the peer allowed.**
    §4.6, line 1553: "Endpoints MUST NOT exceed the limit set by their peer." -/
theorem openedLocal_le_peer {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (d : StreamDir) :
    s.opened.get s.role d ≤ s.maxStreamsPeer.get d :=
  (component.inv_of_reachable h0 h).2.2.2.1 d

/-! ### (c) A stream ID is never reused -/

theorem opened_step {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (r : Role) (d : StreamDir) :
    s.opened.get r d ≤ s'.opened.get r d := by
  cases h with
  | @openOk id e2 st2 gx hx hp hr hl hfc hs =>
    show s.opened.get r d ≤ (s.openThrough id).opened.get r d
    rw [openThrough_opened]
    split
    · rename_i hc
      obtain ⟨h1, h2⟩ := hc
      rw [h1, h2] at *
      omega
    · exact Nat.le_refl _
  | @openLocal dir hlt =>
    show s.opened.get r d ≤ (s.opened.set s.role dir (s.opened.get s.role dir + 1)).get r d
    rw [Opened.get_set]
    split
    · rename_i hc
      obtain ⟨h1, h2⟩ := hc
      rw [← h1, ← h2]
      omega
    · exact Nat.le_refl _
  | _ => exact Nat.le_refl _

/-- **(c) Once a stream exists it exists forever**, and no step ever announces
    the opening of a stream that already existed: §2.1, line 687 "A QUIC
    endpoint MUST NOT reuse a stream ID within a connection." -/
theorem no_reuse {s s' : State} {e : Event} {fx : List Effect} (h : Step s e (.ok s' fx))
    {id : StreamId} (hh : s.has id = true) :
    s'.has id = true ∧ ∀ id', Effect.streamOpened id' ∈ fx → id' ≠ id := by
  constructor
  · simp only [State.has, decide_eq_true_eq] at hh ⊢
    exact Nat.lt_of_lt_of_le hh (opened_step h _ _)
  · intro id' hmem
    cases h with
    | @existOk id₀ e2 st2 gx hx hb hfc hs =>
      simp only [List.mem_map] at hmem
      obtain ⟨a, -, ha⟩ := hmem
      exact absurd ha (by simp)
    | @openOk id₀ e2 st2 gx hx hp hr hl hfc hs =>
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with hmem | ⟨a, -, ha⟩
      · simp only [openedEffects, List.mem_map] at hmem
        obtain ⟨n, hn, hid⟩ := hmem
        simp only [List.mem_range'_1] at hn
        simp only [Effect.streamOpened.injEq] at hid
        subst hid
        intro hc
        subst hc
        simp only [State.has, StreamId.initiator_make, StreamId.dir_make, StreamId.index_make,
          decide_eq_true_eq] at hh
        omega
      · exact absurd ha (by simp)
    | @openLocal dir hlt =>
      simp only [List.mem_singleton, Effect.streamOpened.injEq] at hmem
      subst hmem
      intro hc
      subst hc
      simp only [State.nextLocal, State.has, StreamId.initiator_make, StreamId.dir_make,
        StreamId.index_make, decide_eq_true_eq] at hh
      omega
    | _ => simp_all

/-- The reachable form of (c): every stream of the initial state, and every
    stream opened on the way, is still there. -/
theorem has_forever {s₀ s : State} (h : component.Reachable s₀ s) {id : StreamId}
    (hh : s₀.has id = true) : s.has id = true :=
  component.reachable_induction (motive := fun s => s.has id = true) hh
    (fun _ hstep hprev => (no_reuse hstep hprev).1) h

/-! ### (d) Implicit opening -/

/-- **(d) §2.1, line 712**: "A stream ID that is used out of order results in
    all streams of that type with lower-numbered stream IDs also being opened."
    This holds in every state, hence after every step. -/
theorem has_lower {s : State} {id : StreamId} (h : s.has id = true) {n : Nat}
    (hn : n < id.index) : s.has (StreamId.make id.initiator id.dir n) = true := by
  simp only [State.has, StreamId.initiator_make, StreamId.dir_make, StreamId.index_make,
    decide_eq_true_eq] at h ⊢
  omega

theorem has_lower_step {s s' : State} {e : Event} {fx : List Effect}
    (_h : Step s e (.ok s' fx)) {id : StreamId} (hh : s'.has id = true) {n : Nat}
    (hn : n < id.index) : s'.has (StreamId.make id.initiator id.dir n) = true :=
  has_lower hh hn

/-! ### (e) Lifting WP2 to every stream of the table -/

/-- Which stream a step can have changed: all but one are untouched, and that
    one moved by a `Stream.Step`. -/
theorem get_step {s s' : State} {e : Event} {fx : List Effect} (hi : Inv s)
    (h : Step s e (.ok s' fx)) (id : StreamId) :
    s'.get id = s.get id ∨ ∃ e' gx, Stream.Step (s.get id) e' (.ok (s'.get id) gx) := by
  cases h with
  | @existOk id₀ e2 st2 gx hx hb hfc hs =>
    by_cases hide : id = id₀
    · subst hide
      exact Or.inr ⟨e2, gx, by rw [afterStep_get_self]; exact hs⟩
    · exact Or.inl (afterStep_get_of_ne s _ _ hide)
  | @openOk id₀ e2 st2 gx hx hp hr hl hfc hs =>
    by_cases hide : id = id₀
    · subst hide
      refine Or.inr ⟨e2, gx, ?_⟩
      rw [afterStep_get_self, get_of_not_has hi hx]
      exact hs
    · exact Or.inl (by rw [afterStep_get_of_ne _ _ _ hide, openThrough_get])
  | _ => exact Or.inl rfl

/-- **(e) WP2's invariant holds for every stream of the table**, in every
    reachable state — whether or not the stream has an entry. -/
theorem stream_inv {s₀ s : State} (h0 : Inv s₀) (h : component.Reachable s₀ s)
    (id : StreamId) : Stream.Inv (s.get id) :=
  (inv_get (component.inv_of_reachable h0 h) id).2.2

/-- **(e₁) Lifted from WP2**: no stream has accepted data beyond the credit we
    advertised for it (§4.1, line 1359; `Stream.highest_le_maxData`). -/
theorem stream_highest_le_maxData {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (id : StreamId) {rs : Stream.Recv.State}
    (hr : (s.get id).recv = some rs) : rs.highest ≤ rs.maxData :=
  ((stream_inv h0 h id).2.2.2 rs hr).2.2.1

/-- **(e₂) Lifted from WP2**: the final size of a stream, once known, never
    changes (§4.5, line 1516; `Stream.finalSize_immutable`) — on both halves of
    every stream in the table. -/
theorem stream_finalSize_immutable {s s' : State} {e : Event} {fx : List Effect}
    (hi : Inv s) (h : Step s e (.ok s' fx)) (id : StreamId) :
    (∀ ss ss' f, (s.get id).send = some ss → (s'.get id).send = some ss' →
      ss.finalSize = some f → ss'.finalSize = some f) ∧
    (∀ rs rs' f, (s.get id).recv = some rs → (s'.get id).recv = some rs' →
      rs.finalSize = some f → rs'.finalSize = some f) := by
  rcases get_step hi h id with heq | ⟨e', gx, hs⟩
  · constructor
    · intro a b f h1 h2 h3
      rw [heq, h1] at h2
      simp only [Option.some.injEq] at h2
      subst h2; exact h3
    · intro a b f h1 h2 h3
      rw [heq, h1] at h2
      simp only [Option.some.injEq] at h2
      subst h2; exact h3
  · exact Stream.finalSize_immutable hs

/-! ### (f) Advertised limits never decrease -/

/-- **(f) §4.1, line 1357 and §4.6, line 1559**: a smaller limit "has no
    effect", so what we have advertised — and what we have been told — only
    ever grows. -/
theorem maxDataLocal_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.maxDataLocal ≤ s'.maxDataLocal := by
  cases h with
  | sendMaxData => exact Nat.le_max_left _ _
  | _ => exact Nat.le_refl _

theorem maxStreamsLocal_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (d : StreamDir) :
    s.maxStreamsLocal.get d ≤ s'.maxStreamsLocal.get d := by
  cases h with
  | @sendMaxStreams dir v hle =>
    show s.maxStreamsLocal.get d ≤
      (s.maxStreamsLocal.set dir (max (s.maxStreamsLocal.get dir) v)).get d
    rw [Counts.get_set]
    split
    · rename_i hd; subst hd; exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem maxDataPeer_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) : s.maxDataPeer ≤ s'.maxDataPeer := by
  cases h with
  | @maxDataRaise v hgt => exact Nat.le_of_lt hgt
  | _ => exact Nat.le_refl _

theorem maxStreamsPeer_mono {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (d : StreamDir) :
    s.maxStreamsPeer.get d ≤ s'.maxStreamsPeer.get d := by
  cases h with
  | @maxStreamsRaise dir v hle hgt =>
    show s.maxStreamsPeer.get d ≤ (s.maxStreamsPeer.set dir v).get d
    rw [Counts.get_set]
    split
    · rename_i hd; subst hd; exact Nat.le_of_lt hgt
    · exact Nat.le_refl _
  | _ => exact Nat.le_refl _

/-! ### Routing, as theorems

The three sentences that WP2 left to this package, read off `Step`. -/

/-- §19.8, line 7638 (and §19.4, §19.5, §19.10, §19.13): a frame for a
    locally-initiated stream that has not yet been created is a
    STREAM_STATE_ERROR — and nothing else is permitted. -/
theorem localNotCreated_iff (s : State) (id : StreamId) (e : Stream.Event)
    (hx : s.has id = false) (hp : peerFrame e = true) (hr : id.initiator = s.role) (o : Out) :
    Step s (.stream id e) o ↔ o = .error .streamStateError := by
  rw [← outcomes_iff]
  simp [outcomes, streamOutcomes, hx, hp, hr]

/-- §4.6, line 1554: a frame for a peer-initiated stream beyond the limit we
    advertised is a STREAM_LIMIT_ERROR. -/
theorem openLimit_error (s : State) (id : StreamId) (e : Stream.Event)
    (hx : s.has id = false) (hp : peerFrame e = true) (hr : ¬ id.initiator = s.role)
    (hl : s.maxStreamsLocal.get id.dir ≤ id.index) :
    component.accepts s (.stream id e) (.error .streamLimitError) = true :=
  (component.accepts_iff _ _ _).mpr (.openLimit hx hp hr hl)

/-- §2.1, line 712: receiving a frame for a stream that does not exist yet opens
    it and every lower-numbered stream of its type. -/
theorem openOk_opens_lower {s s' : State} {id : StreamId} {e : Stream.Event}
    {fx : List Effect} (h : Step s (.stream id e) (.ok s' fx)) (hx : s.has id = false)
    {n : Nat} (hn : n ≤ id.index) :
    s'.has (StreamId.make id.initiator id.dir n) = true := by
  cases h with
  | @existOk _ _ st2 gx hx' hb hfc hs => exact absurd (hx.symm.trans hx') (by simp)
  | @openOk _ _ st2 gx hx' hp hr hl hfc hs =>
    rw [afterStep_has]
    simp only [State.has, openThrough_opened, StreamId.initiator_make, StreamId.dir_make,
      StreamId.index_make, and_self, reduceIte, decide_eq_true_eq]
    omega

/-! ## 9. Examples (scenarios from the text) -/

private def lim : Limits :=
  { maxData := 100, maxStreamDataBidiLocal := 100, maxStreamDataBidiRemote := 100,
    maxStreamDataUni := 100, maxStreamsBidi := 3, maxStreamsUni := 3 }

/-- A server that has advertised, and been told, the limits of `lim`. -/
private def srv : State := init .server lim lim

/-- Run a list of events through the reference implementation. -/
private def run (s : State) : List Event → State
  | [] => s
  | e :: es => run ((component.step s e).next s) es

-- §19.11, line 7812: "a server that receives a unidirectional stream limit of 3
-- is permitted to open stream 3, 7, and 11, but not stream 15."
example : component.step srv (.appOpenStream .uni) =
    .ok ((component.step srv (.appOpenStream .uni)).next srv) [.streamOpened ⟨3⟩] := by decide
example : (run srv [.appOpenStream .uni]).nextLocal .uni = ⟨7⟩ := by decide
example : (run srv [.appOpenStream .uni, .appOpenStream .uni]).nextLocal .uni = ⟨11⟩ := by decide
example : component.step (run srv [.appOpenStream .uni, .appOpenStream .uni, .appOpenStream .uni])
    (.appOpenStream .uni) = .drop := by decide

-- §2.1, line 712: a STREAM frame for client-initiated bidirectional stream 8
-- (index 2) opens streams 0 and 4 as well, in increasing order …
example : component.step srv (.stream ⟨8⟩ (.recv (.recvStream 0 5 false))) =
    .ok ((component.step srv (.stream ⟨8⟩ (.recv (.recvStream 0 5 false)))).next srv)
      [.streamOpened ⟨0⟩, .streamOpened ⟨4⟩, .streamOpened ⟨8⟩,
       .stream ⟨8⟩ (.recv (.dataAvailable 5))] := by decide
-- … and they really exist afterwards, while stream 12 does not.
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨0⟩ = true := by decide
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨4⟩ = true := by decide
example : (run srv [.stream ⟨8⟩ (.recv (.recvStream 0 5 false))]).has ⟨12⟩ = false := by decide

-- §4.6, line 1554: stream 12 is index 3, beyond the limit of 3 we advertised.
example : component.step srv (.stream ⟨12⟩ (.recv (.recvStream 0 5 false))) =
    .error .streamLimitError := by decide

-- §19.8, line 7638: stream 1 is server-initiated, so at a server a STREAM frame
-- for it before we created it is a STREAM_STATE_ERROR …
example : component.step srv (.stream ⟨1⟩ (.recv (.recvStream 0 5 false))) =
    .error .streamStateError := by decide
-- … and so are the other four frames of §19.4/§19.5/§19.10/§19.13.
example : component.step srv (.stream ⟨1⟩ (.recv (.recvResetStream 0 5))) =
    .error .streamStateError := by decide
example : component.step srv (.stream ⟨1⟩ (.send (.recvStopSending 0))) =
    .error .streamStateError := by decide
example : component.step srv (.stream ⟨1⟩ (.send (.recvMaxStreamData 5))) =
    .error .streamStateError := by decide
example : component.step srv (.stream ⟨1⟩ (.recv (.recvStreamDataBlocked 5))) =
    .error .streamStateError := by decide

-- §19.10, line 7736 through the routing: MAX_STREAM_DATA for a peer-initiated
-- *unidirectional* stream opens it and then fails, because it is receive-only.
example : component.step srv (.stream ⟨2⟩ (.send (.recvMaxStreamData 5))) =
    .error .streamStateError := by decide

-- §19.9, line 7712: 60 bytes on stream 0 and 60 on stream 4 exceed our MAX_DATA
-- of 100, although each is within its own stream limit of 100.
example : component.step (run srv [.stream ⟨0⟩ (.recv (.recvStream 0 60 false))])
    (.stream ⟨4⟩ (.recv (.recvStream 0 60 false))) = .error .flowControlError := by decide
-- §4.5, line 1495: a reset stream keeps consuming its final size, so the same
-- total is reached through RESET_STREAM.
example : component.step (run srv [.stream ⟨0⟩ (.recv (.recvResetStream 7 60))])
    (.stream ⟨4⟩ (.recv (.recvStream 0 60 false))) = .error .flowControlError := by decide

-- §2.1, line 687: a stream that has been reset is still "used"; its ID is never
-- available again.
example : (run srv [.stream ⟨0⟩ (.recv (.recvResetStream 7 5))]).has ⟨0⟩ = true := by decide

-- §19.11, line 7809: a MAX_STREAMS that does not increase the limit is ignored,
-- a larger one raises it.
example : component.step srv (.recvMaxStreams .uni 2) = .ok srv [] := by decide
example : component.step srv (.recvMaxStreams .uni 5) =
    .ok ((component.step srv (.recvMaxStreams .uni 5)).next srv)
      [.streamsAvailable .uni 5] := by decide
-- §19.14, line 7919: either error code is acceptable for an oversized value.
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1))
    (.error .streamLimitError) = true := by decide
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1))
    (.error .frameEncodingError) = true := by decide
example : component.accepts srv (.recvStreamsBlocked .bidi (2 ^ 60 + 1)) (.ok srv []) = false := by
  decide

-- Following an implementation we cannot see inside (what the WP13 harness does).
example : component.track srv (.recvMaxData 500) (.ok [.dataCreditAvailable 500]) =
    some { srv with maxDataPeer := 500 } := by decide
-- An observation the spec does not permit empties the candidate set.
example : component.trackSet [srv] (.stream ⟨12⟩ (.recv (.recvStream 0 5 false)))
    (Obs.ok []).matchesLoosely = [] := by decide

-- Send side.  §4.1, line 1357: advertising a smaller limit is not an error …
example : component.maySend srv (.maxData 1) = true := by decide
example : component.maySend srv (.maxStreams .bidi 1) = true := by decide
-- … but 2^60 is the ceiling for MAX_STREAMS (§19.11, line 7802).
example : component.maySend srv (.maxStreams .bidi (2 ^ 60 + 1)) = false := by decide
-- §13.3, line 5409: a blocked frame carries the limit in force.
example : component.maySend srv (.dataBlocked 100) = true := by decide
example : component.maySend srv (.dataBlocked 99) = false := by decide
example : component.maySend srv (.streamsBlocked .uni 3) = true := by decide
-- Nothing may be sent for a stream that does not exist yet.
example : component.maySend srv (.stream 3 0 false ByteArray.empty) = false := by decide
-- After opening stream 3, a STREAM frame the application has written is allowed …
private def srvOpen : State :=
  run srv [.appOpenStream .uni, .stream ⟨3⟩ (.send (.appWrite 10))]
example : maySend srvOpen (.stream 3 0 false (ByteArray.mk #[1, 2, 3])) = true := by decide
-- … but not beyond the connection-level credit the peer gave us: with a peer
-- that allows 1000 bytes on the stream but only 100 on the connection, a frame
-- ending at offset 103 is within the stream limit and outside the connection's.
private def limBig : Limits := { lim with maxStreamDataUni := 1000 }
private def srvBig : State :=
  run (init .server lim limBig) [.appOpenStream .uni, .stream ⟨3⟩ (.send (.appWrite 200))]
example : maySend srvBig (.stream 3 0 false (ByteArray.mk #[1, 2, 3, 4, 5])) = true := by decide
example : maySend srvBig (.stream 3 98 false (ByteArray.mk #[1, 2, 3, 4, 5])) = false := by decide

/-! ## 10. Coverage and notes

Assigned text: §2.1 (677–732), §4–§4.3 (1293–1460), §4.6 (1527–1576), the
MAX_DATA / MAX_STREAMS / DATA_BLOCKED / STREAMS_BLOCKED frame sections
(7689–7717, 7773–7856, 7884–7922) and the "locally-initiated stream that has not
yet been created" half of §19.4/§19.5/§19.8/§19.10/§19.13.

| Text (line) | Sentence | Encoded as |
|---|---|---|
| §2.1 (687) | a QUIC endpoint MUST NOT reuse a stream ID | `State.has` (high-water marks), `no_reuse`, `has_forever` |
| §2.1 (697–702) | the two low bits give initiator and directionality | `Spec.StreamId` (WP0), used throughout |
| §2.1 (712) | a stream ID used out of order opens all lower-numbered streams of that type | `State.openThrough`, `Step.openOk`, `openedEffects`, `has_lower`, `openOk_opens_lower` |
| §4 (1298) | streams are flow controlled individually and across the connection | `State.recvTotal`/`maxDataLocal` here, `Stream.Recv.maxData` in WP2 |
| §4 (1304) | the cumulative number of streams a peer can initiate is limited | `State.maxStreamsLocal`/`maxStreamsPeer` |
| §4 (1308) | CRYPTO data is not flow controlled this way | out of scope: WP11 (CRYPTO stream) |
| §4.1 (1330) | senders MUST NOT send data in excess of either limit | `connSendBlocked`, `Step.existSendBlocked`, `MaySend`, `sentTotal_le_peer` |
| §4.1 (1331) | initial limits come from transport parameters | `Limits`, `init` |
| §4.1 (1349) | a receiver can advertise a larger stream limit with MAX_STREAM_DATA | WP2 (`Recv.Step.sendMaxStreamData`), routed here |
| §4.1 (1353) | a receiver can advertise a larger connection limit with MAX_DATA | `Step.sendMaxData`, `Step.maxDataRaise` |
| §4.1 (1355) | a receiver maintains a cumulative sum of bytes received on all streams | `State.recvTotal`, `afterStep` |
| §4.1 (1357) | advertising a smaller limit is not an error but has no effect | `Step.sendMaxData` (takes `max`), `MaySend` does *not* require an increase |
| §4.1 (1359) | FLOW_CONTROL_ERROR if the sender violates the advertised limits | `Step.existFlowControl`, `Step.openFlowControl`, `recvTotal_le_advertised` |
| §4.1 (1361) | a sender MUST ignore MAX_DATA frames that do not increase limits | `Step.maxDataStale` |
| §4.1 (1368–1377) | a blocked sender SHOULD send DATA_BLOCKED, periodically | `Recommended`; `MaySend` permits it whenever the value is the limit in force |
| §4.2 (1395–1429) | when and how much credit to advertise; MAY send repeatedly; autotuning | out of scope by assignment (advice); the "MUST NOT wait for DATA_BLOCKED" of line 1422 constrains a strategy, not an action — see NOTES |
| §4.3 (1437–1455) | flow control performance | out of scope: no observable rule |
| §4.5 (1495) | the receiver MUST use the final size to account for all bytes in its connection-level flow controller | `recvHighest` (RESET_STREAM sets `highest` to the final size in WP2), example at §4.5 above |
| §4.6 (1531) | only streams with an index below the limit may be opened | `Step.openLimit`, `Step.openLocalBlocked` |
| §4.6 (1535) | separate limits for unidirectional and bidirectional streams | `Counts`, `Opened` |
| §4.6 (1543) | a max_streams value above 2^60: FRAME_ENCODING_ERROR (frame) / TRANSPORT_PARAMETER_ERROR (parameter) | `Step.maxStreamsTooLarge`; the transport-parameter half is WP1 |
| §4.6 (1553) | endpoints MUST NOT exceed the peer's limit; a frame beyond the limit we sent is a STREAM_LIMIT_ERROR | `Step.openLimit`, `State.withinPeerStreamLimit`, `openedLocal_le_peer`, `openedRemote_le_advertised` |
| §4.6 (1559) | a MAX_STREAMS that does not increase the limit MUST be ignored | `Step.maxStreamsStale` |
| §4.6 (1563) | implementations decide when to advertise more streams | `Step.sendMaxStreams` is an event: the model tracks what was advertised, not when |
| §4.6 (1569) | an endpoint unable to open a stream SHOULD send STREAMS_BLOCKED; MUST NOT wait for it | `Recommended`; see NOTES |
| §19.9 (7710) | the sum of the final sizes on all streams MUST NOT exceed the advertised value; FLOW_CONTROL_ERROR otherwise | `connRecvViolation`, `recvTotal_le_advertised` |
| §19.10 (7734) | MAX_STREAM_DATA for a locally-initiated stream not yet created: STREAM_STATE_ERROR | `Step.localNotCreated` |
| §19.11 (7802) | MAX_STREAMS above 2^60: FRAME_ENCODING_ERROR | `Step.maxStreamsTooLarge` |
| §19.11 (7809) | MAX_STREAMS that do not increase the limit MUST be ignored | `Step.maxStreamsStale` |
| §19.11 (7812) | an endpoint MUST NOT open more streams than permitted; STREAM_LIMIT_ERROR if a peer does | `Step.openLocalBlocked`, `Step.openLimit` |
| §19.11 (7820) | the limit counts closed streams too | high-water marks never decrease (`opened_step`) |
| §19.12 (7828) | a sender SHOULD send DATA_BLOCKED when blocked | `Recommended`, `Step.dataBlocked` |
| §19.13 (7863) | STREAM_DATA_BLOCKED for a locally-initiated stream not yet created | `Step.localNotCreated` |
| §19.14 (7899) | STREAMS_BLOCKED when unable to open a stream | `Recommended` |
| §19.14 (7903) | STREAMS_BLOCKED does not open the stream | `Step.streamsBlockedOk` (state unchanged) |
| §19.14 (7919) | STREAMS_BLOCKED above 2^60: STREAM_LIMIT_ERROR or FRAME_ENCODING_ERROR | `Step.streamsBlockedTooLarge₁/₂` |
| §19.4 (7431), §19.5 (7476), §19.8 (7638), §19.10 (7736), §19.13 (7864) | the *send-only / receive-only* halves of those sentences | WP2 (`Stream.Step.sendMissing`/`recvMissing`), reached through this file's routing |
| §13.3 (5409) | blocked frames carry the limit in force when transmitted | `MaySend` for DATA_BLOCKED / STREAMS_BLOCKED |
| §13.3 (rest) | retransmission and loss | out of scope by assignment |
| §2.3 (777) | stream prioritisation | out of scope by assignment |

NOTES

* **Existence is the high-water mark, not the table.**  §2.1 opens every
  lower-numbered stream of a type implicitly and forbids reusing an ID, so the
  set of streams of one type is always an initial segment: `State.opened` counts
  them and `State.has` decides existence.  The `Map StreamId Stream.State` holds
  the state of streams that have actually taken a step; `State.get` falls back
  to `State.freshStream`, so an implicitly opened stream that has seen no event
  costs nothing and is still fully specified.  The alternative — materialising
  every implicitly opened stream in the table — is observationally identical
  (all of them are at their initial state) but makes every theorem about
  implicit opening an induction over a range.  One consequence to keep in mind
  for WP12/WP13: two histories that differ only in events that left a stream at
  its initial state can produce table entries that differ syntactically while
  being equal as states, so `trackSet` may carry two candidates where one would
  do; it never loses the real state.
* **Which error when several rules are violated.**  A frame can break the stream
  limit of §4.6, the connection-level limit of §19.9 and a stream-level rule of
  WP2 at once, and the text fixes no order between the checks.  `Step` therefore
  has one constructor per violated rule with no mutual exclusion, and `outcomes`
  lists STREAM_LIMIT_ERROR first, then FLOW_CONTROL_ERROR, then every error the
  stream itself would raise.  The preferred outcome (`component.step`) is the
  first, but `accepts` takes any of them — being stricter here would fail
  implementations that check in a different order.
* **A local action on a stream that does not exist is `.drop`, a frame is an
  error.**  Same split as WP2: the application cannot write to a stream it never
  opened, whereas a *frame* for an uncreated locally-initiated stream is the
  STREAM_STATE_ERROR of §19.4/§19.5/§19.8/§19.10/§19.13.
* **`MaySend` for a stream that does not exist is `False`** (for all five
  stream-scoped frame types).  In this model a locally-initiated stream comes
  into existence through `appOpenStream`, which is where §4.6's "MUST NOT exceed
  the limit set by their peer" is enforced; with no state for the stream, none
  of §3.3, §4.1 or §4.5 can be checked, so nothing may be said about it.  This
  is a modelling decision, not a sentence of the text: an implementation that
  opens a stream and sends on it in one step satisfies the model by emitting
  `appOpenStream` first.  For a peer-initiated stream the answer coincides with
  the text: the peer would treat MAX_STREAM_DATA or STOP_SENDING for a stream it
  has not created as a STREAM_STATE_ERROR (§19.10, line 7734; §19.5, line 7473).
* **Advertising a smaller limit is permitted.**  `Spec/Template.lean` required
  `localMax ≤ v` in `MaySend` for MAX_STREAMS.  The text does not: §4.6,
  line 1559 says only that "advertising a smaller limit has no effect", and
  §4.1, line 1357 says explicitly that "it is not an error to advertise a
  smaller limit".  This file therefore drops that conjunct — "has no effect" is
  not "must not be sent" — and keeps the effect on the state (`max`), which is
  what `maxDataLocal_mono` / `maxStreamsLocal_mono` (theorem (f)) rest on.  This
  is the one place where this package deliberately differs from the template it
  supersedes.
* **Blocked frames must carry the current limit.**  §13.3, line 5409 is explicit
  that a retransmitted blocked frame carries the limit in force at transmission
  time, so requiring `v = s.maxDataPeer` (resp. the stream-type limit) does not
  clash with the project rule that an exact repeat of an accepted frame stays
  acceptable: after the limit moves, the frame that is re-sent is a different
  frame by the text's own account.
* **The 2^62-1 bound on MAX_DATA** is not a sentence of §19.9; it follows from
  §16 (all frame fields are variable-length integers).  `MaySend` uses it as the
  only bound on MAX_DATA, and `Step.sendMaxDataForbidden` mirrors it.
* **Connection-level credit is accounted from the frame, not from the stream's
  reply.**  The check that raises FLOW_CONTROL_ERROR must happen before the
  stream is asked, so it uses the frame's end offset (`recvEnd`); the state then
  moves by what the stream actually did (`afterStep`).  `recvHighest_step`
  proves the second never exceeds the first, which is what makes theorem (a)
  true.  A RESET_STREAM we *send* consumes no new credit because WP2's
  `maySendReset` forces its Final Size to equal `sent`, which is already
  counted.
* **§4.2, line 1422 ("a receiver MUST NOT wait for a STREAM_DATA_BLOCKED or
  DATA_BLOCKED frame before sending MAX_STREAM_DATA or MAX_DATA")** forbids a
  scheduling strategy, not an action: every individual behaviour it rules out is
  permitted frame by frame.  It cannot be stated over a single step and is
  recorded here rather than encoded.
* **The initial state is a parameter.**  `init` takes both endpoints' `Limits`
  as plain numbers; `init_inv` needs only that the four `max_streams` parameters
  are within 2^60, which is exactly what WP1's transport-parameter validity
  guarantees.  WP12 will build the initial state from the negotiated parameters
  (including §7.4.1's remembered 0-RTT limits, which are WP1/WP11's business).
-/

end Quic.Spec.StreamTable
