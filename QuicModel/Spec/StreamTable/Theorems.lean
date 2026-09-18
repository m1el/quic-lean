import QuicModel.Spec.StreamTable.Send

/-
  WP9 StreamTable, part 4 of 5: the named theorems (§8).
-/
namespace Quic.Spec.StreamTable

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

/-! ### (a′) The tracked totals are the sums the text describes

§4.1, line 1358: "A receiver maintains a cumulative sum of bytes received on
all streams."  `recvTotal` and `sentTotal` are that sum, kept incrementally;
these lemmas show the bookkeeping never drifts from the table.  Streams with no
entry contribute nothing, which is right: they are at their initial state. -/

/-- The sum of a per-stream quantity over the table. -/
def sumBy (w : Stream.State → Nat) (m : Map StreamId Stream.State) : Nat :=
  (m.map (fun p => w p.2)).sum

theorem sumBy_set_of_none (w : Stream.State → Nat) (m : Map StreamId Stream.State)
    (k : StreamId) (v : Stream.State) (h : m.get? k = none) :
    sumBy w (m.set k v) = sumBy w m + w v := by
  induction m with
  | nil => simp [sumBy, Map.set]
  | cons p m ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k' = k
    · rw [Map.get?, ite_eq_left hk] at h
      exact absurd h (by simp)
    · rw [Map.get?, ite_eq_right hk] at h
      have hrec := ih h
      rw [Map.set, ite_eq_right hk]
      simp only [sumBy, List.map_cons, List.sum_cons] at hrec ⊢
      omega

theorem sumBy_set_of_some (w : Stream.State → Nat) (m : Map StreamId Stream.State)
    (k : StreamId) (v old : Stream.State) (h : m.get? k = some old) :
    sumBy w (m.set k v) + w old = sumBy w m + w v := by
  induction m with
  | nil => simp [Map.get?] at h
  | cons p m ih =>
    obtain ⟨k', v'⟩ := p
    by_cases hk : k' = k
    · rw [Map.get?, ite_eq_left hk, Option.some.injEq] at h
      subst h
      rw [Map.set, ite_eq_left hk]
      simp only [sumBy, List.map_cons, List.sum_cons]
      omega
    · rw [Map.get?, ite_eq_right hk] at h
      have hrec := ih h
      rw [Map.set, ite_eq_right hk]
      simp only [sumBy, List.map_cons, List.sum_cons] at hrec ⊢
      omega

theorem recv_highest_mono {rs rs' : Stream.Recv.State} {e : Stream.Recv.Event}
    {fx : List Stream.Recv.Effect} (h : Stream.Recv.Step rs e (.ok rs' fx)) :
    rs.highest ≤ rs'.highest := by
  cases h with
  | streamOk => exact Nat.le_max_left _ _
  | streamResetComplete => exact Nat.le_max_left _ _
  | resetOk h1 h2 h3 h4 => exact Stream.Recv.highest_le_of_resetFinalSizeViolation_false h3
  | _ => exact Nat.le_refl _

theorem send_sent_mono {ss ss' : Stream.Send.State} {e : Stream.Send.Event}
    {fx : List Stream.Send.Effect} (h : Stream.Send.Step ss e (.ok ss' fx)) :
    ss.sent ≤ ss'.sent := by
  cases h with
  | sendStream => exact Nat.le_max_left _ _
  | _ => exact Nat.le_refl _

theorem recvHighest_mono {st st' : Stream.State} {e : Stream.Event} {fx : List Stream.Effect}
    (h : Stream.Step st e (.ok st' fx)) : recvHighest st ≤ recvHighest st' := by
  cases h with
  | @recvOk rs e2 rs2 gx hh hs =>
    simp only [recvHighest, hh]
    exact recv_highest_mono hs
  | @sendOk ss e2 ss2 gx hh hs => exact Nat.le_refl _

theorem sentHighest_mono {st st' : Stream.State} {e : Stream.Event} {fx : List Stream.Effect}
    (h : Stream.Step st e (.ok st' fx)) : sentHighest st ≤ sentHighest st' := by
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    simp only [sentHighest, hh]
    exact send_sent_mono hs
  | @recvOk rs e2 rs2 gx hh hs => exact Nat.le_refl _

/-- The step-level form, for either side's weight. -/
theorem sum_afterStep {s : State} {id : StreamId} {st st' : Stream.State} {t : Nat}
    {w : Stream.State → Nat} (hst : st = s.get id) (hzero : w (s.freshStream id) = 0)
    (hmono : w st ≤ w st') (htot : t = sumBy w s.streams) :
    t + (w st' - w st) = sumBy w (s.streams.set id st') := by
  subst htot
  cases hg : s.streams.get? id with
  | none =>
    have h0 : w st = 0 := by rw [hst, State.get, hg, Option.getD_none, hzero]
    rw [sumBy_set_of_none w s.streams id st' hg, h0]
    omega
  | some old =>
    have h0 : st = old := by rw [hst, State.get, hg]; rfl
    have hs := sumBy_set_of_some w s.streams id st' old hg
    subst h0
    omega

/-- **(a′) receive side.**  What the connection-level flow controller tracks is
    the sum of the highest received offsets over every stream in the table. -/
theorem recvTotal_eq_sum {s₀ s : State} (h0 : Inv s₀)
    (hsum : s₀.recvTotal = sumBy recvHighest s₀.streams) (h : component.Reachable s₀ s) :
    s.recvTotal = sumBy recvHighest s.streams := by
  refine component.reachable_induction
    (motive := fun s => s.recvTotal = sumBy recvHighest s.streams) hsum ?_ h
  intro a b e fx hr hstep prev
  have hia : Inv a := component.inv_of_reachable h0 hr
  cases hstep with
  | @existOk id e2 st2 gx hx hb hs hfc =>
    exact sum_afterStep rfl (recvHighest_freshStream a id) (recvHighest_mono hs) prev
  | @openOk id e2 st2 gx hx hp hr' hl hs hfc =>
    refine sum_afterStep (w := recvHighest) ?_ (recvHighest_freshStream a id)
      (recvHighest_mono hs) prev
    exact (get_of_not_has hia hx).symm
  | _ => exact prev

/-- **(a′) send side.** -/
theorem sentTotal_eq_sum {s₀ s : State} (h0 : Inv s₀)
    (hsum : s₀.sentTotal = sumBy sentHighest s₀.streams) (h : component.Reachable s₀ s) :
    s.sentTotal = sumBy sentHighest s.streams := by
  refine component.reachable_induction
    (motive := fun s => s.sentTotal = sumBy sentHighest s.streams) hsum ?_ h
  intro a b e fx hr hstep prev
  have hia : Inv a := component.inv_of_reachable h0 hr
  cases hstep with
  | @existOk id e2 st2 gx hx hb hs hfc =>
    exact sum_afterStep rfl (sentHighest_freshStream a id) (sentHighest_mono hs) prev
  | @openOk id e2 st2 gx hx hp hr' hl hs hfc =>
    refine sum_afterStep (w := sentHighest) ?_ (sentHighest_freshStream a id)
      (sentHighest_mono hs) prev
    exact (get_of_not_has hia hx).symm
  | _ => exact prev

/-! ### (b) Stream-count limits -/

/-- **(b) The peer never opens more streams of a type than we advertised.**
    §19.11, line 7815: "An endpoint MUST terminate a connection with a
    STREAM_LIMIT_ERROR error if a peer opens more streams than was
    permitted." -/
theorem openedRemote_le_advertised {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (d : StreamDir) :
    s.opened.get s.role.peer d ≤ s.maxStreamsLocal.get d :=
  (component.inv_of_reachable h0 h).2.2.1 d

/-- **(b, our side) We never open more streams than the peer allowed.**
    §4.6, line 1546: "Endpoints MUST NOT exceed the limit set by their peer." -/
theorem openedLocal_le_peer {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (d : StreamDir) :
    s.opened.get s.role d ≤ s.maxStreamsPeer.get d :=
  (component.inv_of_reachable h0 h).2.2.2.1 d

/-! ### (c) A stream ID is never reused -/

theorem opened_step {s s' : State} {e : Event} {fx : List Effect}
    (h : Step s e (.ok s' fx)) (r : Role) (d : StreamDir) :
    s.opened.get r d ≤ s'.opened.get r d := by
  cases h with
  | @openOk id e2 st2 gx hx hp hr hl hs hfc =>
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
    | @existOk id₀ e2 st2 gx hx hb hs hfc =>
      simp only [List.mem_map] at hmem
      obtain ⟨a, -, ha⟩ := hmem
      exact absurd ha (by simp)
    | @openOk id₀ e2 st2 gx hx hp hr hl hs hfc =>
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

/-- **(d) §2.1, line 718**: "A stream ID that is used out of order results in
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
  | @existOk id₀ e2 st2 gx hx hb hs hfc =>
    by_cases hide : id = id₀
    · subst hide
      exact Or.inr ⟨e2, gx, by rw [afterStep_get_self]; exact hs⟩
    · exact Or.inl (afterStep_get_of_ne s _ _ hide)
  | @openOk id₀ e2 st2 gx hx hp hr hl hs hfc =>
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
    advertised for it (§4.1, line 1368; `Stream.highest_le_maxData`). -/
theorem stream_highest_le_maxData {s₀ s : State} (h0 : Inv s₀)
    (h : component.Reachable s₀ s) (id : StreamId) {rs : Stream.Recv.State}
    (hr : (s.get id).recv = some rs) : rs.highest ≤ rs.maxData :=
  ((stream_inv h0 h id).2.2.2 rs hr).2.2.1

/-- **(e₂) Lifted from WP2**: the final size of a stream, once known, never
    changes (§4.5, line 1517; `Stream.finalSize_immutable`) — on both halves of
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

/-- **(f) §4.1, line 1364 and §4.6, line 1551**: a smaller limit "has no
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

/-- §19.8, line 7637 (STREAM), §19.5, line 7473 (STOP_SENDING) and §19.10,
    line 7734 (MAX_STREAM_DATA): a frame for a locally-initiated stream that has
    not yet been created is a STREAM_STATE_ERROR — and nothing else is
    permitted.  §19.4, line 7431 and §19.13, line 7863 add RESET_STREAM and
    STREAM_DATA_BLOCKED for a locally-initiated *unidirectional* stream, which
    is send-only; `localNotCreatedMandatory` is exactly that set. -/
theorem localNotCreated_iff (s : State) (id : StreamId) (e : Stream.Event)
    (hx : s.has id = false) (hp : peerFrame e = true) (hr : id.initiator = s.role)
    (hm : localNotCreatedMandatory id e = true) (o : Out) :
    Step s (.stream id e) o ↔ o = .error .streamStateError := by
  rw [← outcomes_iff]
  simp [outcomes, streamOutcomes, hx, hp, hr, hm]

/-- Review finding S-2: where the text mandates nothing — a RESET_STREAM or a
    STREAM_DATA_BLOCKED for a locally-initiated *bidirectional* stream that has
    not been created — exactly two outcomes are permitted, the
    STREAM_STATE_ERROR and ignoring the frame. -/
theorem localNotCreatedIgnored_iff (s : State) (id : StreamId) (e : Stream.Event)
    (hx : s.has id = false) (hp : peerFrame e = true) (hr : id.initiator = s.role)
    (hm : localNotCreatedMandatory id e = false) (o : Out) :
    Step s (.stream id e) o ↔ (o = .error .streamStateError ∨ o = .ok s []) := by
  rw [← outcomes_iff]
  simp [outcomes, streamOutcomes, hx, hp, hr, hm]

/-- §4.6, line 1546: a frame for a peer-initiated stream beyond the limit we
    advertised is a STREAM_LIMIT_ERROR. -/
theorem openLimit_error (s : State) (id : StreamId) (e : Stream.Event)
    (hx : s.has id = false) (hp : peerFrame e = true) (hr : ¬ id.initiator = s.role)
    (hl : s.maxStreamsLocal.get id.dir ≤ id.index) :
    component.accepts s (.stream id e) (.error .streamLimitError) = true :=
  (component.accepts_iff _ _ _).mpr (.openLimit hx hp hr hl)

/-- … and the hypothesis `s.has id = false` of `openLimit_error` is free: in a
    state satisfying the invariant, a peer-initiated stream ID beyond the limit
    we advertised cannot already exist.  So `Step.openLimit` really does cover
    every frame §4.6, line 1546 speaks of. -/
theorem not_has_of_exceeding_limit {s : State} (hi : Inv s) {id : StreamId}
    (hr : ¬ id.initiator = s.role) (hl : s.maxStreamsLocal.get id.dir ≤ id.index) :
    s.has id = false := by
  rw [State.has, decide_eq_false_iff_not, Nat.not_lt, eq_peer_of_ne hr]
  exact Nat.le_trans (hi.2.2.1 id.dir) hl

/-- §2.1, line 718: receiving a frame for a *peer-initiated* stream that does
    not exist yet opens it and every lower-numbered stream of its type.  The
    hypothesis `hr` is needed since review finding S-2: a frame for an uncreated
    *locally*-initiated stream may also be ignored (`Step.localNotCreatedIgnored`),
    and ignoring it opens nothing — a locally-initiated stream is opened by
    `Event.appOpenStream`, never by a frame from the peer. -/
theorem openOk_opens_lower {s s' : State} {id : StreamId} {e : Stream.Event}
    {fx : List Effect} (h : Step s (.stream id e) (.ok s' fx)) (hx : s.has id = false)
    (hr : ¬ id.initiator = s.role) {n : Nat} (hn : n ≤ id.index) :
    s'.has (StreamId.make id.initiator id.dir n) = true := by
  cases h with
  | @existOk _ _ st2 gx hx' hb hs hfc => exact absurd (hx.symm.trans hx') (by simp)
  | @localNotCreatedIgnored _ _ hx' hp hr' hm => exact absurd hr' hr
  | @openOk _ _ st2 gx hx' hp hr' hl hs hfc =>
    rw [afterStep_has]
    simp only [State.has, openThrough_opened, StreamId.initiator_make, StreamId.dir_make,
      StreamId.index_make, and_self, reduceIte, decide_eq_true_eq]
    omega


end Quic.Spec.StreamTable
