import QuicModel.Spec.StreamTable.Step

/-
  WP9 StreamTable, part 3 of 3a: the invariant and its preservation.
-/
namespace Quic.Spec.StreamTable

/-! ## 5. Invariant -/

/-! ### What one stream contributes

Three facts about WP2's `Stream.Step` that the connection needs: a step never
changes which stream it is, and neither half's accounting for connection-level
flow control can move further than the frame that caused it. -/

theorem stream_step_id {st st' : Stream.State} {e : Stream.Event} {fx : List Stream.Effect}
    (h : Stream.Step st e (.ok st' fx)) : st'.id = st.id ∧ st'.role = st.role := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- §4.1, line 1352: the receive-side credit a stream has consumed is its
    highest received offset, which a frame can push no further than its own end
    offset. -/
theorem recv_highest_step {rs rs' : Stream.Recv.State} {e : Stream.Recv.Event}
    {fx : List Stream.Recv.Effect} (h : Stream.Recv.Step rs e (.ok rs' fx)) :
    rs'.highest ≤ max rs.highest
      (match e with
       | .recvStream offset len _ => offset + len
       | .recvResetStream _ fs => fs
       | _ => 0) := by
  cases h with
  | streamOk => exact Nat.le_refl _
  | streamResetComplete => exact Nat.le_refl _
  | resetOk => exact Nat.le_max_right _ _
  | _ => exact Nat.le_max_left _ _

/-- §4.5, line 1479: the send-side credit a stream has consumed is the highest
    offset sent, which only a STREAM or RESET_STREAM frame we transmit moves. -/
theorem send_sent_step {ss ss' : Stream.Send.State} {e : Stream.Send.Event}
    {fx : List Stream.Send.Effect} (h : Stream.Send.Step ss e (.ok ss' fx)) :
    ss'.sent ≤ max ss.sent
      (match e with
       | .sentStream offset len _ => offset + len
       | .sentResetStream _ fs => fs
       | _ => 0) := by
  cases h with
  | sendStream => exact Nat.le_refl _
  | _ => exact Nat.le_max_left _ _

theorem recvHighest_step {st st' : Stream.State} {e : Stream.Event} {fx : List Stream.Effect}
    (h : Stream.Step st e (.ok st' fx)) :
    recvHighest st' ≤ max (recvHighest st) ((recvEnd e).getD 0) := by
  cases h with
  | @recvOk rs e2 rs2 gx hh hs =>
    have h2 := recv_highest_step hs
    simp only [recvHighest, hh]
    cases e2 <;> simpa [recvEnd] using h2
  | @sendOk ss e2 ss2 gx hh hs =>
    simp only [recvHighest]
    exact Nat.le_max_left _ _

theorem sentHighest_step {st st' : Stream.State} {e : Stream.Event} {fx : List Stream.Effect}
    (h : Stream.Step st e (.ok st' fx)) :
    sentHighest st' ≤ max (sentHighest st) ((sentEnd e).getD 0) := by
  cases h with
  | @sendOk ss e2 ss2 gx hh hs =>
    have h2 := send_sent_step hs
    simp only [sentHighest, hh]
    cases e2 <;> simpa [sentEnd] using h2
  | @recvOk rs e2 rs2 gx hh hs =>
    simp only [sentHighest]
    exact Nat.le_max_left _ _

/-! ### The state helpers -/

@[simp] theorem freshStream_id (s : State) (id : StreamId) : (s.freshStream id).id = id := rfl

@[simp] theorem freshStream_role (s : State) (id : StreamId) :
    (s.freshStream id).role = s.role := rfl

theorem freshStream_inv (s : State) (id : StreamId) : Stream.Inv (s.freshStream id) :=
  Stream.init_inv _ _ _ _

@[simp] theorem recvHighest_freshStream (s : State) (id : StreamId) :
    recvHighest (s.freshStream id) = 0 := by
  simp only [recvHighest, State.freshStream, Stream.init]
  cases Stream.hasRecv id s.role <;> rfl

@[simp] theorem sentHighest_freshStream (s : State) (id : StreamId) :
    sentHighest (s.freshStream id) = 0 := by
  simp only [sentHighest, State.freshStream, Stream.init]
  cases Stream.hasSend id s.role <;> rfl

@[simp] theorem openThrough_role (s : State) (id : StreamId) :
    (s.openThrough id).role = s.role := rfl

@[simp] theorem openThrough_streams (s : State) (id : StreamId) :
    (s.openThrough id).streams = s.streams := rfl

@[simp] theorem openThrough_recvTotal (s : State) (id : StreamId) :
    (s.openThrough id).recvTotal = s.recvTotal := rfl

@[simp] theorem openThrough_sentTotal (s : State) (id : StreamId) :
    (s.openThrough id).sentTotal = s.sentTotal := rfl

@[simp] theorem openThrough_maxDataLocal (s : State) (id : StreamId) :
    (s.openThrough id).maxDataLocal = s.maxDataLocal := rfl

@[simp] theorem openThrough_maxDataPeer (s : State) (id : StreamId) :
    (s.openThrough id).maxDataPeer = s.maxDataPeer := rfl

@[simp] theorem openThrough_maxStreamsLocal (s : State) (id : StreamId) :
    (s.openThrough id).maxStreamsLocal = s.maxStreamsLocal := rfl

@[simp] theorem openThrough_maxStreamsPeer (s : State) (id : StreamId) :
    (s.openThrough id).maxStreamsPeer = s.maxStreamsPeer := rfl

@[simp] theorem openThrough_opened (s : State) (id : StreamId) (r : Role) (d : StreamDir) :
    (s.openThrough id).opened.get r d =
      if id.initiator = r ∧ id.dir = d then
        max (s.opened.get id.initiator id.dir) (id.index + 1)
      else s.opened.get r d := by
  simp only [State.openThrough, Opened.get_set]

@[simp] theorem openThrough_freshStream (s : State) (id id' : StreamId) :
    (s.openThrough id).freshStream id' = s.freshStream id' := rfl

@[simp] theorem openThrough_get (s : State) (id id' : StreamId) :
    (s.openThrough id).get id' = s.get id' := rfl

@[simp] theorem openThrough_connRecvViolation (s : State) (id : StreamId) (st : Stream.State)
    (e : Stream.Event) :
    connRecvViolation (s.openThrough id) st e = connRecvViolation s st e := rfl

@[simp] theorem openThrough_connSendBlocked (s : State) (id : StreamId) (st : Stream.State)
    (e : Stream.Event) :
    connSendBlocked (s.openThrough id) st e = connSendBlocked s st e := rfl

/-- §2.1, line 712: after opening `id`, `id` exists … -/
@[simp] theorem has_openThrough_self (s : State) (id : StreamId) :
    (s.openThrough id).has id = true := by
  simp only [State.has, openThrough_opened, and_self, reduceIte, decide_eq_true_eq]
  omega

/-- … and everything that existed still does. -/
theorem has_openThrough (s : State) (id id' : StreamId) (h : s.has id' = true) :
    (s.openThrough id).has id' = true := by
  simp only [State.has, openThrough_opened, decide_eq_true_eq] at h ⊢
  split
  · rename_i hc
    obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    omega
  · exact h

@[simp] theorem afterStep_streams (s : State) (id : StreamId) (st st' : Stream.State) :
    (afterStep s id st st').streams = s.streams.set id st' := rfl

@[simp] theorem afterStep_role (s : State) (id : StreamId) (st st' : Stream.State) :
    (afterStep s id st st').role = s.role := rfl

@[simp] theorem afterStep_has (s : State) (id id' : StreamId) (st st' : Stream.State) :
    (afterStep s id st st').has id' = s.has id' := rfl

@[simp] theorem afterStep_get_self (s : State) (id : StreamId) (st st' : Stream.State) :
    (afterStep s id st st').get id = st' := by
  simp [State.get, afterStep, State.setStream]

theorem afterStep_get_of_ne (s : State) {id id' : StreamId} (st st' : Stream.State)
    (h : id' ≠ id) : (afterStep s id st st').get id' = s.get id' := by
  simp only [State.get, afterStep_streams, Map.get?_set_of_ne _ _ h]
  rfl

/-- The invariant of a whole connection's stream table.

* the two connection-level totals are within the two advertised limits
  (§4.1, line 1359 and §4.1, line 1330 — theorem (a));
* neither side has opened more streams than the other allowed (§4.6,
  line 1553 — theorem (b));
* no advertised stream limit exceeds 2^60 (§4.6, line 1543);
* every stream in the table exists, knows its own ID and our role, and
  satisfies WP2's `Stream.Inv` (theorem (e)). -/
def Inv (s : State) : Prop :=
  s.recvTotal ≤ s.maxDataLocal ∧
  s.sentTotal ≤ s.maxDataPeer ∧
  (∀ d, s.opened.get s.role.peer d ≤ s.maxStreamsLocal.get d) ∧
  (∀ d, s.opened.get s.role d ≤ s.maxStreamsPeer.get d) ∧
  (∀ d, s.maxStreamsLocal.get d ≤ maxStreamsLimit) ∧
  (∀ d, s.maxStreamsPeer.get d ≤ maxStreamsLimit) ∧
  (∀ id st, s.streams.get? id = some st →
    s.has id = true ∧ st.id = id ∧ st.role = s.role ∧ Stream.Inv st)

/-- The initial state satisfies the invariant as soon as the two `max_streams`
    transport parameters are within the 2^60 of §4.6, line 1543 (which is what
    WP1's `TransportParams.Valid` requires of them). -/
theorem init_inv (role : Role) (ours theirs : Limits)
    (h1 : ours.maxStreamsBidi ≤ maxStreamsLimit) (h2 : ours.maxStreamsUni ≤ maxStreamsLimit)
    (h3 : theirs.maxStreamsBidi ≤ maxStreamsLimit) (h4 : theirs.maxStreamsUni ≤ maxStreamsLimit) :
    Inv (init role ours theirs) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro d; cases role <;> cases d <;> exact Nat.zero_le _
  · intro d; cases role <;> cases d <;> exact Nat.zero_le _
  · intro d; cases d <;> assumption
  · intro d; cases d <;> assumption
  · intro id st h; exact absurd h (by simp [init, Map.get?])

/-- Every stream the table can be asked about — in the table or not — knows its
    own identity and satisfies WP2's invariant. -/
theorem inv_get {s : State} (hi : Inv s) (id : StreamId) :
    (s.get id).id = id ∧ (s.get id).role = s.role ∧ Stream.Inv (s.get id) := by
  simp only [State.get]
  cases h : s.streams.get? id with
  | none => exact ⟨rfl, rfl, freshStream_inv s id⟩
  | some st =>
    obtain ⟨-, h1, h2, h3⟩ := hi.2.2.2.2.2.2 id st h
    exact ⟨h1, h2, h3⟩

/-- A stream that does not exist has no entry in the table, so `get` gives its
    initial state. -/
theorem get_of_not_has {s : State} (hi : Inv s) {id : StreamId} (h : s.has id = false) :
    s.get id = s.freshStream id := by
  simp only [State.get]
  cases hg : s.streams.get? id with
  | none => rfl
  | some st =>
    have := (hi.2.2.2.2.2.2 id st hg).1
    rw [this] at h
    exact absurd h (by simp)

/-- The heart of `step_inv`: delivering an event to one stream keeps everything
    the connection tracks in step with it. -/
theorem afterStep_inv {s : State} {id : StreamId} {st st' : Stream.State} {e : Stream.Event}
    {fx : List Stream.Effect} (hi : Inv s) (hh : s.has id = true)
    (hid : st.id = id) (hrole : st.role = s.role) (hst : Stream.Inv st)
    (hfc : connRecvViolation s st e = false) (hb : connSendBlocked s st e = false)
    (h : Stream.Step st e (.ok st' fx)) : Inv (afterStep s id st st') := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
  have hstep := Stream.step_inv st e st' fx hst h
  have hids := stream_step_id h
  have hr := recvHighest_step h
  have hsd := sentHighest_step h
  refine ⟨?_, ?_, i3, i4, i5, i6, ?_⟩
  · show s.recvTotal + (recvHighest st' - recvHighest st) ≤ s.maxDataLocal
    simp only [connRecvViolation] at hfc
    cases he : recvEnd e with
    | none => rw [he] at hr; simp only [Option.getD_none] at hr; omega
    | some k =>
      rw [he] at hfc hr
      simp only [Option.getD_some, decide_eq_false_iff_not, Nat.not_lt] at hfc hr
      omega
  · show s.sentTotal + (sentHighest st' - sentHighest st) ≤ s.maxDataPeer
    simp only [connSendBlocked] at hb
    cases he : sentEnd e with
    | none => rw [he] at hsd; simp only [Option.getD_none] at hsd; omega
    | some k =>
      rw [he] at hb hsd
      simp only [Option.getD_some, decide_eq_false_iff_not, Nat.not_lt] at hb hsd
      omega
  · intro id' st'' hget
    simp only [afterStep_streams] at hget
    by_cases hide : id' = id
    · subst hide
      rw [Map.get?_set_self] at hget
      simp only [Option.some.injEq] at hget
      subst hget
      refine ⟨hh, ?_, ?_, hstep⟩
      · rw [hids.1, hid]
      · show st'.role = s.role
        rw [hids.2, hrole]
    · rw [Map.get?_set_of_ne _ _ hide] at hget
      exact i7 id' st'' hget

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  cases h with
  | @existOk id e2 st2 gx hx hb hfc hs =>
    obtain ⟨hid, hrole, hstinv⟩ := inv_get hi id
    exact afterStep_inv hi hx hid hrole hstinv hfc hb hs
  | @openOk id e2 st2 gx hx hp hr hl hfc hs =>
    have hpeer : id.initiator = s.role.peer := eq_peer_of_ne hr
    have hlt : id.index < s.maxStreamsLocal.get id.dir := Nat.lt_of_not_le hl
    have hbase : Inv (s.openThrough id) := by
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
      refine ⟨i1, i2, ?_, ?_, i5, i6, ?_⟩
      · intro d
        simp only [openThrough_opened, openThrough_maxStreamsLocal, openThrough_role]
        split
        · rename_i hc
          obtain ⟨-, hd⟩ := hc
          rw [← hd, hpeer]
          exact Nat.max_le.mpr ⟨i3 id.dir, hlt⟩
        · exact i3 d
      · intro d
        simp only [openThrough_opened, openThrough_maxStreamsPeer, openThrough_role]
        split
        · rename_i hc; exact absurd hc.1 hr
        · exact i4 d
      · intro id' st'' hget
        simp only [openThrough_streams] at hget
        obtain ⟨h1, h2, h3, h4⟩ := i7 id' st'' hget
        exact ⟨has_openThrough s id id' h1, h2, h3, h4⟩
    exact afterStep_inv hbase (has_openThrough_self s id) rfl rfl (freshStream_inv s id)
      hfc (connSendBlocked_false_of_peerFrame hp) hs
  | maxDataStale => exact hi
  | @maxDataRaise v hgt =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
    exact ⟨i1, by simp only; omega, i3, i4, i5, i6, i7⟩
  | dataBlocked => exact hi
  | maxStreamsStale => exact hi
  | @maxStreamsRaise dir v hle hgt =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
    refine ⟨i1, i2, i3, ?_, i5, ?_, i7⟩
    · intro d
      simp only [Counts.get_set]
      split
      · rename_i hd; subst hd; have := i4 dir; omega
      · exact i4 d
    · intro d
      simp only [Counts.get_set]
      split
      · rename_i hd; subst hd; exact hle
      · exact i6 d
  | streamsBlockedOk => exact hi
  | @openLocal dir hlt =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
    refine ⟨i1, i2, ?_, ?_, i5, i6, ?_⟩
    · intro d
      simp only [Opened.get_set]
      split
      · rename_i hc; exact absurd hc.1 (role_ne_peer s.role)
      · exact i3 d
    · intro d
      simp only [Opened.get_set]
      split
      · rename_i hc
        obtain ⟨-, hd⟩ := hc
        rw [← hd]
        have := i4 dir
        omega
      · exact i4 d
    · intro id' st'' hget
      obtain ⟨h1, h2, h3, h4⟩ := i7 id' st'' hget
      refine ⟨?_, h2, h3, h4⟩
      simp only [State.has, Opened.get_set, decide_eq_true_eq] at h1 ⊢
      split
      · rename_i hc
        obtain ⟨hr1, hd1⟩ := hc
        rw [← hr1, ← hd1] at h1
        omega
      · exact h1
  | @sendMaxData v hle =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
    exact ⟨by simp only; omega, i2, i3, i4, i5, i6, i7⟩
  | @sendMaxStreams dir v hle =>
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hi
    refine ⟨i1, i2, ?_, i4, ?_, i6, i7⟩
    · intro d
      simp only [Counts.get_set]
      split
      · rename_i hd; subst hd; have := i3 dir; omega
      · exact i3 d
    · intro d
      simp only [Counts.get_set]
      split
      · rename_i hd; subst hd; have := i5 dir; omega
      · exact i5 d

end Quic.Spec.StreamTable
