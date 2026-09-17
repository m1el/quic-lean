import QuicModel.Spec.StreamTable.Defs

/-
  WP9 StreamTable, part 2 of 3: the specification (`Step`), its executable form
  (`outcomes`) and the proof that they agree.
-/
namespace Quic.Spec.StreamTable

/-! ## 2. The specification

One constructor per normative sentence; where several rules are violated at
once the text does not say which error is reported, so each violated rule keeps
its own constructor and `outcomes` lists them all (see NOTES). -/

inductive Step : State → Event → Out → Prop
  -- ### A stream that exists
  /-- §4.1, line 1330: "Senders MUST NOT send data in excess of either limit."
      A frame that would take the connection past the peer's MAX_DATA is not
      transmitted, so nothing happens. -/
  | existSendBlocked {s id e} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = true) :
      Step s (.stream id e) .drop
  /-- §19.9, line 7712: "An endpoint MUST terminate a connection with a
      FLOW_CONTROL_ERROR error if it receives more data than the maximum data
      value that it has sent"; §4.1, line 1359 says the same. -/
  | existFlowControl {s id e} (hx : s.has id = true)
      (hfc : connRecvViolation s (s.get id) e = true) :
      Step s (.stream id e) (.error .flowControlError)
  /-- The stream's own rules (WP2) turn the event into a connection error.  This
      is permitted whether or not a connection-level rule was violated too: the
      text fixes no order between the checks. -/
  | existErr {s id e c} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (h : Stream.Step (s.get id) e (.error c)) :
      Step s (.stream id e) (.error c)
  /-- The stream accepts the event; the connection-level totals move with the
      stream's own accounting (§4.1, line 1352). -/
  | existOk {s id e st' fx} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (hfc : connRecvViolation s (s.get id) e = false)
      (h : Stream.Step (s.get id) e (.ok st' fx)) :
      Step s (.stream id e)
        (.ok (afterStep s id (s.get id) st') (fx.map (Effect.stream id)))
  /-- The stream ignores the event entirely. -/
  | existDrop {s id e} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (hfc : connRecvViolation s (s.get id) e = false)
      (h : Stream.Step (s.get id) e .drop) :
      Step s (.stream id e) .drop
  -- ### A peer-initiated stream that does not exist yet
  /-- §4.6, line 1554: "An endpoint that receives a frame with a stream ID
      exceeding the limit it has sent MUST treat this as a connection error of
      type STREAM_LIMIT_ERROR."  §4.6, line 1531: only streams with an index
      below the advertised limit may be opened. -/
  | openLimit {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role) (hl : s.maxStreamsLocal.get id.dir ≤ id.index) :
      Step s (.stream id e) (.error .streamLimitError)
  /-- §19.9, line 7712 again, for the stream the frame opens. -/
  | openFlowControl {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (hfc : connRecvViolation s (s.freshStream id) e = true) :
      Step s (.stream id e) (.error .flowControlError)
  /-- The frame opens the stream and the stream's own rules (WP2) reject it —
      for instance a STREAM frame for a send-only stream (§19.8, line 7638). -/
  | openErr {s id e c} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role) (h : Stream.Step (s.freshStream id) e (.error c)) :
      Step s (.stream id e) (.error c)
  /-- §2.1, line 712: "A stream ID that is used out of order results in all
      streams of that type with lower-numbered stream IDs also being opened."
      The stream and every lower-numbered stream of its type are opened, then
      the frame is delivered. -/
  | openOk {s id e st' fx} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (hl : ¬ s.maxStreamsLocal.get id.dir ≤ id.index)
      (hfc : connRecvViolation s (s.freshStream id) e = false)
      (h : Stream.Step (s.freshStream id) e (.ok st' fx)) :
      Step s (.stream id e)
        (.ok (afterStep (s.openThrough id) id (s.freshStream id) st')
             (openedEffects s id ++ fx.map (Effect.stream id)))
  /-- The stream's own rules ignore the frame; nothing is opened, because
      nothing about the stream changes. -/
  | openDrop {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (hl : ¬ s.maxStreamsLocal.get id.dir ≤ id.index)
      (hfc : connRecvViolation s (s.freshStream id) e = false)
      (h : Stream.Step (s.freshStream id) e .drop) :
      Step s (.stream id e) .drop
  -- ### A locally-initiated stream that does not exist yet
  /-- §19.8, line 7638: "An endpoint MUST terminate the connection with error
      STREAM_STATE_ERROR if it receives a STREAM frame for a locally-initiated
      stream that has not yet been created"; §19.4, line 7431 (RESET_STREAM),
      §19.5, line 7473 (STOP_SENDING), §19.10, line 7734 (MAX_STREAM_DATA) and
      §19.13, line 7863 (STREAM_DATA_BLOCKED) say the same. -/
  | localNotCreated {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : id.initiator = s.role) :
      Step s (.stream id e) (.error .streamStateError)
  /-- A local action on a stream that does not exist cannot happen. -/
  | absentLocalAction {s id e} (hx : s.has id = false) (hp : peerFrame e = false) :
      Step s (.stream id e) .drop
  -- ### Connection-level frames
  /-- §4.1, line 1361: "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA
      frames that do not increase flow control limits." -/
  | maxDataStale {s v} (h : v ≤ s.maxDataPeer) : Step s (.recvMaxData v) (.ok s [])
  /-- §4.1, line 1353: "A receiver can advertise a larger limit for a connection
      by sending a MAX_DATA frame." -/
  | maxDataRaise {s v} (h : s.maxDataPeer < v) :
      Step s (.recvMaxData v) (.ok { s with maxDataPeer := v } [.dataCreditAvailable v])
  /-- §19.12, line 7828: DATA_BLOCKED is a signal only; it changes nothing. -/
  | dataBlocked {s v} : Step s (.recvDataBlocked v) (.ok s [])
  /-- §19.11, line 7802: "Receipt of a frame that permits opening of a stream
      larger than this limit MUST be treated as a FRAME_ENCODING_ERROR." -/
  | maxStreamsTooLarge {s dir v} (h : maxStreamsLimit < v) :
      Step s (.recvMaxStreams dir v) (.error .frameEncodingError)
  /-- §19.11, line 7809 / §4.6, line 1559: "MAX_STREAMS frames that do not
      increase the stream limit MUST be ignored." -/
  | maxStreamsStale {s dir v} (h : v ≤ maxStreamsLimit) (hle : v ≤ s.maxStreamsPeer.get dir) :
      Step s (.recvMaxStreams dir v) (.ok s [])
  /-- §4.6, line 1536: "Subsequent limits are advertised using MAX_STREAMS
      frames." -/
  | maxStreamsRaise {s dir v} (h : v ≤ maxStreamsLimit) (hgt : s.maxStreamsPeer.get dir < v) :
      Step s (.recvMaxStreams dir v)
        (.ok { s with maxStreamsPeer := s.maxStreamsPeer.set dir v } [.streamsAvailable dir v])
  /-- §19.14, line 7919: "Receipt of a frame that encodes a larger stream ID
      MUST be treated as a STREAM_LIMIT_ERROR or a FRAME_ENCODING_ERROR."
      First alternative. -/
  | streamsBlockedTooLarge₁ {s dir v} (h : maxStreamsLimit < v) :
      Step s (.recvStreamsBlocked dir v) (.error .streamLimitError)
  /-- Same sentence, second alternative. -/
  | streamsBlockedTooLarge₂ {s dir v} (h : maxStreamsLimit < v) :
      Step s (.recvStreamsBlocked dir v) (.error .frameEncodingError)
  /-- §19.14, line 7903: "A STREAMS_BLOCKED frame does not open the stream, but
      informs the peer that a new stream was needed". -/
  | streamsBlockedOk {s dir v} (h : v ≤ maxStreamsLimit) :
      Step s (.recvStreamsBlocked dir v) (.ok s [])
  -- ### Local actions
  /-- §4.6, line 1553: "Endpoints MUST NOT exceed the limit set by their peer."
      Opening is sequential, so the new stream's index is the high-water mark. -/
  | openLocal {s dir} (h : s.opened.get s.role dir < s.maxStreamsPeer.get dir) :
      Step s (.appOpenStream dir)
        (.ok { s with opened := s.opened.set s.role dir (s.opened.get s.role dir + 1) }
             [.streamOpened (s.nextLocal dir)])
  /-- §4.6, line 1569: an endpoint that cannot open a stream "SHOULD send a
      STREAMS_BLOCKED frame"; the stream itself is not created. -/
  | openLocalBlocked {s dir} (h : s.maxStreamsPeer.get dir ≤ s.opened.get s.role dir) :
      Step s (.appOpenStream dir) .drop
  /-- §4.1, line 1357: "Once a receiver advertises a limit for the connection or
      a stream, it is not an error to advertise a smaller limit, but the smaller
      limit has no effect." -/
  | sendMaxData {s v} (h : v ≤ maxVarint) :
      Step s (.sentMaxData v) (.ok { s with maxDataLocal := max s.maxDataLocal v } [])
  /-- §16: a value that cannot be encoded as a variable-length integer is not
      sent. -/
  | sendMaxDataForbidden {s v} (h : maxVarint < v) : Step s (.sentMaxData v) .drop
  /-- §4.6, line 1559: "Once a receiver advertises a stream limit using the
      MAX_STREAMS frame, advertising a smaller limit has no effect." -/
  | sendMaxStreams {s dir v} (h : v ≤ maxStreamsLimit) :
      Step s (.sentMaxStreams dir v)
        (.ok { s with maxStreamsLocal :=
                 s.maxStreamsLocal.set dir (max (s.maxStreamsLocal.get dir) v) } [])
  /-- §19.11, line 7802: a limit above 2^60 cannot be advertised. -/
  | sendMaxStreamsForbidden {s dir v} (h : maxStreamsLimit < v) :
      Step s (.sentMaxStreams dir v) .drop

/-! ## 3. Executable form -/

/-- Routing one stream-scoped event by stream ID. -/
def streamOutcomes (s : State) (id : StreamId) (e : Stream.Event) : List Out :=
  if s.has id then
    if connSendBlocked s (s.get id) e then [.drop]
    else if connRecvViolation s (s.get id) e then
      .error .flowControlError :: (delegate s id (s.get id) [] e).filter isErr
    else delegate s id (s.get id) [] e
  else if peerFrame e then
    if id.initiator = s.role then [.error .streamStateError]
    else if s.maxStreamsLocal.get id.dir ≤ id.index then
      if connRecvViolation s (s.freshStream id) e then
        .error .streamLimitError :: .error .flowControlError ::
          (delegate (s.openThrough id) id (s.freshStream id) (openedEffects s id) e).filter isErr
      else
        .error .streamLimitError ::
          (delegate (s.openThrough id) id (s.freshStream id) (openedEffects s id) e).filter isErr
    else if connRecvViolation s (s.freshStream id) e then
      .error .flowControlError ::
        (delegate (s.openThrough id) id (s.freshStream id) (openedEffects s id) e).filter isErr
    else delegate (s.openThrough id) id (s.freshStream id) (openedEffects s id) e
  else [.drop]

def outcomes (s : State) : Event → List Out
  | .stream id e => streamOutcomes s id e
  | .recvMaxData v =>
      if s.maxDataPeer < v then [.ok { s with maxDataPeer := v } [.dataCreditAvailable v]]
      else [.ok s []]
  | .recvDataBlocked _ => [.ok s []]
  | .recvMaxStreams dir v =>
      if maxStreamsLimit < v then [.error .frameEncodingError]
      else if v ≤ s.maxStreamsPeer.get dir then [.ok s []]
      else [.ok { s with maxStreamsPeer := s.maxStreamsPeer.set dir v } [.streamsAvailable dir v]]
  | .recvStreamsBlocked _ v =>
      if maxStreamsLimit < v then [.error .streamLimitError, .error .frameEncodingError]
      else [.ok s []]
  | .appOpenStream dir =>
      if s.opened.get s.role dir < s.maxStreamsPeer.get dir then
        [.ok { s with opened := s.opened.set s.role dir (s.opened.get s.role dir + 1) }
             [.streamOpened (s.nextLocal dir)]]
      else [.drop]
  | .sentMaxData v =>
      if v ≤ maxVarint then [.ok { s with maxDataLocal := max s.maxDataLocal v } []]
      else [.drop]
  | .sentMaxStreams dir v =>
      if v ≤ maxStreamsLimit then
        [.ok { s with maxStreamsLocal :=
                 s.maxStreamsLocal.set dir (max (s.maxStreamsLocal.get dir) v) } []]
      else [.drop]

/-! ## 4. The two forms agree -/

theorem mem_delegate {base : State} {id : StreamId} {st : Stream.State} {pre : List Effect}
    {e : Stream.Event} {o : Out} :
    o ∈ delegate base id st pre e ↔
      (∃ st' fx, Stream.Step st e (.ok st' fx) ∧
        o = .ok (afterStep base id st st') (pre ++ fx.map (Effect.stream id))) ∨
      (∃ c, Stream.Step st e (.error c) ∧ o = .error c) ∨
      (Stream.Step st e .drop ∧ o = .drop) := by
  simp only [delegate, List.mem_map]
  constructor
  · rintro ⟨o', ho', rfl⟩
    have hs := (Stream.outcomes_iff st e o').mp ho'
    cases o' with
    | ok st' fx => exact Or.inl ⟨st', fx, hs, rfl⟩
    | error c => exact Or.inr (Or.inl ⟨c, hs, rfl⟩)
    | drop => exact Or.inr (Or.inr ⟨hs, rfl⟩)
  · rintro (⟨st', fx, hs, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩)
    · exact ⟨.ok st' fx, (Stream.outcomes_iff _ _ _).mpr hs, rfl⟩
    · exact ⟨.error c, (Stream.outcomes_iff _ _ _).mpr hs, rfl⟩
    · exact ⟨.drop, (Stream.outcomes_iff _ _ _).mpr hs, rfl⟩

theorem mem_delegate_filter {base : State} {id : StreamId} {st : Stream.State}
    {pre : List Effect} {e : Stream.Event} {o : Out} :
    o ∈ (delegate base id st pre e).filter isErr ↔
      ∃ c, Stream.Step st e (.error c) ∧ o = .error c := by
  simp only [List.mem_filter, mem_delegate]
  constructor
  · rintro ⟨h, he⟩
    rcases h with ⟨st', fx, _, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨_, rfl⟩
    · exact absurd he (by simp [isErr])
    · exact ⟨c, hs, rfl⟩
    · exact absurd he (by simp [isErr])
  · rintro ⟨c, hs, rfl⟩
    exact ⟨Or.inr (Or.inl ⟨c, hs, rfl⟩), by simp [isErr]⟩

theorem streamOutcomes_iff (s : State) (id : StreamId) (e : Stream.Event) (o : Out) :
    o ∈ streamOutcomes s id e ↔ Step s (.stream id e) o := by
  constructor
  · intro h
    unfold streamOutcomes at h
    split at h
    · rename_i hx
      split at h
      · rename_i hb
        simp only [List.mem_singleton] at h; subst h
        exact .existSendBlocked hx hb
      · rename_i hb
        have hb' : connSendBlocked s (s.get id) e = false := Bool.eq_false_iff.mpr hb
        split at h
        · rename_i hfc
          simp only [List.mem_cons] at h
          rcases h with h | h
          · subst h; exact .existFlowControl hx hfc
          · obtain ⟨c, hs, rfl⟩ := mem_delegate_filter.mp h
            exact .existErr hx hb' hs
        · rename_i hfc
          have hfc' : connRecvViolation s (s.get id) e = false := Bool.eq_false_iff.mpr hfc
          rcases mem_delegate.mp h with ⟨st', fx, hs, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩
          · simpa using .existOk hx hb' hfc' hs
          · exact .existErr hx hb' hs
          · exact .existDrop hx hb' hfc' hs
    · rename_i hx
      have hx' : s.has id = false := Bool.eq_false_iff.mpr hx
      split at h
      · rename_i hp
        split at h
        · rename_i hr
          simp only [List.mem_singleton] at h; subst h
          exact .localNotCreated hx' hp hr
        · rename_i hr
          split at h
          · rename_i hl
            split at h
            · rename_i hfc
              simp only [List.mem_cons] at h
              rcases h with h | h | h
              · subst h; exact .openLimit hx' hp hr hl
              · subst h; exact .openFlowControl hx' hp hr hfc
              · obtain ⟨c, hs, rfl⟩ := mem_delegate_filter.mp h
                exact .openErr hx' hp hr hs
            · simp only [List.mem_cons] at h
              rcases h with h | h
              · subst h; exact .openLimit hx' hp hr hl
              · obtain ⟨c, hs, rfl⟩ := mem_delegate_filter.mp h
                exact .openErr hx' hp hr hs
          · rename_i hl
            split at h
            · rename_i hfc
              simp only [List.mem_cons] at h
              rcases h with h | h
              · subst h; exact .openFlowControl hx' hp hr hfc
              · obtain ⟨c, hs, rfl⟩ := mem_delegate_filter.mp h
                exact .openErr hx' hp hr hs
            · rename_i hfc
              have hfc' : connRecvViolation s (s.freshStream id) e = false :=
                Bool.eq_false_iff.mpr hfc
              rcases mem_delegate.mp h with ⟨st', fx, hs, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩
              · exact .openOk hx' hp hr hl hfc' hs
              · exact .openErr hx' hp hr hs
              · exact .openDrop hx' hp hr hl hfc' hs
      · rename_i hp
        simp only [List.mem_singleton] at h; subst h
        exact .absentLocalAction hx' (Bool.eq_false_iff.mpr hp)
  · intro h
    cases h with
    | existSendBlocked hx hb => simp [streamOutcomes, hx, hb]
    | existFlowControl hx hfc =>
      simp [streamOutcomes, hx, connSendBlocked_false_of_recvViolation hfc, hfc]
    | @existErr id e c hx hb hs =>
      simp only [streamOutcomes, hx, hb, ite_true, Bool.false_eq_true, ite_false]
      split
      · exact List.mem_cons_of_mem _ (mem_delegate_filter.mpr ⟨c, hs, rfl⟩)
      · exact mem_delegate.mpr (Or.inr (Or.inl ⟨c, hs, rfl⟩))
    | @existOk id e st' fx hx hb hfc hs =>
      simp only [streamOutcomes, hx, hb, hfc, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inl ⟨st', fx, hs, by simp⟩)
    | existDrop hx hb hfc hs =>
      simp only [streamOutcomes, hx, hb, hfc, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inr (Or.inr ⟨hs, rfl⟩))
    | openLimit hx hp hr hl =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true, hl]
      split <;> simp
    | openFlowControl hx hp hr hfc =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true, hfc]
      split
      · simp
      · simp
    | @openErr id e c hx hp hr hs =>
      have hmem : ∀ base pre,
          (.error c : Out) ∈ (delegate base id (s.freshStream id) pre e).filter isErr :=
        fun _ _ => mem_delegate_filter.mpr ⟨c, hs, rfl⟩
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true]
      split
      · split
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmem _ _))
        · exact List.mem_cons_of_mem _ (hmem _ _)
      · split
        · exact List.mem_cons_of_mem _ (hmem _ _)
        · exact mem_delegate.mpr (Or.inr (Or.inl ⟨c, hs, rfl⟩))
    | @openOk id e st' fx hx hp hr hl hfc hs =>
      simp only [streamOutcomes, hx, hp, hr, hl, hfc, Bool.false_eq_true, ite_false, ite_true]
      exact mem_delegate.mpr (Or.inl ⟨st', fx, hs, rfl⟩)
    | openDrop hx hp hr hl hfc hs =>
      simp only [streamOutcomes, hx, hp, hr, hl, hfc, Bool.false_eq_true, ite_false, ite_true]
      exact mem_delegate.mpr (Or.inr (Or.inr ⟨hs, rfl⟩))
    | localNotCreated hx hp hr => simp [streamOutcomes, hx, hp, hr]
    | absentLocalAction hx hp => simp [streamOutcomes, hx, hp]

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  cases e with
  | stream id e => exact streamOutcomes_iff s id e o
  | recvMaxData v =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .maxDataRaise ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .maxDataStale (by omega)
    · intro h
      cases h with
      | maxDataStale hle => simp [outcomes, Nat.not_lt.mpr hle]
      | maxDataRaise hgt => simp [outcomes, hgt]
  | recvDataBlocked v =>
    constructor
    · intro h; simp only [outcomes, List.mem_singleton] at h; subst h; exact .dataBlocked
    · intro h; cases h; simp [outcomes]
  | recvMaxStreams dir v =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .maxStreamsTooLarge ‹_›
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact .maxStreamsStale (by omega) ‹_›
        · simp only [List.mem_singleton] at h; subst h
          exact .maxStreamsRaise (by omega) (by omega)
    · intro h
      cases h with
      | maxStreamsTooLarge hgt => simp [outcomes, hgt]
      | maxStreamsStale h hle => simp [outcomes, Nat.not_lt.mpr h, hle]
      | maxStreamsRaise h hgt => simp [outcomes, Nat.not_lt.mpr h, Nat.not_le.mpr hgt]
  | recvStreamsBlocked dir v =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .streamsBlockedTooLarge₁ ‹_›
        · exact .streamsBlockedTooLarge₂ ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .streamsBlockedOk (by omega)
    · intro h
      cases h with
      | streamsBlockedTooLarge₁ hgt => simp [outcomes, hgt]
      | streamsBlockedTooLarge₂ hgt => simp [outcomes, hgt]
      | streamsBlockedOk hle => simp [outcomes, Nat.not_lt.mpr hle]
  | appOpenStream dir =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .openLocal ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .openLocalBlocked (by omega)
    · intro h
      cases h with
      | openLocal hlt => simp [outcomes, hlt]
      | openLocalBlocked hle => simp [outcomes, Nat.not_lt.mpr hle]
  | sentMaxData v =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .sendMaxData ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .sendMaxDataForbidden (by omega)
    · intro h
      cases h with
      | sendMaxData hle => simp [outcomes, hle]
      | sendMaxDataForbidden hgt => simp [outcomes, Nat.not_le.mpr hgt]
  | sentMaxStreams dir v =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact .sendMaxStreams ‹_›
      · simp only [List.mem_singleton] at h; subst h
        exact .sendMaxStreamsForbidden (by omega)
    · intro h
      cases h with
      | sendMaxStreams hle => simp [outcomes, hle]
      | sendMaxStreamsForbidden hgt => simp [outcomes, Nat.not_le.mpr hgt]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e with
  | stream id e =>
    simp only [outcomes, streamOutcomes]
    repeat' split
    all_goals first
      | exact delegate_ne _ _ _ _ _
      | simp
  | _ => simp only [outcomes] <;> repeat' split
         all_goals simp

end Quic.Spec.StreamTable
