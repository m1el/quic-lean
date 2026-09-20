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
      value that it has sent"; §4.1, line 1368 says the same.  The bytes that
      count are the ones the *stream* accepts (§4.5, line 1495), so this rule
      fires only for an outcome in which the stream's own highest received
      offset moves past the connection-level credit. -/
  | existFlowControl {s id e st' fx} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (h : Stream.Step (s.get id) e (.ok st' fx))
      (hfc : connRecvViolation s (s.get id) st' = true) :
      Step s (.stream id e) (.error .flowControlError)
  /-- The stream's own rules (WP2) turn the event into a connection error.  This
      is permitted whether or not a connection-level rule was violated too: the
      text fixes no order between the checks. -/
  | existErr {s id e c} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (h : Stream.Step (s.get id) e (.error c)) :
      Step s (.stream id e) (.error c)
  /-- The stream accepts the event; the connection-level totals move with the
      stream's own accounting (§4.1, line 1358). -/
  | existOk {s id e st' fx} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (h : Stream.Step (s.get id) e (.ok st' fx))
      (hfc : connRecvViolation s (s.get id) st' = false) :
      Step s (.stream id e)
        (.ok (afterStep s id (s.get id) st') (firstUse s id e ++ fx.map (Effect.stream id)))
  /-- The stream ignores the event entirely; nothing is charged. -/
  | existDrop {s id e} (hx : s.has id = true)
      (hb : connSendBlocked s (s.get id) e = false)
      (h : Stream.Step (s.get id) e .drop) :
      Step s (.stream id e) .drop
  -- ### A peer-initiated stream that does not exist yet
  /-- §4.6, line 1546: "An endpoint that receives a frame with a stream ID
      exceeding the limit it has sent MUST treat this as a connection error of
      type STREAM_LIMIT_ERROR."  §4.6, line 1530: only streams with an index
      below the advertised limit may be opened. -/
  | openLimit {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role) (hl : s.maxStreamsLocal.get id.dir ≤ id.index) :
      Step s (.stream id e) (.error .streamLimitError)
  /-- §19.9, line 7712 again, for the stream the frame opens. -/
  | openFlowControl {s id e st' fx} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (h : Stream.Step (s.freshStream id) e (.ok st' fx))
      (hfc : connRecvViolation s (s.freshStream id) st' = true) :
      Step s (.stream id e) (.error .flowControlError)
  /-- The frame opens the stream and the stream's own rules (WP2) reject it —
      for instance a STREAM frame for a send-only stream (§19.8, line 7637). -/
  | openErr {s id e c} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role) (h : Stream.Step (s.freshStream id) e (.error c)) :
      Step s (.stream id e) (.error c)
  /-- §2.1, line 718: "A stream ID that is used out of order results in all
      streams of that type with lower-numbered stream IDs also being opened."
      The stream and every lower-numbered stream of its type are opened, then
      the frame is delivered. -/
  | openOk {s id e st' fx} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (hl : ¬ s.maxStreamsLocal.get id.dir ≤ id.index)
      (h : Stream.Step (s.freshStream id) e (.ok st' fx))
      (hfc : connRecvViolation s (s.freshStream id) st' = false) :
      Step s (.stream id e)
        (.ok (afterStep (s.openThrough id) id (s.freshStream id) st')
             (openedEffects s id ++ fx.map (Effect.stream id)))
  /-- The stream's own rules ignore the frame; nothing is opened, because
      nothing about the stream changes. -/
  | openDrop {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : ¬ id.initiator = s.role)
      (hl : ¬ s.maxStreamsLocal.get id.dir ≤ id.index)
      (h : Stream.Step (s.freshStream id) e .drop) :
      Step s (.stream id e) .drop
  -- ### A locally-initiated stream that does not exist yet
  /-- §19.8, line 7637: "An endpoint MUST terminate the connection with error
      STREAM_STATE_ERROR if it receives a STREAM frame for a locally-initiated
      stream that has not yet been created"; §19.5, line 7473 (STOP_SENDING) and
      §19.10, line 7734 (MAX_STREAM_DATA) say the same.  §19.4, line 7431
      (RESET_STREAM) and §19.13, line 7863 (STREAM_DATA_BLOCKED) say it only of
      a *send-only* stream, which a locally-initiated stream is exactly when it
      is unidirectional — see `localNotCreatedMandatory`. -/
  | localNotCreated {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : id.initiator = s.role) :
      Step s (.stream id e) (.error .streamStateError)
  /-- Where the text mandates nothing — a RESET_STREAM or STREAM_DATA_BLOCKED
      for a locally-initiated *bidirectional* stream that has not been created —
      ignoring the frame is permitted too (review finding S-2).  §4.5,
      line 1522 is the text's own reason: an endpoint need not "maintain the
      final size state for closed streams", so it cannot in general tell a
      stream it never created from one it created and closed, and the text never
      asks it to.  The outcome is `.ok s []`, not `.drop`: the frame is
      processed to no effect and the packet carrying it is still acknowledged. -/
  | localNotCreatedIgnored {s id e} (hx : s.has id = false) (hp : peerFrame e = true)
      (hr : id.initiator = s.role) (hm : localNotCreatedMandatory id e = false) :
      Step s (.stream id e) (.ok s [])
  /-- A local action on a stream that does not exist cannot happen. -/
  | absentLocalAction {s id e} (hx : s.has id = false) (hp : peerFrame e = false) :
      Step s (.stream id e) .drop
  -- ### Connection-level frames
  /-- §4.1, line 1372: "A sender MUST ignore any MAX_STREAM_DATA or MAX_DATA
      frames that do not increase flow control limits." -/
  | maxDataStale {s v} (h : v ≤ s.maxDataPeer) : Step s (.recvMaxData v) (.ok s [])
  /-- §4.1, line 1356: "A receiver can advertise a larger limit for a connection
      by sending a MAX_DATA frame." -/
  | maxDataRaise {s v} (h : s.maxDataPeer < v) :
      Step s (.recvMaxData v) (.ok { s with maxDataPeer := v } [.dataCreditAvailable v])
  /-- §19.12, line 7827: DATA_BLOCKED is a signal only; it changes nothing. -/
  | dataBlocked {s v} : Step s (.recvDataBlocked v) (.ok s [])
  /-- §19.11, line 7803: "Receipt of a frame that permits opening of a stream
      larger than this limit MUST be treated as a FRAME_ENCODING_ERROR." -/
  | maxStreamsTooLarge {s dir v} (h : maxStreamsLimit < v) :
      Step s (.recvMaxStreams dir v) (.error .frameEncodingError)
  /-- §19.11, line 7809: "MAX_STREAMS frames that do not increase the stream
      limit MUST be ignored"; §4.6, line 1552 says the same. -/
  | maxStreamsStale {s dir v} (h : v ≤ maxStreamsLimit) (hle : v ≤ s.maxStreamsPeer.get dir) :
      Step s (.recvMaxStreams dir v) (.ok s [])
  /-- §4.6, line 1533: "Subsequent limits are advertised using MAX_STREAMS
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
  /-- §19.14, line 7901: "A STREAMS_BLOCKED frame does not open the stream, but
      informs the peer that a new stream was needed". -/
  | streamsBlockedOk {s dir v} (h : v ≤ maxStreamsLimit) :
      Step s (.recvStreamsBlocked dir v) (.ok s [])
  -- ### Local actions
  /-- §4.6, line 1546: "Endpoints MUST NOT exceed the limit set by their peer."
      Opening is sequential, so the new stream's index is the high-water mark. -/
  | openLocal {s dir} (h : s.opened.get s.role dir < s.maxStreamsPeer.get dir) :
      Step s (.appOpenStream dir)
        (.ok { s with opened := s.opened.set s.role dir (s.opened.get s.role dir + 1) }
             [.streamOpened (s.nextLocal dir)])
  /-- §4.6, line 1561: an endpoint that cannot open a stream "SHOULD send a
      STREAMS_BLOCKED frame"; the stream itself is not created. -/
  | openLocalBlocked {s dir} (h : s.maxStreamsPeer.get dir ≤ s.opened.get s.role dir) :
      Step s (.appOpenStream dir) .drop
  /-- §4.1, line 1364: "Once a receiver advertises a limit for the connection or
      a stream, it is not an error to advertise a smaller limit, but the smaller
      limit has no effect." -/
  | sendMaxData {s v} (h : v ≤ maxVarint) :
      Step s (.sentMaxData v) (.ok { s with maxDataLocal := max s.maxDataLocal v } [])
  /-- §16: a value that cannot be encoded as a variable-length integer is not
      sent. -/
  | sendMaxDataForbidden {s v} (h : maxVarint < v) : Step s (.sentMaxData v) .drop
  /-- §4.6, line 1551: "Once a receiver advertises a stream limit using the
      MAX_STREAMS frame, advertising a smaller limit has no effect." -/
  | sendMaxStreams {s dir v} (h : v ≤ maxStreamsLimit) :
      Step s (.sentMaxStreams dir v)
        (.ok { s with maxStreamsLocal :=
                 s.maxStreamsLocal.set dir (max (s.maxStreamsLocal.get dir) v) } [])
  /-- §19.11, line 7802: a limit above 2^60 cannot be advertised. -/
  | sendMaxStreamsForbidden {s dir v} (h : maxStreamsLimit < v) :
      Step s (.sentMaxStreams dir v) .drop

/-! ## 3. Executable form -/

/-- Routing one stream-scoped event by stream ID.

    The connection-level flow-control check is inside `delegate` (through
    `lift`), because what it charges is what the stream accepts; the two checks
    that do *not* depend on the stream's answer — the peer's MAX_DATA on the
    send side and the stream limit of §4.6 — stay here. -/
def streamOutcomes (s : State) (id : StreamId) (e : Stream.Event) : List Out :=
  if s.has id then
    if connSendBlocked s (s.get id) e then [.drop]
    else delegate s id (s.get id) (firstUse s id e) e
  else if peerFrame e then
    if id.initiator = s.role then
      if localNotCreatedMandatory id e then [.error .streamStateError]
      else [.error .streamStateError, .ok s []]
    else if s.maxStreamsLocal.get id.dir ≤ id.index then
      -- an error outcome carries no effects (`lift`), so none are built for it
      .error .streamLimitError ::
        (delegate (s.openThrough id) id (s.freshStream id) [] e).filter isErr
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
      (∃ st' fx, Stream.Step st e (.ok st' fx) ∧ connRecvViolation base st st' = true ∧
        o = .error .flowControlError) ∨
      (∃ st' fx, Stream.Step st e (.ok st' fx) ∧ connRecvViolation base st st' = false ∧
        o = .ok (afterStep base id st st') (pre ++ fx.map (Effect.stream id))) ∨
      (∃ c, Stream.Step st e (.error c) ∧ o = .error c) ∨
      (Stream.Step st e .drop ∧ o = .drop) := by
  simp only [delegate, List.mem_map]
  constructor
  · rintro ⟨o', ho', rfl⟩
    have hs := (Stream.outcomes_iff st e o').mp ho'
    cases o' with
    | ok st' fx =>
      by_cases hv : connRecvViolation base st st' = true
      · exact Or.inl ⟨st', fx, hs, hv, by simp [lift, hv]⟩
      · have hv' : connRecvViolation base st st' = false := Bool.eq_false_iff.mpr hv
        exact Or.inr (Or.inl ⟨st', fx, hs, hv', by simp [lift, hv']⟩)
    | error c => exact Or.inr (Or.inr (Or.inl ⟨c, hs, rfl⟩))
    | drop => exact Or.inr (Or.inr (Or.inr ⟨hs, rfl⟩))
  · rintro (⟨st', fx, hs, hv, rfl⟩ | ⟨st', fx, hs, hv, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩)
    · exact ⟨.ok st' fx, (Stream.outcomes_iff _ _ _).mpr hs, by simp [lift, hv]⟩
    · exact ⟨.ok st' fx, (Stream.outcomes_iff _ _ _).mpr hs, by simp [lift, hv]⟩
    · exact ⟨.error c, (Stream.outcomes_iff _ _ _).mpr hs, rfl⟩
    · exact ⟨.drop, (Stream.outcomes_iff _ _ _).mpr hs, rfl⟩

theorem mem_delegate_filter {base : State} {id : StreamId} {st : Stream.State}
    {pre : List Effect} {e : Stream.Event} {o : Out} :
    o ∈ (delegate base id st pre e).filter isErr ↔
      (∃ st' fx, Stream.Step st e (.ok st' fx) ∧ connRecvViolation base st st' = true ∧
        o = .error .flowControlError) ∨
      (∃ c, Stream.Step st e (.error c) ∧ o = .error c) := by
  simp only [List.mem_filter, mem_delegate]
  constructor
  · rintro ⟨h, he⟩
    rcases h with ⟨st', fx, hs, hv, rfl⟩ | ⟨st', fx, _, _, rfl⟩ | ⟨c, hs, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl ⟨st', fx, hs, hv, rfl⟩
    · exact absurd he (by simp [isErr])
    · exact Or.inr ⟨c, hs, rfl⟩
    · exact absurd he (by simp [isErr])
  · rintro (⟨st', fx, hs, hv, rfl⟩ | ⟨c, hs, rfl⟩)
    · exact ⟨Or.inl ⟨st', fx, hs, hv, rfl⟩, by simp [isErr]⟩
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨c, hs, rfl⟩)), by simp [isErr]⟩

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
        rcases mem_delegate.mp h with ⟨st', fx, hs, hv, rfl⟩ | ⟨st', fx, hs, hv, rfl⟩ |
            ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩
        · exact .existFlowControl hx hb' hs hv
        · simpa using Step.existOk hx hb' hs hv
        · exact .existErr hx hb' hs
        · exact .existDrop hx hb' hs
    · rename_i hx
      have hx' : s.has id = false := Bool.eq_false_iff.mpr hx
      split at h
      · rename_i hp
        split at h
        · rename_i hr
          split at h
          · simp only [List.mem_singleton] at h; subst h
            exact .localNotCreated hx' hp hr
          · rename_i hm
            have hm' : localNotCreatedMandatory id e = false := Bool.eq_false_iff.mpr hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h <;> subst h
            · exact .localNotCreated hx' hp hr
            · exact .localNotCreatedIgnored hx' hp hr hm'
        · rename_i hr
          split at h
          · rename_i hl
            simp only [List.mem_cons] at h
            rcases h with h | h
            · subst h; exact .openLimit hx' hp hr hl
            · rcases mem_delegate_filter.mp h with ⟨st', fx, hs, hv, rfl⟩ | ⟨c, hs, rfl⟩
              · exact .openFlowControl hx' hp hr hs hv
              · exact .openErr hx' hp hr hs
          · rename_i hl
            rcases mem_delegate.mp h with ⟨st', fx, hs, hv, rfl⟩ | ⟨st', fx, hs, hv, rfl⟩ |
                ⟨c, hs, rfl⟩ | ⟨hs, rfl⟩
            · exact .openFlowControl hx' hp hr hs hv
            · exact .openOk hx' hp hr hl hs hv
            · exact .openErr hx' hp hr hs
            · exact .openDrop hx' hp hr hl hs
      · rename_i hp
        simp only [List.mem_singleton] at h; subst h
        exact .absentLocalAction hx' (Bool.eq_false_iff.mpr hp)
  · intro h
    cases h with
    | existSendBlocked hx hb => simp [streamOutcomes, hx, hb]
    | @existFlowControl id e st' fx hx hb hs hfc =>
      simp only [streamOutcomes, hx, hb, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inl ⟨st', fx, hs, hfc, rfl⟩)
    | @existErr id e c hx hb hs =>
      simp only [streamOutcomes, hx, hb, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inr (Or.inr (Or.inl ⟨c, hs, rfl⟩)))
    | @existOk id e st' fx hx hb hs hfc =>
      simp only [streamOutcomes, hx, hb, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inr (Or.inl ⟨st', fx, hs, hfc, by simp⟩))
    | @existDrop id e hx hb hs =>
      simp only [streamOutcomes, hx, hb, ite_true, Bool.false_eq_true, ite_false]
      exact mem_delegate.mpr (Or.inr (Or.inr (Or.inr ⟨hs, rfl⟩)))
    | openLimit hx hp hr hl =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true, hl]
      simp
    | @openFlowControl id e st' fx hx hp hr hs hfc =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true]
      split
      · exact List.mem_cons_of_mem _ (mem_delegate_filter.mpr (Or.inl ⟨st', fx, hs, hfc, rfl⟩))
      · exact mem_delegate.mpr (Or.inl ⟨st', fx, hs, hfc, rfl⟩)
    | @openErr id e c hx hp hr hs =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true]
      split
      · exact List.mem_cons_of_mem _ (mem_delegate_filter.mpr (Or.inr ⟨c, hs, rfl⟩))
      · exact mem_delegate.mpr (Or.inr (Or.inr (Or.inl ⟨c, hs, rfl⟩)))
    | @openOk id e st' fx hx hp hr hl hs hfc =>
      simp only [streamOutcomes, hx, hp, hr, hl, Bool.false_eq_true, ite_false, ite_true]
      exact mem_delegate.mpr (Or.inr (Or.inl ⟨st', fx, hs, hfc, rfl⟩))
    | @openDrop id e hx hp hr hl hs =>
      simp only [streamOutcomes, hx, hp, hr, hl, Bool.false_eq_true, ite_false, ite_true]
      exact mem_delegate.mpr (Or.inr (Or.inr (Or.inr ⟨hs, rfl⟩)))
    | localNotCreated hx hp hr =>
      simp only [streamOutcomes, hx, hp, hr, Bool.false_eq_true, ite_false, ite_true]
      split <;> simp
    | localNotCreatedIgnored hx hp hr hm => simp [streamOutcomes, hx, hp, hr, hm]
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
