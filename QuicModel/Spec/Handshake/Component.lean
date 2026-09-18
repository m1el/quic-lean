import QuicModel.Spec.Handshake.Basic

/-!
  WP11 "Handshake", part 3: the two forms of the specification agree, the
  invariant, the send side, and the `Component` value.  Sections 4–7 of the
  order `Spec/Template.lean` fixes; sections 1–3 are in `Handshake/Basic.lean`
  and sections 8–10 in `Spec/Handshake.lean`.
-/
namespace Quic.Spec.Handshake

open Quic.Spec.ConnIds (Cid)

/-! ## 4. The two forms agree

One lemma per sub-relation, then the dispatch. -/

theorem mem_headerOutcomes_iff (s : State) (pt : PacketType) (d c : Cid) (o : Out) :
    o ∈ headerOutcomes s pt d c ↔ HdrStep s pt d c o := by
  constructor
  · intro h
    simp only [headerOutcomes] at h
    split at h
    · rename_i hk
      simp only [List.mem_singleton] at h; subst h; exact .keysDiscarded hk
    · rename_i hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> subst h
      · exact .keysAbsentBuffer hk
      · exact .keysAbsentDrop hk
    · rename_i hk
      cases hrole : s.role
      · cases pt
        · simp only [cidOutcomes, hrole] at h
          split at h
          · rename_i hs
            split at h
            · rename_i hc; simp only [List.mem_singleton] at h; subst h
              exact .cliInitialSame hk hrole hs hc
            · rename_i hc; simp only [List.mem_singleton] at h; subst h
              exact .cliInitialOther hk hrole hs hc
          · rename_i hs; simp only [List.mem_singleton] at h; subst h
            exact .cliInitialFirst hk hrole (by simpa using hs)
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .cliZeroRtt hk hrole
        · simp only [cidOutcomes, hrole] at h
          split at h
          · rename_i hs
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
            simp only [List.mem_singleton] at h; subst h
            exact .cliHandshakeOther hk hrole hs.1 hs.2
          · rename_i hs
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hs
            simp only [List.mem_singleton] at h; subst h
            refine .cliHandshakeOk hk hrole ?_
            cases hb : s.sawPeerInitial
            · exact Or.inl rfl
            · by_cases hc : s.peerScid = some c
              · exact Or.inr hc
              · exact absurd hc (hs hb)
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .cliOneRtt hk hrole
        · simp only [cidOutcomes, hrole] at h
          split at h
          · rename_i hs; simp only [List.mem_singleton] at h; subst h
            simp only [Bool.or_eq_true] at hs
            exact .cliRetryLate hk hrole hs
          · rename_i hs; simp only [List.mem_singleton] at h; subst h
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hs
            exact .cliRetryFirst hk hrole hs.1 hs.2
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .cliVn hrole
      · cases pt
        · simp only [cidOutcomes, hrole] at h
          split at h
          · rename_i hs
            split at h
            · rename_i hc; simp only [List.mem_singleton] at h; subst h
              exact .srvInitialSame hk hrole hs hc
            · rename_i hc; simp only [List.mem_singleton] at h; subst h
              exact .srvInitialOther hk hrole hs hc
          · rename_i hs; simp only [List.mem_singleton] at h; subst h
            exact .srvInitialFirst hk hrole (by simpa using hs)
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .srvAppData hk hrole (Or.inl rfl)
        · simp only [cidOutcomes, hrole] at h
          split at h
          · rename_i hd; simp only [List.mem_singleton] at h; subst h
            exact .srvHandshakeAgain hk hrole hd
          · rename_i hd; simp only [List.mem_singleton] at h; subst h
            exact .srvHandshakeDiscard hk hrole hd
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .srvAppData hk hrole (Or.inr rfl)
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .srvRetry hrole
        · simp only [cidOutcomes, hrole, List.mem_singleton] at h; subst h
          exact .srvVn hrole
  · intro h
    cases h with
    | keysDiscarded hk => simp [headerOutcomes, hk]
    | keysAbsentBuffer hk => simp [headerOutcomes, hk]
    | keysAbsentDrop hk => simp [headerOutcomes, hk]
    | cliInitialFirst hk hr hs => simp [headerOutcomes, hk, cidOutcomes, hr, hs]
    | cliInitialSame hk hr hs hc => simp [headerOutcomes, hk, cidOutcomes, hr, hs, hc]
    | cliInitialOther hk hr hs hc => simp [headerOutcomes, hk, cidOutcomes, hr, hs, hc]
    | cliRetryFirst hk hr hs ht => simp [headerOutcomes, hk, cidOutcomes, hr, hs, ht]
    | cliRetryLate hk hr h =>
      rcases h with h | h <;> simp [headerOutcomes, hk, cidOutcomes, hr, h]
    | cliHandshakeOther hk hr hs hc => simp [headerOutcomes, hk, cidOutcomes, hr, hs, hc]
    | cliHandshakeOk hk hr h =>
      rcases h with h | h <;> simp [headerOutcomes, hk, cidOutcomes, hr, h]
    | cliOneRtt hk hr => simp [headerOutcomes, hk, cidOutcomes, hr]
    | cliZeroRtt hk hr => simp [headerOutcomes, hk, cidOutcomes, hr]
    | cliVn hr => simp [headerOutcomes, State.readKeyFor, levelOf, cidOutcomes, hr]
    | srvInitialFirst hk hr hs => simp [headerOutcomes, hk, cidOutcomes, hr, hs]
    | srvInitialSame hk hr hs hc => simp [headerOutcomes, hk, cidOutcomes, hr, hs, hc]
    | srvInitialOther hk hr hs hc => simp [headerOutcomes, hk, cidOutcomes, hr, hs, hc]
    | srvHandshakeDiscard hk hr hd => simp [headerOutcomes, hk, cidOutcomes, hr, hd]
    | srvHandshakeAgain hk hr hd => simp [headerOutcomes, hk, cidOutcomes, hr, hd]
    | srvAppData hk hr hp =>
      rcases hp with rfl | rfl <;> simp [headerOutcomes, hk, cidOutcomes, hr]
    | srvRetry hr => simp [headerOutcomes, State.readKeyFor, levelOf, cidOutcomes, hr]
    | srvVn hr => simp [headerOutcomes, State.readKeyFor, levelOf, cidOutcomes, hr]

theorem mem_cryptoOutcomes_iff (s : State) (l : CryptoLevel) (off len : Nat) (o : Out) :
    o ∈ cryptoOutcomes s l off len ↔ CryptoStep s l off len o := by
  constructor
  · intro h
    simp only [cryptoOutcomes] at h
    split at h
    · rename_i hk; simp only [List.mem_singleton] at h; subst h; exact .levelGone hk
    · rename_i hk
      split at h
      · rename_i ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · exact .tooLargeEncoding hk ho
        · exact .tooLargeBuffer hk ho
      · rename_i ho
        split at h
        · rename_i hd; simp only [List.mem_singleton] at h; subst h
          exact .alreadyDiscarding hk (by omega) hd
        · rename_i hd
          split at h
          · rename_i hb
            split at h
            · rename_i hc
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h | h <;> subst h
              · exact .overflowDiscard hk (by omega) (by simpa using hd) hb hc
              · exact .expand hk (by omega) (by simpa using hd) hb
              · exact .overflowClose hk (by omega) (by simpa using hd) hb
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h <;> subst h
              · exact .expand hk (by omega) (by simpa using hd) hb
              · exact .overflowClose hk (by omega) (by simpa using hd) hb
          · rename_i hb; simp only [List.mem_singleton] at h; subst h
            exact .accept hk (by omega) (by simpa using hd) (by omega)
  · intro h
    cases h with
    | levelGone hk => simp [cryptoOutcomes, hk]
    | tooLargeEncoding hk ho => simp [cryptoOutcomes, hk, ho]
    | tooLargeBuffer hk ho => simp [cryptoOutcomes, hk, ho]
    | alreadyDiscarding hk ho hd =>
      simp [cryptoOutcomes, hk, hd, Nat.not_lt.mpr ho]
    | accept hk ho hd hb =>
      simp [cryptoOutcomes, hk, hd, Nat.not_lt.mpr ho, Nat.not_lt.mpr hb]
    | expand hk ho hd hb =>
      simp only [cryptoOutcomes, hk, hd, Nat.not_lt.mpr ho, hb, ↓reduceIte, Bool.false_eq_true]
      split <;> simp
    | overflowClose hk ho hd hb =>
      simp only [cryptoOutcomes, hk, hd, Nat.not_lt.mpr ho, hb, ↓reduceIte, Bool.false_eq_true]
      split <;> simp
    | overflowDiscard hk ho hd hb hc =>
      simp [cryptoOutcomes, hk, hd, hc, Nat.not_lt.mpr ho, hb]

theorem mem_paramOutcomes_iff (s : State) (b : ByteArray) (o : Out) :
    o ∈ paramOutcomes s b ↔ ParamStep s b o := by
  constructor
  · intro h
    simp only [paramOutcomes, List.mem_flatMap] at h
    obtain ⟨o₁, ho₁, ho⟩ := h
    have hs := (TransportParams.outcomes_iff _ _ _).mp ho₁
    cases o₁ with
    | error e => simp only [List.mem_singleton] at ho; subst ho; exact .wp1Error hs
    | drop => simp only [List.mem_singleton] at ho; subst ho; exact .wp1Drop hs
    | ok tps fx =>
      simp only [authOutcomes] at ho
      split at ho
      · rename_i hp; simp only [List.mem_singleton] at ho; subst ho
        exact .acceptNone hs hp
      · rename_i tp hp
        split at ho
        · rename_i hm; simp only [List.mem_singleton] at ho; subst ho
          exact .missing hs hp hm
        · rename_i hm
          split at ho
          · rename_i hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
            rcases ho with ho | ho <;> subst ho
            · exact .mismatchTpe hs hp (by simpa using hm) hc
            · exact .mismatchPv hs hp (by simpa using hm) hc
          · rename_i hc; simp only [List.mem_singleton] at ho; subst ho
            exact .accept hs hp (by simpa using hm) (by simpa using hc)
  · intro h
    have mem : ∀ o₁ : Outcome TransportParams.State TransportParams.Effect,
        TransportParams.Step ⟨s.role, s.peerParams⟩ (.recvParams b) o₁ →
        ∀ o', o' ∈ (match o₁ with
                    | .error e => [Outcome.error e]
                    | .drop => [Outcome.drop]
                    | .ok tps _ => authOutcomes s tps) → o' ∈ paramOutcomes s b := by
      intro o₁ h₁ o' ho'
      exact List.mem_flatMap.mpr ⟨o₁, (TransportParams.outcomes_iff _ _ _).mpr h₁, ho'⟩
    cases h with
    | wp1Error h => exact mem _ h _ (by simp)
    | wp1Drop h => exact mem _ h _ (by simp)
    | missing h hp hm => exact mem _ h _ (by simp [authOutcomes, hp, hm])
    | mismatchTpe h hp hm hc => exact mem _ h _ (by simp [authOutcomes, hp, hm, hc])
    | mismatchPv h hp hm hc => exact mem _ h _ (by simp [authOutcomes, hp, hm, hc])
    | accept h hp hm hc => exact mem _ h _ (by simp [authOutcomes, hp, hm, hc])
    | acceptNone h hp => exact mem _ h _ (by simp [authOutcomes, hp])

theorem outcomes_iff (s : State) (e : Event) (o : Out) : o ∈ outcomes s e ↔ Step s e o := by
  cases e with
  | tlsKeys dir l =>
    constructor
    · intro h; simp only [outcomes, List.mem_singleton] at h; subst h; exact .keys
    · intro h; cases h with | keys => simp [outcomes]
  | tlsDiscardKeys l =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i hg; simp only [List.mem_singleton] at h; subst h; exact .discardAgain hg
      · rename_i hg; simp only [List.mem_singleton] at h; subst h
        exact .discard (by simpa using hg)
    · intro h
      cases h with
      | discard hg => simp [outcomes, hg]
      | discardAgain hg => simp [outcomes, hg]
  | tlsSend l n =>
    constructor
    · intro h; simp only [outcomes, List.mem_singleton] at h; subst h; exact .send
    · intro h; cases h with | send => simp [outcomes]
  | tlsPeerParams b =>
    constructor
    · intro h; exact .params ((mem_paramOutcomes_iff s b o).mp h)
    · intro h; cases h with | params hp => exact (mem_paramOutcomes_iff s b o).mpr hp
  | tlsZeroRtt a =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i ha; subst ha; simp only [List.mem_singleton] at h; subst h
        exact .zeroRttAccepted
      · rename_i ha
        have : a = false := by simpa using ha
        subst this
        simp only [List.mem_singleton] at h; subst h; exact .zeroRttRejected
    · intro h
      cases h with
      | zeroRttAccepted => simp [outcomes]
      | zeroRttRejected => simp [outcomes]
  | tlsComplete =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i hc; simp only [List.mem_singleton] at h; subst h; exact .completeAgain hc
      · rename_i hc
        have hc' : s.complete = false := by simpa using hc
        split at h
        · rename_i hr; simp only [List.mem_singleton] at h; subst h
          exact .completeServer hc' hr
        · rename_i hr; simp only [List.mem_singleton] at h; subst h
          exact .completeClient hc' hr
    · intro h
      cases h with
      | completeServer hc hr => simp [outcomes, hc, hr]
      | completeClient hc hr => simp [outcomes, hc, hr]
      | completeAgain hc => simp [outcomes, hc]
  | tlsAlert a =>
    constructor
    · intro h; simp only [outcomes, List.mem_singleton] at h; subst h; exact .alert
    · intro h; cases h with | alert => simp [outcomes]
  | recvHeader pt d c =>
    constructor
    · intro h; exact .header ((mem_headerOutcomes_iff s pt d c o).mp h)
    · intro h; cases h with | header hh => exact (mem_headerOutcomes_iff s pt d c o).mpr hh
  | recvCrypto l off len =>
    constructor
    · intro h; exact .crypto ((mem_cryptoOutcomes_iff s l off len o).mp h)
    · intro h; cases h with | crypto hh => exact (mem_cryptoOutcomes_iff s l off len o).mpr hh
  | recvHandshakeDone =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i hr; simp only [List.mem_singleton] at h; subst h; exact .doneServer hr
      · rename_i hr
        split at h
        · rename_i hc; simp only [List.mem_singleton] at h; subst h
          exact .doneClient hr hc
        · rename_i hc; simp only [List.mem_singleton] at h; subst h
          exact .doneEarly hr (by simpa using hc)
    · intro h
      cases h with
      | doneClient hr hc => simp [outcomes, hr, hc]
      | doneEarly hr hc => simp [outcomes, hr, hc]
      | doneServer hr => simp [outcomes, hr]
  | sentPacket pt =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i hc
        obtain ⟨h1, rfl, h3⟩ := hc
        simp only [List.mem_singleton] at h; subst h
        exact .sentHandshake h1 h3
      · rename_i hc
        simp only [List.mem_singleton] at h; subst h
        refine .sentOther ?_
        by_cases h1 : s.role = .client
        · by_cases h2 : pt = .handshake
          · refine Or.inr (Or.inr ?_)
            by_cases h3 : s.write.get .initial = .discarded
            · exact h3
            · exact absurd ⟨h1, h2, h3⟩ hc
          · exact Or.inr (Or.inl h2)
        · exact Or.inl h1
    · intro h
      cases h with
      | sentHandshake hr hd => simp [outcomes, hr, hd]
      | sentOther hp =>
        have hno : ¬(s.role = .client ∧ pt = .handshake ∧ s.write.get .initial ≠ .discarded) := by
          rintro ⟨h1, h2, h3⟩
          rcases hp with h | h | h
          · exact h h1
          · exact h h2
          · exact h3 h
        simp [outcomes, hno]
  | sentRetry c =>
    constructor
    · intro h
      simp only [outcomes] at h
      split at h
      · rename_i hr; simp only [List.mem_singleton] at h; subst h; exact .sentRetry hr
      · rename_i hr; simp only [List.mem_singleton] at h; subst h; exact .sentRetryClient hr
    · intro h
      cases h with
      | sentRetry hr => simp [outcomes, hr]
      | sentRetryClient hr => simp [outcomes, hr]

theorem outcomes_ne (s : State) (e : Event) : outcomes s e ≠ [] := by
  cases e with
  | tlsPeerParams b =>
    simp only [outcomes, paramOutcomes]
    cases hh : TransportParams.outcomes ⟨s.role, s.peerParams⟩ (.recvParams b) with
    | nil => exact absurd hh (TransportParams.outcomes_ne _ _)
    | cons a t =>
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro hnil
      cases a with
      | error e => simp at hnil
      | drop => simp at hnil
      | ok tps fx =>
        simp only [authOutcomes] at hnil
        split at hnil
        · simp at hnil
        · split at hnil
          · simp at hnil
          · split at hnil <;> simp at hnil
  | recvHeader pt d c =>
    simp only [outcomes, headerOutcomes]
    split
    · simp
    · simp
    · cases s.role <;> cases pt <;> simp only [cidOutcomes] <;> repeat' split
      all_goals simp
  | recvCrypto l o n =>
    simp only [outcomes, cryptoOutcomes]; repeat' split
    all_goals simp
  | _ => simp only [outcomes] <;> repeat' split
         all_goals simp

/-! ## 5. Invariant -/

/-- Three things hold of every reachable state:

* the handshake is not confirmed before it is complete (§19.20, line 8207:
  "Servers MUST NOT send a HANDSHAKE_DONE frame before completing the
  handshake", and RFC 9001 §4.1.2 for the client);
* §7.5, line 2703: "Implementations MUST support buffering at least 4096 bytes
  of data received in out-of-order CRYPTO frames";
* every CRYPTO stream is canonical and fully flushed — nothing buffered is
  already deliverable. -/
def Inv (s : State) : Prop :=
  (s.confirmed = true → s.complete = true) ∧ 4096 ≤ s.bufLimit ∧
    ∀ l : CryptoLevel, (s.stream l).WF

theorem stream_setStream (s : State) (l l' : CryptoLevel) (c : Crypto) :
    (s.setStream l c).stream l' = if l' = l then c else s.stream l' :=
  Streams.get_set _ _ _ _

/-- Announcing a key touches nothing but the key sets. -/
theorem provideKey_eq (s : State) (d : KeyDir) (l : Level) :
    ∃ r w, s.provideKey d l = { s with read := r, write := w } := by
  cases d
  · by_cases hd : s.read.get l = .discarded
    · exact ⟨s.read, s.write, by simp [State.provideKey, hd]⟩
    · exact ⟨s.read.set l .present, s.write, by simp [State.provideKey, hd]⟩
  · by_cases hd : s.write.get l = .discarded
    · exact ⟨s.read, s.write, by simp [State.provideKey, hd]⟩
    · exact ⟨s.read, s.write.set l .present, by simp [State.provideKey, hd]⟩

theorem step_inv (s : State) (e : Event) (s' : State) (fx : List Effect)
    (hi : Inv s) (h : Step s e (.ok s' fx)) : Inv s' := by
  obtain ⟨hcc, hbl, hwf⟩ := hi
  cases h with
  | keys =>
    rename_i dir l
    obtain ⟨r, w, he⟩ := provideKey_eq s dir l
    rw [he]
    exact ⟨hcc, hbl, hwf⟩
  | discard => exact ⟨hcc, hbl, hwf⟩
  | discardAgain => exact ⟨hcc, hbl, hwf⟩
  | send =>
    refine ⟨hcc, hbl, fun l' => ?_⟩
    rw [stream_setStream]
    split
    · rename_i he; subst he; exact hwf _
    · exact hwf l'
  | params hp =>
    cases hp with
    | accept => exact ⟨hcc, hbl, hwf⟩
    | acceptNone => exact ⟨hcc, hbl, hwf⟩
  | zeroRttAccepted => exact ⟨hcc, hbl, hwf⟩
  | zeroRttRejected => exact ⟨hcc, hbl, hwf⟩
  | completeServer => exact ⟨fun _ => rfl, hbl, hwf⟩
  | completeClient => exact ⟨fun _ => rfl, hbl, hwf⟩
  | completeAgain => exact ⟨hcc, hbl, hwf⟩
  | header hh =>
    cases hh with
    | keysAbsentBuffer => exact ⟨hcc, hbl, hwf⟩
    | cliInitialFirst => exact ⟨hcc, hbl, hwf⟩
    | cliInitialSame => exact ⟨hcc, hbl, hwf⟩
    | cliRetryFirst => exact ⟨hcc, hbl, hwf⟩
    | cliHandshakeOk => exact ⟨hcc, hbl, hwf⟩
    | cliOneRtt => exact ⟨hcc, hbl, hwf⟩
    | cliVn => exact ⟨hcc, hbl, hwf⟩
    | srvInitialFirst => exact ⟨hcc, hbl, hwf⟩
    | srvInitialSame => exact ⟨hcc, hbl, hwf⟩
    | srvHandshakeDiscard => exact ⟨hcc, hbl, hwf⟩
    | srvHandshakeAgain => exact ⟨hcc, hbl, hwf⟩
    | srvAppData => exact ⟨hcc, hbl, hwf⟩
    | srvVn => exact ⟨hcc, hbl, hwf⟩
  | crypto hh =>
    cases hh with
    | alreadyDiscarding => exact ⟨hcc, hbl, hwf⟩
    | accept =>
      refine ⟨hcc, hbl, fun l' => ?_⟩
      rw [stream_setStream]
      split
      · rename_i he; subst he; exact Crypto.WF_recv (hwf _) _ _
      · exact hwf l'
    | expand =>
      refine ⟨hcc, hbl, fun l' => ?_⟩
      rw [stream_setStream]
      split
      · rename_i he; subst he; exact Crypto.WF_recv (hwf _) _ _
      · exact hwf l'
    | overflowDiscard =>
      refine ⟨hcc, hbl, fun l' => ?_⟩
      rw [stream_setStream]
      split
      · rename_i he; subst he; exact hwf _
      · exact hwf l'
  | doneClient _ hc => exact ⟨fun _ => hc, hbl, hwf⟩
  | doneEarly => exact ⟨hcc, hbl, hwf⟩
  | doneServer => exact ⟨hcc, hbl, hwf⟩
  | sentHandshake => exact ⟨hcc, hbl, hwf⟩
  | sentOther => exact ⟨hcc, hbl, hwf⟩
  | sentRetry => exact ⟨hcc, hbl, hwf⟩
  | sentRetryClient => exact ⟨hcc, hbl, hwf⟩

/-! ## 6. Send side -/

/-- §19.6: a CRYPTO frame at level `l` that we are allowed to put on the wire.
    The bytes must be ones TLS has handed over (an exact repeat is therefore
    always permitted: §12.4, line 4936, "All frames are idempotent in this
    version of QUIC"), the stream must not have been discarded with its keys
    (§17.2.2.1, line 6407), and §19.6's offset limit must hold. -/
def maySendCryptoAt (s : State) (l : CryptoLevel) (off len : Nat) : Bool :=
  decide (off + len ≤ (s.stream l).handed) && decide (off + len ≤ maxCryptoOffset) &&
    !(s.write.get l.level == KeyState.discarded)

def cryptoLevels : List CryptoLevel := [.initial, .handshake, .oneRtt]

theorem mem_cryptoLevels (l : CryptoLevel) : l ∈ cryptoLevels := by
  cases l <;> simp [cryptoLevels]

/-- Frame-level send rules.  A CRYPTO frame does not say which level it belongs
    to, so the frame alone is only required to be sendable at *some* level; the
    level-exact rule is in `MaySendPacket`, which sees the packet type. -/
def MaySend (s : State) : Frame → Prop
  | .crypto off data => ∃ l : CryptoLevel, maySendCryptoAt s l off data.size = true
  -- §19.20, line 8207: "A HANDSHAKE_DONE frame can only be sent by the server.
  -- Servers MUST NOT send a HANDSHAKE_DONE frame before completing the
  -- handshake."
  | .handshakeDone => s.role = .server ∧ s.complete = true
  | _ => True

def maySend (s : State) : Frame → Bool
  | .crypto off data => cryptoLevels.any (fun l => maySendCryptoAt s l off data.size)
  | .handshakeDone => (s.role == .server) && s.complete
  | _ => true

theorem maySend_iff (s : State) (f : Frame) : maySend s f = true ↔ MaySend s f := by
  cases f with
  | crypto off data =>
    simp only [maySend, MaySend, List.any_eq_true]
    constructor
    · rintro ⟨l, _, hl⟩; exact ⟨l, hl⟩
    · rintro ⟨l, hl⟩; exact ⟨l, mem_cryptoLevels l, hl⟩
  | handshakeDone => simp [maySend, MaySend]
  | _ => simp [maySend, MaySend]

/-- The CRYPTO frames of a packet at level `l`. -/
def cryptoFrameOk (s : State) (l : CryptoLevel) : Frame → Bool
  | .crypto off data => maySendCryptoAt s l off data.size
  | _ => true

/-- Packet-level send rules:

* no packet may be sent at a level whose write keys we do not have, or have
  discarded (§17.2.2.1, line 6398: "A client stops both sending and processing
  Initial packets when it sends its first Handshake packet");
* §17.2.3, line 6415: a 0-RTT packet carries early data "from the client to the
  server as part of the first flight", and line 6476: "A client MUST NOT send
  0-RTT packets once it starts processing 1-RTT packets from the server";
* §19.6: a CRYPTO frame must be within what TLS handed over *at this packet's
  level* — the frame-level rule cannot see the level. -/
def MaySendPacket (s : State) (p : OutPacket) : Prop :=
  (∀ l, levelOf p.ptype = some l → s.write.get l = .present) ∧
  (p.ptype = .zeroRtt → s.role = .client ∧ s.processed1Rtt = false) ∧
  (∀ l, cryptoLevelOf p.ptype = some l → ∀ f ∈ p.frames, cryptoFrameOk s l f = true)

def maySendPacket (s : State) (p : OutPacket) : Bool :=
  (match levelOf p.ptype with
   | none => true
   | some l => s.write.get l == KeyState.present) &&
  (match p.ptype with
   | .zeroRtt => (s.role == .client) && !s.processed1Rtt
   | _ => true) &&
  (match cryptoLevelOf p.ptype with
   | none => true
   | some l => p.frames.all (cryptoFrameOk s l))

theorem maySendPacket_iff (s : State) (p : OutPacket) :
    maySendPacket s p = true ↔ MaySendPacket s p := by
  cases hp : p.ptype <;>
    simp [maySendPacket, MaySendPacket, hp, levelOf, cryptoLevelOf, List.all_eq_true]

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
  MaySendPacket := MaySendPacket
  maySendPacket := maySendPacket
  maySendPacket_iff := maySendPacket_iff

end Quic.Spec.Handshake
