import QuicModel.Spec.Endpoint.Pipeline

/-!
  WP12 "Endpoint", part 3 (continued): the other four event families —
  the application, TLS, the clock, and the endpoint's own decisions — and the
  `sendPending` post-pass.

  Nothing here invents a rule: every branch is one of the merged components'
  own events, and the only thing this file adds is *which* component (or
  components) a request is routed to.
-/
namespace Quic.Spec.Endpoint

open Quic.Spec

/-! ## 3a. The application -/

def appEvent (now : Time) (a : AppAction) (s : State) : List Out :=
  match a with
  | .openStream dir => stepSt s (.appOpenStream dir)
  | .write id len => stepSt s (.stream id (.send (.appWrite len)))
  | .fin id => stepSt s (.stream id (.send .appEnd))
  | .reset id code => stepSt s (.stream id (.send (.appReset code)))
  | .stopSending id code => stepSt s (.stream id (.recv (.appAbortRead code)))
  | .read id len => stepSt s (.stream id (.recv (.appRead len)))
  | .extendMaxStreamData id v => stepSt s (.stream id (.recv (.sentMaxStreamData v)))
  | .extendMaxData v => stepSt s (.sentMaxData v)
  | .extendMaxStreams dir v => stepSt s (.sentMaxStreams dir v)
  | .close code => stepTerm s (.appClose now s.pto code)

theorem appEvent_ne (now : Time) (a : AppAction) (s : State) : appEvent now a s ≠ [] := by
  cases a <;> simp only [appEvent] <;> first | exact stepSt_ne _ _ | exact stepTerm_ne _ _

theorem appEvent_inv {s : State} (hs : Inv s) (now : Time) (a : AppAction) :
    InvOk (appEvent now a s) := by
  cases a <;> simp only [appEvent] <;>
    first | exact stepSt_inv hs _ | exact stepTerm_inv hs _

/-! ## 3b. A frame we put on the wire

The bookkeeping every component needs when a frame it governs actually travels
(§3.1's "Sending the first STREAM … frame", §8.2.2 line 3205's "MUST NOT send
more than one PATH_RESPONSE", §13.2.1's discharge of the acknowledgment
obligation, §17.2.2 line 6378's "the first CRYPTO frame sent always begins at an
offset of 0"). -/

def sentFrame (pt : PacketType) (p : Migration.Path) (f : Frame) (s : State) : List Out :=
  match f with
  | .stream id off fin data => stepSt s (.stream ⟨id⟩ (.send (.sentStream off data.size fin)))
  | .resetStream id code fs => stepSt s (.stream ⟨id⟩ (.send (.sentResetStream code fs)))
  | .streamDataBlocked id v => stepSt s (.stream ⟨id⟩ (.send (.sentStreamDataBlocked v)))
  | .maxStreamData id v => stepSt s (.stream ⟨id⟩ (.recv (.sentMaxStreamData v)))
  | .stopSending id code => stepSt s (.stream ⟨id⟩ (.recv (.sentStopSending code)))
  | .maxData v => stepSt s (.sentMaxData v)
  | .maxStreams dir v => stepSt s (.sentMaxStreams dir v)
  | .pathResponse d => stepPvThen s p (.responseSent (s.pathOf p) d)
  | .crypto off data =>
    match cryptoLevelOf pt with
    | some l => stepHs s (.sentCrypto l off data.size)
    | none => keep s
  | .ack largest _ first ranges _ =>
    match pt.space with
    | some sp => stepAck s sp (.sentAck largest first ranges.toList)
    | none => keep s
  -- PATH_CHALLENGE was recorded when the validation started (§8.2.1); every
  -- other frame changes no component's state by being transmitted.
  | _ => keep s

theorem sentFrame_ne (pt : PacketType) (p : Migration.Path) (f : Frame) (s : State) :
    sentFrame pt p f s ≠ [] := by
  cases f <;> simp only [sentFrame] <;>
    first
      | exact keep_ne _
      | exact stepSt_ne _ _
      | exact stepPvThen_ne _ _ _
      | (split <;> first | exact keep_ne _ | exact stepHs_ne _ _ | exact stepAck_ne _ _ _)

theorem sentFrame_inv {s : State} (hs : Inv s) (pt : PacketType) (p : Migration.Path)
    (f : Frame) : InvOk (sentFrame pt p f s) := by
  cases f <;> simp only [sentFrame] <;>
    first
      | exact keep_inv hs
      | exact stepSt_inv hs _
      | exact stepPvThen_inv hs _ _
      | (split <;>
          first | exact keep_inv hs | exact stepHs_inv hs _ | exact stepAck_inv hs _ _)

/-! ## 3c. A packet we put on the wire -/

/-- §17.2.2.1's key discard, §13.1's "a packet it did not send" bookkeeping, and
    §10.1 line 3842's idle-timer restart. -/
def sentPacket (now : Time) (pt : PacketType) (pn : Nat) (ae : Bool) (s : State) : List Out :=
  bindAll (stepHs s (.sentPacket pt)) (fun s1 =>
    match pt.space with
    | none => keep s1
    | some sp =>
      bindAll (stepAck s1 sp (.sentPacket pn)) (fun s2 =>
        if ae then stepTerm s2 (.sentAckEliciting now s2.pto) else keep s2))

theorem sentPacket_ne (now : Time) (pt : PacketType) (pn : Nat) (ae : Bool) (s : State) :
    sentPacket now pt pn ae s ≠ [] := by
  refine bindAll_ne (stepHs_ne _ _) (fun s1 => ?_)
  split
  · exact keep_ne _
  · exact bindAll_ne (stepAck_ne _ _ _) (fun s2 => by
      split
      · exact stepTerm_ne _ _
      · exact keep_ne _)

theorem sentPacket_inv {s : State} (hs : Inv s) (now : Time) (pt : PacketType) (pn : Nat)
    (ae : Bool) : InvOk (sentPacket now pt pn ae s) := by
  refine invOk_bindAll (stepHs_inv hs _) (fun s1 h1 => ?_)
  split
  · exact keep_inv h1
  · exact invOk_bindAll (stepAck_inv h1 _ _) (fun s2 h2 => by
      split
      · exact stepTerm_inv h2 _
      · exact keep_inv h2)

/-! ## 3d. The endpoint's own decisions -/

def localEvent (now : Time) (a : LocalAction) (s : State) : List Out :=
  match a with
  | .issueCid cid token rpt => stepCidLocal s (.issueCid cid token rpt)
  | .retireCid seq => stepCidRemote s (.retireCid seq)
  | .retirementBacklog n => stepCidRemote s (.retirementBacklog n)
  | .startPathValidation p d dl =>
    bindAll (register p s) (fun s1 => stepPvThen s1 p (.startValidation (s1.pathOf p) d dl))
  | .pathTimeout p =>
    bindAll (register p s) (fun s1 => stepPvThen s1 p (.timeout (s1.pathOf p) now))
  | .migrate p => bindAll (register p s) (fun s1 => stepMig s1 (.requestMigrate p))
  | .probe p => bindAll (register p s) (fun s1 => stepMig s1 (.requestProbe p))
  | .beginSendOn p n => bindAll (register p s) (fun s1 => stepMig s1 (.beginSendOn p n))
  | .learnPreferredAddress a => stepMig s (.learnPreferredAddress a)
  | .sentPacket pt pn ae => sentPacket now pt pn ae s
  | .sentAck sp largest first ranges => stepAck s sp (.sentAck largest first ranges)
  | .sentFrameIn pt p f => bindAll (register p s) (sentFrame pt p f)
  | .sentDatagram a n => stepAv s (.datagramSent a n)
  | .statelessReset => stepTerm s (.statelessReset now s.pto)
  | .pnExhausted => stepTerm s (.pnExhausted now s.pto)
  | .localError err ft => stepTerm s (.localError now s.pto err ft)
  | .icmpPtb pmtu => stepDsz s (.icmpPtb pmtu)
  | .pathBelowMinimum alt => stepDsz s (.pathBelowMinimum alt)

theorem localEvent_ne (now : Time) (a : LocalAction) (s : State) :
    localEvent now a s ≠ [] := by
  cases a <;> simp only [localEvent] <;>
    first
      | exact stepCidLocal_ne _ _
      | exact stepCidRemote_ne _ _
      | exact stepMig_ne _ _
      | exact stepAck_ne _ _ _
      | exact stepAv_ne _ _
      | exact stepTerm_ne _ _
      | exact stepDsz_ne _ _
      | exact sentPacket_ne _ _ _ _ _
      | exact bindAll_ne (register_ne _ _) (fun _ => stepPvThen_ne _ _ _)
      | exact bindAll_ne (register_ne _ _) (fun _ => stepMig_ne _ _)
      | exact bindAll_ne (register_ne _ _) (fun _ => sentFrame_ne _ _ _ _)

theorem localEvent_inv {s : State} (hs : Inv s) (now : Time) (a : LocalAction) :
    InvOk (localEvent now a s) := by
  cases a <;> simp only [localEvent] <;>
    first
      | exact stepCidLocal_inv hs _
      | exact stepCidRemote_inv hs _
      | exact stepMig_inv hs _
      | exact stepAck_inv hs _ _
      | exact stepAv_inv hs _
      | exact stepTerm_inv hs _
      | exact stepDsz_inv hs _
      | exact sentPacket_inv hs _ _ _ _
      | exact invOk_bindAll (register_inv hs _) (fun _ h => stepPvThen_inv h _ _)
      | exact invOk_bindAll (register_inv hs _) (fun _ h => stepMig_inv h _)
      | exact invOk_bindAll (register_inv hs _) (fun _ h => sentFrame_inv h _ _ _)

/-! ## 3e. The clock

§10.1's idle timeout and §10.2's closing / draining periods are the only
deadlines the transport itself owns; the path-validation abandon timer of
§8.2.4 arrives as `LocalAction.pathTimeout`, because the model has no list of
armed timers. -/

def timerEvent (now : Time) (s : State) : List Out := stepTerm s (.tick now s.pto)

theorem timerEvent_ne (now : Time) (s : State) : timerEvent now s ≠ [] := stepTerm_ne _ _

theorem timerEvent_inv {s : State} (hs : Inv s) (now : Time) : InvOk (timerEvent now s) :=
  stepTerm_inv hs _

/-! ## 3f. Frames a component asks to have queued

`Effect.sendPending f` is the marker: "the rules say this frame is now owed".
It is not a packet going out — §13.2 and §13.3 decide when a frame travels, and
both are out of scope — so it is an effect and never a state change. -/

def closeFrameOf : Termination.CloseReason → Frame
  | .transport e ft => .connectionClose e.code (some ft) ByteArray.empty
  | .application c => .connectionClose c none ByteArray.empty

def pendingOf : Effect → List Effect
  -- §19.15: the frame that carries a connection ID we just issued
  | .cidLocal (.sendNewCid seq rpt cid token) =>
    [.sendPending (.newConnectionId seq rpt (bytes cid) (bytes token))]
  -- §5.1.2, line 1781 / §19.16
  | .cidRemote (.queueRetire n) => [.sendPending (.retireConnectionId n)]
  -- §3.5, line 1243: "the application aborted reading, so a STOP_SENDING frame
  -- should be sent"
  | .st (.stream id (.recv (.stopSendingRequested c))) =>
    [.sendPending (.stopSending id.val c)]
  -- §10.2, line 3912 / §11.1, line 4446
  | .term (.sendClose r) => [.sendPending (closeFrameOf r)]
  | _ => []

/-- Add the `sendPending` markers to an outcome's effect list.  Errors and drops
    carry no effects at all (PLAN §4a: ngtcp2 fires callbacks and then fails, so
    only the error code is compared). -/
def withPending : Out → Out
  | .ok s fx => .ok s (fx ++ fx.flatMap pendingOf)
  | o => o

theorem withPending_eq_ok {o : Out} {s' : State} {fx : List Effect}
    (h : withPending o = .ok s' fx) : ∃ gx, o = .ok s' gx := by
  cases o with
  | ok x gx =>
    simp only [withPending, Outcome.ok.injEq] at h
    exact ⟨gx, by rw [h.1]⟩
  | error c => simp [withPending] at h
  | drop => simp [withPending] at h

/-! ## 3g. Every permitted outcome of one event -/

def rawOutcomes (prot : Protection) (s : State) : Event → List Out
  | .datagram src dest buf now => recvDatagram prot s src dest buf now
  | .app a now => appEvent now a s
  | .tls e => stepHs s e
  | .timer now => timerEvent now s
  | .local a now => localEvent now a s

theorem rawOutcomes_ne (prot : Protection) (s : State) (e : Event) :
    rawOutcomes prot s e ≠ [] := by
  cases e <;> simp only [rawOutcomes]
  · exact recvDatagram_ne _ _ _ _ _ _
  · exact appEvent_ne _ _ _
  · exact stepHs_ne _ _
  · exact timerEvent_ne _ _
  · exact localEvent_ne _ _ _

theorem rawOutcomes_inv {s : State} (hs : Inv s) (prot : Protection) (e : Event) :
    InvOk (rawOutcomes prot s e) := by
  cases e <;> simp only [rawOutcomes]
  · exact recvDatagram_inv hs _ _ _ _ _
  · exact appEvent_inv hs _ _
  · exact stepHs_inv hs _
  · exact timerEvent_inv hs _
  · exact localEvent_inv hs _ _

end Quic.Spec.Endpoint
