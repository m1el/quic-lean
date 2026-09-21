import QuicModel.Spec.Stream
import QuicModel.Spec.StreamTable
import QuicModel.Violations.Trace

/-!
  One manufactured violation per executable Stream and StreamTable requirement.
  `true` means the verifier rejects that trace.
  Names starting with `advice:` are SHOULDs or MAYs the checker is specified not to reject.
-/
namespace Quic.Violations.Stream

open Quic Quic.Spec

def send0 : Stream.Send.State := Stream.Send.init ⟨0⟩ .client 100

def recv1 : Stream.Recv.State := Stream.Recv.init ⟨1⟩ .client 100

def rSize : Stream.Recv.State :=
  { recv1 with phase := .sizeKnown, highest := 10, ranges := [(5, 10)], finalSize := some 10 }

def rData : Stream.Recv.State :=
  { recv1 with phase := .dataRecvd, highest := 10, ranges := [(0, 10)], finalSize := some 10 }

def rReset : Stream.Recv.State :=
  { recv1 with phase := .resetRecvd, highest := 4, finalSize := some 4 }

def rRead : Stream.Recv.State :=
  { recv1 with phase := .resetRead, highest := 4, finalSize := some 4 }

def ordPrefix : Stream.Recv.State :=
  { recv1 with highest := 5, ranges := [(0, 5)] }

def ordRead : Stream.Recv.State :=
  { ordPrefix with read := 5 }

def stopped : Stream.Send.State :=
  { send0 with phase := .send, written := 10, sent := 4, resetCode := some 9 }

def dataSent : Stream.Send.State :=
  { send0 with phase := .dataSent, written := 5, finWritten := true, sent := 5, finalSize := some 5 }

def pastFin : Stream.Send.State :=
  { send0 with phase := .dataSent, written := 10, finWritten := true, sent := 5, finalSize := some 5 }

/-- Client-initiated unidirectional stream: send-only at the client. -/
def uniC : Stream.State :=
  Stream.init (StreamId.make .client .uni 0) .client 100 100

/-- The same stream at the server: receive-only. -/
def uniS : Stream.State :=
  Stream.init (StreamId.make .client .uni 0) .server 100 100

def biSize : Stream.State :=
  let id := StreamId.make .client .bidi 0
  let s := Stream.init id .client 100 100
  let rs := { Stream.Recv.init id .client 100 with
    phase := .sizeKnown, highest := 10, ranges := [(5, 10)], finalSize := some 10 }
  { s with recv := some rs }

def lim3 : StreamTable.Limits :=
  { maxData := 100, maxStreamDataBidiLocal := 100, maxStreamDataBidiRemote := 100,
    maxStreamDataUni := 100, maxStreamsBidi := 3, maxStreamsUni := 3 }

def srv : StreamTable.State := StreamTable.init .server lim3 lim3

def limSmall : StreamTable.Limits :=
  { lim3 with maxData := 50 }

def limConn : StreamTable.Limits :=
  { maxData := 100, maxStreamDataBidiLocal := 1000, maxStreamDataBidiRemote := 1000,
    maxStreamDataUni := 1000, maxStreamsBidi := 4, maxStreamsUni := 4 }

/-- Server uni stream 3, written past the peer's connection credit of 100. -/
def srvPastConn : StreamTable.State :=
  let role := Role.server
  let id : StreamId := ⟨3⟩
  let base := StreamTable.init role limConn limConn
  let opened := { base with opened := base.opened.set role .uni 1 }
  let st0 := opened.freshStream id
  let ss := match st0.send with
    | some ss => { ss with written := 200 }
    | none => Stream.Send.init id role 1000
  opened.setStream id { st0 with send := some ss }

def limWide : StreamTable.Limits :=
  { maxData := 20, maxStreamDataBidiLocal := 1000, maxStreamDataBidiRemote := 1000,
    maxStreamDataUni := 1000, maxStreamsBidi := 3, maxStreamsUni := 3 }

def srvBidiFull : StreamTable.State :=
  { srv with opened := srv.opened.set .server .bidi 3 }

def srvUniFull : StreamTable.State :=
  { srv with opened := srv.opened.set .server .uni 3 }

def srvSmall : StreamTable.State := StreamTable.init .server limSmall limSmall

/-- Client has stream 3 at final size 10, inside a connection limit of 20. -/
def finTable : StreamTable.State :=
  let role := Role.client
  let id : StreamId := ⟨3⟩
  let base := StreamTable.init role limWide limWide
  let opened := base.openThrough id
  let rs : Stream.Recv.State :=
    { Stream.Recv.init id role 1000 with
        phase := .dataRecvd, highest := 10, ranges := [(0, 10)], finalSize := some 10 }
  let st := { Stream.init id role 1000 1000 with recv := some rs }
  { opened.setStream id st with recvTotal := 10 }

def checks : List Trace := [
  -- §13.3: MAX_STREAM_DATA after "Size Known" is not recommended, and not forbidden.
  advice "Stream §13.3 (5393) Recv.RecommendedSend" (!(Stream.Recv.maySend rSize (.maxStreamData 1 200))),
  -- §19.4: RESET_STREAM on a send-only stream, accepted instead of STREAM_STATE_ERROR.
  must "Stream §19.4 (7431) Step.recvMissing" (!(Stream.component.accepts uniC (.recv (.recvResetStream 1 0)) (.ok uniC []))),
  -- §19.5: STOP_SENDING on a receive-only stream, discarded instead of the error.
  must "Stream §19.5 (7476) Step.sendMissing" (!(Stream.component.accepts uniS (.send (.recvStopSending 3)) .drop)),
  -- §19.8: STREAM on a send-only stream, accepted.
  must "Stream §19.8 (7638) Step.recvMissing" (!(Stream.component.accepts uniC (.recv (.recvStream 0 5 false)) (.ok uniC []))),
  -- §19.10: MAX_STREAM_DATA on a receive-only stream, accepted.
  must "Stream §19.10 (7736) Step.sendMissing" (!(Stream.component.accepts uniS (.send (.recvMaxStreamData 200)) (.ok uniS []))),
  -- §19.13: STREAM_DATA_BLOCKED on a send-only stream, accepted.
  must "Stream §19.13 (7864) Step.recvMissing" (!(Stream.component.accepts uniC (.recv (.recvStreamDataBlocked 0)) (.ok uniC []))),
  -- §2.2: bytes that are not the contiguous prefix cannot be read.
  must "Stream §2.2 (739) ordered delivery" (!(Stream.Recv.component.accepts
        { recv1 with highest := 10, ranges := [(5, 10)] }
        (.appRead 5) (.ok recv1 []))),
  -- §2.2 MAY: delivering only the ordered prefix is not rejected.
  advice "Stream §2.2 (744) MAY out-of-order" (!(Stream.Recv.component.accepts ordPrefix (.appRead 5) (.ok ordRead []))),
  -- §3.2: in "Data Recvd" only suppress-or-signal are permitted; a third outcome is not.
  must "Stream §3.2 (1127)" (!(Stream.Recv.component.accepts rData (.recvResetStream 7 10) .drop)),
  -- §3.3: STOP_SENDING after RESET_STREAM has been received.
  must "Stream §3.3 (1157)" (!(Stream.Recv.maySendStopSending rRead 9)),
  -- §3.5: aborting the read without asking for STOP_SENDING.
  must "Stream §3.5 (1243)" (!(Stream.Recv.component.accepts recv1 (.appAbortRead 9)
        (.ok { recv1 with stopSending := some 9 } []))),
  -- §3.5: STOP_SENDING for a stream the peer has already reset.
  must "Stream §3.5 (1269)" (!(Stream.Recv.maySend rReset (.stopSending 1 3))),
  -- §4.1: STREAM past the advertised stream limit, taken as ok.
  must "Stream §4.1 (1330)" (!(Stream.Recv.component.accepts recv1 (.recvStream 90 20 false) (.ok recv1 []))),
  -- §4.1: RESET_STREAM whose final size exceeds the limit, taken as ok.
  must "Stream §4.1 (1368)" (!(Stream.Recv.component.accepts recv1 (.recvResetStream 1 101) (.ok recv1 []))),
  -- §4.5: a FIN that changes the final size is stored.
  must "Stream §4.5 (1517)" (!(Stream.Recv.component.accepts rSize (.recvStream 0 9 true)
        (.ok { rSize with finalSize := some 9 } []))),
  -- §4.5: data past the final size is buffered.
  must "Stream §4.5 (1520)" (!(Stream.Recv.component.accepts rSize (.recvStream 10 1 false)
        (.ok { rSize with highest := 11 } []))),
  -- §13.3 again, on the whole stream: the same MAX_STREAM_DATA is still permitted.
  advice "Stream §13.3 (5393) send" (!(Stream.maySend biSize (.maxStreamData 0 200))),
  -- §3.1: RESET_STREAM from a terminal sending state.
  must "Stream §3.1 (986)" (!(Stream.Send.maySendReset
        { send0 with phase := .resetRecvd, finalSize := some 0 } 7 0)),
  -- §3.3: no data-carrying frame and no RESET_STREAM from "Data Recvd".
  must "Stream §3.3 (1146)" (!(Stream.Send.Phase.mayCarryData .dataRecvd) &&
      !(Stream.Send.maySendReset
          { send0 with phase := .dataRecvd, finalSize := some 5, sent := 5 } 1 5)),
  -- §3.3: STREAM after RESET_STREAM ("Reset Sent" carries no data).
  must "Stream §3.3 (1147)" (!(Stream.Send.Phase.mayCarryData .resetSent) &&
      !(Stream.Send.maySendStream
          { send0 with phase := .resetSent, written := 8, finalSize := some 0, resetCode := some 1 }
          0 1 false)),
  -- §3.5: STOP_SENDING makes the matching RESET_STREAM sendable; a wrong final size is not.
  must "Stream §3.5 (1254)" (Stream.Send.maySendReset stopped 9 4 && !(Stream.Send.maySendReset stopped 9 8)),
  -- §3.5 SHOULD: retransmitting the FIN from "Data Sent" is still permitted.
  advice "Stream §3.5 (1259)" (!(Stream.Send.maySend dataSent (.stream 0 0 true (ByteArray.mk #[1, 2, 3, 4, 5])))),
  -- §3.5 SHOULD: a different application error code may still be sent.
  advice "Stream §3.5 (1263)" (!(Stream.Send.maySendReset { send0 with resetCode := some 9 } 3 0)),
  -- §4.1: five bytes when the peer has granted four.
  must "Stream §4.1 (1330) send" (!(Stream.Send.maySendStream { send0 with maxData := 4, written := 10 } 0 5 false)),
  -- §4.1: a later offset that still ends past the same credit.
  must "Stream §4.1 (1368) send" (!(Stream.Send.maySendStream { send0 with maxData := 8, written := 20 } 6 4 false)),
  -- §4.1: a MAX_STREAM_DATA that does not raise the limit, applied as a raise.
  must "Stream §4.1 (1372)" (!(Stream.Send.component.accepts send0 (.recvMaxStreamData 80)
        (.ok { send0 with maxData := 200 } [.creditAvailable 200]))),
  -- §4.1: STREAM_DATA_BLOCKED naming a limit other than the one in force.
  must "Stream §4.1 (1376)" (!(Stream.Send.maySendBlocked { send0 with maxData := 40, written := 80 } 0)),
  -- §4.5: data past a final size the FIN already fixed.
  must "Stream §4.5 (1499)" (!(Stream.Send.maySendStream pastFin 0 6 false)),
  -- §13.3: a retransmitted RESET_STREAM whose final size differs.
  must "Stream §13.3 (5359)" (!(Stream.Send.maySendReset
        { send0 with phase := .resetSent, sent := 4, finalSize := some 4, resetCode := some 7 }
        7 9)),
  -- §19.13: STREAM_DATA_BLOCKED from "Reset Sent".
  must "Stream §19.13 (7859)" (!(Stream.Send.maySend
        { send0 with phase := .resetSent, finalSize := some 0, resetCode := some 4 }
        (.streamDataBlocked 0 100))),
  -- §2.1: no fresh stream id once the peer's bidirectional limit is used up.
  must "StreamTable §2.1 (687)" (!(StreamTable.component.accepts srvBidiFull (.appOpenStream .bidi) (.ok srvBidiFull []))),
  -- §4.1: a STREAM the stream limit allows and the connection limit does not.
  must "StreamTable §4.1 (1330)" (!(StreamTable.maySend srvPastConn
        (.stream 3 98 false (ByteArray.mk #[1, 2, 3, 4, 5])))),
  -- §4.1: a MAX_DATA that does not increase the peer limit, stored as a higher one.
  must "StreamTable §4.1 (1372)" (!(StreamTable.component.accepts srv (.recvMaxData 40)
        (.ok { srv with maxDataPeer := 200 } [.dataCreditAvailable 200]))),
  -- §4.1: DATA_BLOCKED and STREAMS_BLOCKED naming something other than the limit in force.
  must "StreamTable §4.1 (1375, 1376, 1381)" (!(StreamTable.maySend srv (.dataBlocked 99)) &&
      !(StreamTable.maySend srv (.streamsBlocked .uni 2))),
  -- §4.2 MAY: an early MAX_DATA above the limit already received is permitted.
  advice "StreamTable §4.2 (1392)" (!(StreamTable.maySend srv (.maxData 500))),
  -- §4.2: MAX_STREAMS with no STREAMS_BLOCKED ever received is permitted.
  advice "StreamTable §4.2 (1422)" (!(StreamTable.maySend srv (.maxStreams .bidi 10))),
  -- §4.5: a final size the stream accepts but the connection limit does not, taken as ok.
  must "StreamTable §4.5 (1495)" (!(StreamTable.component.accepts srvSmall
        (.stream ⟨0⟩ (.recv (.recvResetStream 7 60))) (.ok srvSmall []))),
  -- §4.5: data past a known final size charged against the connection.
  must "StreamTable §4.5 (1517, 1519, 1520, 1522)" (!(StreamTable.component.accepts finTable
        (.stream ⟨3⟩ (.recv (.recvStream 0 200 false)))
        (.ok { finTable with recvTotal := 200 } []))),
  -- §4.6: a peer stream id past the limit we advertised, accepted.
  must "StreamTable §4.6 (1546)" (!(StreamTable.component.accepts srv
        (.stream ⟨12⟩ (.recv (.recvStream 0 5 false))) (.ok srv []))),
  -- §4.6: a MAX_STREAMS that does not increase the limit, applied as one.
  must "StreamTable §4.6 (1552)" (!(StreamTable.component.accepts srv (.recvMaxStreams .uni 3)
        (.ok { srv with maxStreamsPeer := srv.maxStreamsPeer.set .uni 3 }
             [.streamsAvailable .uni 3]))),
  -- §4.6 SHOULD: STREAMS_BLOCKED at the real limit is permitted even when not blocked.
  advice "StreamTable §4.6 (1561)" (!(StreamTable.maySend srv (.streamsBlocked .bidi 3))),
  -- §4.6: MAX_STREAMS above 2^60, accepted.
  must "StreamTable §4.6 (1563)" (!(StreamTable.component.accepts srv (.recvMaxStreams .bidi (2 ^ 60 + 1)) (.ok srv []))),
  -- §19.11: a smaller MAX_STREAMS stored as the new limit.
  must "StreamTable §19.11 (7809)" (!(StreamTable.component.accepts srv (.recvMaxStreams .bidi 1)
        (.ok { srv with maxStreamsPeer := srv.maxStreamsPeer.set .bidi 1 }
             [.streamsAvailable .bidi 1]))),
  -- §19.11: opening one more unidirectional stream than the peer allowed.
  must "StreamTable §19.11 (7812)" (!(StreamTable.component.accepts srvUniFull (.appOpenStream .uni) (.ok srvUniFull []))),
  -- §19.12: DATA_BLOCKED naming a limit other than the peer's MAX_DATA.
  must "StreamTable §19.12 (7827)" (!(StreamTable.maySend srv (.dataBlocked 0))),
  -- §19.13 SHOULD: STREAM_DATA_BLOCKED while not blocked is still permitted.
  advice "StreamTable §19.13 (7859)" (!(Stream.Send.maySend send0 (.streamDataBlocked 0 100))),
  -- §19.13: STREAM_DATA_BLOCKED for a local uni stream that was never created, accepted.
  must "StreamTable §19.13 (7863)" (!(StreamTable.component.accepts srv
        (.stream ⟨3⟩ (.recv (.recvStreamDataBlocked 5))) (.ok srv []))),
]

end Quic.Violations.Stream
