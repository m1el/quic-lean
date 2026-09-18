import QuicModel.Spec.Endpoint.Exports

/- Third transport audit probes. Helpers adapted from Endpoint/Examples.lean.
   The guards asserted the observed defects when the audit was written; the four
   marked "fixed" are inverted now that D34-5/6/7 are fixed in `Endpoint/Send.lean`
   (regression guards: `Endpoint/Examples.lean`, sections D34-5 to D34-7). -/
set_option maxRecDepth 40000
namespace Quic.Spec.Endpoint.Audit3
open Quic Quic.Spec Quic.Spec.Endpoint

private def localCid : ByteArray := bytes [0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7]
private def peerCid : ByteArray := bytes [0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7]
private def cfgOf (isServer : Bool) : Config :=
  harnessConfig isServer localCid peerCid 4096 1024 4 2 30000000 25000 4 100000
private def prot : Protection := harnessProtection
private def peerAddr : Addr := ⟨1⟩
private def selfAddr : Addr := ⟨0⟩
private def thePath : Migration.Path := ⟨⟨0⟩, peerAddr⟩
private def tls (s : State) (e : TlsEvent) : State := (step prot s (.tls e)).next s
private def app (s : State) (a : AppAction) : State := (step prot s (.app a 0)).next s
private def loc (s : State) (a : LocalAction) : State := (step prot s (.local a 0)).next s
private def postHandshake (s : State) : State :=
  tls (tls (tls (tls (tls s
    (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)) .tlsComplete
private def cli : State := postHandshake (init (cfgOf false))

private def shortPacket (pn : UInt8) (payload : ByteArray) : ByteArray :=
  let body := payload ++ bytes (List.replicate (4 - payload.size) 0) ++
    bytes (List.replicate 16 0xa5)
  let pnOff := 1 + localCid.size
  let plain := bytes [0x40] ++ localCid ++ bytes [pn] ++ body
  let mask := (Protection.stub 16).hpMask (plain.extract (pnOff + 4) (pnOff + 4 + 16))
  bytes [0x40 ^^^ (byteAt mask 0 &&& 0x1f)] ++ localCid ++
    bytes [pn ^^^ byteAt mask 1] ++ body
private def dgram (pn : UInt8) (fs : List Frame) : ByteArray :=
  shortPacket pn (encodeFrames fs.toArray)

-- Two individually legal STREAM frames exceed the connection's total credit.
private def smallCfg : Config :=
  { cfgOf false with theirs := { (cfgOf false).theirs with maxData := 10 } }
private def smallCli : State :=
  tls (tls (tls (tls (tls (init smallCfg)
    (.tlsKeys .read .handshake)) (.tlsKeys .write .handshake))
    (.tlsKeys .read .oneRtt)) (.tlsKeys .write .oneRtt)) .tlsComplete
private def ready : State :=
  app (app (app (app smallCli (.openStream .bidi)) (.openStream .bidi))
    (.write ⟨0⟩ 6)) (.write ⟨4⟩ 6)
private def f0 : Frame := .stream 0 0 false (bytes [1,2,3,4,5,6])
private def f4 : Frame := .stream 4 0 false (bytes [1,2,3,4,5,6])
private def packet : OutPacket := ⟨.oneRtt, [f0, f4]⟩
private def dg (fs : List Frame) : OutDatagram :=
  { size := 100, packets := [⟨.oneRtt, fs⟩], src := selfAddr, dest := peerAddr,
    dcid := some peerCid.toList, scid := some localCid.toList }
#guard ready.st.maxDataPeer == 10
#guard ready.st.sentTotal == 0
#guard !maySendPacket ready packet  -- fixed (D34-5)
#guard !maySendDatagram ready (dg [f0, f4])  -- fixed (D34-5)
private def afterFirst : State := loc ready (.sentFrameIn .oneRtt thePath f0)
#guard afterFirst.st.sentTotal == 6
#guard !maySend afterFirst f4

-- A NEW_CONNECTION_ID retires the original DCID, but it remains sendable.
private def newCidFrame : Frame :=
  .newConnectionId 1 1 (bytes [0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7])
    (bytes (List.replicate 16 1))
private def retiredCli : State :=
  (step prot cli (.datagram peerAddr selfAddr (dgram 0 [newCidFrame]) 0)).next cli
#guard retiredCli.cidRemote.isRetired 0
#guard !maySendDatagram retiredCli (dg [.ping])  -- fixed (D34-6)

-- CID bytes never reach Migration, so its recorded CID-use history is bypassed.
private def confirmedCli : State :=
  (step prot cli (.datagram peerAddr selfAddr (dgram 0 [.handshakeDone]) 0)).next cli
private def newPath : Migration.Path := ⟨⟨2⟩, peerAddr⟩
#guard confirmedCli.hs.confirmed
#guard confirmedCli.mig.peerCids.isEmpty
#guard confirmedCli.mig.reusedAcrossLocal newPath 0
#guard !decide (Migration.MaySendCidOn confirmedCli.mig newPath 0)
#guard !maySendDatagram confirmedCli { dg [.ping] with src := ⟨2⟩ }  -- fixed (D34-7)

end Quic.Spec.Endpoint.Audit3
