import QuicModel

def main (args : List String) : IO UInt32 := do
  for path in args do
    let buf ← IO.FS.readBinFile path
    IO.println s!"== {path} ({buf.size} bytes)"
    IO.print (Quic.dumpFrames buf (verbose := true))
  return 0
