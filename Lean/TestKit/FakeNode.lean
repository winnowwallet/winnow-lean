import Winnow.IO

/-! # A fake peer

What io-test's misbehaving peers and backend-test's peer ahead of the wallet run on: a local listener that
speaks just enough of the protocol to be connected to. -/

namespace TestKit
open Winnow Winnow.Net Winnow.IO

/-- A fake node that accepts any number of connections and handshakes each (version with
NODE_COMPACT_FILTERS, verack), or with `silent` accepts and never speaks; `params` picks the magic, `v6`
listens on `::1`. It answers pings unless `pongs` is off, and hands every other message and each ping to
`answer`, which by default says nothing, so an announced transaction is never asked for. Resolving `hangUp`
closes its connections, and any made later, from the node's side. -/
def fakeNode (params : NetworkParams) (silent : Bool := false) (v6 : Bool := false) (pongs : Bool := true)
    (startHeight : Int32 := 0)
    (answer : (PeerMessage → IO Unit) → PeerMessage → IO Unit := fun _ _ => pure ())
    (hangUp : Option (IO.Promise Unit) := none) : IO PeerEndpoint := do
  let server ← Std.Async.TCP.Socket.Server.mk
  server.bind (if v6 then .v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 1, 0⟩ else .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 16
  let port := (← server.getSockName).port
  spawn do
    let keep := server
    repeat
      let sock ← keep.accept.block
      spawn do
        let send (m : PeerMessage) : IO Unit := (sock.send (MessageFramer.frame m.command m.payload params.magic)).block
        if let some p := hangUp then
          discard <| IO.mapTask (fun _ => discard <| sock.shutdown.toIO) p.result?
        let mut framer : MessageFramer := { magic := params.magic }
        repeat
          let some chunk ← (sock.recv? 65536).block | break
          if chunk.isEmpty then break
          framer := framer.append chunk
          let mut alive := true
          repeat
            match framer.nextMessage with
            | .ok (some (cmd, payload), f) =>
              framer := f
              if !silent then
                match cmd with
                | "version" =>
                  send (.version { version := 70016, services := 64 ||| 1, timestamp := 0, receiver := .unspecified,
                                   sender := .unspecified, nonce := 9, userAgent := "/fake-node:0/", startHeight,
                                   relay := false })
                  send .verack
                | _ =>
                  if let .ok m := PeerMessage.decode cmd payload then
                    if let (.ping n, true) := (m, pongs) then send (.pong n)
                    answer send m
            | .ok (none, _) => break
            | .error _ => alive := false; break
          if !alive then break
        discard <| sock.shutdown.toIO
  return { host := if v6 then "::1" else "127.0.0.1", port }

end TestKit
