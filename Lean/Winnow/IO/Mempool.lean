import Winnow.IO.Pool

/-! # The bounded mempool window, the I/O half (`Network/Mempool/MempoolWindow.swift`)

The bookkeeping is the Net area's pure `MempoolWindow` (dedupe, in-flight cap and expiry, matching,
echo detection); this module runs its `MempoolEffect`s: the auto-close timer (`armStop`, re-armed by
`start`/`extend`), a listener per connected peer (subscribed before `start` returns, so an inv right
after it is seen; a stream that went stale across a stop/start is dropped unconsumed — the
`generation` check), the sweep every `sweepInterval` (attach to replacement peers, expire requests),
`getdata(MSG_WITNESS_TX)` to the announcing peer (rolled back on a failed send), and the event
multicast. The connections must have been made with `relayPreference := true` for peers to inv
every relayed transaction. -/

namespace Winnow.IO
open Winnow.Net

structure MempoolWindowIO where
  pool : PeerPool
  sweepIntervalMs : Nat
  state : IO.Ref MempoolWindow
  stopToken : IO.Ref Nat
  /-- endpoint description → the listener's stream. -/
  listeners : IO.Ref (Array (String × PeerStream))
  subscribers : IO.Ref (Array (EventStream MempoolEvent Unit))
  nextId : IO.Ref Nat

namespace MempoolWindowIO

def new (pool : PeerPool) (watchScripts : Array ByteArray) (maxSeenTxids : Nat := 10_000) (maxInFlight : Nat := 512)
    (requestTimeoutSeconds : Nat := 30) (sweepIntervalMs : Nat := 5_000) : IO MempoolWindowIO := do
  let w : MempoolWindow := { watchScripts := watchScripts.foldl (·.insert ·) {}, maxSeenTxids, maxInFlight,
                             requestTimeout := requestTimeoutSeconds }
  return { pool, sweepIntervalMs, state := ← IO.mkRef w, stopToken := ← IO.mkRef 0, listeners := ← IO.mkRef #[],
           subscribers := ← IO.mkRef #[], nextId := ← IO.mkRef 0 }

def isRunning (m : MempoolWindowIO) : BaseIO Bool := do return (← m.state.get).running

/-- The window's events; each caller gets its own stream. -/
def events (m : MempoolWindowIO) : IO (EventStream MempoolEvent Unit) := do
  let id ← m.nextId.modifyGet fun n => (n, n + 1)
  let s ← EventStream.new id 1_000_000
  s.onCancel.set (m.subscribers.modify (·.filter (·.id != id)))
  m.subscribers.modify (·.push s)
  return s

private def emit (m : MempoolWindowIO) (e : MempoolEvent) : IO Unit := do
  for s in ← m.subscribers.get do s.yield e

private def nowSeconds : IO Nat := do return (← wallSeconds).toNat

mutual
/-- Closes the window: listeners and timers are cancelled, in-flight state dropped. -/
partial def stop (m : MempoolWindowIO) : IO Unit := do
  m.stopToken.modify (· + 1)
  m.state.modify fun w => (w.stop).1
  let ls ← m.listeners.modifyGet fun ls => (ls, #[])
  for (_, s) in ls do s.cancel

partial def armStop (m : MempoolWindowIO) (seconds : Nat) : IO Unit := do
  let token ← m.stopToken.modifyGet fun t => (t + 1, t + 1)
  after (seconds * 1000) do
    if (← m.stopToken.get) == token then m.stop
end

private def handle (m : MempoolWindowIO) (msg : PeerMessage) (peer : PeerConnection) : IO Unit := do
  let now ← nowSeconds
  let effects ← m.state.modifyGet fun w => let (w, es) := w.handle msg peer.endpoint now; (es, w)
  for e in effects do
    match e with
    | .emit ev => m.emit ev
    | .sendGetData _ p =>
      match ← (peer.send (.getdata p)).attempt with
      | .ok () => pure ()
      | .error _ => m.state.modify (·.sendFailed p.vectors)
    | _ => pure ()

private partial def listen (m : MempoolWindowIO) (peer : PeerConnection) (stream : PeerStream) (gen : Nat) : IO Unit := do
  repeat
    match ← stream.next with
    | .value (.message msg) =>
      if !(← m.isRunning) then break
      m.handle msg peer
    | .value .disconnected => pure ()
    | .finished _ => break
  if (← m.state.get).generation == gen then
    m.listeners.modify (·.filter (·.1 != peer.endpoint.description))

private def attachToConnectedPeers (m : MempoolWindowIO) : IO Unit := do
  -- a relay-only pool holds its seats for a payment going out, not for reading what the network relays
  if !(← m.isRunning) || (← m.pool.mode) != .full then return
  for peer in ← m.pool.connectedPeers do
    let key := peer.endpoint.description
    if (← m.listeners.get).any (·.1 == key) then continue
    let gen := (← m.state.get).generation
    let stream ← peer.events
    let w ← m.state.get
    if !(w.running && w.generation == gen) || (← m.listeners.get).any (·.1 == key) then
      stream.cancel
      continue
    m.listeners.modify (·.push (key, stream))
    spawn (m.listen peer stream gen)

private partial def sweepLoop (m : MempoolWindowIO) (gen : Nat) : IO Unit := do
  after m.sweepIntervalMs do
    let w ← m.state.get
    if !w.running || w.generation != gen then return
    m.attachToConnectedPeers
    let now ← nowSeconds
    m.state.modify (·.sweep now)
    m.sweepLoop gen

/-- Opens the window for `seconds` (default 20 minutes), re-arming the deadline when already open. -/
def start (m : MempoolWindowIO) (seconds : Nat := MempoolWindow.defaultDurationSeconds) : IO Unit := do
  let effects ← m.state.modifyGet fun w => let (w, es) := w.start seconds; (es, w)
  for e in effects do
    match e with
    | .armStop s => m.armStop s
    | .startSweep =>
      m.attachToConnectedPeers
      m.sweepLoop (← m.state.get).generation
    | _ => pure ()

/-- Pushes the automatic close `seconds` into the future. -/
def extend (m : MempoolWindowIO) (seconds : Nat) : IO Unit := do
  let (_, effects) := (← m.state.get).extend seconds
  for e in effects do
    if let .armStop s := e then m.armStop s

def watchEcho (m : MempoolWindowIO) (txid : ByteArray) : BaseIO Unit := m.state.modify (·.watchEcho txid)
def unwatchEcho (m : MempoolWindowIO) (txid : ByteArray) : BaseIO Unit := m.state.modify (·.unwatchEcho txid)

end MempoolWindowIO
end Winnow.IO
