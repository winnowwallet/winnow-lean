import Std.Data.HashMap
import Std.Data.HashSet
import Winnow.Net.Messages
import Winnow.Net.Params

/-! # The bounded mempool window: the pure state machine (`Network/Mempool/MempoolWindow.swift`)

While the window is open every transaction `inv` from connected peers is answered with
`getdata(MSG_WITNESS_TX)`, and fetched transactions are matched against watched scriptPubKeys.
The Swift actor's bookkeeping is here as functions over `MempoolWindow`: dedupe through a capped FIFO
seen set, the in-flight cap and request expiry, notfound release, matching once per fetched tx, echo
detection of our own broadcasts, and the start/stop/extend lifecycle.

Left for the I/O layer (described by the `Effect`s these functions return): the timers (`armStop`
after a duration, the sweep every `sweepInterval`), attaching a listener to each connected peer (and
dropping a stream that went stale across a stop/start — the `generation` check), sending `getdata`
(on failure: `sendFailed`), the clock, and multicasting `Event`s to subscribers. -/

namespace Winnow.Net

inductive MempoolEvent where
  /-- A relayed transaction pays a watched script: the summed amount and the first matched script. -/
  | paymentSeen (txid : ByteArray) (amount : Int64) (scriptPubKey : ByteArray)
  /-- A peer announced a txid registered with `watchEcho` (once per txid per peer). -/
  | txidEchoed (txid : ByteArray) (peer : PeerEndpoint)
  deriving Inhabited

inductive MempoolEffect where
  /-- Cancel any pending close and close the window after this many seconds. -/
  | armStop (seconds : Nat)
  /-- Attach listeners to connected peers and start the periodic sweep. -/
  | startSweep
  /-- Cancel timers and listeners. -/
  | cancelAll
  /-- Send this `getdata` to the peer that announced the txids. -/
  | sendGetData (peer : PeerEndpoint) (p : InventoryPayload)
  | emit (e : MempoolEvent)
  deriving Inhabited

structure MempoolWindow where
  watchScripts : Std.HashSet ByteArray
  maxSeenTxids : Nat := 10_000
  maxInFlight : Nat := 512
  /-- Seconds a getdata may go unanswered. -/
  requestTimeout : Nat := 30
  running : Bool := false
  generation : Nat := 0
  seenTxids : Std.HashSet ByteArray := {}
  seenOrder : Array ByteArray := #[]
  /-- txid → when the getdata was sent (seconds). -/
  inFlight : Std.HashMap ByteArray Nat := {}
  echoTxids : Std.HashSet ByteArray := {}
  /-- "txidHex|host:port" pairs already echoed. -/
  echoed : Std.HashSet String := {}

namespace MempoolWindow

def defaultDurationSeconds : Nat := 1_200

def start (w : MempoolWindow) (seconds : Nat := defaultDurationSeconds) : MempoolWindow × Array MempoolEffect :=
  if w.running then (w, #[.armStop seconds])
  else ({ w with running := true, generation := w.generation + 1 }, #[.armStop seconds, .startSweep])

def extend (w : MempoolWindow) (seconds : Nat) : MempoolWindow × Array MempoolEffect :=
  if w.running then (w, #[.armStop seconds]) else (w, #[])

/-- Closes the window; echo watches survive (they belong to the caller). -/
def stop (w : MempoolWindow) : MempoolWindow × Array MempoolEffect :=
  ({ w with running := false, generation := w.generation + 1, seenTxids := {}, seenOrder := #[], inFlight := {},
            echoed := {} }, #[.cancelAll])

def watchEcho (w : MempoolWindow) (txid : ByteArray) : MempoolWindow := { w with echoTxids := w.echoTxids.insert txid }

def unwatchEcho (w : MempoolWindow) (txid : ByteArray) : MempoolWindow :=
  let pre := hex txid ++ "|"
  { w with echoTxids := w.echoTxids.erase txid, echoed := w.echoed.filter fun k => !k.startsWith pre }

/-- Drops a txid from the seen set (the ordered list is searched only for one actually seen). -/
def forget (w : MempoolWindow) (txid : ByteArray) : MempoolWindow :=
  if !w.seenTxids.contains txid then w
  else
    let w := { w with seenTxids := w.seenTxids.erase txid }
    match w.seenOrder.findIdx? (· == txid) with
    | some i => { w with seenOrder := w.seenOrder.eraseIdx! i }
    | none => w

/-- The tx announcements of an inv worth fetching (echo tracking, dedupe, in-flight cap), recorded
as seen before the request goes out; the FIFO is trimmed to `maxSeenTxids`. -/
def admitAnnouncements (w : MempoolWindow) (p : InventoryPayload) (peer : PeerEndpoint) :
    MempoolWindow × Array InventoryVector × Array MempoolEvent := Id.run do
  let mut w := w
  let mut request : Array InventoryVector := #[]
  let mut events : Array MempoolEvent := #[]
  for v in p.vectors do
    if !(v.type.baseType == InventoryType.tx) then continue
    let txid := v.hash
    if w.echoTxids.contains txid then
      let key := hex txid ++ "|" ++ peer.description
      if !w.echoed.contains key then
        w := { w with echoed := w.echoed.insert key }
        events := events.push (.txidEchoed txid peer)
    if w.seenTxids.contains txid || !(w.inFlight.size + request.size < w.maxInFlight) then continue
    w := { w with seenTxids := w.seenTxids.insert txid, seenOrder := w.seenOrder.push txid }
    request := request.push { type := InventoryType.witnessTx, hash := txid }
  while w.seenOrder.size > w.maxSeenTxids do
    let evicted := w.seenOrder[0]!
    w := { w with seenOrder := w.seenOrder.eraseIdx! 0, seenTxids := w.seenTxids.erase evicted }
  return (w, request, events)

/-- An `inv` from a peer: what to send, and the events to emit. `now` stamps the in-flight requests
(the Swift actor stamps them after the send returns). -/
def handleInv (w : MempoolWindow) (p : InventoryPayload) (peer : PeerEndpoint) (now : Nat) :
    MempoolWindow × Array MempoolEffect :=
  let (w, request, events) := w.admitAnnouncements p peer
  let effects := events.map MempoolEffect.emit
  if request.isEmpty then (w, effects)
  else
    let w := request.foldl (fun w v => { w with inFlight := w.inFlight.insert v.hash now }) w
    (w, effects.push (.sendGetData peer { vectors := request }))

/-- The getdata could not be sent: roll the txids back so another peer's announcement re-requests them. -/
def sendFailed (w : MempoolWindow) (request : Array InventoryVector) : MempoolWindow :=
  request.foldl (fun w v => (w.forget v.hash) |> fun w => { w with inFlight := w.inFlight.erase v.hash }) w

/-- A fetched transaction, matched once (its in-flight entry is consumed). -/
def handleTx (w : MempoolWindow) (tx : Transaction) : MempoolWindow × Option MempoolEvent :=
  let txid := tx.txid
  if !w.inFlight.contains txid then (w, none)
  else
    let w := { w with inFlight := w.inFlight.erase txid }
    let (amount, script) := tx.outputs.foldl (fun (acc : Int64 × Option ByteArray) o =>
      if w.watchScripts.contains o.scriptPubKey then (acc.1 + o.value, acc.2 <|> some o.scriptPubKey) else acc) (0, none)
    match script with
    | some s => if amount > 0 then (w, some (.paymentSeen txid amount s)) else (w, none)
    | none => (w, none)

/-- `notfound`: free the txids so a duplicate announcement from another peer re-requests them. -/
def handleNotfound (w : MempoolWindow) (p : InventoryPayload) : MempoolWindow :=
  p.vectors.foldl (fun w v => if v.type.baseType == InventoryType.tx then
    (({ w with inFlight := w.inFlight.erase v.hash } : MempoolWindow).forget v.hash) else w) w

/-- A message from a peer while the window is open. -/
def handle (w : MempoolWindow) (m : PeerMessage) (peer : PeerEndpoint) (now : Nat) : MempoolWindow × Array MempoolEffect :=
  if !w.running then (w, #[])
  else match m with
    | .inv p => w.handleInv p peer now
    | .tx t => match w.handleTx t with
      | (w, some e) => (w, #[.emit e])
      | (w, none) => (w, #[])
    | .notfound p => (w.handleNotfound p, #[])
    | _ => (w, #[])

/-- The periodic sweep: expire requests older than `requestTimeout` (listener attach is I/O). -/
def sweep (w : MempoolWindow) (now : Nat) : MempoolWindow :=
  if !w.running then w
  else
    let expired := w.inFlight.fold (fun acc txid at_ => if at_ + w.requestTimeout < now then acc.push txid else acc) #[]
    expired.foldl (fun w txid => ({ w with inFlight := w.inFlight.erase txid } : MempoolWindow).forget txid) w

end MempoolWindow
end Winnow.Net
