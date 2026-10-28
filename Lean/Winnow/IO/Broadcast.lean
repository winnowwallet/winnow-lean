import Winnow.IO.Pool
import Winnow.Keys.Unicode
import Winnow.Wallet.SwiftDouble

/-! # P2P transaction relay (`Network/Broadcast/TxBroadcaster.swift`)

Announce with `inv(MSG_WITNESS_TX)` to the connected peers, answer `getdata` with the transaction
(once per peer), re-announce on an exponential backoff (60 s doubling to 3600 s, attempt count capped
at 63) until confirmed or cancelled. Per peer and transaction: `announced → requested → served`, plus
`failed` (announcement unanswered for 120 s, disconnect, failed serve — retried on the next attempt)
and `deprioritized` (three announcements without a getdata: skipped from then on). A peer whose BIP133
fee filter exceeds the transaction's rate is skipped (not marked); `feeFloorExceeded` is emitted once
per crossing of the minimum filter across connected peers. Confirmed entries are kept as silent
tombstones until 100 blocks deep, so a reorg can reactivate them. The retry schedule is persisted
before any announcement; a failed write stops the loop (`persistenceFailed`).

`broadcast.json` (version 1): `{"version":1,"transactions":{"<txid hex, internal order>":{"rawTx":…,
"feeRateSatPerVByte":…?,"attempt":…,"nextAttemptAt":<seconds since 1970>,"confirmedAtHeight":…?,
"served":…}}}` — the key order `JSONEncoder` writes, doubles in its shortest form. Loading accepts the
unversioned and the legacy (txid → raw hex) shapes and validates every record (canonical encoding,
txid, fee rate, retry count, retry time at most 366 days ahead), refusing a damaged file rather than
repairing it.

One deliberate difference: a peer's getdata listener subscribes before the announcement is sent
(Swift subscribes inside a task it starts, which can miss a fast reply). -/

namespace Winnow.IO
open Winnow.Net Lean

inductive AnnouncementState where
  | announced | requested | served | failed | deprioritized
  deriving BEq, Inhabited, Repr

def AnnouncementState.rawValue : AnnouncementState → String
  | .announced => "announced" | .requested => "requested" | .served => "served" | .failed => "failed"
  | .deprioritized => "deprioritized"

/-- Why a relay-only session ended (`RelaySessionEnd`). -/
inductive RelaySessionEnd where
  /-- nothing left to relay: confirmed, cancelled or replaced -/
  | drained
  /-- no seat left that can hear about anything pending -/
  | seatsGone
  /-- a retry could not be saved, so the backoff loop stopped -/
  | persistenceBlocked
  deriving Repr, BEq, Inhabited

def RelaySessionEnd.rawValue : RelaySessionEnd → String
  | .drained => "drained" | .seatsGone => "seatsGone" | .persistenceBlocked => "persistenceBlocked"

inductive TxEvent where
  | announced (txid : ByteArray) (peerCount : Nat)
  | requested (txid : ByteArray) (peer : PeerEndpoint)
  | served (txid : ByteArray) (peer : PeerEndpoint)
  | failed (txid : ByteArray) (peer : PeerEndpoint) (reason : String)
  | deprioritized (txid : ByteArray) (peer : PeerEndpoint)
  | confirmed (txid : ByteArray)
  | cancelled (txid : ByteArray)
  | feeFloorExceeded (txid : ByteArray) (floor : Int64)
  | persistenceFailed (reason : String)
  /-- the relay-only session this broadcaster opened has ended; the pool it narrowed is stopped unless the
  caller had resumed full service, and anything pending stays saved for the next start -/
  | relaySessionEnded (reason : RelaySessionEnd)
  deriving Inhabited

inductive BroadcastPersistenceState where
  | disabled | missing
  | loaded (transactionCount : Nat)
  deriving BEq, Inhabited, Repr

structure PeerRelay where
  state : AnnouncementState
  announcements : Nat
  lastAnnouncedAt : Float
  deriving Inhabited

structure PendingTx where
  rawTx : ByteArray
  transaction : Transaction
  feeRate : Option Float
  peers : Std.HashMap String PeerRelay := {}
  attempt : Nat
  nextAttemptAt : Float
  feeFloorExceededEmitted : Bool := false
  served : Bool := false
  confirmedAtHeight : Option UInt32 := none
  deriving Inhabited

structure BroadcastState where
  pending : Std.HashMap ByteArray PendingTx := {}
  persistenceBlocked : Bool := false
  listenedPeers : Std.HashSet String := {}
  subscribers : Array (EventStream TxEvent Unit) := #[]
  stopped : Bool := false
  rebroadcastGeneration : Nat := 0
  nextId : Nat := 0
  /-- a relay-only session this broadcaster opened (`enterRelayOnly`) is open -/
  relayOnlySession : Bool := false

structure TxBroadcaster where
  pool : PeerPool
  path : Option System.FilePath
  rebroadcastBaseMs : Nat
  maxRebroadcastMs : Nat
  maxAnnouncementsPerPeer : Nat
  announcementTimeoutMs : Nat
  /-- Wall clock, seconds since 1970 (`Date()`). -/
  now : IO Float
  persistenceState : BroadcastPersistenceState
  state : IO.Ref BroadcastState

namespace TxBroadcaster

def storageVersion : Nat := 1
def maximumStoredTransactions : Nat := 4_096
def maximumStorageBytes : Nat := 64 * 1_024 * 1_024
def maximumRawTransactionBytes : Nat := 4_000_000
def maximumAttempt : Nat := 63
def maximumFeeRate : Float := 2_100_000_000_000_000.0
def maximumFutureSchedule : Float := 366 * 24 * 60 * 60
/-- `Date.distantFuture.timeIntervalSince1970`. -/
def distantFuture : Float := 64_092_211_200.0

/-- base × 2^attempt, capped. -/
def backoffInterval (attempt base cap : Nat) : Nat := Id.run do
  let mut interval := base
  for _ in [0:attempt] do
    let doubled := interval + interval
    if !(doubled < cap) then return cap
    interval := doubled
  return min interval cap

private def seconds (ms : Nat) : Float := ms.toFloat / 1000

private def damaged {α} (r : String) : Except BroadcastStorageError α := .error (.damaged r)

def validatedTransaction (raw : ByteArray) : Except WireError Transaction := do
  if raw.isEmpty || raw.size > maximumRawTransactionBytes then throw (.malformed s!"raw transaction size {raw.size}")
  let tx ← Transaction.decode raw
  if !(tx.serialized true == raw) then throw (.malformed "non-canonical transaction encoding")
  return tx

def validFeeRate (r : Option Float) : Bool :=
  match r with
  | none => true
  | some x => !x.isNaN && !x.isInf && x > 0 && x ≤ maximumFeeRate

/-! ## The file -/

structure StoredTx where
  rawTx : String
  feeRate : Option Float
  attempt : Int
  nextAttemptAt : Float
  confirmedAtHeight : Option UInt32
  served : Option Bool

private def jsonDouble? (j : Json) : Option Float :=
  match j with
  | .num n =>
    let f := Winnow.SwiftDouble.ofDecimal (n.mantissa < 0) n.mantissa.natAbs (-(n.exponent : Int))
    if f.isInf || f.isNaN then none else some f
  | _ => none

private def optField (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

private def storedTxOf (j : Json) : Option StoredTx := do
  let .str rawTx ← (j.getObjVal? "rawTx").toOption | none
  let feeRate ← match optField j "feeRateSatPerVByte" with
    | none => some none
    | some v => (jsonDouble? v).map some
  let attempt ← PersistedPeers.jsonInt? (← (j.getObjVal? "attempt").toOption) (-(2 ^ 63)) (2 ^ 63 - 1)
  let nextAttemptAt ← jsonDouble? (← (j.getObjVal? "nextAttemptAt").toOption)
  let confirmed ← match optField j "confirmedAtHeight" with
    | none => some none
    | some v => (PersistedPeers.jsonNat? v 0xFFFFFFFF).map (some ·.toUInt32)
  let served ← match optField j "served" with
    | none => some none
    | some (.bool b) => some (some b)
    | some _ => none
  return { rawTx, feeRate, attempt, nextAttemptAt, confirmedAtHeight := confirmed, served }

private def recordIdentity (txidHex rawHex : String) : Except BroadcastStorageError (ByteArray × ByteArray × Transaction) := do
  let some txid := (if txidHex.utf8ByteSize == 64 then Winnow.Keys.dataOfHex? txidHex else none) |>.filter (·.size == 32)
    | damaged "a transaction ID is invalid"
  let some raw := (if rawHex.utf8ByteSize ≤ maximumRawTransactionBytes * 2 then Winnow.Keys.dataOfHex? rawHex else none)
    | damaged s!"transaction {displayHex txid} has invalid raw bytes"
  let .ok tx := validatedTransaction raw | damaged s!"transaction {displayHex txid} cannot be decoded"
  if !(tx.txid == txid) then damaged "a transaction ID does not match its raw bytes"
  return (txid, raw, tx)

private def validatedRecords (records : Array (String × StoredTx)) (now : Float) :
    Except BroadcastStorageError (Std.HashMap ByteArray PendingTx) := do
  if records.size > maximumStoredTransactions then damaged "there are too many pending transactions"
  let mut out : Std.HashMap ByteArray PendingTx := {}
  for (txidHex, r) in records do
    let (txid, raw, tx) ← recordIdentity txidHex r.rawTx
    if !validFeeRate r.feeRate then damaged s!"transaction {displayHex txid} has an invalid fee rate"
    if r.attempt < 0 || r.attempt > maximumAttempt then damaged s!"transaction {displayHex txid} has an invalid retry count"
    if r.nextAttemptAt.isNaN || r.nextAttemptAt.isInf || r.nextAttemptAt < 0 || r.nextAttemptAt > now + maximumFutureSchedule then
      damaged s!"transaction {displayHex txid} has an invalid retry time"
    let entry : PendingTx := {
      rawTx := raw
      transaction := tx
      feeRate := r.feeRate
      attempt := r.attempt.toNat
      nextAttemptAt := if r.confirmedAtHeight.isNone then r.nextAttemptAt else distantFuture
      served := r.served.getD false
      confirmedAtHeight := r.confirmedAtHeight }
    out := out.insert txid entry
  return out

private def objectEntries (j : Json) : Option (Array (String × Json)) :=
  match j with
  | .obj kvs => some kvs.toArray
  | _ => none

/-- Decodes the store's bytes (after the size checks). -/
def decodeStore (data : ByteArray) (now : Float) : Except BroadcastStorageError (Std.HashMap ByteArray PendingTx) := do
  let some text := String.fromUTF8? data | damaged "the JSON is invalid"
  let .ok j := Json.parse text | damaged "the JSON is invalid"
  let .obj _ := j | damaged "the top level is not an object"
  match j.getObjVal? "version" with
  | .ok v =>
    let version : Int ← match v with
      | .num n =>
        let f := jsonDouble? v
        match f with
        | none => damaged "the format version is invalid"
        | some x => if x.floor != x then damaged "the format version is invalid" else
            pure (n.mantissa / (10 ^ n.exponent : Int))
      | .bool b => pure (if b then 1 else 0)
      | _ => damaged "the format version is invalid"
    if version != storageVersion then throw (.unsupportedVersion version)
    let some _ := PersistedPeers.jsonNat? v (2 ^ 63) | damaged "a versioned relay record is invalid"
    let some entries := (j.getObjVal? "transactions").toOption.bind objectEntries | damaged "a versioned relay record is invalid"
    let some records := entries.mapM (fun (k, r) => (storedTxOf r).map (k, ·)) | damaged "a versioned relay record is invalid"
    validatedRecords records now
  | .error _ =>
    let entries := (j.getObjVal? "transactions").toOption.bind objectEntries
    if let some es := entries then
      if let some records := es.mapM (fun (k, r) => (storedTxOf r).map (k, ·)) then
        return ← validatedRecords records now
      if let some legacy := es.mapM (fun (k, r) => match r with | .str s => some (k, s) | _ => none) then
        if legacy.size > maximumStoredTransactions then damaged "there are too many pending transactions"
        let mut out : Std.HashMap ByteArray PendingTx := {}
        for (txidHex, rawHex) in legacy do
          let (txid, raw, tx) ← recordIdentity txidHex rawHex
          out := out.insert txid { rawTx := raw, transaction := tx, feeRate := none, attempt := 0, nextAttemptAt := now }
        return out
    damaged "the relay record format is not recognized"

/-- The JSON `persist` writes. -/
def encodeStore (pending : Std.HashMap ByteArray PendingTx) : ByteArray :=
  let entries := pending.toArray.qsort (fun a b => hex a.1 < hex b.1) |>.toList.map fun (txid, e) =>
    let fee := match e.feeRate with | some r => s!",\"feeRateSatPerVByte\":{Winnow.SwiftDouble.jsonText r}" | none => ""
    let next := if e.confirmedAtHeight.isNone then e.nextAttemptAt else 0
    let conf := match e.confirmedAtHeight with | some h => s!",\"confirmedAtHeight\":{h}" | none => ""
    s!"\"{hex txid}\":\{\"rawTx\":\"{hex e.rawTx}\"{fee},\"attempt\":{e.attempt},\"nextAttemptAt\":{Winnow.SwiftDouble.jsonText next}{conf},\"served\":{e.served}}"
  s!"\{\"version\":{storageVersion},\"transactions\":\{{",".intercalate entries}}}".toUTF8

private def load (path : System.FilePath) (now : Float) :
    NetM (BroadcastPersistenceState × Std.HashMap ByteArray PendingTx) := do
  if !(← fileExists path) then return (.missing, {})
  let some size ← fileSize? path | throw (.broadcastStorage .unreadable)
  if size > maximumStorageBytes then throw (.broadcastStorage (.tooLarge maximumStorageBytes))
  let data ← match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok d => pure d
    | .error _ => throw (.broadcastStorage .unreadable)
  if data.size > maximumStorageBytes then throw (.broadcastStorage (.tooLarge maximumStorageBytes))
  if data.isEmpty then throw (.broadcastStorage (.damaged "the file is empty"))
  match decodeStore data now with
  | .ok p => return (.loaded p.size, p)
  | .error e => throw (.broadcastStorage e)

private def persist (b : TxBroadcaster) (pending : Std.HashMap ByteArray PendingTx) : NetM Unit := do
  let some path := b.path | return
  if pending.size > maximumStoredTransactions then throw (.broadcastStorage .writeFailed)
  let data := encodeStore pending
  if data.size > maximumStorageBytes then throw (.broadcastStorage .writeFailed)
  match ← (writeAtomic path data).toBaseIO with
  | .ok () => pure ()
  | .error _ => throw (.broadcastStorage .writeFailed)

/-! ## Events and accessors -/

private def emit (b : TxBroadcaster) (e : TxEvent) : IO Unit := do
  for s in (← b.state.get).subscribers do s.yield e

def events (b : TxBroadcaster) : IO (EventStream TxEvent Unit) := do
  let id ← b.state.modifyGet fun st => (st.nextId, { st with nextId := st.nextId + 1 })
  let s ← EventStream.new id 1_000_000
  s.onCancel.set (b.state.modify fun st => { st with subscribers := st.subscribers.filter (·.id != id) })
  b.state.modify fun st => { st with subscribers := st.subscribers.push s }
  return s

/-- Transactions still being relayed (confirmed-held entries excluded). -/
def pendingTxids (b : TxBroadcaster) : BaseIO (Array ByteArray) := do
  return (← b.state.get).pending.fold (fun acc k v => if v.confirmedAtHeight.isNone then acc.push k else acc) #[]

def rawTransaction (b : TxBroadcaster) (txid : ByteArray) : BaseIO (Option ByteArray) := do
  match (← b.state.get).pending[txid]? with
  | some e => return if e.confirmedAtHeight.isNone then some e.rawTx else none
  | none => return none

def wasServed (b : TxBroadcaster) (txid : ByteArray) : BaseIO Bool := do
  return ((← b.state.get).pending[txid]?.map (·.served)).getD false

def relayStatus (b : TxBroadcaster) (txid : ByteArray) : BaseIO (Array (String × AnnouncementState)) := do
  match (← b.state.get).pending[txid]? with
  | some e => return e.peers.toArray.map fun (k, r) => (k, r.state)
  | none => return #[]

def attemptCount (b : TxBroadcaster) (txid : ByteArray) : BaseIO (Option Nat) := do
  return (← b.state.get).pending[txid]?.map (·.attempt)
def nextAttemptDate (b : TxBroadcaster) (txid : ByteArray) : BaseIO (Option Float) := do
  return (← b.state.get).pending[txid]?.map (·.nextAttemptAt)

/-! ## Relay -/

private def endpointOfKey (key : String) : Option PeerEndpoint :=
  let cs := key.toList
  match cs.reverse.findIdx? (· == ':') with
  | some i =>
    let sep := cs.length - 1 - i
    let portText := String.ofList (cs.drop (sep + 1))
    match parseUInt32? portText with
    | some p => if p ≤ 65535 then some { host := String.ofList (cs.take sep), port := p.toUInt16 } else none
    | none => none
  | none => none

private def feeFilterRefuses (b : TxBroadcaster) (txid : ByteArray) (peer : PeerConnection) : IO Bool := do
  let some rate := (← b.state.get).pending[txid]? >>= (·.feeRate) | return false
  let some floor ← peer.feeFilter | return false
  return Float.ofInt floor.toInt > rate * 1_000

private def admitsAnnouncement (b : TxBroadcaster) (txid : ByteArray) (peer : PeerConnection) : IO Bool := do
  let key := peer.endpoint.description
  let r ← b.state.modifyGet fun st =>
    match st.pending[txid]? with
    | none => ((true, false), st)
    | some e => match e.peers[key]? with
      | none => ((true, false), st)
      | some relay =>
        if relay.state == .deprioritized then ((false, false), st)
        else if relay.state != .requested && relay.state != .served && relay.announcements ≥ b.maxAnnouncementsPerPeer then
          let e' := { e with peers := e.peers.insert key { relay with state := .deprioritized } }
          ((false, true), { st with pending := st.pending.insert txid e' })
        else ((true, false), st)
  if r.2 then b.emit (.deprioritized txid peer.endpoint)
  return r.1

private def recordAnnouncement (b : TxBroadcaster) (txid : ByteArray) (key : String) : IO Unit := do
  let now ← b.now
  b.state.modify fun st =>
    match st.pending[txid]? with
    | none => st
    | some e =>
      let relay := match e.peers[key]? with
        | some r => { r with
            announcements := r.announcements + 1
            lastAnnouncedAt := now
            state := if r.state == .failed then .announced else r.state }
        | none => { state := .announced, announcements := 1, lastAnnouncedAt := now }
      { st with pending := st.pending.insert txid { e with peers := e.peers.insert key relay } }

private def announce (b : TxBroadcaster) (txid : ByteArray) : IO Unit := do
  if !(← b.state.get).pending.contains txid then return
  let announcement := PeerMessage.inv { vectors := #[{ type := InventoryType.witnessTx, hash := txid }] }
  let mut announced := 0
  for peer in ← b.pool.connectedPeers do
    if ← b.feeFilterRefuses txid peer then continue
    if !(← b.admitsAnnouncement txid peer) then continue
    let .ok () ← (peer.send announcement).attempt | continue
    announced := announced + 1
    b.recordAnnouncement txid peer.endpoint.description
  b.emit (.announced txid announced)

private def expireStaleAnnouncements (b : TxBroadcaster) (txid : ByteArray) : IO Unit := do
  let deadline := (← b.now) - seconds b.announcementTimeoutMs
  let expired ← b.state.modifyGet fun st =>
    match st.pending[txid]? with
    | none => (#[], st)
    | some e =>
      let keys := e.peers.fold (fun acc k r => if r.state == .announced && r.lastAnnouncedAt < deadline then acc.push k else acc) #[]
      let peers := keys.foldl (fun ps k => ps.modify k fun r => { r with state := .failed }) e.peers
      (keys, { st with pending := st.pending.insert txid { e with peers } })
  for k in expired do
    if let some ep := endpointOfKey k then b.emit (.failed txid ep "announcement timeout")

private def markPeerFailed (b : TxBroadcaster) (peer : PeerConnection) (reason : String) : IO Unit := do
  let key := peer.endpoint.description
  let failed ← b.state.modifyGet fun st =>
    let (txids, pending) := st.pending.fold (fun (acc : Array ByteArray × Std.HashMap ByteArray PendingTx) txid e =>
      match e.peers[key]? with
      | some r =>
        if e.confirmedAtHeight.isNone && r.state != .failed && r.state != .deprioritized && r.state != .served then
          (acc.1.push txid, acc.2.insert txid { e with peers := e.peers.insert key { r with state := .failed } })
        else acc
      | none => acc) (#[], st.pending)
    (txids, { st with pending })
  for t in failed do b.emit (.failed t peer.endpoint reason)

private def checkFeeFloors (b : TxBroadcaster) : IO Unit := do
  let mut floors : Array Int64 := #[]
  for peer in ← b.pool.connectedPeers do floors := floors.push ((← peer.feeFilter).getD 0)
  let some minimum := floors.foldl (fun acc x => some (match acc with | some m => min m x | none => x)) none | return
  let fired ← b.state.modifyGet fun st =>
    st.pending.fold (fun (acc : Array ByteArray × BroadcastState) txid e =>
      match e.confirmedAtHeight, e.feeRate with
      | none, some rate =>
        let exceeded := Float.ofInt minimum.toInt > rate * 1_000
        if exceeded && !e.feeFloorExceededEmitted then
          (acc.1.push txid, { acc.2 with pending := acc.2.pending.insert txid { e with feeFloorExceededEmitted := true } })
        else if !exceeded && e.feeFloorExceededEmitted then
          (acc.1, { acc.2 with pending := acc.2.pending.insert txid { e with feeFloorExceededEmitted := false } })
        else acc
      | _, _ => acc) (#[], st)
  for t in fired do b.emit (.feeFloorExceeded t minimum)

private def serve (b : TxBroadcaster) (payload : InventoryPayload) (peer : PeerConnection) : IO Unit := do
  let key := peer.endpoint.description
  let mut seen : Std.HashSet ByteArray := {}
  for v in payload.vectors do
    if !(v.type.baseType == InventoryType.tx) then continue
    let txid := v.hash
    if !(← b.state.get).pending.contains txid || seen.contains txid then continue
    seen := seen.insert txid
    let now ← b.now
    let some e := (← b.state.get).pending[txid]? | continue
    let relay := e.peers[key]?.getD { state := .announced, announcements := 0, lastAnnouncedAt := now }
    if relay.state == .served then continue
    let relay := { relay with state := .requested }
    b.state.modify fun st => match st.pending[txid]? with
      | some e => { st with pending := st.pending.insert txid { e with peers := e.peers.insert key relay } }
      | none => st
    b.emit (.requested txid peer.endpoint)
    let some tx := (← b.state.get).pending[txid]?.map (·.transaction) | continue
    match ← (peer.send (.tx tx)).attempt with
    | .ok () =>
      let firstServe ← b.state.modifyGet fun st => match st.pending[txid]? with
        | some e => (!e.served, { st with pending := st.pending.insert txid { e with served := true } })
        | none => (false, st)
      if firstServe then discard <| (b.persist (← b.state.get).pending).attempt
      b.state.modify fun st => match st.pending[txid]? with
        | some e => { st with pending := st.pending.insert txid { e with peers := e.peers.insert key { relay with state := .served } } }
        | none => st
      b.emit (.served txid peer.endpoint)
    | .error _ =>
      b.state.modify fun st => match st.pending[txid]? with
        | some e => { st with pending := st.pending.insert txid { e with peers := e.peers.insert key { relay with state := .failed } } }
        | none => st
      b.emit (.failed txid peer.endpoint "serve failed")

private partial def listen (b : TxBroadcaster) (peer : PeerConnection) (stream : PeerStream) : IO Unit := do
  let key := peer.endpoint.description
  repeat
    match ← stream.next with
    | .value ev =>
      if (← b.state.get).stopped then return
      match ev with
      | .message (.getdata p) => b.serve p peer
      | .message (.feefilter _) => b.checkFeeFloors
      | .message _ => pure ()
      | .disconnected => b.markPeerFailed peer "disconnected"
    | .finished err =>
      if err.isSome then b.markPeerFailed peer "disconnected"
      break
  b.state.modify fun st => { st with listenedPeers := st.listenedPeers.erase key }

private def ensurePeerListeners (b : TxBroadcaster) : IO Unit := do
  if (← b.state.get).stopped then return
  for peer in ← b.pool.connectedPeers do
    let key := peer.endpoint.description
    let fresh ← b.state.modifyGet fun st =>
      if st.listenedPeers.contains key then (false, st) else (true, { st with listenedPeers := st.listenedPeers.insert key })
    if !fresh then continue
    let stream ← peer.events
    spawn (b.listen peer stream)

/-- Anything still being relayed (a confirmed entry held for a reorg is not relay work). -/
private def hasPendingRelay (st : BroadcastState) : Bool := st.pending.any fun _ e => e.confirmedAtHeight.isNone

/-- Ends the session, stops the pool it narrowed (re-reading its mode, so a caller who resumed full service
keeps it), and says why. -/
private def endRelayOnlySession (b : TxBroadcaster) (reason : RelaySessionEnd) : IO Unit := do
  let was ← b.state.modifyGet fun st => (st.relayOnlySession, { st with relayOnlySession := false })
  if !was then return
  b.pool.stopIfRelayOnly
  b.emit (.relaySessionEnded reason)

/-- Whether any of `peers` can still hear about something pending: a seat that has not given up on a
transaction (requested or served it, or has announcements left and was not deprioritized). -/
private def canAnnounce (b : TxBroadcaster) (st : BroadcastState) (peers : Array PeerConnection) : Bool :=
  let unconfirmed := st.pending.toArray.filter (·.2.confirmedAtHeight.isNone)
  peers.any fun peer =>
    let key := peer.endpoint.description
    unconfirmed.any fun (_, e) =>
      match e.peers[key]? with
      | none => true
      | some r => r.state == .requested || r.state == .served ||
          (r.state != .deprioritized && r.announcements < b.maxAnnouncementsPerPeer)

/-- A session whose seats are gone ends rather than outliving them: an empty pool in a mode that dials
nothing announces to nobody, and no confirmation can arrive over a pool that refuses filter sync. -/
private def endRelayOnlySessionIfSeatsGone (b : TxBroadcaster) : IO Unit := do
  let st ← b.state.get
  if !st.relayOnlySession then return
  let peers ← b.pool.connectedPeers
  if peers.isEmpty || !b.canAnnounce st peers then b.endRelayOnlySession .seatsGone

/-- Announces every due transaction after advancing its schedule durably. -/
private def fireDueAttempts (b : TxBroadcaster) : IO Bool := do
  -- where a session that lost its seats is noticed; the attempt then runs as always (the payment stays
  -- pending and saved for the next start)
  b.endRelayOnlySessionIfSeatsGone
  b.ensurePeerListeners
  let firedAt ← b.now
  let st ← b.state.get
  let due := (st.pending.toArray.qsort (fun x y => hex x.1 < hex y.1)).filter (·.2.nextAttemptAt ≤ firedAt) |>.map (·.1)
  if due.isEmpty then return true
  let candidate := due.foldl (fun (p : Std.HashMap ByteArray PendingTx) txid =>
    match p[txid]? with
    | some e =>
      let attempt := min (e.attempt + 1) maximumAttempt
      p.insert txid { e with attempt, nextAttemptAt := firedAt + seconds (backoffInterval attempt b.rebroadcastBaseMs b.maxRebroadcastMs) }
    | none => p) st.pending
  match ← (b.persist candidate).attempt with
  | .error e =>
    b.state.modify fun s => { s with persistenceBlocked := true }
    b.emit (.persistenceFailed e.description)
    -- the loop stops here, and a session must not outlive it
    b.endRelayOnlySession .persistenceBlocked
    return false
  | .ok () =>
    -- Merge the schedule into the live state (listeners may have changed relay state meanwhile).
    let merge (pending : Std.HashMap ByteArray PendingTx) : Std.HashMap ByteArray PendingTx :=
      due.foldl (fun p txid =>
        match p[txid]?, candidate[txid]? with
        | some live, some c => p.insert txid { live with attempt := c.attempt, nextAttemptAt := c.nextAttemptAt }
        | _, _ => p) pending
    b.state.modify fun s => { s with persistenceBlocked := false, pending := merge s.pending }
  for txid in due do
    b.expireStaleAnnouncements txid
    b.announce txid
  b.checkFeeFloors
  return true

/-- (Re)schedules the backoff loop: wait for the earliest attempt, fire what is due, repeat. -/
partial def scheduleRebroadcast (b : TxBroadcaster) : IO Unit := do
  let gen ← b.state.modifyGet fun st => (st.rebroadcastGeneration + 1, { st with rebroadcastGeneration := st.rebroadcastGeneration + 1 })
  let st ← b.state.get
  if st.stopped || st.persistenceBlocked || !hasPendingRelay st then
    -- the drain, wherever it came from (a confirmation, a cancellation, a replacement): a relay-only
    -- session with no work left ends, and the pool stops itself
    if !hasPendingRelay st then b.endRelayOnlySession .drained
    return
  let rec loop : IO Unit := do
    let st ← b.state.get
    if st.rebroadcastGeneration != gen then return
    let some next := st.pending.fold (fun acc _ e => some (match acc with | some m => min m e.nextAttemptAt | none => e.nextAttemptAt)) none
      | return
    let wait := next - (← b.now)
    let go : IO Unit := do
      if (← b.state.get).rebroadcastGeneration != gen then return
      if ← b.fireDueAttempts then loop
    if wait > 0 then after (wait * 1000).ceil.toUInt64.toNat go else go
  spawn loop

/-! ## API -/

def new (pool : PeerPool) (path : Option System.FilePath := none) (rebroadcastBaseMs : Nat := 60_000)
    (maxRebroadcastMs : Nat := 3_600_000) (maxAnnouncementsPerPeer : Nat := 3) (announcementTimeoutMs : Nat := 120_000)
    (now : IO Float := wallTime) : NetM TxBroadcaster := do
  let (persistenceState, pending) ← match path with
    | some p => load p (← now)
    | none => pure (.disabled, {})
  let stateRef ← IO.mkRef ({ pending } : BroadcastState)
  let b : TxBroadcaster := {
    pool, path, rebroadcastBaseMs, maxRebroadcastMs, maxAnnouncementsPerPeer
    announcementTimeoutMs, now, persistenceState
    state := stateRef }
  if !pending.isEmpty then b.scheduleRebroadcast
  return b

/-- Ends this relay session without changing the durable pending set. -/
def shutdown (b : TxBroadcaster) : IO Unit := do
  let subs ← b.state.modifyGet fun st =>
    if st.stopped then (#[], st)
    else (st.subscribers, { st with stopped := true, rebroadcastGeneration := st.rebroadcastGeneration + 1,
                                    pending := {}, subscribers := #[], relayOnlySession := false })
  for s in subs do s.finish none

/-- Whether a relay-only session this broadcaster opened is still open (a test seam: `pool.mode` is the
truth about the pool, which a caller's `start` takes back without telling this). -/
def isRelayOnly (b : TxBroadcaster) : BaseIO Bool := do return (← b.state.get).relayOnlySession

/-- `enterRelayOnly(seats:)`: goes on relaying with the pool narrowed to a relay-only session, and stops the
pool once nothing is left to relay (the drain, a lost seat or a halted backoff loop ends the session and
emits `relaySessionEnded`). False when no session was opened, and then the pool goes quiet: nothing
pending, a halted loop, or no seat kept (a zero-seat session would announce to nobody and never drain).
The checks are made again after the narrowing, which another task may have run inside; a stop from there
re-reads the mode, so a caller who resumed full service in the gap keeps the pool. -/
def enterRelayOnly (b : TxBroadcaster) (seats : Nat := PeerPool.defaultRelaySeats) : NetM Bool := do
  let st ← b.state.get
  if st.stopped then throw (.broadcast .stopped)
  if !hasPendingRelay st || st.persistenceBlocked then
    b.state.modify fun s => { s with relayOnlySession := false }
    b.pool.stop
    return false
  if (← b.pool.enterRelayOnly seats) == 0 then
    b.state.modify fun s => { s with relayOnlySession := false }
    b.pool.stopIfRelayOnly
    return false
  let opened ← b.state.modifyGet fun s =>
    if s.stopped || s.persistenceBlocked || !hasPendingRelay s then (false, { s with relayOnlySession := false })
    else (true, { s with relayOnlySession := true })
  if !opened then b.pool.stopIfRelayOnly
  return opened

/-- Validates, stores and announces a raw signed transaction; returns its txid (internal order). -/
def broadcast (b : TxBroadcaster) (rawTx : ByteArray) (feeRate : Option Float := none) : NetM ByteArray := do
  if (← b.state.get).stopped then throw (.broadcast .stopped)
  let tx ← match validatedTransaction rawTx with
    | .ok t => pure t
    | .error e => throw (.wire e)
  if !validFeeRate feeRate then throw (.broadcast .invalidFeeRate)
  let txid := tx.txid
  let now ← b.now
  let entry : PendingTx := {
    rawTx, transaction := tx, feeRate, attempt := 0
    nextAttemptAt := now + seconds (backoffInterval 0 b.rebroadcastBaseMs b.maxRebroadcastMs) }
  let candidate := (← b.state.get).pending.insert txid entry
  b.persist candidate
  b.state.modify fun st => { st with pending := candidate, persistenceBlocked := false }
  b.ensurePeerListeners
  b.announce txid
  b.checkFeeFloors
  b.scheduleRebroadcast
  return txid

/-- The transaction was seen in a matched block: keep it as a silent tombstone. -/
def markConfirmed (b : TxBroadcaster) (txid : ByteArray) (height : UInt32) : NetM Unit := do
  let st ← b.state.get
  if st.stopped then throw (.broadcast .stopped)
  let some e := st.pending[txid]? | return
  if e.confirmedAtHeight.isSome then return
  let candidate := st.pending.insert txid { e with confirmedAtHeight := some height, nextAttemptAt := distantFuture }
  b.persist candidate
  b.state.modify fun s => { s with pending := candidate, persistenceBlocked := false }
  b.emit (.confirmed txid)
  b.scheduleRebroadcast

/-- Reactivates entries whose confirming block was disconnected. -/
def rollBack (b : TxBroadcaster) (forkHeight : UInt32) : NetM Unit := do
  let st ← b.state.get
  if st.stopped then throw (.broadcast .stopped)
  let now ← b.now
  let (candidate, reactivated) := st.pending.fold (fun (acc : Std.HashMap ByteArray PendingTx × Bool) txid e =>
    match e.confirmedAtHeight with
    | some h => if h > forkHeight then (acc.1.insert txid { e with confirmedAtHeight := none, nextAttemptAt := now, peers := {} }, true) else acc
    | none => acc) (st.pending, false)
  if !reactivated then return
  b.persist candidate
  b.state.modify fun s => { s with pending := candidate, persistenceBlocked := false }
  b.scheduleRebroadcast

/-- Drops held entries confirmed 100 or more blocks below `tip`. -/
def pruneConfirmed (b : TxBroadcaster) (tip : UInt32) : NetM Unit := do
  let st ← b.state.get
  if st.stopped then return
  let candidate := st.pending.filter fun _ e => match e.confirmedAtHeight with
    | some h => h.toNat + 100 > tip.toNat
    | none => true
  if candidate.size == st.pending.size then return
  b.persist candidate
  b.state.modify fun s => { s with pending := candidate }

/-- Stops relaying a pending transaction without a confirmation. -/
def cancel (b : TxBroadcaster) (txid : ByteArray) : NetM Unit := do
  let st ← b.state.get
  if st.stopped then throw (.broadcast .stopped)
  if !st.pending.contains txid then return
  let candidate := st.pending.erase txid
  b.persist candidate
  b.state.modify fun s => { s with pending := candidate, persistenceBlocked := false }
  b.emit (.cancelled txid)
  b.scheduleRebroadcast

end TxBroadcaster
end Winnow.IO
