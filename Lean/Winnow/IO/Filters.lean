import Winnow.IO.Pool

/-! # BIP157 filter sync, the I/O half (`Network/Filters/FilterSync.swift`)

The decisions are the Net area's pure functions (`Winnow.Net.FilterSync`); this module runs the
exchanges in Swift's order (see the list at the end of that module): header sync through the pool,
rollback on a fork (`onReorg` awaited first), the `getcfcheckpt` vote across up to three peers
(transport failures cool a peer off, wrong answers evict it), the per-batch `getcfheaders` vote across
a cross-source set, the pinned-boundary check, then `getcfilters` a chunk at a time with
`requestMany`, each filter verified and matched, matched blocks fetched with `getdata(witness block)`
and merkle-checked before `onMatch`, and the progress file written after every batch.

`filters.json` is the Swift `Progress` JSON (`{"filterHeaders":{…},"nextScanHeight":N}` — key order
aside), written atomically, at most 128 MiB. `busy` guards one request at a time. -/

namespace Winnow.IO
open Winnow.Net Winnow.Net.FilterSync

/-- What one range-scan run has spent (`RangeScanRun`), held for the length of a run so the chunk loop can
refuse from inside: the byte and time caps bound a run, not a batch. -/
structure RangeRun where
  deadlineMs : Nat
  maxDurationMs : Nat
  maxBytes : Nat
  filterBytesRead : Nat := 0
  blockBytesRead : Nat := 0
  matchedHeights : Array UInt32 := #[]

structure FilterSyncIO where
  pool : PeerPool
  chain : HeaderStore
  requiredCheckpointPeers : Nat
  filtersPerChunk : UInt32
  /-- whether a run may advance on answers from one acquisition channel (`CrossCheckPolicy`) -/
  crossCheckPolicy : CrossCheckPolicy
  path : Option System.FilePath
  persistenceState : PersistenceState
  progress : IO.Ref Progress
  requesting : IO.Ref Bool
  /-- Test seam: the most filter bytes held at once. -/
  peakChunkFilterBytes : IO.Ref Nat
  /-- the range scan running, if one is (none on the forward path) -/
  rangeRun : IO.Ref (Option RangeRun)

namespace FilterSyncIO

private def readProgressFile (p : System.FilePath) : NetM (Option String) := do
  if !(← fileExists p) then return none
  let some size ← fileSize? p | throw (.filterStorage .unreadable)
  if size > maximumProgressBytes then throw (.filterStorage (.tooLarge maximumProgressBytes))
  let data ← match ← (IO.FS.readBinFile p).toBaseIO with
    | .ok d => pure d
    | .error _ => throw (.filterStorage .unreadable)
  if data.size > maximumProgressBytes then throw (.filterStorage (.tooLarge maximumProgressBytes))
  match String.fromUTF8? data with
  | some t => return some t
  | none => throw (.filterStorage (.damaged "the JSON or a progress field is invalid"))

def new (pool : PeerPool) (chain : HeaderStore) (startHeight : UInt32) (path : Option System.FilePath := none)
    (requiredCheckpointPeers : Nat := 3) (filtersPerChunk : UInt32 := defaultFiltersPerChunk)
    (crossCheckPolicy : CrossCheckPolicy := .acceptSingleSource) : NetM FilterSyncIO := do
  let file ← match path with
    | some p => readProgressFile p
    | none => pure none
  let (state, progress) ← match initialProgress path.isSome file startHeight with
    | .ok r => pure r
    | .error e => throw (.filterStorage e)
  return { pool, chain, requiredCheckpointPeers, filtersPerChunk := clampFiltersPerChunk filtersPerChunk, crossCheckPolicy, path,
           persistenceState := state, progress := ← IO.mkRef progress, requesting := ← IO.mkRef false,
           peakChunkFilterBytes := ← IO.mkRef 0, rangeRun := ← IO.mkRef none }

def nextScanHeight (f : FilterSyncIO) : BaseIO UInt32 := do return (← f.progress.get).nextScanHeight
/-- Who corroborated the checkpoint answer the frontier stands on (`lastCrossCheck`). -/
def lastCrossCheck (f : FilterSyncIO) : BaseIO (Option CrossCheckReceipt) := do return (← f.progress.get).crossCheck
def lastScannedHeight (f : FilterSyncIO) : BaseIO (Option UInt32) := do return FilterSync.lastScannedHeight (← f.progress.get)

/-- The next height to scan and the hash of the last block scanned (none before anything is scanned), read
together so a caller can persist both (`Wallet.recordScanHeight`). -/
def frontier (f : FilterSyncIO) : IO (UInt32 × Option ByteArray) := do
  let next := (← f.progress.get).nextScanHeight
  if next == 0 then return (next, none)
  return (next, ← f.chain.blockHash (next - 1))
def filterHeader (f : FilterSyncIO) (height : UInt32) : BaseIO (Option ByteArray) := do
  return filterHeader? (← f.progress.get).filterHeaders height
def pinnedFilterHeaders (f : FilterSyncIO) : BaseIO (Std.HashMap String String) := do return (← f.progress.get).filterHeaders

private def persist (f : FilterSyncIO) (candidate : Progress) : NetM Unit := do
  let some p := f.path | return
  let data := candidate.toJson.compress.toUTF8
  if data.size > maximumProgressBytes then throw (.filterStorage (.tooLarge maximumProgressBytes))
  match ← (writeAtomic p data).toBaseIO with
  | .ok () => pure ()
  | .error _ => throw (.filterStorage .writeFailed)

/-- Rewinds progress to a fork height (idempotent; the frontier never moves forward). -/
def rollBack (f : FilterSyncIO) (forkHeight : UInt32) : NetM Unit := do
  let some candidate := FilterSync.rollBack (← f.progress.get) forkHeight | return
  f.persist candidate
  f.progress.set candidate

/-- Test seam: sets progress directly. -/
def recordProgress (f : FilterSyncIO) (nextScanHeight : UInt32) (filterHeaders : Std.HashMap String String := {}) :
    NetM Unit := do
  let c : Progress := { nextScanHeight, filterHeaders }
  f.persist c
  f.progress.set c

private def beginRequest (f : FilterSyncIO) : NetM Unit := do
  let ok ← f.requesting.modifyGet fun r => (!r, true)
  if !ok then throw (.filters .busy)

private def noPeersError (f : FilterSyncIO) : IO NetError := do
  let cooling := (← f.pool.coolingEndpoints).size
  return if cooling > 0 then .filters (.peersCoolingDown cooling) else .filters .noPeers

private def classes (f : FilterSyncIO) (peers : Array PeerConnection) : IO (Array (Option PeerSource)) :=
  peers.mapM fun c => f.pool.source c.endpoint

private def sourceSpanOf (f : FilterSyncIO) (agreeing dissenting : Array PeerConnection) : IO (Bool × Bool) := do
  return sourceSpan (← f.classes agreeing) (← f.classes dissenting)

private def refuseDisputedVote {α} (f : FilterSyncIO) (peers : Array PeerConnection) (reason : String) : NetM α := do
  for c in peers do f.pool.transportFailure c reason
  throw (.filters (.checkpointMismatch reason))

/-- The still-connected peers whose cfcheckpt answer was adopted (never a refreshed list). -/
private def approved (f : FilterSyncIO) (endpoints : Array String) : NetM (Array PeerConnection) := do
  let result := (← f.pool.connectedPeers).filter (endpoints.contains ·.endpoint.description)
  if result.isEmpty then throw (.filters .noPeers)
  return result

private def collectedCheckpoints (f : FilterSyncIO) (peers : Array PeerConnection) (tipHash : ByteArray) (tip : UInt32) :
    NetM (Array (PeerConnection × CFCheckptMessage)) := do
  let checkpointPeers := peers.extract 0 (max 1 (min 3 f.requiredCheckpointPeers))
  let mut out := #[]
  for peer in checkpointPeers do
    let response ← match ← (peer.request (.getcfcheckpt { stopHash := tipHash }) #["cfcheckpt"]).attempt with
      | .ok r => pure r
      | .error e@(.peer pe) =>
        if pe.isTransport then f.pool.transportFailure peer e.description; continue else throw e
      | .error e => throw e
    let .cfcheckpt m := response | throw (.filters (.badPeerResponse "expected cfcheckpt"))
    if !(m.stopHash == tipHash) then f.pool.misbehaving peer "cfcheckpt stop hash mismatch"; continue
    if m.filterHeaders.size != (tip / checkpointInterval).toNat then
      f.pool.misbehaving peer "cfcheckpt count mismatch"; continue
    out := out.push (peer, m)
  if out.isEmpty then throw (.filters (.badPeerResponse "no peer answered the cfcheckpt request for our chain tip"))
  return out

private def majorityReference (f : FilterSyncIO) (checkpoints : Array (PeerConnection × CFCheckptMessage)) :
    NetM (CFCheckptMessage × Bool) := do
  if checkpoints.size ≤ 1 then
    match checkpoints[0]? with
    | some (_, m) => return (m, false)
    | none => throw (.filters (.badPeerResponse "no peer answered the cfcheckpt request for our chain tip"))
  let some (value, minority) := strictMajority checkpoints | do
    for (c, _) in checkpoints do f.pool.misbehaving c "cfcheckpt no majority"
    throw (.filters (.checkpointMismatch s!"no cfcheckpt majority across {checkpoints.size} peers"))
  let agreeing := (checkpoints.filter (·.2 == value)).map (·.1)
  let (crossSource, disputed) ← f.sourceSpanOf agreeing minority
  if disputed then f.refuseDisputedVote (checkpoints.map (·.1)) "cfcheckpt: one source class outvotes another"
  -- a majority the policy is about to refuse is not evidence against its dissenters: under
  -- `requireDistinctSources` a single-class majority advances nothing, so they are cooled off rather than
  -- struck from the good-peers list on one channel's word (`dismissMinority`)
  let condemned := crossSource || f.crossCheckPolicy == .acceptSingleSource
  for c in minority do
    if condemned then f.pool.misbehaving c "cfcheckpt mismatch"
    else f.pool.transportFailure c "cfcheckpt mismatch in a single-class vote"
  return (value, crossSource)

private def reconcile (f : FilterSyncIO) (reference : CFCheckptMessage) (crossSource : Bool) (tip : UInt32)
    (onReorg : Option (UInt32 → NetM Unit)) : NetM Unit := do
  match reconcilePins (← f.progress.get).filterHeaders reference crossSource tip with
  | .error e => throw (.filters e)
  | .ok none => pure ()
  | .ok (some target) =>
    if let some cb := onReorg then cb target
    f.rollBack target

/-- `receipt(tipHeight:answer:agreed:)`: the agreeing peers with the class the pool reached each through. -/
def receiptOf (f : FilterSyncIO) (tip : UInt32) (answer : CFCheckptMessage) (agreeing : Array PeerConnection) :
    IO CrossCheckReceipt := do
  let agreed ← agreeing.mapM fun c => do
    return ({ endpoint := c.endpoint.description, source := ← f.pool.source c.endpoint } : CrossCheckAgreement)
  return { tipHeight := tip, answerDigest := hex (sha256d answer.serialized), agreed }

/-- `requireAdmissible`: the policy's verdict on who agreed, before anything is scanned. -/
def requireAdmissible (f : FilterSyncIO) (r : CrossCheckReceipt) : NetM Unit := do
  unless f.crossCheckPolicy.admits r do
    let peers := r.agreed.size
    let classes := r.sourceClasses.size
    throw (.filters (.crossCheckUnavailable
      s!"{peers} peer{if peers == 1 then "" else "s"} agreed, from {classes} known source class{if classes == 1 then "" else "es"}"))

/-- `anchoredReference`: the majority cfcheckpt answer, the peers that gave it and the receipt naming them,
admitted by the policy. -/
def anchoredReference (f : FilterSyncIO) (peers : Array PeerConnection) (tip : UInt32) (tipHash : ByteArray) :
    NetM (CFCheckptMessage × Array String × CrossCheckReceipt × Bool) := do
  let checkpoints ← f.collectedCheckpoints peers tipHash tip
  let (reference, crossSource) ← f.majorityReference checkpoints
  let agreeing := (checkpoints.filter (·.2 == reference)).map (·.1)
  let receipt ← f.receiptOf tip reference agreeing
  f.requireAdmissible receipt
  return (reference, agreeing.map (·.endpoint.description), receipt, crossSource)

private def adoptReference (f : FilterSyncIO) (peers : Array PeerConnection) (tipHash : ByteArray) (tip : UInt32)
    (onReorg : Option (UInt32 → NetM Unit)) : NetM (CFCheckptMessage × Array String × CrossCheckReceipt) := do
  let (reference, approvedEndpoints, receipt, _) ← f.anchoredReference peers tip tipHash
  -- a contradicted pin is rewound only by a reference whose agreement spans source classes
  f.reconcile reference receipt.spansDistinctSources tip onReorg
  return (reference, approvedEndpoints, receipt)

private def collectedCFHeaders (f : FilterSyncIO) (batchStart : UInt32) (stopHash : ByteArray) (queryPeers : Array PeerConnection) :
    NetM (Array (PeerConnection × CFHeadersMessage)) := do
  let mut answers := #[]
  for peer in queryPeers do
    let response ← match ← (peer.request (.getcfheaders { startHeight := batchStart, stopHash }) #["cfheaders"]).attempt with
      | .ok r => pure r
      | .error e@(.peer pe) =>
        if pe.isTransport then f.pool.transportFailure peer e.description; continue else throw e
      | .error e => throw e
    let .cfheaders m := response | throw (.filters (.badPeerResponse "expected cfheaders"))
    if !(m.stopHash == stopHash) then
      f.pool.misbehaving peer s!"cfheaders stop hash mismatch at {batchStart}"; continue
    answers := answers.push (peer, m)
  return answers

private def crossCheckedCFHeaders (f : FilterSyncIO) (batchStart batchStop : UInt32) (stopHash : ByteArray)
    (queryPeers : Array PeerConnection) : NetM CFHeadersMessage := do
  let answers ← f.collectedCFHeaders batchStart stopHash queryPeers
  if answers.isEmpty then throw (← f.noPeersError)
  let some (value, minority) := strictMajority answers | do
    for (c, _) in answers do f.pool.transportFailure c s!"cfheaders disagree at {batchStart}"
    throw (.filters (.checkpointMismatch s!"cfheaders disagree at {batchStart}"))
  let agreeing := (answers.filter (·.2 == value)).map (·.1)
  if (← f.sourceSpanOf agreeing minority).2 then
    f.refuseDisputedVote (answers.map (·.1)) s!"cfheaders at {batchStart}: one source class outvotes another"
  for c in minority do f.pool.misbehaving c s!"cfheaders mismatch at {batchStart}"
  match checkCFHeadersCount value batchStart batchStop with
  | .error e => throw (.filters e)
  | .ok () => return value

private def pinFilterHeaders (f : FilterSyncIO) (batchStart batchStop : UInt32) (stopHash : ByteArray)
    (peers : Array PeerConnection) (stored : Std.HashMap String String) : NetM (Std.HashMap String String) := do
  let mut sourced := #[]
  for c in peers do sourced := sourced.push (c, ← f.pool.source c.endpoint)
  let queryPeers := crossSourceSet sourced
  let mut start := requestStart stored batchStart
  let mut headers := stored
  while start ≤ batchStop do
    let stop := (min (start.toNat + maxRangePerRequest.toNat - 1) batchStop.toNat).toUInt32
    let some hash ← (if stop == batchStop then pure (some stopHash) else f.chain.blockHash stop)
      | throw (.filters (.badPeerResponse "missing reconstruction header"))
    let message ← f.crossCheckedCFHeaders start stop hash queryPeers
    headers ← match walkFilterHeaders message start stored headers with
      | .ok h => pure h
      | .error e => throw (.filters e)
    if stop == batchStop then break
    start := stop + 1
  return headers

private def verifiedBlock (f : FilterSyncIO) (peer : PeerConnection) (height : UInt32) (blockHash : ByteArray)
    (timeoutMs : Nat := 120_000) : NetM Block := do
  let limit := blockTimeoutMs timeoutMs peer.endpoint.isOverlay
  let response ← peer.request (.getdata { vectors := #[{ type := InventoryType.witnessBlock, hash := blockHash }] })
    #["block", "notfound"] limit
  match response with
  | .block b =>
    if !(b.hash == blockHash) then
      f.pool.misbehaving peer s!"block hash mismatch at {height}"
      throw (.filters (.badPeerResponse s!"block hash mismatch at {height}"))
    if !b.hasValidMerkleRoot then
      f.pool.misbehaving peer s!"merkle root mismatch at {height}"
      throw (.filters (.badPeerResponse s!"merkle root mismatch at {height}"))
    return b
  | .notfound _ => throw (.filters (.badPeerResponse s!"peer lost block at {height}"))
  | _ => throw (.filters (.badPeerResponse "expected block"))

/-- The range run's deadline (free on the forward path), read before every chunk and every matched filter. -/
def checkRangeDeadline (f : FilterSyncIO) : NetM Unit := do
  let some r ← f.rangeRun.get | return
  if (← monoMs) ≥ r.deadlineMs then throw (.range (.runTimedOut r.maxDurationMs))

/-- Charges a run's byte budget (filters and matched blocks together) and refuses past it. -/
def chargeRange (f : FilterSyncIO) (filterBytes blockBytes : Nat) : NetM Unit := do
  let some r ← f.rangeRun.modifyGet fun r => match r with
      | some r =>
        let r := { r with filterBytesRead := r.filterBytesRead + filterBytes, blockBytesRead := r.blockBytesRead + blockBytes }
        (some r, some r)
      | none => (none, none)
    | return
  let total := r.filterBytesRead + r.blockBytesRead
  if total > r.maxBytes then throw (.range (.filterBytesExhausted total r.maxBytes))

/-- One chunk: the burst is bounded (`chunkByteBound`; past it the connection is torn down and the peer
marked misbehaving), every filter is verified against its pinned header before any is matched, the range
budget is charged for the chunk, then each filter is matched and each hit's block fetched and delivered. -/
private def scanChunk (f : FilterSyncIO) (chunkStart chunkStop : UInt32) (peer : PeerConnection)
    (watchScripts : Array ByteArray) (filterHeaders : Std.HashMap String String)
    (onMatch : BlockMatch → NetM Unit) : NetM (Std.HashMap UInt32 Unit) := do
  f.checkRangeDeadline
  let some stopHash ← f.chain.blockHash chunkStop | throw (.filters (.badPeerResponse s!"missing header at {chunkStop}"))
  let count := (chunkStop - chunkStart).toNat + 1
  let responses ← match ← (peer.requestMany (.getcfilters { startHeight := chunkStart, stopHash }) "cfilter" count
      (chunkTimeoutSeconds count peer.endpoint.isOverlay * 1000) (maxTotalBytes := some (chunkByteBound count))).toBaseIO with
    | .ok r => pure r
    | .error e@(.peer (.protocolViolation _)) => f.pool.misbehaving peer e.description; throw e
    | .error e => throw e
  let mut heightByHash : Std.HashMap ByteArray UInt32 := {}
  for i in [0:count] do
    let h := chunkStart + i.toUInt32
    if let some hash ← f.chain.blockHash h then heightByHash := heightByHash.insert hash h
  let mut seen : Std.HashMap UInt32 Unit := {}
  let mut verified : Array (UInt32 × CFilterMessage) := #[]
  let mut chunkBytes := 0
  for response in responses do
    let .cfilter m := response | throw (.filters (.badPeerResponse "expected cfilter"))
    let (height, seen') ← match verifiedFilter m heightByHash seen filterHeaders with
      | .ok r => pure r
      | .error e => throw (.filters e)
    seen := seen'
    chunkBytes := chunkBytes + m.filter.size
    verified := verified.push (height, m)
  f.peakChunkFilterBytes.modify (max · chunkBytes)
  f.chargeRange chunkBytes 0
  if watchScripts.isEmpty then return seen
  for (height, m) in verified do
    f.checkRangeDeadline
    let hit ← match filterMatches m watchScripts with
      | .ok b => pure b
      | .error e => throw (.other s!"filter decode: {e}")
    if !hit then continue
    let block ← f.verifiedBlock peer height m.blockHash
    onMatch { height, blockHash := m.blockHash, block }
    -- serialising again only when a range budget is counting
    if (← f.rangeRun.get).isSome then f.chargeRange 0 block.serialized.size
  return seen

private def scanFilters (f : FilterSyncIO) (batchStart batchStop : UInt32) (peer : PeerConnection)
    (watchScripts : Array ByteArray) (filterHeaders : Std.HashMap String String)
    (onMatch : BlockMatch → NetM Unit) : NetM Unit := do
  let count := (batchStop - batchStart).toNat + 1
  let mut seen : Nat := 0
  for (cs, ce) in chunks batchStart batchStop f.filtersPerChunk do
    seen := seen + (← f.scanChunk cs ce peer watchScripts filterHeaders onMatch).size
  if seen != count then throw (.filters (.badPeerResponse s!"missing cfilters: {seen}/{count}"))

/-- One sync run (see the module doc). `maxBlocks` bounds it; `onReorg` is awaited before any filter work. -/
def sync (f : FilterSyncIO) (watchScripts : Array ByteArray) (maxBlocks : Option UInt32 := none)
    (onReorg : Option (UInt32 → NetM Unit) := none) (onMatch : BlockMatch → NetM Unit) : NetM Unit := do
  f.beginRequest
  try
    -- a pool holding seats so a signed payment can go out is not a pool to scan over
    if (← f.pool.mode) != .full then throw (.filters .relayOnly)
    let peers ← f.pool.connectedPeers
    if peers.isEmpty then throw (← f.noPeersError)
    let headerOutcome ← f.pool.syncHeaders f.chain
    if let some fork := headerOutcome.minForkHeight then
      if let some cb := onReorg then cb fork
      f.rollBack fork
    let peers ← f.pool.connectedPeers
    if peers.isEmpty then throw (.filters .noPeers)
    let tip ← f.chain.height
    let tipHash ← f.chain.tipHash
    if let .error e := validateAgainstTip (← f.progress.get) tip then throw (.filterStorage e)
    if tip < (← f.progress.get).nextScanHeight then return
    let some room := scanCeiling (← f.progress.get).nextScanHeight maxBlocks tip | return
    let (reference, approvedEndpoints, receipt) ← f.adoptReference peers tipHash tip onReorg
    let mut peers ← f.approved approvedEndpoints
    let ceiling := (scanCeiling (← f.progress.get).nextScanHeight maxBlocks tip).getD room
    while (← f.progress.get).nextScanHeight ≤ ceiling do
      let progress ← f.progress.get
      let batchStart := progress.nextScanHeight
      let batchStop := (min (batchStart.toNat + maxRangePerRequest.toNat - 1) ceiling.toNat).toUInt32
      let some stopHash ← f.chain.blockHash batchStop | throw (.filters (.badPeerResponse s!"missing header at {batchStop}"))
      let proposed ← f.pinFilterHeaders batchStart batchStop stopHash peers progress.filterHeaders
      if let .error e := checkPinnedBoundaries proposed reference tip then throw (.filters e)
      peers ← f.approved approvedEndpoints
      let some first := peers[0]? | throw (.filters .noPeers)
      f.scanFilters batchStart batchStop first watchScripts proposed onMatch
      -- the receipt is written on every batch, so the corroboration on disk never describes an older pass
      let candidate : Progress := { nextScanHeight := batchStop + 1,
                                    filterHeaders := prunedFilterHeaders proposed (batchStop + 1),
                                    crossCheck := some receipt }
      f.persist candidate
      f.progress.set candidate
    if let .error e := finalCheckpointGuard (← f.progress.get).filterHeaders reference tip then throw (.filters e)
  finally
    f.requesting.set false

/-- A historical receipt, without changing progress: the block at `height` from up to three peers. -/
def transaction (f : FilterSyncIO) (txid : ByteArray) (height : UInt32) : NetM Transaction := do
  f.beginRequest
  try
    let some hash ← f.chain.blockHash height
      | throw (.filters (.badPeerResponse "the payment's block header is unavailable"))
    let mut lastError : NetError := .filters .noPeers
    for peer in (← f.pool.connectedPeers).extract 0 3 do
      match ← (do
          let block ← f.verifiedBlock peer height hash 30_000
          let still ← f.chain.blockHash height
          match block.transactions.find? (·.txid == txid) with
          | some tx => if still == some hash then pure tx else throw (.filters (.badPeerResponse "the payment is not in this block"))
          | none => throw (.filters (.badPeerResponse "the payment is not in this block")) : NetM Transaction).attempt with
      | .ok tx => return tx
      | .error e => lastError := e
    throw lastError
  finally
    f.requesting.set false

end FilterSyncIO

/-! ## Restore-only range scans (`scanRange`, upstream #226) -/

namespace FilterSyncIO

private def liftRange {α} (r : Except RangeScanError α) : NetM α :=
  match r with | .ok a => pure a | .error e => throw (.range e)

private def readRangeRecord (path : Option System.FilePath) : NetM (Option RangeScanProgress) := do
  let some p := path | return none
  if !(← fileExists p) then return none
  let some size ← fileSize? p | throw (.range .recordUnreadable)
  if size > RangeScanProgress.maxBytes then throw (.range (.recordTooLarge RangeScanProgress.maxBytes))
  let data ← match ← (IO.FS.readBinFile p).toBaseIO with
    | .ok d => pure d
    | .error _ => throw (.range .recordUnreadable)
  let some text := String.fromUTF8? data | throw (.range (.recordDamaged "the JSON or a progress field is invalid"))
  liftRange (RangeScanProgress.load (some text))

private def persistRangeRecord (path : Option System.FilePath) (r : RangeScanProgress) : NetM Unit := do
  let some p := path | return
  let data := r.toJson.compress.toUTF8
  if data.size > RangeScanProgress.maxBytes then throw (.range (.recordTooLarge RangeScanProgress.maxBytes))
  match ← (writeAtomic p data).toBaseIO with
  | .ok () => pure ()
  | .error _ => throw (.range .recordWriteFailed)

/-- The batch loop: the forward scan's, with the range's record in place of the frontier and no reorg
handling (the chain is read, never advanced). Every batch is judged as the forward path judges it, and a
batch that fails any check commits nothing. -/
private def runRange (f : FilterSyncIO) (initial : RangeScanProgress) (tip : UInt32) (tipHash : ByteArray)
    (watchScripts : Array ByteArray) (path : Option System.FilePath) (onMatch : BlockMatch → NetM Unit) :
    NetM RangeScanProgress := do
  let peers ← f.pool.connectedPeers
  if peers.isEmpty then throw (← f.noPeersError)
  let (reference, approvedEndpoints, receipt, _) ← f.anchoredReference peers tip tipHash
  if let .error e := checkPinnedBoundaries initial.filterHeaders reference tip then throw (.filters e)
  let mut peers ← f.approved approvedEndpoints
  let collect : BlockMatch → NetM Unit := fun m => do
    f.rangeRun.modify (·.map fun r => { r with matchedHeights := r.matchedHeights.push m.height })
    onMatch m
  let mut record := initial
  while record.nextScanHeight ≤ record.toHeight do
    f.checkRangeDeadline
    let batchStart := record.nextScanHeight
    let batchStop := (min (batchStart.toNat + maxRangePerRequest.toNat - 1) record.toHeight.toNat).toUInt32
    let some stopHash ← f.chain.blockHash batchStop | throw (.filters (.badPeerResponse s!"missing header at {batchStop}"))
    -- read before the peer is asked: pinning writes the announced previous header when the record holds none
    let anchored := batchStart == 0 || record.filterHeaders.contains (toString (batchStart - 1).toNat)
    let proposed ← f.pinFilterHeaders batchStart batchStop stopHash peers record.filterHeaders
    if let .error e := checkPinnedBoundaries proposed reference tip then throw (.filters e)
    if !anchored then
      if let .error e := RangeScan.requireComparedBoundary proposed batchStart batchStop tip then throw (.filters e)
    peers ← f.approved approvedEndpoints
    let some first := peers[0]? | throw (.filters .noPeers)
    f.scanFilters batchStart batchStop first watchScripts proposed collect
    let candidate := { record with nextScanHeight := batchStop + 1,
                                   filterHeaders := RangeScan.prunedRangeHeaders proposed (batchStop + 1) initial.fromHeight,
                                   crossCheck := some receipt }
    persistRangeRecord path candidate
    record := candidate
  return record

/-- `scanRange(from:to:watchScripts:limits:storageURL:onMatch:)`: scans `[from, to]` for `watchScripts`
without moving the forward frontier: one pass, or one run of a pass, of a restore's back-scan. The header
chain is read, never advanced; the range must be inside it. The record at `path` (never the forward
progress file: each loader refuses the other's) resumes, restarts for a new script set, or starts fresh;
`none` keeps it in memory. A run stopped by a cap or a peer leaves the record at the last batch that
committed, so `onMatch` must be idempotent per height. Shares the busy flag with `sync`. -/
def scanRange (f : FilterSyncIO) (fromHeight toHeight : UInt32) (watchScripts : Array ByteArray)
    (limits : RangeScanLimits := RangeScanLimits.make) (path : Option System.FilePath := none)
    (onMatch : BlockMatch → NetM Unit) : NetM RangeScanOutcome := do
  f.beginRequest
  try
    liftRange (RangeScan.checkShape fromHeight toHeight watchScripts.size limits)
    if (← f.pool.mode) != .full then throw (.filters .relayOnly)
    -- the tip and its hash in one read
    let chain ← f.chain.snapshot
    let tip := chain.height
    let tipHash := chain.tipHash
    liftRange (RangeScan.checkChain fromHeight toHeight chain.startHeight tip)
    let mut record ← liftRange (RangeScanProgress.resumed (← readRangeRecord path) fromHeight toHeight
      (RangeScanProgress.fingerprint watchScripts) limits)
    liftRange (RangeScan.checkCheckpointAnchor record toHeight tip)
    f.rangeRun.set (some { deadlineMs := (← monoMs) + limits.maxDurationMs, maxDurationMs := limits.maxDurationMs,
                           maxBytes := limits.maxFilterBytes })
    if !record.isComplete then record ← f.runRange record tip tipHash watchScripts path onMatch
    let run := (← f.rangeRun.get).getD { deadlineMs := 0, maxDurationMs := 0, maxBytes := 0 }
    return { fromHeight, toHeight, matchedHeights := run.matchedHeights, scannedThrough := record.scannedThrough,
             isComplete := record.isComplete, iteration := record.iteration, filterBytesRead := run.filterBytesRead,
             blockBytesRead := run.blockBytesRead, crossCheck := record.crossCheck }
  finally
    f.rangeRun.set none
    f.requesting.set false

end FilterSyncIO
end Winnow.IO
