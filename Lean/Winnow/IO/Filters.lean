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
  /-- the wallet's first height: where a scan starts again when nothing pinned can be kept -/
  startHeight : UInt32
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
  return { pool, chain, requiredCheckpointPeers, filtersPerChunk := clampFiltersPerChunk filtersPerChunk, crossCheckPolicy,
           startHeight, path,
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

private def beginRequest (f : FilterSyncIO) : NetM Unit := do
  let ok ← f.requesting.modifyGet fun r => (!r, true)
  if !ok then throw (.filters .busy)

private def advanceFrontierTo (f : FilterSyncIO) (next : UInt32) : NetM Bool := do
  let p ← f.progress.get
  if next ≤ p.nextScanHeight then return false
  if next.toNat > (← f.chain.height).toNat + 1 then return false
  let candidate : Progress := { nextScanHeight := next,
                                filterHeaders := p.filterHeaders.filter fun k _ => match parseUInt32? k with
                                  | some h => h < next
                                  | none => false }
  f.persist candidate
  f.progress.set candidate
  return true

/-- Moves the frontier forward to `next`, as a scan begun there would start (`new` at that height): what is
below it was scanned elsewhere, by a scan the caller trusts with it (another of the person's devices, its state
anchored to a block of this chain). Pins below `next` stay; nothing moves back, and nothing moves while a run
is under way. -/
def jumpTo (f : FilterSyncIO) (next : UInt32) : NetM Bool := do
  f.beginRequest
  try f.advanceFrontierTo next
  finally f.requesting.set false

private def noPeersError (f : FilterSyncIO) : IO NetError := do
  let cooling := (← f.pool.coolingEndpoints).size
  return if cooling > 0 then .filters (.peersCoolingDown cooling) else .filters .noPeers

private def classes (f : FilterSyncIO) (peers : Array PeerConnection) : IO (Array (Option PeerSource)) :=
  peers.mapM fun c => f.pool.source c.endpoint

private def sourceSpanOf (f : FilterSyncIO) (agreeing dissenting : Array PeerConnection) : IO (Bool × Bool) := do
  return sourceSpan (← f.classes agreeing) (← f.classes dissenting)

/-- A vote one source class carried alone: everyone is cooled off, nobody condemned (io-test's `voteChecks`). -/
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
  let checkpointPeers := peers.extract 0 (checkpointPeerCount f.requiredCheckpointPeers peers.size)
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

/-- The cfheaders answer the query peers agree on, and whether those who gave it span two known source
classes (what a rewind of a contradicted pin asks for). -/
private def crossCheckedCFHeaders (f : FilterSyncIO) (batchStart batchStop : UInt32) (stopHash : ByteArray)
    (queryPeers : Array PeerConnection) : NetM (CFHeadersMessage × Bool) := do
  let answers ← f.collectedCFHeaders batchStart stopHash queryPeers
  if answers.isEmpty then throw (← f.noPeersError)
  let some (value, minority) := strictMajority answers | do
    for (c, _) in answers do f.pool.transportFailure c s!"cfheaders disagree at {batchStart}"
    throw (.filters (.checkpointMismatch s!"cfheaders disagree at {batchStart}"))
  let agreeing := (answers.filter (·.2 == value)).map (·.1)
  if (← f.sourceSpanOf agreeing minority).2 then
    f.refuseDisputedVote (answers.map (·.1)) s!"cfheaders at {batchStart}: one source class outvotes another"
  let spansClasses := spansKnownClasses (← f.classes agreeing)
  for c in minority do f.pool.misbehaving c s!"cfheaders mismatch at {batchStart}"
  match checkCFHeadersCount value batchStart batchStop with
  | .error e => throw (.filters e)
  | .ok () => return (value, spansClasses)

/-- What pinning a batch came to. -/
inductive Pinned where
  | headers (h : Std.HashMap String String)
  /-- an answer agreed across source classes contradicts the stored pin at this height, under the batch -/
  | disputed (anchor : UInt32)

/-- The batch's filter headers, cross-checked and walked from the stored pin under it. With `rewinds`, a
stored pin that an answer agreed across source classes contradicts is reported and nothing is walked;
without (a range scan, whose record is not the frontier), it is the mismatch it always was. -/
private def pinFilterHeaders (f : FilterSyncIO) (batchStart batchStop : UInt32) (stopHash : ByteArray)
    (peers : Array PeerConnection) (stored : Std.HashMap String String) (rewinds : Bool := false) : NetM Pinned := do
  let mut sourced := #[]
  for c in peers do sourced := sourced.push (c, ← f.pool.source c.endpoint)
  let queryPeers := crossSourceSet sourced
  let mut headers := stored
  for (start, stop) in batches (requestStart stored batchStart) batchStop do
    let some hash ← (if stop == batchStop then pure (some stopHash) else f.chain.blockHash stop)
      | throw (.filters (.badPeerResponse "missing reconstruction header"))
    let (message, spansClasses) ← f.crossCheckedCFHeaders start stop hash queryPeers
    if rewinds && spansClasses && anchorDisputed message start stored then return .disputed (start - 1)
    headers ← match walkFilterHeaders message start stored headers with
      | .ok h => pure h
      | .error e => throw (.filters e)
  return .headers headers

/-- A range scan's pins: nothing is rewound there. -/
private def pinRangeHeaders (f : FilterSyncIO) (batchStart batchStop : UInt32) (stopHash : ByteArray)
    (peers : Array PeerConnection) (stored : Std.HashMap String String) : NetM (Std.HashMap String String) := do
  match ← f.pinFilterHeaders batchStart batchStop stopHash peers stored with
  | .headers h => return h
  | .disputed anchor => throw (.filters (.filterHeaderMismatch (anchor + 1)))

/-- Goes back from a pin a cross-class answer contradicts (`disputedAnchorBoundary`): to the highest
checkpoint boundary pinned below it, or to the wallet's first height with nothing pinned. `onReorg` hears
of it first, as for a fork, so the wallet lets go of what it recorded above. -/
private def rewindDisputedPin (f : FilterSyncIO) (anchor : UInt32) (onReorg : Option (UInt32 → NetM Unit)) : NetM Unit := do
  let progress ← f.progress.get
  match disputedAnchorBoundary progress.filterHeaders anchor with
  | some boundary =>
    if let some cb := onReorg then cb boundary
    f.rollBack boundary
  | none =>
    let resume := min f.startHeight progress.nextScanHeight
    if let some cb := onReorg then cb (if resume == 0 then 0 else resume - 1)
    let candidate : Progress := { nextScanHeight := resume }
    f.persist candidate
    f.progress.set candidate

private def verifiedBlock (f : FilterSyncIO) (peer : PeerConnection) (height : UInt32) (blockHash : ByteArray)
    (timeoutMs : Nat := 120_000) : NetM Block := do
  let limit := blockTimeoutMs timeoutMs peer.endpoint.isOverlay
  let response ← peer.request (.getdata { vectors := #[{ type := InventoryType.witnessBlock, hash := blockHash }] })
    #["block", "notfound"] limit
  match response with
  | .block b =>
    match FilterSync.verifiedBlock b blockHash height with
    | .ok b => return b
    | .error e =>
      f.pool.misbehaving peer (match e with | .badPeerResponse why => why | e => FilterSyncError.description e)
      throw (.filters e)
  | .notfound _ => throw (.filters (.badPeerResponse s!"peer lost block at {height}"))
  | _ => throw (.filters (.badPeerResponse "expected block"))

/-- The range run's deadline (free on the forward path), read before every chunk is asked for and before every
matched block after a batch's first chunk. -/
def checkRangeDeadline (f : FilterSyncIO) : NetM Unit := do
  let some r ← f.rangeRun.get | return
  if (← monoMs) ≥ r.deadlineMs then throw (.range (.runTimedOut r.maxDurationMs))

/-- Counts bytes a run has already read against its budget without refusing: what came in is spent whether or
not it is kept. -/
def countRange (f : FilterSyncIO) (filterBytes blockBytes : Nat) : BaseIO Unit :=
  f.rangeRun.modify (·.map fun r => { r with filterBytesRead := r.filterBytesRead + filterBytes,
                                              blockBytesRead := r.blockBytesRead + blockBytes })

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

/-- A scan this peer failed: it is rested, so the next pass asks another. A peer already refused for the
session (a burst past its bound, a wrong block) is left as judged, and a cancelled scan is nobody's fault.
The failure used to be thrown with the peer left in its seat, the first one, so a peer that withheld its
filters or sent wrong ones was asked again on every pass. A rest and not a ban: a filter that contradicts
its pinned header says the peer or the pin is wrong, not which. -/
private def failedScan {α} (f : FilterSyncIO) (peer : PeerConnection) (e : NetError) : NetM α := do
  match e with
  | .cancelled => pure ()
  | _ => if (← f.pool.connectedPeers).contains peer then f.pool.transportFailure peer e.description
  throw e

/-- One chunk's filters from one peer: the burst is bounded (`chunkByteBound`; past it the connection is torn
down and the peer marked misbehaving), every filter is verified against its pinned header and the chunk must
be whole before any is matched, and the heights whose filters match come back with their block hashes and the
chunk's filter byte count. The filters themselves are not kept. -/
private def fetchChunk (f : FilterSyncIO) (chunkStart chunkStop : UInt32) (peer : PeerConnection)
    (watchScripts : Array ByteArray) (filterHeaders : Std.HashMap String String) :
    NetM (Array (UInt32 × ByteArray) × Nat) := do
  f.checkRangeDeadline
  let some stopHash ← f.chain.blockHash chunkStop | throw (.filters (.badPeerResponse s!"missing header at {chunkStop}"))
  let count := (chunkStop - chunkStart).toNat + 1
  let responses ← match ← (peer.requestMany (.getcfilters { startHeight := chunkStart, stopHash }) "cfilter" count
      (chunkTimeoutSeconds count peer.endpoint.isOverlay * 1000) (maxTotalBytes := some (chunkByteBound count))).toBaseIO with
    | .ok r => pure r
    | .error e@(.peer (.protocolViolation _)) => f.pool.misbehaving peer e.description; throw e
    | .error e => f.failedScan peer e
  let mut heightByHash : Std.HashMap ByteArray UInt32 := {}
  for i in [0:count] do
    let h := chunkStart + i.toUInt32
    if let some hash ← f.chain.blockHash h then heightByHash := heightByHash.insert hash h
  let mut seen : Std.HashMap UInt32 Unit := {}
  let mut verified : Array (UInt32 × CFilterMessage) := #[]
  let mut chunkBytes := 0
  for response in responses do
    let .cfilter m := response | f.failedScan peer (.filters (.badPeerResponse "expected cfilter"))
    let (height, seen') ← match verifiedFilter m heightByHash seen filterHeaders with
      | .ok r => pure r
      | .error e => f.failedScan peer (.filters e)
    seen := seen'
    chunkBytes := chunkBytes + m.filter.size
    verified := verified.push (height, m)
  if seen.size != count then f.failedScan peer (.filters (.badPeerResponse s!"missing cfilters: {seen.size}/{count}"))
  f.peakChunkFilterBytes.modify (max · chunkBytes)
  let mut hits := #[]
  for (height, m) in verified do
    let hit ← match filterMatches m watchScripts with
      | .ok b => pure b
      | .error e => f.failedScan peer (.other s!"filter decode: {e}")
    if hit then hits := hits.push (height, m.blockHash)
  return (hits.qsort (·.1 < ·.1), chunkBytes)

/-- Errors that end the batch for every peer rather than for the one that met them: a cancelled scan, and a
range run's deadline or byte budget. -/
private def endsBatch : NetError → Bool
  | .cancelled | .range _ => true
  | _ => false

/-- The two spending caps of a range run (`RangeScanError`): time and bytes. -/
private def isRangeCap : NetError → Bool
  | .range (.runTimedOut _) | .range (.filterBytesExhausted ..) => true
  | _ => false

/-- A hit's block: from the peer that served its filter, else from each other seat in turn. A peer that fails
to give it is rested, as `failedScan` says; a cancelled scan or a spent run ends the search. -/
private def matchedBlock (f : FilterSyncIO) (peers : Array PeerConnection) (served : PeerConnection)
    (height : UInt32) (blockHash : ByteArray) : NetM Block := do
  let mut first : Option NetError := none
  for peer in #[served] ++ peers.filter (· != served) do
    match ← (f.verifiedBlock peer height blockHash).toBaseIO with
    | .ok b => return b
    | .error e =>
      if endsBatch e then throw e
      first := first.orElse fun _ => some e
      discard <| (f.failedScan (α := Unit) peer e).toBaseIO
  throw (first.getD (.filters .noPeers))

/-- A batch's filters, from every approved peer at once. Each peer takes the next chunk as it finishes one
(one `getcfilters` at a time per connection: a second would cancel the first's collector), so a slow peer
holds up only its own chunk; a chunk a peer fails (it is rested, as `failedScan` says) goes back for the
others, and the batch fails only when no peer is left to take what remains. Then, in height order, each hit's
block is fetched (`matchedBlock`: from the peer that served its filter, else another seat), checked and
delivered, so `onMatch` sees blocks in the order a single peer would have given them.

A range run's caps are kept as one peer kept them. No chunk is asked for once the bytes read, with one chunk as
large as the largest yet for each chunk being fetched, pass the byte budget, so the seats together read past it
by about the one chunk a single peer did; the budget is charged again as chunks and blocks are delivered.
The deadline stops chunks being asked for; the blocks of a batch's first fetched chunk are delivered whatever
the clock says, and only then is the deadline read before each block. Without that, a run cut by its minute
while fetching would refuse the first hit it came to, keep nothing past it, and the next run would stop at the
same hit: an account with a payment in a range longer than a run could never get past it. Every chunk read is
counted against the budget, delivered or not.

Returns `(deliveredThrough, halt)`: `(some batchStop, none)` when the whole batch succeeded; when an
`endsBatch` error (cancellation or a range cap) halted the batch, delivers the contiguous prefix of completed
chunks from chunk 0 in height order and returns the last height whose chunk's hits were all delivered along
with the halting error. A peer failure with no peer left throws without delivering or committing.

One peer used to serve every chunk: over Tor and I2P a batch of mainnet filters took as long as that
peer's tunnel, whatever the other seats could carry. -/
private def scanFilters (f : FilterSyncIO) (batchStart batchStop : UInt32) (peers : Array PeerConnection)
    (watchScripts : Array ByteArray) (filterHeaders : Std.HashMap String String)
    (onMatch : BlockMatch → NetM Unit) : NetM (Option UInt32 × Option NetError) := do
  if peers.isEmpty then throw (.filters .noPeers)
  let work := chunks batchStart batchStop f.filtersPerChunk
  -- the chunks not yet taken, and how many are being fetched: one cell, so a worker that finds nothing to
  -- take waits while a chunk could still come back, and leaves only when none can
  let queue : IO.Ref (List Nat × Nat) ← IO.mkRef (List.range work.size, 0)
  let results : IO.Ref (Array (Option (PeerConnection × Array (UInt32 × ByteArray) × Nat))) ←
    IO.mkRef (Array.replicate work.size none)
  let failure : IO.Ref (Option NetError) ← IO.mkRef none
  let halted : IO.Ref (Option NetError) ← IO.mkRef none
  let rangeRun ← f.rangeRun.get
  let rangeBudget : Option Nat := rangeRun.map (·.maxBytes)
  let fetchedBytes ← IO.mkRef (rangeRun.map (fun r => r.filterBytesRead + r.blockBytesRead) |>.getD 0)
  let worker (peer : PeerConnection) : BaseIO Unit := do
    repeat
      if (← halted.get).isSome then break
      if let some maxBytes := rangeBudget then
        let read ← fetchedBytes.get
        let (_, active) ← queue.get
        let chunk ← f.peakChunkFilterBytes.get
        -- a single peer read on until a chunk took it past the budget: the chunks in flight count as read
        if read + active * chunk > maxBytes then
          halted.modify (·.orElse fun _ => some (.range (.filterBytesExhausted read maxBytes)))
          break
      let taken ← queue.modifyGet fun (l, active) => match l with
        | i :: rest => (some (some i), (rest, active + 1))
        | [] => (if active == 0 then none else some none, ([], active))
      let some next := taken | break
      let some i := next | (IO.sleep 50 : BaseIO Unit); continue
      let (cs, ce) := work[i]!
      match ← (f.fetchChunk cs ce peer watchScripts filterHeaders).toBaseIO with
      | .ok (hits, chunkBytes) =>
        results.modify (·.set! i (some (peer, hits, chunkBytes)))
        if let some maxBytes := rangeBudget then
          let seen ← fetchedBytes.modifyGet fun b => (b + chunkBytes, b + chunkBytes)
          if seen > maxBytes then
            halted.modify (·.orElse fun _ => some (.range (.filterBytesExhausted seen maxBytes)))
        queue.modify fun (l, active) => (l, active - 1)
      | .error e =>
        failure.modify (·.orElse fun _ => some e)
        if endsBatch e then
          halted.modify (·.orElse fun _ => some e)
          queue.modify fun (l, active) => (l, active - 1)
        else
          queue.modify fun (l, active) => (i :: l, active - 1)
        break
  let tasks ← peers.mapM fun peer => BaseIO.asTask (prio := .dedicated) (worker peer)
  for t in tasks do discard <| IO.wait t
  let collected ← results.get
  -- a byte halt names what was read in the end, the chunks in flight when it was called among it
  let batchHalt ← match ← halted.get with
    | some (.range (.filterBytesExhausted _ maxBytes)) => pure (some (.range (.filterBytesExhausted (← fetchedBytes.get) maxBytes)))
    | other => pure other
  if collected.any (·.isNone) && batchHalt.isNone then
    throw ((← failure.get).getD (.filters .noPeers))
  -- chunks read but not reached below are still counted: from `i` on, their filter bytes
  let countRest (i : Nat) : BaseIO Unit := do
    for j in [i:work.size] do
      if let some (_, _, bytes) := collected[j]! then f.countRange bytes 0
  let mut deliveredThrough : Option UInt32 := none
  for i in [0:work.size] do
    let some (peer, hits, chunkBytes) := collected[i]! | do countRest (i + 1); break
    -- the batch's first chunk is delivered whatever the clock says (see above); the byte budget holds for all
    let first := i == 0
    match ← (f.chargeRange chunkBytes 0).toBaseIO with
    | .ok () => pure ()
    | .error e => countRest (i + 1); return (deliveredThrough, some e)
    for (height, blockHash) in hits do
      let step : NetM Unit := do
        if !first then f.checkRangeDeadline
        let block ← f.matchedBlock peers peer height blockHash
        onMatch { height, blockHash, block }
        -- serialising again only when a range budget is counting
        if (← f.rangeRun.get).isSome then f.chargeRange 0 block.serialized.size
      match ← step.toBaseIO with
      | .ok () => pure ()
      | .error e =>
        countRest (i + 1)
        if endsBatch e then return (deliveredThrough, some e)
        else throw e
    deliveredThrough := some work[i]!.2
  return (deliveredThrough, batchHalt)

private def rollBackWithNotify (f : FilterSyncIO) (forkHeight : UInt32)
    (onReorg : Option (UInt32 → NetM Unit)) : NetM Unit := do
  if let some cb := onReorg then cb forkHeight
  f.rollBack forkHeight

private def checkAfterHeaders (f : FilterSyncIO) (afterHeaders : Option (NetM (Option UInt32)))
    (onReorg : Option (UInt32 → NetM Unit)) : NetM Unit := do
  let some check := afterHeaders | return
  let some fork ← check | return
  f.rollBackWithNotify fork onReorg

private def applyForwardTo (f : FilterSyncIO) (forwardTo : Option (NetM (Option UInt32))) : NetM Unit := do
  let some ask := forwardTo | return
  let some next ← ask | return
  discard <| f.advanceFrontierTo next

/-- Syncs headers, applies any header or `afterHeaders` reorg, and advances the frontier via `forwardTo`.
Returns `false` when the chain is not yet proven past its checkpoint, ending the pass before filter work. -/
private def prepareHeaders (f : FilterSyncIO) (onReorg : Option (UInt32 → NetM Unit))
    (afterHeaders : Option (NetM (Option UInt32))) (forwardTo : Option (NetM (Option UInt32))) :
    NetM Bool := do
  let headerOutcome ← f.pool.syncHeaders f.chain
  if let some fork := headerOutcome.minForkHeight then
    f.rollBackWithNotify fork onReorg
  -- a chain held from genesis that has not reached the checkpoint may be a peer's invention: nothing is
  -- scanned on it, and the pass ends as one that did not reach the tip
  if !(← f.chain.proven) then return false
  f.checkAfterHeaders afterHeaders onReorg
  -- what was scanned elsewhere for every script the caller watches is not scanned here again (`jumpTo`)
  f.applyForwardTo forwardTo
  return true

/-- Pins, verifies, scans, and commits one batch; returns `none` when a disputed pin rewound the frontier
and ended the pass early, or `some peers` (the refreshed approved set) to continue. -/
private def syncBatch (f : FilterSyncIO) (ceiling tip : UInt32) (reference : CFCheckptMessage)
    (approvedEndpoints : Array String) (receipt : CrossCheckReceipt) (peers : Array PeerConnection)
    (watchScripts : Array ByteArray) (onReorg : Option (UInt32 → NetM Unit))
    (onMatch : BlockMatch → NetM Unit) : NetM (Option (Array PeerConnection)) := do
  let progress ← f.progress.get
  let batchStart := progress.nextScanHeight
  let batchStop := FilterSync.batchStop batchStart ceiling
  let some stopHash ← f.chain.blockHash batchStop | throw (.filters (.badPeerResponse s!"missing header at {batchStop}"))
  let proposed ← match ← f.pinFilterHeaders batchStart batchStop stopHash peers progress.filterHeaders (rewinds := true) with
    | .headers h => pure h
    | .disputed anchor =>
      -- the pass ends here as one that did not reach the tip, and the next scans again from the boundary
      f.rewindDisputedPin anchor onReorg
      return none
  if let .error e := checkPinnedBoundaries proposed reference tip then throw (.filters e)
  let peers ← f.approved approvedEndpoints
  let (_, halt) ← f.scanFilters batchStart batchStop peers watchScripts proposed onMatch
  if let some e := halt then throw e
  -- the receipt is written on every batch, so the corroboration on disk never describes an older pass
  let candidate : Progress := { nextScanHeight := batchStop + 1,
                                filterHeaders := prunedFilterHeaders proposed (batchStop + 1),
                                crossCheck := some receipt }
  f.persist candidate
  f.progress.set candidate
  return some peers

/-- One sync run (see the module doc). `maxBlocks` bounds it; `onReorg` is awaited before any filter work.
`forwardTo`, asked after that, may move the frontier forward to a height every watched script was scanned to
elsewhere.
`afterHeaders` runs once the headers are in and proven, before any filter work: a fork height it returns
(state that came from elsewhere naming a block this chain does not have) is handled as a reorg to it. -/
def sync (f : FilterSyncIO) (watchScripts : Array ByteArray) (maxBlocks : Option UInt32 := none)
    (onReorg : Option (UInt32 → NetM Unit) := none) (onMatch : BlockMatch → NetM Unit)
    (afterHeaders : Option (NetM (Option UInt32)) := none) (forwardTo : Option (NetM (Option UInt32)) := none) :
    NetM Unit := do
  f.beginRequest
  try
    -- a pool holding seats so a signed payment can go out is not a pool to scan over
    if (← f.pool.mode) != .full then throw (.filters .relayOnly)
    if (← f.pool.connectedPeers).isEmpty then throw (← f.noPeersError)
    if !(← f.prepareHeaders onReorg afterHeaders forwardTo) then return
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
      let some nextPeers ← f.syncBatch ceiling tip reference approvedEndpoints receipt peers watchScripts onReorg onMatch
        | return
      peers := nextPeers
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
handling (the chain is read, never advanced). Every batch is judged as the forward path judges it; a batch
that fails any check or peer commits nothing, while one cut by a range cap (time or bytes) commits the
contiguous prefix of chunks whose filters and matches were delivered. -/
private def runRange (f : FilterSyncIO) (initial : RangeScanProgress) (tip : UInt32) (tipHash : ByteArray)
    (watchScripts : Array ByteArray) (path : Option System.FilePath) (stopAtCaps : Bool)
    (onMatch : BlockMatch → NetM Unit) :
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
    match ← f.checkRangeDeadline.toBaseIO with
    | .ok () => pure ()
    | .error e =>
      if stopAtCaps && isRangeCap e then return record
      else throw e
    let batchStart := record.nextScanHeight
    let batchStop := FilterSync.batchStop batchStart record.toHeight
    let some stopHash ← f.chain.blockHash batchStop | throw (.filters (.badPeerResponse s!"missing header at {batchStop}"))
    -- read before the peer is asked: pinning writes the announced previous header when the record holds none
    let anchored := batchStart == 0 || record.filterHeaders.contains (toString (batchStart - 1).toNat)
    let proposed ← f.pinRangeHeaders batchStart batchStop stopHash peers record.filterHeaders
    if let .error e := checkPinnedBoundaries proposed reference tip then throw (.filters e)
    if !anchored then
      if let .error e := RangeScan.requireComparedBoundary proposed batchStart batchStop tip then throw (.filters e)
    peers ← f.approved approvedEndpoints
    let (deliveredThrough, halt) ← f.scanFilters batchStart batchStop peers watchScripts proposed collect
    match halt with
    | none =>
      let candidate := { record with nextScanHeight := batchStop + 1,
                                     filterHeaders := RangeScan.prunedRangeHeaders proposed (batchStop + 1) initial.fromHeight,
                                     crossCheck := some receipt }
      persistRangeRecord path candidate
      record := candidate
    | some e =>
      if isRangeCap e then
        if let some h := deliveredThrough then
          let candidate := { record with nextScanHeight := h + 1,
                                         filterHeaders := RangeScan.prunedRangeHeaders proposed (h + 1) initial.fromHeight,
                                         crossCheck := some receipt }
          persistRangeRecord path candidate
          record := candidate
        if stopAtCaps then return record
      throw e
  return record

/-- `scanRange(from:to:watchScripts:limits:storageURL:onMatch:)`: scans `[from, to]` for `watchScripts`
without moving the forward frontier: one pass, or one run of a pass, of a restore's back-scan. The header
chain is read, never advanced; the range must be inside it. The record at `path` (never the forward
progress file: each loader refuses the other's) resumes, restarts for a new script set, or starts fresh;
`none` keeps it in memory. A run stopped by a cap commits any contiguous prefix of completed chunks before
stopping (a peer failure still leaves the record at the last batch that committed), so `onMatch` must be
idempotent per height. With `stopAtCaps := true`, hitting the time or byte cap ends the run cleanly with an
incomplete `RangeScanOutcome` at the last commit instead of throwing: a run inside a pass is cut by its
minute; that minute is progress, not a failure. Shares the busy flag with `sync`. -/
def scanRange (f : FilterSyncIO) (fromHeight toHeight : UInt32) (watchScripts : Array ByteArray)
    (limits : RangeScanLimits := RangeScanLimits.make) (path : Option System.FilePath := none)
    (onMatch : BlockMatch → NetM Unit) (stopAtCaps : Bool := false) : NetM RangeScanOutcome := do
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
    if !record.isComplete then record ← f.runRange record tip tipHash watchScripts path stopAtCaps onMatch
    let run := (← f.rangeRun.get).getD { deadlineMs := 0, maxDurationMs := 0, maxBytes := 0 }
    return { fromHeight, toHeight, matchedHeights := run.matchedHeights, scannedThrough := record.scannedThrough,
             isComplete := record.isComplete, iteration := record.iteration, filterBytesRead := run.filterBytesRead,
             blockBytesRead := run.blockBytesRead, crossCheck := record.crossCheck }
  finally
    f.rangeRun.set none
    f.requesting.set false

end FilterSyncIO
end Winnow.IO
