import Lean.Data.Json
import Std.Data.HashMap
import Winnow.Net.GCS
import Winnow.Net.Messages
import Winnow.Net.HeaderChain

/-! # BIP157 filter sync: the pure logic (`Network/Filters/FilterSync.swift`)

The Swift `FilterSync` is an actor talking to a `PeerPool` and a `HeaderChain`. Everything it decides
without a socket is here as a function over explicit values: the scan ceiling, the progress file
(JSON, validation, pruning, rollback), the cross-check peer set, the strict-majority vote and its
source span, the pinned-boundary comparison, the filter-header chain walk, cfilter verification
and matching, and the merkle check of a fetched block.

What stays with the I/O layer (described, not implemented): `sync(watchScripts:maxBlocks:onReorg:onMatch:)`
and `transaction(_:at:)` — the request/response exchanges (`getcfcheckpt`, `getcfheaders`,
`getcfilters` in chunks of `filtersPerChunk` with `chunkTimeout`, `getdata` for matched blocks), the
pool callbacks (`misbehaving` bans, `transportFailure` cooldowns, `connectedPeers`, `source(of:)`,
`coolingEndpoints`), the `busy` guard, the awaited `onReorg`/`onMatch` callbacks, and the atomic file
write of `Progress` (bounded to 128 MiB). The last section lists the order in which the steps run. -/

namespace Winnow.Net
open Lean

inductive FilterSyncError where
  | busy
  | noPeers
  /-- the pool is in a relay-only session (`PeerPool.enterRelayOnly`), which does not read the chain -/
  | relayOnly
  /-- `requireDistinctSources` refused the agreement this run found -/
  | crossCheckUnavailable (reason : String)
  | peersCoolingDown (count : Nat)
  | checkpointMismatch (reason : String)
  | badPeerResponse (reason : String)
  | filterHeaderMismatch (height : UInt32)
  | unexpectedBlockHash
  deriving Repr, BEq, Inhabited

def FilterSyncError.name : FilterSyncError → String
  | .busy => "busy" | .noPeers => "noPeers" | .relayOnly => "relayOnly" | .crossCheckUnavailable _ => "crossCheckUnavailable"
  | .peersCoolingDown _ => "peersCoolingDown"
  | .checkpointMismatch _ => "checkpointMismatch" | .badPeerResponse _ => "badPeerResponse"
  | .filterHeaderMismatch _ => "filterHeaderMismatch" | .unexpectedBlockHash => "unexpectedBlockHash"

inductive FilterSyncStorageError where
  | unreadable
  | tooLarge (maxBytes : Nat)
  | damaged (reason : String)
  | writeFailed
  | frontierBeforeWallet (stored wallet : UInt32)
  | frontierBeyondTip (stored tip : UInt32)
  deriving Repr, BEq, Inhabited

def FilterSyncStorageError.name : FilterSyncStorageError → String
  | .unreadable => "unreadable" | .tooLarge _ => "tooLarge" | .damaged _ => "damaged"
  | .writeFailed => "writeFailed" | .frontierBeforeWallet .. => "frontierBeforeWallet"
  | .frontierBeyondTip .. => "frontierBeyondTip"

/-- Where a peer came from (`PeerSource`, Network/Peers/PeerDiversity.swift). -/
inductive PeerSource where
  | manual | persisted
  /-- The census list (upstream renamed `fallback` to `census` and kept the raw value `"fallback"`, so a
  saved peer keeps its provenance). -/
  | census
  | dnsSeed
  deriving BEq, Inhabited, Repr, DecidableEq

def PeerSource.ofRaw? : String → Option PeerSource
  | "manual" => some .manual | "persisted" => some .persisted | "fallback" => some .census
  | "dnsSeed" => some .dnsSeed | _ => none

def PeerSource.rawValue : PeerSource → String
  | .manual => "manual" | .persisted => "persisted" | .census => "fallback" | .dnsSeed => "dnsSeed"

/-- Whether a scan may advance on answers that all reached us through one acquisition channel
(`FilterSync.CrossCheckPolicy`). Every network defaults to `acceptSingleSource`, the behaviour before the
policy existed; a caller that wants distinct sources asks for it. -/
inductive CrossCheckPolicy where
  /-- whatever agreed is enough, down to a lone surviving peer -/
  | acceptSingleSource
  /-- the adopted cfcheckpt answer must come from peers of at least two distinct known classes, or the run
  throws `crossCheckUnavailable` having changed nothing -/
  | requireDistinctSources
  deriving Repr, BEq, Inhabited

/-- How many distinct source classes must agree before `requireDistinctSources` lets a scan advance. -/
def minimumAgreeingSourceClasses : Nat := 2

/-- One peer whose cfcheckpt answer was adopted: its `host:port`, and the class the pool reached it through
(`none` when unknown; an unknown class never counts towards distinct sources). -/
structure CrossCheckAgreement where
  endpoint : String
  source : Option PeerSource
  deriving Repr, BEq, Inhabited

/-- Who agreed about the filter commitments a run scanned on (`CrossCheckReceipt`): the tip the answers
were about, SHA256d of the adopted cfcheckpt message (hex), and the agreeing peers in the order asked.
Saved with the frontier and rewritten on every commit; a degraded run writes an honest one-class receipt. -/
structure CrossCheckReceipt where
  tipHeight : UInt32
  answerDigest : String
  agreed : Array CrossCheckAgreement
  deriving Repr, BEq, Inhabited

namespace CrossCheckReceipt
/-- The distinct known classes among the agreeing peers (not the pool's: a pool holding three classes proves
nothing about which of them answered). -/
def sourceClasses (r : CrossCheckReceipt) : Array PeerSource :=
  r.agreed.foldl (fun acc a => match a.source with
    | some s => if acc.contains s then acc else acc.push s
    | none => acc) #[]
def spansDistinctSources (r : CrossCheckReceipt) : Bool := r.sourceClasses.size ≥ minimumAgreeingSourceClasses

def toJson (r : CrossCheckReceipt) : Json :=
  Json.mkObj [("tipHeight", Lean.toJson r.tipHeight.toNat), ("answerDigest", Json.str r.answerDigest),
    ("agreed", Json.arr (r.agreed.map fun a =>
      Json.mkObj ([("endpoint", Json.str a.endpoint)] ++
        (match a.source with | some s => [("source", Json.str s.rawValue)] | none => []))))]

/-- A class this build does not know decodes as `none` rather than refusing the file. -/
def ofJson? (j : Json) : Option CrossCheckReceipt := do
  let tip ← (j.getObjValAs? Nat "tipHeight").toOption
  if tip > 0xFFFFFFFF then none
  let digest ← (j.getObjValAs? String "answerDigest").toOption
  let agreed ← (j.getObjValAs? (Array Json) "agreed").toOption
  let agreed ← agreed.mapM fun a => do
    let endpoint ← (a.getObjValAs? String "endpoint").toOption
    let source := match a.getObjVal? "source" with
      | .ok (.str s) => PeerSource.ofRaw? s
      | _ => none
    return ({ endpoint, source } : CrossCheckAgreement)
  return { tipHeight := tip.toUInt32, answerDigest := digest, agreed }
end CrossCheckReceipt

def CrossCheckPolicy.admits (p : CrossCheckPolicy) (r : CrossCheckReceipt) : Bool :=
  match p with
  | .acceptSingleSource => true
  | .requireDistinctSources => r.spansDistinctSources

inductive PersistenceState where
  | disabled | missing | loaded
  deriving BEq, Inhabited, Repr

def PersistenceState.name : PersistenceState → String
  | .disabled => "disabled" | .missing => "missing" | .loaded => "loaded"

/-- A block whose compact filter matched the watch list. -/
structure BlockMatch where
  height : UInt32
  blockHash : ByteArray
  block : Block

/-- Persisted sync progress: the next height to scan and pinned filter headers
(decimal height → hex, internal byte order). Keys are kept as written. -/
structure Progress where
  nextScanHeight : UInt32
  filterHeaders : Std.HashMap String String := {}
  /-- the cross-check of the run that last moved this frontier; none in an older file and after a rollback -/
  crossCheck : Option CrossCheckReceipt := none
  /-- what the file says it is, when it says: forward progress never writes it; a range-scan record writes
  `"range"`, which the forward loader refuses -/
  record : Option String := none
  deriving Inhabited

namespace Progress
def eq (a b : Progress) : Bool :=
  a.nextScanHeight == b.nextScanHeight && a.crossCheck == b.crossCheck && a.record == b.record &&
    a.filterHeaders.size == b.filterHeaders.size &&
    a.filterHeaders.toList.all fun (k, v) => b.filterHeaders[k]? == some v
instance : BEq Progress := ⟨eq⟩

/-- The keys in a stable order (for encoding). -/
def sortedHeaders (p : Progress) : Array (String × String) :=
  p.filterHeaders.toArray.qsort (fun a b => a.1 < b.1)

/-- The JSON `JSONEncoder` writes (key order aside, which carries no meaning). -/
def toJson (p : Progress) : Json :=
  Json.mkObj ([("nextScanHeight", Lean.toJson p.nextScanHeight.toNat),
    ("filterHeaders", Json.mkObj (p.sortedHeaders.toList.map fun (k, v) => (k, Json.str v)))] ++
    (match p.crossCheck with | some r => [("crossCheck", r.toJson)] | none => []) ++
    (match p.record with | some k => [("record", Json.str k)] | none => []))

/-- `JSONDecoder().decode(Progress.self, …)`: an object with an integral `nextScanHeight` in UInt32 range
(`5.0`, `1e2`, `-0` are accepted, as Foundation accepts them) and an object of strings `filterHeaders`;
other fields are ignored. Any failure is `damaged`. (Foundation also takes a trailing comma and the
first of duplicated keys; this parser takes neither.) -/
def ofJsonText (text : String) : Except FilterSyncStorageError Progress := do
  let bad : FilterSyncStorageError := .damaged "the JSON or a progress field is invalid"
  let j ← (Json.parse text).mapError fun _ => bad
  let .num n ← (j.getObjVal? "nextScanHeight").mapError (fun _ => bad) | throw bad
  -- n = mantissa / 10^exponent
  let scale := 10 ^ n.exponent
  if n.mantissa % (scale : Int) != 0 then throw bad
  let v := n.mantissa / (scale : Int)
  if v < 0 || v > 0xFFFFFFFF then throw bad
  let .obj kvs ← (j.getObjVal? "filterHeaders").mapError (fun _ => bad) | throw bad
  let mut headers : Std.HashMap String String := {}
  for (k, val) in kvs.toArray do
    let .str s := val | throw bad
    headers := headers.insert k s
  let crossCheck ← match j.getObjVal? "crossCheck" with
    | .ok .null | .error _ => pure none
    | .ok r => match CrossCheckReceipt.ofJson? r with
      | some c => pure (some c)
      | none => throw bad
  let record ← match j.getObjVal? "record" with
    | .ok .null | .error _ => pure none
    | .ok (.str k) => pure (some k)
    | .ok _ => throw bad
  return { nextScanHeight := v.toNat.toUInt32, filterHeaders := headers, crossCheck, record }
end Progress

namespace FilterSync

def basicFilterType : UInt8 := 0
def maxRangePerRequest : UInt32 := 1_000
def checkpointInterval : UInt32 := 1_000
def defaultFiltersPerChunk : UInt32 := 100
def maximumProgressBytes : Nat := 128 * 1_024 * 1_024
def maximumPinnedHeaders : Nat := 2_000_000
/-- The largest cfilter message a chunk may carry (BIP158 filters are tens of kilobytes on mainnet). -/
def maxFilterMessageBytes : Nat := 1_250_000
/-- `chunkByteBound(filters:)`: how many bytes a chunk of `filters` cfilters may total. -/
def chunkByteBound (filters : Nat) : Nat := filters * maxFilterMessageBytes

/-- `filtersPerChunk` clamped to 1 … `maxRangePerRequest`. -/
def clampFiltersPerChunk (n : UInt32) : UInt32 := min (max 1 n) maxRangePerRequest

def filterHeader? (headers : Std.HashMap String String) (height : UInt32) : Option ByteArray :=
  headers[toString height.toNat]? >>= Winnow.Wire.dataOfHex?

def lastScannedHeight (p : Progress) : Option UInt32 :=
  if p.nextScanHeight == 0 then none else some (p.nextScanHeight - 1)

/-! ## The progress file -/

/-- `validate(progress:startHeight:)`, run on a loaded file. -/
def maximumReceiptEntries : Nat := 64
def maximumReceiptEndpointBytes : Nat := 320

/-- `validate(receipt:)`: at most 64 peers, a 64-character hex digest of 32 bytes, plausible endpoints. -/
def validateReceipt (r : Option CrossCheckReceipt) : Except FilterSyncStorageError Unit := do
  let some r := r | return
  if r.agreed.size > maximumReceiptEntries then throw (.damaged "the cross-check receipt names too many peers")
  unless r.answerDigest.utf8ByteSize == 64 && ((Winnow.Wire.dataOfHex? r.answerDigest).map (·.size == 32) |>.getD false) do
    throw (.damaged "the cross-check receipt's answer digest is not 32 bytes")
  unless r.agreed.all (fun a => 1 ≤ a.endpoint.utf8ByteSize && a.endpoint.utf8ByteSize ≤ maximumReceiptEndpointBytes) do
    throw (.damaged "a cross-check receipt endpoint is not a plausible length")

/-- `validate(filterHeaders:below:maxPinned:)`: canonical decimal heights below the frontier, 32-byte hex. -/
def validateFilterHeaders (headers : Std.HashMap String String) (frontier : UInt32) (maxPinned : Nat) :
    Except FilterSyncStorageError Unit := do
  if headers.size > maxPinned then throw (.damaged "there are too many pinned filter headers")
  for (key, value) in headers.toArray do
    let some height := parseUInt32? key | throw (.damaged "a filter-header height is not canonical decimal")
    if toString height.toNat != key then throw (.damaged "a filter-header height is not canonical decimal")
    -- (two keys naming one height cannot survive the canonical check)
    if !(height < frontier) then throw (.damaged "a pinned filter header is at or beyond the scan frontier")
    if !(value.utf8ByteSize == 64 && ((Winnow.Wire.dataOfHex? value).map (·.size == 32) |>.getD false)) then
      throw (.damaged "a pinned filter header is not 32 bytes")

def validateLoaded (p : Progress) (startHeight : UInt32) : Except FilterSyncStorageError Unit := do
  if let some kind := p.record then throw (.damaged s!"the file is a \"{kind}\" record, not compact-filter progress")
  if p.nextScanHeight < startHeight then throw (.frontierBeforeWallet p.nextScanHeight startHeight)
  validateFilterHeaders p.filterHeaders p.nextScanHeight maximumPinnedHeaders
  validateReceipt p.crossCheck

/-- `load(storageURL:startHeight:)` over the file's text (`none`: no file). -/
def load (file : Option String) (startHeight : UInt32) : Except FilterSyncStorageError (PersistenceState × Progress) := do
  let some text := file | return (.missing, { nextScanHeight := startHeight })
  if text.utf8ByteSize > maximumProgressBytes then throw (.tooLarge maximumProgressBytes)
  let p ← Progress.ofJsonText text
  validateLoaded p startHeight
  return (.loaded, p)

/-- `init`: progress from storage when enabled, else fresh at `startHeight`. -/
def initialProgress (storage : Bool) (file : Option String) (startHeight : UInt32) :
    Except FilterSyncStorageError (PersistenceState × Progress) :=
  if storage then load file startHeight else .ok (.disabled, { nextScanHeight := startHeight })

def validateAgainstTip (p : Progress) (tip : UInt32) : Except FilterSyncStorageError Unit :=
  if p.nextScanHeight.toNat > tip.toNat + 1 then .error (.frontierBeyondTip p.nextScanHeight tip) else .ok ()

/-- Rewinds to a fork: the frontier never moves forward; pins above the fork are dropped (keys that do
not parse as a height are dropped too). `none`: nothing changes, so nothing is persisted. -/
def rollBack (p : Progress) (forkHeight : UInt32) : Option Progress :=
  let resumeFrom := if forkHeight == 0xFFFFFFFF then forkHeight else forkHeight + 1
  let candidate : Progress := {
    nextScanHeight := min p.nextScanHeight resumeFrom
    filterHeaders := p.filterHeaders.filter fun k _ => match parseUInt32? k with
      | some h => h ≤ forkHeight
      | none => false
    -- a corroboration taken on a branch that no longer exists
    crossCheck := none }
  if candidate == p then none else some candidate

/-- The pinned headers a frontier can still be asked for: every checkpoint boundary, the earliest pin,
and everything from the boundary below the last one. Nothing is pruned when the anchor at
`frontier - 1` is missing. -/
def prunedFilterHeaders (headers : Std.HashMap String String) (frontier : UInt32) : Std.HashMap String String :=
  if frontier == 0 then headers
  else
    let anchor := frontier - 1
    if !headers.contains (toString anchor.toNat) then headers
    else
      let lastBoundary := (anchor / checkpointInterval) * checkpointInterval
      let keepFrom := if lastBoundary < checkpointInterval then 0 else lastBoundary - checkpointInterval
      let firstAnchor := headers.fold (fun acc k _ => match parseUInt32? k with
        | some h => some (match acc with | some m => min m h | none => h)
        | none => acc) (none : Option UInt32)
      headers.filter fun k _ => match parseUInt32? k with
        | some h => some h == firstAnchor || h ≥ keepFrom || (h > 0 && h % checkpointInterval == 0)
        | none => false

/-! ## Scheduling -/

/-- The highest block one run may scan (`maxBlocks` from the frontier, never past the tip, never a
block whose successor height cannot be stored); `none`: no room. -/
def scanCeiling (frontier : UInt32) (maxBlocks : Option UInt32) (tip : UInt32) : Option UInt32 :=
  let representableTip := min tip (0xFFFFFFFF - 1)
  if frontier > representableTip then none
  else match maxBlocks with
    | none => some representableTip
    | some 0 => none
    | some m => some (min (frontier.toNat + m.toNat - 1) representableTip.toNat).toUInt32

/-- The batches of one run: ≤ `maxRangePerRequest` blocks from the frontier to the ceiling. -/
def batches (frontier ceiling : UInt32) : Array (UInt32 × UInt32) := Id.run do
  let mut out := #[]
  let mut start := frontier.toNat
  while start ≤ ceiling.toNat do
    let stop := min (start + maxRangePerRequest.toNat - 1) ceiling.toNat
    out := out.push (start.toUInt32, stop.toUInt32)
    start := stop + 1
  return out

/-- The chunks of a batch, `filtersPerChunk` filters each. -/
def chunks (batchStart batchStop filtersPerChunk : UInt32) : Array (UInt32 × UInt32) := Id.run do
  let mut out := #[]
  let mut start := batchStart.toNat
  while start ≤ batchStop.toNat do
    let stop := min (start + filtersPerChunk.toNat - 1) batchStop.toNat
    out := out.push (start.toUInt32, stop.toUInt32)
    if stop == batchStop.toNat then break
    start := stop + 1
  return out

/-- A chunk's deadline in seconds: its share of 120 s per 1000 filters, at least 30 s. A Tor or I2P peer
gets ten times that share and at least two minutes (a chunk of mainnet filters is megabytes, and an I2P
tunnel carried the census at about half a megabit a second). -/
def chunkTimeoutSeconds (filters : Nat) (overlay : Bool := false) : Nat :=
  if overlay then max 120 (1_200 * filters / maxRangePerRequest.toNat)
  else max 30 (120 * filters / maxRangePerRequest.toNat)

/-- A matched block's deadline in milliseconds: whole blocks are megabytes too, so an overlay peer gets
at least five minutes. -/
def blockTimeoutMs (timeoutMs : Nat) (overlay : Bool) : Nat :=
  if overlay then max timeoutMs 300_000 else timeoutMs

/-- How many peers the cfcheckpt comparison asks (1 … 3 of those connected). -/
def checkpointPeerCount (requiredCheckpointPeers connected : Nat) : Nat :=
  min connected (max 1 (min 3 requiredCheckpointPeers))

/-! ## Choosing and judging peers -/

/-- The cross-check set (`crossSourceSet`): the first peer, then the first of each class not yet
represented, then the rest in seating order, up to `limit`. Peers are named by an id. -/
def crossSourceSet {ι} [BEq ι] (peers : Array (ι × Option PeerSource)) (limit : Nat := 3) : Array ι := Id.run do
  let some (a, s) := peers[0]? | return #[]
  if limit == 0 then return #[]
  let mut chosen := #[a]
  let mut classes := #[s]
  let rest := peers.extract 1 peers.size
  for (p, src) in rest do
    if chosen.size < limit && !classes.contains src then
      chosen := chosen.push p
      classes := classes.push src
  for (p, _) in rest do
    if chosen.size < limit && !chosen.contains p then chosen := chosen.push p
  return chosen

/-- The answer more than half gave, and the peers that gave something else (ties: the first counted). -/
def strictMajority {ι α} [BEq α] (answers : Array (ι × α)) : Option (α × Array ι) := Id.run do
  let mut tally : Array (α × Nat) := #[]
  for (_, v) in answers do
    match tally.findIdx? (·.1 == v) with
    | some i => tally := tally.modify i fun (x, c) => (x, c + 1)
    | none => tally := tally.push (v, 1)
  let some best := tally.foldl (fun acc e => match acc with
      | none => some e
      | some b => if b.2 < e.2 then some e else some b) none
    | return none
  if !(best.2 * 2 > answers.size) then return none
  return some (best.1, (answers.filter fun (_, v) => !(v == best.1)).map (·.1))

/-- `sourceSpan`: (crossSource, disputed) from the classes of the agreeing and dissenting peers. -/
def sourceSpan (agreeing dissenting : Array (Option PeerSource)) : Bool × Bool :=
  let dedup (xs : Array (Option PeerSource)) := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]
  let a := dedup agreeing
  let d := dedup dissenting
  let crossSource := a.size > 1
  (crossSource, !crossSource && !(d.all a.contains))

/-- One cfcheckpt reply as `collectedCheckpoints` judges it: answered about our tip, with
`tip / 1000` headers. `false`: the peer is evicted as misbehaving and the others are still asked. -/
def acceptCheckpoint (m : CFCheckptMessage) (tipHash : ByteArray) (tip : UInt32) : Bool :=
  m.stopHash == tipHash && m.filterHeaders.size == (tip / checkpointInterval).toNat

/-- The lowest checkpoint height (1000, 2000, … ≤ tip) whose pinned header differs from the reference. -/
def lowestDisputedBoundary (headers : Std.HashMap String String) (reference : CFCheckptMessage) (tip : UInt32) : Option UInt32 := Id.run do
  for i in [0:reference.filterHeaders.size] do
    let height := (i + 1) * checkpointInterval.toNat
    if height > tip.toNat then break
    if let some pinned := filterHeader? headers height.toUInt32 then
      if !(pinned == reference.filterHeaders[i]!) then return some height.toUInt32
  return none

def checkPinnedBoundaries (headers : Std.HashMap String String) (reference : CFCheckptMessage) (tip : UInt32) :
    Except FilterSyncError Unit :=
  match lowestDisputedBoundary headers reference tip with
  | some h => .error (.checkpointMismatch s!"pinned header at {h} disagrees with cfcheckpt")
  | none => .ok ()

/-- `reconcilePins`: `none` when nothing pinned is disputed; else the height to roll back to (the
boundary below the disputed one) when the reference was agreed across source classes. -/
def reconcilePins (headers : Std.HashMap String String) (reference : CFCheckptMessage) (crossSource : Bool) (tip : UInt32) :
    Except FilterSyncError (Option UInt32) :=
  match lowestDisputedBoundary headers reference tip with
  | none => .ok none
  | some disputed =>
    if !crossSource then .error (.checkpointMismatch s!"pinned header at {disputed} disagrees with cfcheckpt")
    else .ok (some (disputed - checkpointInterval))

/-- `pinFilterHeaders`' starting point: after a deep rollback into pruned history, reconstruct from
the closest surviving pin below the batch. -/
def requestStart (stored : Std.HashMap String String) (batchStart : UInt32) : UInt32 :=
  if batchStart > 0 && !stored.contains (toString (batchStart - 1).toNat) then
    let below := stored.fold (fun acc k _ => match parseUInt32? k with
      | some h => if h < batchStart then some (match acc with | some m => max m h | none => h) else acc
      | none => acc) (none : Option UInt32)
    match below with
    | some a => a + 1
    | none => batchStart
  else batchStart

/-- `anchorPreviousHeader`: zero at genesis, our pin when one exists, else adopt the peer's value. -/
def anchorPreviousHeader (m : CFHeadersMessage) (batchStart : UInt32) (headers : Std.HashMap String String) :
    Except FilterSyncError (Std.HashMap String String) :=
  if batchStart == 0 then
    if m.previousFilterHeader == zeroHash then .ok headers else .error (.filterHeaderMismatch batchStart)
  else match filterHeader? headers (batchStart - 1) with
    | some pinned => if m.previousFilterHeader == pinned then .ok headers else .error (.filterHeaderMismatch batchStart)
    | none => .ok (headers.insert (toString (batchStart - 1).toNat) (hex m.previousFilterHeader))

/-- The adopted cfheaders answer must cover the request exactly. -/
def checkCFHeadersCount (m : CFHeadersMessage) (start stop : UInt32) : Except FilterSyncError Unit :=
  let want := (stop - start).toNat + 1
  if m.filterHashes.size != want then .error (.badPeerResponse s!"cfheaders count {m.filterHashes.size} != {want}")
  else .ok ()

/-- Walks one cfheaders answer forward from its anchored previous header, pinning each height;
a height already pinned in `stored` must agree. -/
def walkFilterHeaders (m : CFHeadersMessage) (start : UInt32) (stored headers : Std.HashMap String String) :
    Except FilterSyncError (Std.HashMap String String) := do
  let mut hs ← anchorPreviousHeader m start headers
  let mut previous := m.previousFilterHeader
  for i in [0:m.filterHashes.size] do
    let height := start + i.toUInt32
    let header := sha256d (m.filterHashes[i]! ++ previous)
    if let some pinned := filterHeader? stored height then
      if !(pinned == header) then throw (.filterHeaderMismatch height)
    hs := hs.insert (toString height.toNat) (hex header)
    previous := header
  return hs

/-- One cfilter, verified: basic type, a block of this chunk not seen yet, and a filter reproducing
the pinned header chain. Returns its height and the updated `seen` set. -/
def verifiedFilter (m : CFilterMessage) (heightByHash : Std.HashMap ByteArray UInt32) (seen : Std.HashMap UInt32 Unit)
    (headers : Std.HashMap String String) : Except FilterSyncError (UInt32 × Std.HashMap UInt32 Unit) := do
  if m.filterType != basicFilterType then throw (.badPeerResponse s!"unexpected filter type {m.filterType}")
  let some height := heightByHash[m.blockHash]? | throw .unexpectedBlockHash
  if seen.contains height then throw .unexpectedBlockHash
  let seen := seen.insert height ()
  let previous := if height == 0 then zeroHash else (filterHeader? headers (height - 1)).getD zeroHash
  match filterHeader? headers height with
  | some pinned =>
    if sha256d (GCSFilter.filterHash m.filter ++ previous) == pinned then return (height, seen)
    else throw (.filterHeaderMismatch height)
  | none => throw (.filterHeaderMismatch height)

/-- Does a verified filter match the watch list? (Parse errors are the Wire/GCS refusals Swift throws.) -/
def filterMatches (m : CFilterMessage) (watchScripts : Array ByteArray) : Except String Bool := do
  if watchScripts.isEmpty then return false
  let (n, encoded) ← (m.parsedFilter).mapError (·.name)
  let f ← (GCSFilter.decode GCSFilter.defaultP GCSFilter.defaultM (m.blockHash.extract 0 16) n encoded).mapError (·.name)
  return f.containsAny watchScripts

/-- A fetched block, checked against the matched filter's block hash and its merkle root. -/
def verifiedBlock (b : Block) (blockHash : ByteArray) (height : UInt32) : Except FilterSyncError Block :=
  if !(b.hash == blockHash) then .error (.badPeerResponse s!"block hash mismatch at {height}")
  else if !b.hasValidMerkleRoot then .error (.badPeerResponse s!"merkle root mismatch at {height}")
  else .ok b

/-- The final guard: the highest checkpoint header pinned must equal the last one announced. -/
def finalCheckpointGuard (headers : Std.HashMap String String) (reference : CFCheckptMessage) (tip : UInt32) :
    Except FilterSyncError Unit :=
  let last := (tip / checkpointInterval) * checkpointInterval
  if last > 0 then
    match filterHeader? headers last, reference.filterHeaders.back? with
    | some pinned, some announced =>
      if pinned == announced then .ok ()
      else .error (.checkpointMismatch s!"checkpoint filter header at {last} disagrees with cfcheckpt")
    | _, _ => .ok ()
  else .ok ()

/-! ## The order of one `sync` run (each step is I/O or one of the functions above)

1. no connected peers → `peersCoolingDown n` / `noPeers`; 2. `PeerPool.syncHeaders` (HeaderChain.syncStep);
3. a fork → `onReorg minForkHeight`, then `rollBack`; 4. `validateAgainstTip`; tip < frontier → done;
5. `scanCeiling` (none → done); 6. cfcheckpt from `checkpointPeerCount` peers, `acceptCheckpoint`,
`strictMajority`, `sourceSpan` (disputed → cool all, `checkpointMismatch`), ban the minority, `reconcilePins`
(→ `onReorg`, `rollBack`); 7. per batch (`batches`): `requestStart`, cfheaders from `crossSourceSet`,
strict majority again (none → cool all, `checkpointMismatch`), `checkCFHeadersCount`, `walkFilterHeaders`,
`checkPinnedBoundaries`; then `chunks`: `getcfilters`, `verifiedFilter` each, `filterMatches` →
`getdata` + `verifiedBlock` + `onMatch`; all heights seen (else `badPeerResponse "missing cfilters"`);
persist `{ nextScanHeight := stop + 1, filterHeaders := prunedFilterHeaders … }`; 8. `finalCheckpointGuard`. -/

end FilterSync
end Winnow.Net
