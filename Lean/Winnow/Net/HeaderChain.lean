import Winnow.Net.UInt256
import Winnow.Net.Params
import Winnow.Net.Header
import Std.Data.HashMap

/-! # The header chain (`Network/Headers/HeaderChain.swift`)

The Swift `HeaderChain` is an actor owning a file. Here it is a value: `connect` returns the next chain,
what the batch did, and the storage writes the I/O layer must apply in order (`StorageWrite`), which
`StorageWrite.apply` also simulates on the file's bytes. The device clock (`now`) is an argument.

Validated per header, as in Swift: linkage, compact bits → target ≤ powLimit, SHA256d(header) ≤ target,
the timestamp at most two hours past `now`, and the required difficulty (every
`difficultyAdjustmentInterval` blocks; bounded to ≤ 4× easier when a checkpoint hides the period start).
Fork choice is cumulative work; a replacement branch must carry strictly more.

Left for the I/O layer (`sync(using:)`): the getheaders loop against a peer (described at `syncStep`),
reading the file (size-capped at `maximumHeaderFileBytes` before and after reading) and writing it
(atomic rewrite, or payload-then-count append with `synchronize()` between). -/

namespace Winnow.Net

inductive HeaderChainError where
  | doesNotConnect
  | invalidTarget (height : UInt32)
  | targetAbovePowLimit (height : UInt32)
  | insufficientProofOfWork (height : UInt32)
  | unexpectedDifficulty (height : UInt32)
  | timestampTooFarInFuture (height : UInt32)
  | reorgWithoutMoreWork
  | storageCorrupt (reason : String)
  | storageUnavailable (reason : String)
  | badPeerResponse (reason : String)
  | startMismatch (stored wanted : UInt32)
  deriving Repr, BEq, Inhabited

def HeaderChainError.name : HeaderChainError → String
  | .doesNotConnect => "doesNotConnect"
  | .invalidTarget _ => "invalidTarget"
  | .targetAbovePowLimit _ => "targetAbovePowLimit"
  | .insufficientProofOfWork _ => "insufficientProofOfWork"
  | .unexpectedDifficulty _ => "unexpectedDifficulty"
  | .timestampTooFarInFuture _ => "timestampTooFarInFuture"
  | .reorgWithoutMoreWork => "reorgWithoutMoreWork"
  | .storageCorrupt _ => "storageCorrupt"
  | .storageUnavailable _ => "storageUnavailable"
  | .badPeerResponse _ => "badPeerResponse"
  | .startMismatch .. => "startMismatch"

/-- Where a fresh chain begins. -/
inductive ChainStart where
  | genesis | checkpoint
  deriving BEq, Inhabited, Repr

/-- `Start.forWallet`: the checkpoint is a speed decision, never a correctness one — a wallet whose
history begins below it starts at genesis. -/
def ChainStart.forWallet (birthday : Option UInt32) (checkpoint : Option Checkpoint) (verifyFromGenesis : Bool) : ChainStart :=
  if verifyFromGenesis then .genesis
  else match checkpoint with
    | none => .genesis
    | some c => match birthday with
      | none => .checkpoint
      | some b => if b ≥ c.height then .checkpoint else .genesis

/-- What one batch of headers did. -/
structure ConnectOutcome where
  appended : Nat
  forkHeight : Option UInt32 := none
  disconnectedHeaders : Nat := 0
  deriving BEq, Inhabited, Repr

/-- What a whole sync did (the lowest fork height of any swap). -/
structure SyncOutcome where
  connected : Nat := 0
  minForkHeight : Option UInt32 := none
  disconnectedHeaders : Nat := 0
  staleSiblings : Nat := 0
  deriving BEq, Inhabited, Repr

def SyncOutcome.absorb (o : SyncOutcome) (b : ConnectOutcome) : SyncOutcome :=
  let o := { o with connected := o.connected + b.appended, disconnectedHeaders := o.disconnectedHeaders + b.disconnectedHeaders }
  match b.forkHeight with
  | none => o
  | some f => { o with minForkHeight := some (match o.minForkHeight with | some m => min m f | none => f) }

/-- A write to the header file, in the order the Swift code performs them. -/
inductive StorageWrite where
  /-- Atomic rewrite of the whole file. -/
  | replace (bytes : ByteArray)
  /-- Append: write `payload` at `offset`, truncate (or zero-extend) to `length`, then write `count` at `countOffset`. -/
  | append (offset : Nat) (payload : ByteArray) (length : Nat) (countOffset : Nat) (count : ByteArray)
  deriving Inhabited

/-- `bytes` written at `offset` (a write past the end zero-fills the gap, as a seek-and-write does). -/
def writeAt (file : ByteArray) (offset : Nat) (bytes : ByteArray) : ByteArray := Id.run do
  let mut f := file
  while f.size < offset do f := f.push 0
  let head := f.extract 0 offset
  let tail := if offset + bytes.size < f.size then f.extract (offset + bytes.size) f.size else .empty
  return head ++ bytes ++ tail

def StorageWrite.apply (file : Option ByteArray) : StorageWrite → ByteArray
  | .replace b => b
  | .append off payload len cOff count =>
    let f := writeAt (file.getD .empty) off payload
    let f := if f.size ≥ len then f.extract 0 len else writeAt f len .empty
    writeAt f cOff count

structure HeaderChain where
  params : NetworkParams
  /-- Main chain; element 0 is at `baseHeight`. -/
  headers : Array BlockHeader
  /-- Cumulative work aligned with `headers` (element 0 carries everything up to it). -/
  chainwork : Array UInt256
  baseHeight : UInt32
  /-- Whether a storage file backs the chain (Swift's `storageURL != nil`). -/
  storage : Bool := false
  /-- Headers the file currently claims. -/
  persistedCount : Nat := 0
  deriving Inhabited

namespace HeaderChain

def maxHeadersPerRequest : Nat := 2_000
def maximumFutureDrift : UInt32 := 2 * 60 * 60
def maxReplayedBatches : Nat := 4
def maximumHeaderFileBytes : Nat := 256 * 1_024 * 1_024
def formatMarker : UInt32 := 0xFFFFFFFF
def formatVersion : UInt32 := 1

def genesisHeader (p : NetworkParams) : BlockHeader :=
  BlockHeader.mk' 1 (ByteArray.mk (Array.replicate 32 0)) p.genesisMerkleRoot p.genesisTime p.genesisBits p.genesisNonce

def tip (c : HeaderChain) : BlockHeader := c.headers.back!
def tipHash (c : HeaderChain) : ByteArray := c.tip.hash
def height (c : HeaderChain) : UInt32 := c.baseHeight + (c.headers.size - 1).toUInt32
def startHeight (c : HeaderChain) : UInt32 := c.baseHeight
/-- Cumulative chainwork at the tip, big-endian. -/
def tipWork (c : HeaderChain) : ByteArray := c.chainwork.back!.bigEndianData

def header? (c : HeaderChain) (height : UInt32) : Option BlockHeader :=
  if height < c.baseHeight then none else c.headers[(height - c.baseHeight).toNat]?

def blockHash? (c : HeaderChain) (height : UInt32) : Option ByteArray := (c.header? height).map (·.hash)

/-- getheaders locator: ten heights step 1, then doubling steps, ending at the first header held. -/
def blockLocator (c : HeaderChain) : Array ByteArray := Id.run do
  let mut locator : Array ByteArray := #[]
  let mut step := 1
  let mut index := c.headers.size - 1
  while index > 0 do
    locator := locator.push c.headers[index]!.hash
    if locator.size ≥ 10 then step := step * 2
    index := if index ≥ step then index - step else 0
  return locator.push c.headers[0]!.hash

/-! ## Proof-of-work rules -/

/-- Target and block work for `bits` (they depend on nothing else). -/
def targetAndWork (bits : UInt32) (p : NetworkParams) (height : UInt32) : Except HeaderChainError (UInt256 × UInt256) := do
  let some target := UInt256.target bits | throw (.invalidTarget height)
  if !(target ≤ UInt256.ofLittleEndian p.powLimit) then throw (.targetAbovePowLimit height)
  let some work := UInt256.blockWork target | throw (.invalidTarget height)
  return (target, work)

/-- Validates one header's proof of work; returns its work. -/
def checkedWork (h : BlockHeader) (p : NetworkParams) (height : UInt32) : Except HeaderChainError UInt256 := do
  let (target, work) ← targetAndWork h.bits p height
  if !(UInt256.ofLittleEndian h.hash ≤ target) then throw (.insufficientProofOfWork height)
  return work

/-- Core's CalculateNextWorkRequired (regtest: fixed). `none`: the period's first header is unavailable. -/
def expectedBits (height : UInt32) (previous : BlockHeader) (periodFirst : Option BlockHeader) (p : NetworkParams) :
    Except HeaderChainError (Option UInt32) := do
  if p.noRetargeting || height % p.difficultyAdjustmentInterval != 0 then return some previous.bits
  let some first := periodFirst | return none
  let some target := UInt256.target previous.bits | throw (.invalidTarget (height - 1))
  let timespan : Int := p.powTargetTimespan.toNat
  let raw : Int := (previous.time.toNat : Int) - (first.time.toNat : Int)
  let elapsed := Min.min (Max.max raw (timespan / 4)) (timespan * 4)
  let adjusted := (target.multiplied elapsed.toNat.toUInt32).quotientAndRemainder ⟨timespan.toNat⟩ |>.1
  return some (min adjusted (UInt256.ofLittleEndian p.powLimit)).compact

/-- The one adjustment a mid-period checkpoint cannot verify exactly: at most 4× easier, never past powLimit. -/
def requireBoundedAdjustment (h previous : BlockHeader) (p : NetworkParams) (height : UInt32) : Except HeaderChainError Unit := do
  let (some target, some previousTarget) := (UInt256.target h.bits, UInt256.target previous.bits)
    | throw (.invalidTarget height)
  let ceiling := min (previousTarget.multiplied 4) (UInt256.ofLittleEndian p.powLimit)
  if !(target ≤ ceiling) then throw (.unexpectedDifficulty height)

/-- The required difficulty; `preceding i` is the header at index `i` of the branch being checked. -/
def requireDifficulty (h : BlockHeader) (height baseHeight : UInt32) (p : NetworkParams)
    (preceding : Nat → BlockHeader) : Except HeaderChainError Unit := do
  if height ≤ baseHeight then return
  let interval := p.difficultyAdjustmentInterval
  let firstIndex : Int := (height.toNat : Int) - interval.toNat - baseHeight.toNat
  let first := if height % interval == 0 && firstIndex ≥ 0 then some (preceding firstIndex.toNat) else none
  let previous := preceding ((height - baseHeight).toNat - 1)
  match ← expectedBits height previous first p with
  | some expected => if h.bits != expected then throw (.unexpectedDifficulty height)
  | none => requireBoundedAdjustment h previous p height

/-- Core's future-drift rule (the limit wraps like Swift's `&+`). -/
def requireTimestamp (h : BlockHeader) (height now : UInt32) : Except HeaderChainError Unit :=
  if h.time > now + maximumFutureDrift then .error (.timestampTooFarInFuture height) else .ok ()

/-! ## Persistence (file layout) -/

/-- Bytes before the first header: a bare count at genesis, marker + version + base + work + count otherwise. -/
def prefixSize (c : HeaderChain) : Nat := if c.baseHeight == 0 then 4 else 4 + 4 + 4 + 32 + 4
def countOffset (c : HeaderChain) : Nat := if c.baseHeight == 0 then 0 else 4 + 4 + 4 + 32

def fileBytes (c : HeaderChain) : ByteArray := Id.run do
  let mut data :=
    if c.baseHeight == 0 then u32LE c.headers.size.toUInt32
    else u32LE formatMarker ++ u32LE formatVersion ++ u32LE c.baseHeight ++ c.chainwork[0]!.bigEndianData ++
      u32LE c.headers.size.toUInt32
  for h in c.headers do data := data ++ h.serialized
  return data

def persist (c : HeaderChain) : HeaderChain × Array StorageWrite :=
  if !c.storage then (c, #[]) else ({ c with persistedCount := c.headers.size }, #[.replace c.fileBytes])

/-- Writes only the headers appended since the last save (payload first, then the count); a full
rewrite when the file is not in the state that assumes. -/
def persistAppended (c : HeaderChain) (oldCount : Nat) : HeaderChain × Array StorageWrite :=
  if !c.storage then (c, #[])
  else if !(oldCount == c.persistedCount && oldCount > 0) then c.persist
  else
    let payload := (c.headers.extract oldCount c.headers.size).foldl (fun d h => d ++ h.serialized) .empty
    ({ c with persistedCount := c.headers.size },
     #[.append (c.prefixSize + oldCount * 80) payload (c.prefixSize + c.headers.size * 80) c.countOffset
        (u32LE c.headers.size.toUInt32)])

/-- The file's prefix: (baseHeight, baseWork, count, prefix size). -/
def parsePrefix (data : ByteArray) : Except HeaderChainError (UInt32 × UInt256 × UInt32 × Nat) := do
  if data.size < 4 then throw (.storageCorrupt "bad length")
  let first := (readLE data 0 4).toUInt32
  if first != formatMarker then return (0, UInt256.zero, first, 4)
  if data.size < 8 || (readLE data 4 4).toUInt32 != formatVersion then
    throw (.storageCorrupt "unsupported header-file version")
  if data.size < 48 then throw (.storageCorrupt "truncated header-file prefix")
  return ((readLE data 8 4).toUInt32, UInt256.ofBigEndian (data.extract 12 44), (readLE data 44 4).toUInt32, 48)

/-- Reads a header file: every header is proof-of-work, lineage and difficulty checked; a file longer
than its count (an interrupted append) is read up to the count. -/
def load (data : ByteArray) (p : NetworkParams) : Except HeaderChainError (Array BlockHeader × Array UInt256 × UInt32) := do
  if data.size > maximumHeaderFileBytes then
    throw (.storageCorrupt s!"header file is {data.size} bytes, above the {maximumHeaderFileBytes}-byte limit")
  let (baseHeight, baseWork, count, pre) ← parsePrefix data
  if data.size < pre + count.toNat * 80 then throw (.storageCorrupt "bad length")
  let genesis := genesisHeader p
  let mut loaded : Array BlockHeader := Array.mkEmpty count.toNat
  let mut works : Array UInt256 := Array.mkEmpty count.toNat
  let mut work := UInt256.zero
  let mut cache : Std.HashMap UInt32 (UInt256 × UInt256) := {}
  for index in [0:count.toNat] do
    let off := pre + index * 80
    let h := BlockHeader.mk' (readLE data off 4).toUInt32.toInt32 (data.extract (off + 4) (off + 36))
      (data.extract (off + 36) (off + 68)) (readLE data (off + 68) 4).toUInt32 (readLE data (off + 72) 4).toUInt32
      (readLE data (off + 76) 4).toUInt32
    let height := baseHeight + index.toUInt32
    let (target, blockWork) ← match cache[h.bits]? with
      | some tw => pure tw
      | none => targetAndWork h.bits p height
    cache := cache.insert h.bits (target, blockWork)
    if !(UInt256.ofLittleEndian h.hash ≤ target) then throw (.insufficientProofOfWork height)
    work := if index == 0 && baseHeight > 0 then baseWork else work + blockWork
    if baseHeight == 0 && index == 0 && !(h == genesis) then throw (.storageCorrupt "genesis mismatch")
    if index > 0 && !(h.previousHash == loaded.back!.hash) then
      throw (.storageCorrupt s!"broken linkage at {height}")
    let soFar := loaded
    requireDifficulty h height baseHeight p fun i => soFar[i]!
    loaded := loaded.push h
    works := works.push work
  return (loaded, works, baseHeight)

/-- A stored chain answers one question — "starting where?"; a genesis-rooted file is always accepted. -/
def checkStoredStart (storedBase : UInt32) (headers : Array BlockHeader) (wanted : Option Checkpoint) :
    Except HeaderChainError Unit := do
  if storedBase == 0 then return
  let some w := wanted | throw (.startMismatch storedBase 0)
  if !(storedBase == w.height && (headers[0]?.map (·.serialized == w.header) |>.getD false)) then
    throw (.startMismatch storedBase w.height)

/-- `HeaderChain.init`: from the stored file's bytes when one exists, else the checkpoint or genesis.
(A stored file of zero headers is refused here; Swift accepts it and then traps on the first `tip`.) -/
def create (p : NetworkParams) (stored : Option ByteArray) (start : ChainStart := .genesis) (storage : Bool := stored.isSome) :
    Except HeaderChainError HeaderChain := do
  let checkpoint := if start == .checkpoint then p.checkpoint else none
  match stored with
  | some data =>
    let (headers, chainwork, baseHeight) ← load data p
    checkStoredStart baseHeight headers checkpoint
    if headers.isEmpty then throw (.storageCorrupt "empty header file")
    return { params := p, headers, chainwork, baseHeight, storage, persistedCount := headers.size }
  | none =>
    match checkpoint with
    | some c =>
      let header ← match BlockHeader.decode c.header with
        | .ok h => pure h
        | .error _ => throw (.storageCorrupt "checkpoint header")
      let _ ← checkedWork header p c.height
      return { params := p, headers := #[header], chainwork := #[UInt256.ofBigEndian c.chainwork],
               baseHeight := c.height, storage }
    | none =>
      let genesis := genesisHeader p
      let work ← checkedWork genesis p 0
      return { params := p, headers := #[genesis], chainwork := #[work], baseHeight := 0, storage }

/-! ## Connecting headers -/

/-- Index of the header with this hash: the tip, or found through its child's `previousHash`. -/
def indexOf? (c : HeaderChain) (hash : ByteArray) : Option Nat := Id.run do
  if hash == c.tipHash then return some (c.headers.size - 1)
  let mut i := c.headers.size
  while i > 0 do
    i := i - 1
    if c.headers[i]!.previousHash == hash then
      return if i > 0 then some (i - 1) else none
  return none

def appendToTip (c : HeaderChain) (newHeaders : Array BlockHeader) (now : UInt32) :
    Except HeaderChainError (HeaderChain × ConnectOutcome × Array StorageWrite) := do
  let mut previous := c.tip
  let mut work := c.chainwork.back!
  let mut appended : Array BlockHeader := #[]
  let mut appendedWork : Array UInt256 := #[]
  for h in newHeaders do
    let height := c.baseHeight + (c.headers.size + appended.size).toUInt32
    if !(h.previousHash == previous.hash) then throw .doesNotConnect
    work := work + (← checkedWork h c.params height)
    requireTimestamp h height now
    let soFar := appended
    requireDifficulty h height c.baseHeight c.params fun i =>
      if i < c.headers.size then c.headers[i]! else soFar[i - c.headers.size]!
    appended := appended.push h
    appendedWork := appendedWork.push work
    previous := h
  let c' := { c with headers := c.headers ++ appended, chainwork := c.chainwork ++ appendedWork }
  let (c'', writes) := c'.persistAppended (c'.headers.size - appended.size)
  return (c'', { appended := newHeaders.size }, writes)

def replaceBranch (c : HeaderChain) (newHeaders : Array BlockHeader) (forkHeight now : UInt32) :
    Except HeaderChainError (HeaderChain × ConnectOutcome × Array StorageWrite) := do
  let forkIndex := (forkHeight - c.baseHeight).toNat
  let mut staged := c.headers.extract 0 (forkIndex + 1)
  let mut stagedWork := c.chainwork.extract 0 (forkIndex + 1)
  for h in newHeaders do
    let height := c.baseHeight + staged.size.toUInt32
    let previous := staged.back!
    if !(h.previousHash == previous.hash) then throw .doesNotConnect
    let work ← checkedWork h c.params height
    requireTimestamp h height now
    let soFar := staged
    requireDifficulty h height c.baseHeight c.params fun i => soFar[i]!
    staged := staged.push h
    stagedWork := stagedWork.push (stagedWork.back! + work)
  if forkIndex < c.headers.size - 1 && stagedWork.back! ≤ c.chainwork.back! then throw .reorgWithoutMoreWork
  let disconnected := c.headers.size - 1 - forkIndex
  let (c', writes) := { c with headers := staged, chainwork := stagedWork }.persist
  return (c', { appended := newHeaders.size, forkHeight := if disconnected > 0 then some forkHeight else none,
                disconnectedHeaders := disconnected }, writes)

/-- Connects a batch from a peer: it must build on a header already held (an earlier one means a
reorg, accepted only with strictly more work). Known headers at the front are skipped. -/
def connect (c : HeaderChain) (newHeaders : Array BlockHeader) (now : UInt32) :
    Except HeaderChainError (HeaderChain × ConnectOutcome × Array StorageWrite) := do
  let some first := newHeaders[0]? | return (c, { appended := 0 }, #[])
  let some parent := c.indexOf? first.previousHash | throw .doesNotConnect
  let mut nextIndex := parent + 1
  let mut skip := 0
  while skip < newHeaders.size && nextIndex < c.headers.size && newHeaders[skip]! == c.headers[nextIndex]! do
    skip := skip + 1
    nextIndex := nextIndex + 1
  if skip == newHeaders.size then return (c, { appended := 0 }, #[])
  let rest := newHeaders.extract skip newHeaders.size
  if nextIndex == c.headers.size then c.appendToTip rest now
  else c.replaceBranch rest (c.baseHeight + (nextIndex - 1).toUInt32) now

/-- One reply of the sync loop (`connectSyncReply`): connect it, and say whether it answered nothing
(only known headers, a racing one-header announcement that does not connect — within the replay
budget — or a losing sibling of the tip). -/
def connectSyncReply (c : HeaderChain) (batch : Array BlockHeader) (replays : Nat) (outcome : SyncOutcome) (now : UInt32) :
    Except HeaderChainError (HeaderChain × SyncOutcome × Bool × Array StorageWrite) :=
  match c.connect batch now with
  | .ok (c', connected, writes) => .ok (c', outcome.absorb connected, connected.appended == 0, writes)
  | .error .doesNotConnect =>
    if batch.size == 1 then
      if replays < maxReplayedBatches then .ok (c, outcome, true, #[]) else .error .doesNotConnect
    else .error .doesNotConnect
  | .error .reorgWithoutMoreWork =>
    if batch.size == 1 && batch[0]!.previousHash == c.tip.previousHash then
      .ok (c, { outcome with staleSiblings := outcome.staleSiblings + 1 }, true, #[])
    else .error .reorgWithoutMoreWork
  | .error e => .error e

/-- What the sync loop does with a reply (`sync(using:timeout:)`, whose requests are I/O): send
`getheaders(locator: blockLocator)`, expect `headers` (anything else: `badPeerResponse "expected headers"`);
an empty batch ends the sync; a reply that answered nothing counts a replay and asks again until more
than `maxReplayedBatches`; a batch shorter than `maxHeadersPerRequest` ends it. `none`: continue. -/
def syncStep (c : HeaderChain) (batch : Array BlockHeader) (replays : Nat) (outcome : SyncOutcome) (now : UInt32) :
    Except HeaderChainError (HeaderChain × SyncOutcome × Nat × Bool × Array StorageWrite) := do
  if batch.isEmpty then return (c, outcome, replays, true, #[])
  let (c', o, answeredNothing, writes) ← c.connectSyncReply batch replays outcome now
  if answeredNothing then
    let r := replays + 1
    return (c', o, r, r > maxReplayedBatches, writes)
  return (c', o, replays, batch.size < maxHeadersPerRequest, writes)

end HeaderChain
end Winnow.Net
