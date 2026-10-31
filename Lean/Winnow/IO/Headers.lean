import Winnow.IO.Transport

/-! # The header chain's I/O half (`Network/Headers/HeaderChain.swift`: `init` reading the file, the
writes, and `sync(using:timeout:)`)

The chain itself is the Net area's pure `HeaderChain` value; `HeaderStore` holds it under a mutex
(the actor), with the device clock and the storage path. Every connect runs the pure step and then
applies its `StorageWrite`s in order, inside the lock, as the Swift actor does synchronously:

* `replace` — an atomic rewrite (temporary file + rename).
* `append` — when the file is exactly as long as the append offset, the payload is appended and then
  the prefix (whose last field is the count) is rewritten in place: payload first, count second, so a
  crash leaves a stale count over an ignored tail. Lean's file API has no `seek` and no `fsync`: the
  count is rewritten by writing the whole fixed-size prefix from offset 0, each step ends with a
  `flush` (not `synchronize()`), and a file of any other length (an interrupted earlier append) is
  rewritten whole, which is the same bytes Swift's seek-write-truncate produces.

`sync` is Swift's loop: `getheaders(blockLocator)` → `headers` (anything else: `badPeerResponse
"expected headers"`), connected through `HeaderChain.syncStep` until an empty or short batch, or more
than four replies that answered nothing. A failed write keeps the connected headers in memory (as the
Swift actor does, having mutated before persisting) and throws `storageUnavailable`. -/

namespace Winnow.IO
open Winnow.Net

structure HeaderStore where
  params : NetworkParams
  path : Option System.FilePath
  /-- The device clock in seconds (injectable, as Swift's `now`). -/
  now : IO UInt32
  chain : Std.Mutex HeaderChain

namespace HeaderStore

def defaultNow : IO UInt32 := do
  let s ← wallSeconds
  return if s < 0 then 0 else if s > 0xFFFFFFFF then 0xFFFFFFFF else s.toNat.toUInt32

private def readBounded (p : System.FilePath) : NetM ByteArray := do
  let limit := HeaderChain.maximumHeaderFileBytes
  if let some size ← fileSize? p then
    if size > limit then
      throw (.headers (.storageCorrupt s!"header file is {size} bytes, above the {limit}-byte limit"))
  let data ← match ← (IO.FS.readBinFile p).toBaseIO with
    | .ok d => pure d
    | .error e => throw (.headers (.storageUnavailable s!"could not read the header file: {e}"))
  if data.size > limit then
    throw (.headers (.storageCorrupt s!"header file is {data.size} bytes, above the {limit}-byte limit"))
  return data

/-- `HeaderChain(params:storageURL:start:now:)`. -/
def «open» (params : NetworkParams) (path : Option System.FilePath := none) (start : ChainStart := .genesis)
    (now : IO UInt32 := defaultNow) : NetM HeaderStore := do
  let stored ← match path with
    | some p => if ← fileExists p then some <$> readBounded p else pure none
    | none => pure none
  match HeaderChain.create params stored start (storage := path.isSome) with
  | .ok c => return { params, path, now, chain := ← Std.Mutex.new c }
  | .error e => throw (.headers e)

def snapshot (s : HeaderStore) : BaseIO HeaderChain := s.chain.atomically (m := BaseIO) get

def height (s : HeaderStore) : BaseIO UInt32 := return (← s.snapshot).height
def tipHash (s : HeaderStore) : BaseIO ByteArray := return (← s.snapshot).tipHash
def startHeight (s : HeaderStore) : BaseIO UInt32 := return (← s.snapshot).startHeight
def blockHash (s : HeaderStore) (height : UInt32) : BaseIO (Option ByteArray) := return (← s.snapshot).blockHash? height
def header (s : HeaderStore) (height : UInt32) : BaseIO (Option BlockHeader) := return (← s.snapshot).header? height
def blockLocator (s : HeaderStore) : BaseIO (Array ByteArray) := return (← s.snapshot).blockLocator
def tipWork (s : HeaderStore) : BaseIO ByteArray := return (← s.snapshot).tipWork

/-- The prefix bytes of the file (`fileBytes` up to the first header). -/
def prefixBytes (c : HeaderChain) : ByteArray :=
  if c.baseHeight == 0 then u32LE c.headers.size.toUInt32
  else u32LE HeaderChain.formatMarker ++ u32LE HeaderChain.formatVersion ++ u32LE c.baseHeight ++
    c.chainwork[0]!.bigEndianData ++ u32LE c.headers.size.toUInt32

private def applyWrite (p : System.FilePath) (c : HeaderChain) : StorageWrite → NetM Unit
  | .replace bytes => do
    match ← (writeAtomic p bytes).toBaseIO with
    | .ok () => pure ()
    | .error e => throw (.headers (.storageUnavailable s!"could not save the header file: {e}"))
  | .append offset payload _length _countOffset _count => do
    let size ← fileSize? p
    if size != some offset then
      match ← (writeAtomic p c.fileBytes).toBaseIO with
      | .ok () => pure ()
      | .error e => throw (.headers (.storageUnavailable s!"could not save the header file: {e}"))
    else
      let r ← (do
        let h ← IO.FS.Handle.mk p .append
        h.write payload
        h.flush
        let h2 ← IO.FS.Handle.mk p .readWrite
        h2.write (prefixBytes c)
        h2.flush : IO Unit).toBaseIO
      match r with
      | .ok () => pure ()
      | .error e => throw (.headers (.storageUnavailable s!"could not append to the header file: {e}"))

/-- Applies a pure step's chain and writes under the lock. -/
private def commit (s : HeaderStore) (old new : HeaderChain) (writes : Array StorageWrite) : NetM Unit := do
  match s.path with
  | none => s.chain.atomically (m := BaseIO) (set new)
  | some p =>
    try
      for w in writes do applyWrite p new w
      s.chain.atomically (m := BaseIO) (set new)
    catch e =>
      s.chain.atomically (m := BaseIO) (set { new with persistedCount := old.persistedCount })
      throw e

/-- `connect(_:)`: one batch from a peer. -/
def connect (s : HeaderStore) (batch : Array BlockHeader) : NetM ConnectOutcome := do
  let now ← s.now
  -- The whole step runs under the chain's lock, as one actor call.
  let lockOut ← s.chain.atomically (m := BaseIO) (do
    let c ← get
    match c.connect batch now with
    | .error e => return Sum.inl e
    | .ok (c', o, w) => return .inr (c, c', o, w))
  match lockOut with
  | .inl e => throw (.headers e)
  | .inr (c, c', o, w) => s.commit c c' w; return o

/-- Syncs from the current tip to the peer's best tip via getheaders. -/
def sync (s : HeaderStore) (peer : PeerConnection) (timeoutMs : Nat := 30_000) : NetM SyncOutcome := do
  let mut outcome : SyncOutcome := {}
  let mut replays := 0
  while true do
    let locator ← s.blockLocator
    let message ← peer.request (.getheaders { version := PeerConnection.protocolVersion, locatorHashes := locator })
      #["headers"] timeoutMs
    let .headers batch := message | throw (.headers (.badPeerResponse "expected headers"))
    let now ← s.now
    let stepped ← s.chain.atomically (m := BaseIO) (do
      let c ← get
      match c.syncStep batch replays outcome now with
      | .error e => return Sum.inl e
      | .ok r => return .inr (c, r))
    match stepped with
    | .inl e => throw (.headers e)
    | .inr (old, (c', o, r, done, writes)) =>
      s.commit old c' writes
      outcome := o
      replays := r
      if done then return outcome
  return outcome

end HeaderStore
end Winnow.IO
