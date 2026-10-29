import Std.Async
import Std.Time
import Lean.Data.Json
import Winnow.Net

/-! # Shared I/O plumbing for the I/O area

The Swift networking code is a set of actors whose methods `throw` many unrelated error types, and
whose callers dispatch on the type (`catch let e as PeerError where e.isTransport`). Here every I/O
operation runs in `NetM := EIO NetError`, one error type with a case per Swift error type, so the same
dispatch is a `match`. Lean `IO` errors (sockets, files, processes) are lifted into `NetError.other`.

Also here: the clocks (wall clock in seconds, monotonic milliseconds), one-shot timers on libuv
(`after`, no thread is held while waiting), atomic file writes (temp file + rename: Foundation's
`.atomic`; the iOS file-protection class has no Lean equivalent), size-bounded reads, and
`EventStream`, the stand-in for `AsyncStream`/`AsyncThrowingStream` with `bufferingNewest`. -/

namespace Winnow.IO
open Winnow.Net

/-! ## Errors -/

/-- `PeerError` (Network/Transport/PeerConnection.swift). -/
inductive PeerError where
  | timeout
  | notConnected
  | disconnected (reason : String)
  | handshakeFailed (reason : String)
  | missingCompactFilters (services : UInt64)
  | protocolViolation (reason : String)
  deriving Repr, BEq, Inhabited

namespace PeerError
def name : PeerError → String
  | .timeout => "timeout" | .notConnected => "notConnected" | .disconnected _ => "disconnected"
  | .handshakeFailed _ => "handshakeFailed" | .missingCompactFilters _ => "missingCompactFilters"
  | .protocolViolation _ => "protocolViolation"

def description : PeerError → String
  | .timeout => "The peer did not answer in time."
  | .notConnected => "The connection to the peer was not open."
  | .disconnected r => s!"The peer disconnected ({r})."
  | .handshakeFailed r => s!"The peer handshake failed ({r})."
  | .missingCompactFilters s => s!"The peer does not serve compact block filters (services {s})."
  | .protocolViolation r => s!"The peer violated the protocol ({r})."

/-- The connection failing rather than the peer being dishonest (cooldown, not ban). -/
def isTransport : PeerError → Bool
  | .timeout | .notConnected | .disconnected _ | .handshakeFailed _ => true
  | .missingCompactFilters _ | .protocolViolation _ => false
end PeerError

/-- `PeerPoolHeaderSyncError` (Network/Peers/PeerPool.swift). -/
inductive PoolError where
  | noPeers
  /-- the pool is in a relay-only session, which does not read the chain -/
  | relayOnly
  | exhausted (attempts : Nat) (lastError : String)
  | allPeersCoolingDown (cooling : Nat) (lastError : String)
  deriving Repr, BEq, Inhabited

namespace PoolError
def name : PoolError → String
  | .noPeers => "noPeers" | .relayOnly => "relayOnly" | .exhausted .. => "exhausted"
  | .allPeersCoolingDown .. => "allPeersCoolingDown"
def description : PoolError → String
  | .noPeers => "No Bitcoin peers are available for block-header sync."
  | .relayOnly =>
    "Winnow is keeping Bitcoin peers connected only to finish relaying a payment. Resume syncing to download block headers."
  | .exhausted a e =>
    s!"Winnow tried {a} Bitcoin peer{if a == 1 then "" else "s"}, but none supplied a usable block-header chain. Last error: {e}"
  | .allPeersCoolingDown c e =>
    s!"{c} Bitcoin peer{if c == 1 then " was" else "s were"} slow to answer and {if c == 1 then "is" else "are"} being rested briefly. Syncing will resume on its own. Last error: {e}"
end PoolError

def HeaderChainError.description : HeaderChainError → String
  | .doesNotConnect => "A peer sent block headers that do not connect to the known Bitcoin chain."
  | .startMismatch s w => s!"The stored chain starts at block {s} but this setting needs one starting at {w}."
  | .invalidTarget h => s!"A peer sent an invalid proof-of-work target at block {h}."
  | .targetAbovePowLimit h => s!"A peer sent an impossibly easy proof-of-work target at block {h}."
  | .insufficientProofOfWork h => s!"A peer sent a header without enough proof of work at block {h}."
  | .unexpectedDifficulty h => s!"A peer sent the wrong proof-of-work difficulty at block {h}."
  | .timestampTooFarInFuture h => s!"A peer sent a block header dated too far in the future at block {h}."
  | .reorgWithoutMoreWork => "A peer offered an older or weaker Bitcoin chain."
  | .storageCorrupt r => s!"The saved block-header data is damaged ({r})."
  | .storageUnavailable r => s!"Winnow could not read or save its local block-header data ({r})."
  | .badPeerResponse r => s!"A peer returned an invalid block-header response ({r})."

def FilterSyncError.description : FilterSyncError → String
  | .busy => "Finishing sync. Try loading the payment again in a moment."
  | .noPeers => "No Bitcoin peers are available for compact-filter synchronization."
  | .relayOnly =>
    "Winnow is keeping Bitcoin peers connected only to finish relaying a payment. Resume syncing to scan for new blocks."
  | .crossCheckUnavailable r =>
    s!"Winnow could not check this scan against connections from different sources ({r}). Nothing was scanned; it will try again as the peer pool changes."
  | .peersCoolingDown c =>
    s!"{c} Bitcoin peer{if c == 1 then " is" else "s are"} resting briefly after a slow reply. Scanning will resume on its own."
  | .checkpointMismatch r => s!"Bitcoin peers disagreed about compact-filter checkpoints ({r})."
  | .badPeerResponse r => s!"A Bitcoin peer returned invalid compact-filter data ({r})."
  | .filterHeaderMismatch h => s!"A compact filter did not match its authenticated header at block {h}."
  | .unexpectedBlockHash => "A Bitcoin peer returned a compact filter for a block Winnow did not request."

def FilterSyncStorageError.description : FilterSyncStorageError → String
  | .unreadable => "Winnow could not read its compact-filter progress file. Scanning is stopped so wallet history is not skipped."
  | .tooLarge m => s!"The compact-filter progress file is unexpectedly large (limit: {m} bytes). Scanning is stopped."
  | .damaged r => s!"The compact-filter progress file is damaged ({r}). Scanning is stopped; Winnow will not replace it automatically."
  | .writeFailed => "Winnow could not safely save compact-filter progress. The scan frontier was not advanced."
  | .frontierBeforeWallet s w => s!"Saved compact-filter progress starts at block {s}, behind the wallet's required block {w}. Scanning is stopped."
  | .frontierBeyondTip s t => s!"Saved compact-filter progress points to block {s}, beyond the validated chain tip {t}. Scanning is stopped."

/-- `TxBroadcasterError`. -/
inductive BroadcastError where
  | invalidFeeRate | stopped
  deriving Repr, BEq, Inhabited

/-- `TxBroadcasterStorageError`. -/
inductive BroadcastStorageError where
  | unreadable
  | tooLarge (maxBytes : Nat)
  | damaged (reason : String)
  | unsupportedVersion (version : Int)
  | writeFailed
  deriving Repr, BEq, Inhabited

def BroadcastStorageError.name : BroadcastStorageError → String
  | .unreadable => "unreadable" | .tooLarge _ => "tooLarge" | .damaged _ => "damaged"
  | .unsupportedVersion _ => "unsupportedVersion" | .writeFailed => "writeFailed"

def BroadcastStorageError.description : BroadcastStorageError → String
  | .unreadable => "Winnow could not read its pending-transaction file. Relay is stopped until local storage is available."
  | .tooLarge m => s!"The pending-transaction file is unexpectedly large (limit: {m} bytes). Relay is stopped to protect the wallet."
  | .damaged r => s!"The pending-transaction file is damaged ({r}). Relay is stopped; Winnow will not discard or replay its entries."
  | .unsupportedVersion v => s!"The pending-transaction file uses unsupported version {v}. Update Winnow before relaying transactions."
  | .writeFailed => "Winnow could not safely save pending transaction state. The relay change was not accepted."

/-- `RoutedHTTPClient.Failure` and `HTTPFailure` (Network/Transport/RoutedHTTPClient.swift); `transport`
is what URLSession itself throws (a `URLError`): the fetch failed below HTTP. -/
inductive HttpError where
  | unavailable | response | tooLarge | redirect
  | status (code : Nat)
  | transport (reason : String)
  | cancelled
  deriving Repr, BEq, Inhabited

def HttpError.name : HttpError → String
  | .unavailable => "unavailable" | .response => "response" | .tooLarge => "tooLarge" | .redirect => "redirect"
  | .status _ => "HTTPFailure" | .transport _ => "URLError" | .cancelled => "cancelled"

def HttpError.description : HttpError → String
  | .status c => s!"The server returned HTTP {c}."
  | .transport r => s!"The network request failed ({r})."
  | .cancelled => "The request was cancelled."
  | e => s!"Network request failed: {e.name}."

/-- One error type for everything the I/O layer throws, a case per Swift error type. -/
inductive NetError where
  | peer (e : PeerError)
  /-- The receive loop's framer refused the stream (Swift tears down with the `FramingError` itself). -/
  | framing (e : FramingError)
  | headers (e : HeaderChainError)
  | pool (e : PoolError)
  | filters (e : FilterSyncError)
  | filterStorage (e : FilterSyncStorageError)
  /-- a restore-only range scan's refusal (`RangeScanError`) -/
  | range (e : RangeScanError)
  | broadcast (e : BroadcastError)
  | broadcastStorage (e : BroadcastStorageError)
  | wire (e : WireError)
  | http (e : HttpError)
  | cancelled
  /-- A Lean `IO` error, or anything a caller-supplied callback threw. -/
  | other (message : String)
  deriving Repr, Inhabited

namespace NetError
/-- The Swift `kind(error)`: the enum case name. -/
def name : NetError → String
  | .peer e => e.name | .framing e => e.name | .headers e => e.name | .pool e => e.name
  | .filters e => e.name | .filterStorage e => e.name | .range e => e.name
  | .broadcast .invalidFeeRate => "invalidFeeRate" | .broadcast .stopped => "stopped"
  | .broadcastStorage e => e.name | .wire e => e.name | .http e => e.name
  | .cancelled => "cancelled" | .other _ => "other"

/-- `localizedDescription`. -/
def description : NetError → String
  | .peer e => e.description
  | .framing e =>
    -- `FramingError` is not a `LocalizedError`: Foundation's default text, with the case index as the code.
    let code := match e with | .badMagic => 0 | .badCommand => 1 | .payloadTooLarge _ => 2 | .checksumMismatch _ => 3
    s!"The operation couldn’t be completed. (WalletCore.FramingError error {code}.)"
  | .headers e => HeaderChainError.description e
  | .pool e => e.description
  | .filters e => FilterSyncError.description e
  | .filterStorage e => FilterSyncStorageError.description e
  | .range e => e.description
  | .broadcast .invalidFeeRate => "The transaction fee rate must be a positive, finite number within Bitcoin's monetary range."
  | .broadcast .stopped => "This transaction relay session has stopped. Reconnect before changing relay state."
  | .broadcastStorage e => e.description
  | .wire e =>
    let code := match e with | .truncated .. => 0 | .trailingBytes _ => 1 | .invalidVarInt => 2 | .malformed _ => 3
    s!"The operation couldn’t be completed. (WalletCore.WireError error {code}.)"
  | .http e => e.description
  | .cancelled => "The operation was cancelled."
  | .other m => m

def isTransportPeerError : NetError → Bool
  | .peer e => e.isTransport
  | _ => false
end NetError

instance : ToString NetError := ⟨fun e => s!"{e.name}: {e.description}"⟩

abbrev NetM := EIO NetError

instance : MonadLift IO NetM := ⟨IO.toEIO fun e => NetError.other (toString e)⟩

def NetM.toIO {α} (x : NetM α) : IO α := EIO.toIO (fun e => IO.userError (toString e)) x

/-- Runs and returns the outcome (never throws). -/
def NetM.attempt {α} (x : NetM α) : BaseIO (Except NetError α) := EIO.toBaseIO x

/-- Swift's `"\(error)"` for a `WireError` (the case and its payload). -/
def wireErrorText : WireError → String
  | .truncated e r => s!"truncated(expected: {e}, remaining: {r})"
  | .trailingBytes c => s!"trailingBytes({c})"
  | .invalidVarInt => "invalidVarInt"
  | .malformed r => s!"malformed(\"{r}\")"

/-! ## Clocks and timers -/

/-- Wall clock, whole seconds since 1970 (Swift `Date()`). -/
def wallSeconds : IO Int := do return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- Wall clock as a `Double` of seconds (`Date().timeIntervalSince1970`). -/
def wallTime : IO Float := do
  let ns := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val
  return Float.ofInt ns / 1e9

/-- Monotonic milliseconds (`ContinuousClock.now`). -/
def monoMs : IO Nat := IO.monoMsNow

/-- Runs `act` after `ms` milliseconds on a libuv timer: nothing blocks while it waits. -/
def after (ms : Nat) (act : IO Unit) : IO Unit := do
  let t ← (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat ms)).toIO
  discard <| IO.mapTask (t := t) fun _ => try act catch _ => pure ()

/-- Blocks this thread for `ms` (used only by long-lived dedicated loops). -/
def sleepMs (ms : Nat) : IO Unit := IO.sleep (min ms 0xFFFFFFFF).toUInt32

/-- A dedicated thread (the Swift `Task { … }` of a long-lived loop). -/
def spawn (act : IO Unit) : IO Unit :=
  discard <| IO.asTask (prio := .dedicated) (try act catch _ => pure ())

def randomU64 : IO UInt64 := do
  let b ← IO.getRandomBytes 8
  return readLE b 0 8

/-- Fisher–Yates with the system RNG (Swift's `shuffled()`). -/
def shuffle {α} (xs : Array α) : IO (Array α) := do
  let mut a := xs
  let mut i := a.size
  while i > 1 do
    let r ← randomU64
    let j := (r.toNat % i)
    i := i - 1
    a := a.swapIfInBounds i j
  return a

/-! ## Files -/

/-- Foundation's `Data.write(to:options: .atomic)`: a temporary file beside the target, then a rename. -/
def writeAtomic (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let r ← randomU64
  let tmp : System.FilePath := path.toString ++ s!".tmp-{r}"
  IO.FS.writeBinFile tmp bytes
  try IO.FS.rename tmp path
  catch e => (try IO.FS.removeFile tmp catch _ => pure ()); throw e

def fileExists (path : System.FilePath) : IO Bool := path.pathExists

/-- The file's size as the filesystem reports it, `none` when it cannot be read. -/
def fileSize? (path : System.FilePath) : IO (Option Nat) := do
  try return some (← path.metadata).byteSize.toNat catch _ => return none

/-- Reads at most `limit + 1` bytes (a caller compares against `limit`). -/
def readUpTo (path : System.FilePath) (limit : Nat) : IO ByteArray := do
  let h ← IO.FS.Handle.mk path .read
  let mut out := ByteArray.empty
  while out.size ≤ limit do
    let chunk ← h.read (min (limit + 1 - out.size) 1_048_576).toUSize
    if chunk.isEmpty then break
    out := out ++ chunk
  return out

/-! ## Multicast event streams -/

inductive StreamItem (α ε : Type) where
  | value (a : α)
  /-- The stream ended, with the error it was finished with. -/
  | finished (error : Option ε)

structure StreamState (α ε : Type) where
  queue : Array α := #[]
  done : Option (Option ε) := none
  waiter : Option (IO.Promise Unit) := none

/-- `AsyncThrowingStream(bufferingPolicy: .bufferingNewest(capacity))` with one consumer:
`yield` past the capacity drops the oldest buffered element. -/
structure EventStream (α ε : Type) where
  id : Nat
  capacity : Nat
  state : IO.Ref (StreamState α ε)
  /-- Run once when the consumer cancels (`onTermination`). -/
  onCancel : IO.Ref (IO Unit)

namespace EventStream
variable {α ε : Type}

def new (id capacity : Nat) : IO (EventStream α ε) := do
  return { id, capacity, state := ← IO.mkRef {}, onCancel := ← IO.mkRef (pure ()) }

private def wake (w : Option (IO.Promise Unit)) : BaseIO Unit :=
  match w with | some p => p.resolve () | none => pure ()

def yield (s : EventStream α ε) (a : α) : BaseIO Unit := do
  let w ← s.state.modifyGet fun st =>
    if st.done.isSome then (none, st)
    else
      let q := st.queue.push a
      let q := if q.size > s.capacity then q.extract (q.size - s.capacity) q.size else q
      (st.waiter, { st with queue := q, waiter := none })
  wake w

def finish (s : EventStream α ε) (error : Option ε := none) : BaseIO Unit := do
  let w ← s.state.modifyGet fun st =>
    if st.done.isSome then (none, st) else (st.waiter, { st with done := some error, waiter := none })
  wake w

/-- The next element, or the end of the stream (after every buffered element). Blocks this thread. -/
partial def next (s : EventStream α ε) : IO (StreamItem α ε) := do
  let p ← IO.Promise.new
  let r ← s.state.modifyGet fun st =>
    if h : 0 < st.queue.size then (some (StreamItem.value st.queue[0]), { st with queue := st.queue.extract 1 st.queue.size })
    else match st.done with
      | some e => (some (.finished e), st)
      | none => (none, { st with waiter := some p })
  match r with
  | some item => return item
  | none =>
    discard <| IO.wait p.result?
    s.next

/-- The consumer stops listening: the stream ends and the producer forgets it. -/
def cancel (s : EventStream α ε) : IO Unit := do
  s.finish none
  let act ← s.onCancel.modifyGet fun a => (a, pure ())
  act
end EventStream

/-! ## Small JSON helpers (Foundation's `JSONEncoder` forms) -/

/-- A JSON string as `JSONEncoder` writes it (slashes escaped, controls as `\uXXXX`). -/
def jsonString (s : String) : String := Id.run do
  let hexd := "0123456789abcdef".toList.toArray
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '/' => "\\/"
      | '\x08' => "\\b" | '\x0c' => "\\f" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
      | c => if c.toNat < 0x20 then
               "\\u00" ++ String.singleton hexd[c.toNat / 16]! ++ String.singleton hexd[c.toNat % 16]!
             else String.singleton c
  return out ++ "\""

end Winnow.IO
