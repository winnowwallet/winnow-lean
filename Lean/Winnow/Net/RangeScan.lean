import Winnow.Net.FilterSync
import Winnow.Crypto

/-! # Restore-only range scans: the pure logic (`Network/Filters/RangeScan.swift`, upstream #226)

A restore that has a mnemonic and no wallet file has no birthday to scan forward from, so the caller may
choose a bounded back-scan of `[from, to]` for a set of scripts, run it, derive more scripts from what it
found, and scan again until a pass finds nothing new. Ordinary sync stays forward-only; this never reads or
writes the forward frontier. Every dimension is capped (`RangeScanLimits`, clamped to ceilings on the way
in). The record (`RangeScanProgress`) is its own file, marked `"range"` so the forward loader refuses it
and this loader refuses a forward file.

Here: the errors, the limits, the record (JSON, validation, resume or restart), and the checks made before
any peer is asked. The batch loop is `FilterSyncIO.scanRange`. Durations are milliseconds; Swift prints a
`Duration` as `300.0 seconds`, and `runTimedOut`'s text does the same. -/

namespace Winnow.Net
open Lean

/-- Why a range scan refused (`RangeScanError`). Every case is a refusal, never a truncation. The two
spending caps (`filterBytesExhausted`, `runTimedOut`) leave the record at the last batch that committed, so
the next call resumes; the shape refusals are decided before any peer is asked. -/
inductive RangeScanError where
  | invalidRange (fromHeight toHeight : UInt32)
  | noWatchScripts
  | rangeTooWide (blocks : Nat) (limit : UInt32)
  | tooManyScripts (count limit : Nat)
  | tooManyIterations (count limit : Nat)
  | filterBytesExhausted (read limit : Nat)
  | runTimedOut (limitMs : Nat)
  | rangeBelowChain (fromHeight start : UInt32)
  | rangeAboveChain (toHeight tip : UInt32)
  | rangeSpansNoCheckpoint (fromHeight toHeight : UInt32)
  | recordUnreadable
  | recordTooLarge (maxBytes : Nat)
  | recordDamaged (reason : String)
  | recordWriteFailed
  deriving Repr, BEq, Inhabited

namespace RangeScanError

def name : RangeScanError → String
  | .invalidRange .. => "invalidRange" | .noWatchScripts => "noWatchScripts" | .rangeTooWide .. => "rangeTooWide"
  | .tooManyScripts .. => "tooManyScripts" | .tooManyIterations .. => "tooManyIterations"
  | .filterBytesExhausted .. => "filterBytesExhausted" | .runTimedOut _ => "runTimedOut"
  | .rangeBelowChain .. => "rangeBelowChain" | .rangeAboveChain .. => "rangeAboveChain"
  | .rangeSpansNoCheckpoint .. => "rangeSpansNoCheckpoint" | .recordUnreadable => "recordUnreadable"
  | .recordTooLarge _ => "recordTooLarge" | .recordDamaged _ => "recordDamaged" | .recordWriteFailed => "recordWriteFailed"

/-- Swift's `Duration` description, for a whole number of seconds or milliseconds. -/
def durationText (ms : Nat) : String :=
  if ms % 1000 == 0 then s!"{ms / 1000}.0 seconds" else s!"{ms / 1000}.{toString (1000 + ms % 1000) |>.drop 1} seconds"

def description : RangeScanError → String
  | .invalidRange f t => s!"Winnow was asked to scan blocks {f} to {t}, which is not a range it can scan."
  | .noWatchScripts => "A block range scan needs at least one script to look for."
  | .rangeTooWide b l => s!"That restore would scan {b} blocks, past the {l}-block limit for one range."
  | .tooManyScripts c l => s!"That restore looks for {c} scripts, past the limit of {l}."
  | .tooManyIterations c l =>
    s!"That restore has already rescanned its range {l} time{if l == 1 then "" else "s"} and asked for pass {c}."
  | .rangeBelowChain f s =>
    s!"The restore scan starts at block {f}, below block {s}, which is the first block Winnow holds a header for."
  | .rangeAboveChain t tip => s!"The restore scan ends at block {t}, above the validated chain tip {tip}."
  | .rangeSpansNoCheckpoint f t =>
    s!"Blocks {f} to {t} hold no filter checkpoint, and Winnow has no verified filter header below them, so nothing could check what a peer sent. Scan a wider range."
  | .filterBytesExhausted r l =>
    s!"The restore scan reached its data limit ({r} of {l} bytes of compact filters). It can be resumed."
  | .runTimedOut l => s!"The restore scan reached its time limit ({durationText l}). It can be resumed."
  | .recordUnreadable =>
    "Winnow could not read the restore scan's progress file. The scan is stopped so a payment is not skipped."
  | .recordTooLarge m => s!"The restore scan's progress file is unexpectedly large (limit: {m} bytes). The scan is stopped."
  | .recordDamaged r =>
    s!"The restore scan's progress file is damaged ({r}). The scan is stopped; Winnow will not replace it automatically."
  | .recordWriteFailed => "Winnow could not safely save the restore scan's progress. Nothing was recorded for this batch."

/-- `init(storage:)`: a range record's reading of a storage failure (the frontier cases cannot arise from a
range record and read as damage). -/
def ofStorage : FilterSyncStorageError → RangeScanError
  | .unreadable => .recordUnreadable
  | .tooLarge m => .recordTooLarge m
  | .damaged r => .recordDamaged r
  | .writeFailed => .recordWriteFailed
  | .frontierBeforeWallet s w => .recordDamaged s!"Saved compact-filter progress starts at block {s}, behind the wallet's required block {w}. Scanning is stopped."
  | .frontierBeyondTip s t => .recordDamaged s!"Saved compact-filter progress points to block {s}, beyond the validated chain tip {t}. Scanning is stopped."

end RangeScanError

/-- What bounds one run and the restore it is part of (`RangeScanLimits`), each clamped to its ceiling: five
years of mainnet blocks, 20,000 scripts, 1 GiB, an hour, 50 passes. -/
structure RangeScanLimits where
  maxBlocks : UInt32
  maxScripts : Nat
  /-- compact filters and the blocks their matches fetched, together -/
  maxFilterBytes : Nat
  maxDurationMs : Nat
  maxIterations : Nat
  deriving Repr, BEq, Inhabited

namespace RangeScanLimits
def blocksCeiling : UInt32 := 262_800
def scriptsCeiling : Nat := 20_000
def filterBytesCeiling : Nat := 1_024 * 1_024 * 1_024
def durationCeilingMs : Nat := 3_600_000
def iterationsCeiling : Nat := 50

def make (maxBlocks : UInt32 := 105_120) (maxScripts : Nat := 2_000) (maxFilterBytes : Nat := 64 * 1_024 * 1_024)
    (maxDurationMs : Nat := 300_000) (maxIterations : Nat := 10) : RangeScanLimits :=
  { maxBlocks := min maxBlocks blocksCeiling, maxScripts := min maxScripts scriptsCeiling
    maxFilterBytes := min maxFilterBytes filterBytesCeiling, maxDurationMs := min maxDurationMs durationCeilingMs
    maxIterations := min maxIterations iterationsCeiling }

instance : Inhabited RangeScanLimits := ⟨make⟩
end RangeScanLimits

/-- A range scan's persisted, resumable progress (`RangeScanProgress`). Same range and scripts resumes at
`nextScanHeight`; same range and a different script set is the next pass (back to `from`, `iteration` + 1,
the anchor below `from` kept); a different range replaces the record. -/
structure RangeScanProgress where
  fromHeight : UInt32
  toHeight : UInt32
  /-- `to + 1` when the range is finished -/
  nextScanHeight : UInt32
  /-- SHA256d over the sorted distinct watch scripts -/
  watchFingerprint : String
  /-- the fixed-point pass, counting from one -/
  iteration : Nat
  filterHeaders : Std.HashMap String String := {}
  crossCheck : Option CrossCheckReceipt := none
  deriving Inhabited

namespace RangeScanProgress

def recordKind : String := "range"

def eq (a b : RangeScanProgress) : Bool :=
  a.fromHeight == b.fromHeight && a.toHeight == b.toHeight && a.nextScanHeight == b.nextScanHeight &&
    a.watchFingerprint == b.watchFingerprint && a.iteration == b.iteration && a.crossCheck == b.crossCheck &&
    a.filterHeaders.size == b.filterHeaders.size && a.filterHeaders.toList.all fun (k, v) => b.filterHeaders[k]? == some v
instance : BEq RangeScanProgress := ⟨eq⟩

def isComplete (p : RangeScanProgress) : Bool := p.nextScanHeight > p.toHeight
def scannedThrough (p : RangeScanProgress) : Option UInt32 :=
  if p.nextScanHeight > p.fromHeight then some (p.nextScanHeight - 1) else none

/-- The next fixed-point pass: the same range from the start with a new script set, keeping only the pins
below `from` (the anchor a later peer must continue). -/
def restarted (p : RangeScanProgress) (fingerprint : String) : RangeScanProgress :=
  { p with nextScanHeight := p.fromHeight, watchFingerprint := fingerprint, iteration := p.iteration + 1,
           filterHeaders := p.filterHeaders.filter (fun k _ => match parseUInt32? k with
             | some h => h < p.fromHeight
             | none => false),
           crossCheck := none }

/-- One identity for a watch set, independent of order and repeats: the distinct scripts as sorted hex,
each followed by a newline, hashed with SHA256d. -/
def fingerprint (scripts : Array ByteArray) : String :=
  let distinct := (scripts.map hex).foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]
  let joined := (distinct.qsort (· < ·)).foldl (fun acc s => acc ++ s.toUTF8 ++ ByteArray.mk #[0x0A]) ByteArray.empty
  hex (sha256d joined)

def toJson (p : RangeScanProgress) : Json :=
  Json.mkObj ([("record", Json.str recordKind), ("from", Lean.toJson p.fromHeight.toNat), ("to", Lean.toJson p.toHeight.toNat),
    ("nextScanHeight", Lean.toJson p.nextScanHeight.toNat), ("watchFingerprint", Json.str p.watchFingerprint),
    ("iteration", Lean.toJson p.iteration),
    ("filterHeaders", Json.mkObj ((p.filterHeaders.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, Json.str v)))] ++
    (match p.crossCheck with | some r => [("crossCheck", r.toJson)] | none => []))

/-- `recordKind(in:)`: what a file says it is. -/
def recordKindOf (text : String) : Option String :=
  match Json.parse text with
  | .ok j => (j.getObjValAs? String "record").toOption
  | .error _ => none

private def u32? (j : Json) (k : String) : Option UInt32 := do
  let n ← (j.getObjValAs? Nat k).toOption
  if n > 0xFFFFFFFF then none else some n.toUInt32

/-- The refusal for a file not marked `"range"`, naming what it is marked. -/
def notRangeRecord (text : String) : Option RangeScanError :=
  let kind := recordKindOf text
  if kind == some recordKind then none
  else some (.recordDamaged s!"the file is not a range-scan record (it is marked {(kind.map fun k => s!"\"{k}\"").getD "nothing"})")

def decode (text : String) : Except RangeScanError RangeScanProgress := do
  let bad : RangeScanError := (notRangeRecord text).getD (.recordDamaged "the JSON or a progress field is invalid")
  let j ← (Json.parse text).mapError fun _ => bad
  let some fromHeight := u32? j "from" | throw bad
  let some toHeight := u32? j "to" | throw bad
  let some nextScanHeight := u32? j "nextScanHeight" | throw bad
  let some watchFingerprint := (j.getObjValAs? String "watchFingerprint").toOption | throw bad
  let some iteration := (j.getObjValAs? Nat "iteration").toOption | throw bad
  let .ok (.obj kvs) := j.getObjVal? "filterHeaders" | throw bad
  let mut filterHeaders : Std.HashMap String String := {}
  for (k, v) in kvs.toArray do
    let .str s := v | throw bad
    filterHeaders := filterHeaders.insert k s
  let crossCheck ← match j.getObjVal? "crossCheck" with
    | .ok .null | .error _ => pure none
    | .ok r => match CrossCheckReceipt.ofJson? r with
      | some c => pure (some c)
      | none => throw bad
  if (j.getObjValAs? String "record").toOption != some recordKind then
    throw ((notRangeRecord text).getD (.recordDamaged "the file is not a range-scan record"))
  return { fromHeight, toHeight, nextScanHeight, watchFingerprint, iteration, filterHeaders, crossCheck }

def maxBytes : Nat := 16 * 1_024 * 1_024
def maxPinnedHeaders : Nat := 2_000_000

def validate (p : RangeScanProgress) : Except RangeScanError Unit := do
  unless p.fromHeight ≤ p.toHeight && p.nextScanHeight ≥ p.fromHeight && p.nextScanHeight.toNat ≤ p.toHeight.toNat + 1 do
    throw (.recordDamaged "the range and its frontier disagree")
  unless 1 ≤ p.iteration && p.iteration ≤ RangeScanLimits.iterationsCeiling do
    throw (.recordDamaged "the pass number is out of range")
  unless ((Winnow.Wire.dataOfHex? p.watchFingerprint).map (·.size == 32)).getD false do
    throw (.recordDamaged "the watch-script fingerprint is not 32 bytes")
  (FilterSync.validateFilterHeaders p.filterHeaders p.nextScanHeight maxPinnedHeaders).mapError RangeScanError.ofStorage
  (FilterSync.validateReceipt p.crossCheck).mapError RangeScanError.ofStorage

/-- `load` over the file's text (`none`: no file). Damage is reported, never repaired. -/
def load (file : Option String) : Except RangeScanError (Option RangeScanProgress) := do
  let some text := file | return none
  if text.utf8ByteSize > maxBytes then throw (.recordTooLarge maxBytes)
  let p ← decode text
  p.validate
  return some p

/-- `resumed(stored:from:to:fingerprint:limits:)`: the stored record resumed, restarted for a new script
set, or a fresh one; the pass cap is checked here. -/
def resumed (stored : Option RangeScanProgress) (fromHeight toHeight : UInt32) (fingerprint : String)
    (limits : RangeScanLimits) : Except RangeScanError RangeScanProgress := do
  let mut record : RangeScanProgress :=
    { fromHeight, toHeight, nextScanHeight := fromHeight, watchFingerprint := fingerprint, iteration := 1 }
  if let some s := stored then
    if s.fromHeight == fromHeight && s.toHeight == toHeight then
      record := if s.watchFingerprint == fingerprint then s else s.restarted fingerprint
  if record.iteration > limits.maxIterations then throw (.tooManyIterations record.iteration limits.maxIterations)
  return record

end RangeScanProgress

namespace RangeScan
open FilterSync

/-- `checkShape`: everything about the request that can be judged before a peer is asked. -/
def checkShape (fromHeight toHeight : UInt32) (scripts : Nat) (limits : RangeScanLimits) : Except RangeScanError Unit := do
  unless fromHeight ≤ toHeight && toHeight < 0xFFFFFFFF do throw (.invalidRange fromHeight toHeight)
  if scripts == 0 then throw .noWatchScripts
  let blocks := toHeight.toNat - fromHeight.toNat + 1
  if blocks > limits.maxBlocks.toNat then throw (.rangeTooWide blocks limits.maxBlocks)
  if scripts > limits.maxScripts then throw (.tooManyScripts scripts limits.maxScripts)

/-- `checkChain`: the range must be inside the headers held. -/
def checkChain (fromHeight toHeight start tip : UInt32) : Except RangeScanError Unit := do
  unless fromHeight ≥ start do throw (.rangeBelowChain fromHeight start)
  unless toHeight ≤ tip do throw (.rangeAboveChain toHeight tip)

/-- The lowest positive multiple of `checkpointInterval` in `[low, high]` the tip reaches. -/
def boundary (low high tip : UInt32) : Option UInt32 :=
  let interval := checkpointInterval.toNat
  let ceiling := min high.toNat tip.toNat
  let floor := max low.toNat interval
  let first := ((floor + interval - 1) / interval) * interval
  if first ≤ ceiling then some first.toUInt32 else none

/-- `checkCheckpointAnchor`: the run must be able to check what a peer tells it: the record holds the
header below its frontier, or what is left to scan reaches a boundary cfcheckpt speaks for. Permitted when
the chain holds no boundary at all (a tip below 1,000: regtest, a brand-new signet). -/
def checkCheckpointAnchor (record : RangeScanProgress) (toHeight tip : UInt32) : Except RangeScanError Unit := do
  let frontier := record.nextScanHeight
  if frontier > toHeight then return
  if frontier == 0 || record.filterHeaders.contains (toString (frontier - 1).toNat) then return
  if tip < checkpointInterval then return
  if (boundary (frontier - 1) toHeight tip).isSome then return
  throw (.rangeSpansNoCheckpoint frontier toHeight)

/-- `requireComparedBoundary`: a batch anchored on a peer's word must pin a boundary the reference covers. -/
def requireComparedBoundary (headers : Std.HashMap String String) (batchStart batchStop tip : UInt32) :
    Except FilterSyncError Unit := do
  if tip < checkpointInterval then return
  let low := if batchStart > 0 then batchStart - 1 else 0
  match boundary low batchStop tip with
  | some h => if headers.contains (toString h.toNat) then return
  | none => pure ()
  throw (.checkpointMismatch s!"blocks {batchStart} to {batchStop} pin no checkpoint the cfcheckpt reference covers")

/-- `prunedRangeHeaders`: the forward scan's pruning, keeping the anchor below the range's first block. -/
def prunedRangeHeaders (headers : Std.HashMap String String) (frontier rangeStart : UInt32) : Std.HashMap String String :=
  let pruned := prunedFilterHeaders headers frontier
  if rangeStart == 0 then pruned
  else match headers[toString (rangeStart - 1).toNat]? with
    | some anchor => pruned.insert (toString (rangeStart - 1).toNat) anchor
    | none => pruned

end RangeScan

/-- What one run did (`RangeScanOutcome`); the blocks themselves went to `onMatch`. -/
structure RangeScanOutcome where
  fromHeight : UInt32
  toHeight : UInt32
  /-- heights this run delivered -/
  matchedHeights : Array UInt32
  scannedThrough : Option UInt32
  isComplete : Bool
  iteration : Nat
  filterBytesRead : Nat
  blockBytesRead : Nat
  crossCheck : Option CrossCheckReceipt
  deriving Repr, Inhabited

end Winnow.Net
