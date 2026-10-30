import WinnowApp.Real.Peers
import LeanNative.Native.BackgroundRun

/-! # Background chain checks (`BackgroundSyncScheduler.swift`, AppModel's `runBackgroundSync`, upstream 66c6a48)

iOS decides when, and whether, a background task runs; an earliest-begin date is a request, never a
promise. Both task kinds (`refreshID`, `processingID`) enter the same single scan: the foreground's
routing, peers and checks, at most 2,000 blocks, then networking stops. Foreground networking and a
background check never run together: the scene becoming active cancels the check first, and a check
does not start while the scene is active.

`BackgroundSyncRun` is LeanNative's `BackgroundRun` with this app's budgets: it completes exactly once,
including when iOS expires the task during start-up or the app returns to the foreground, and is kept
apart from the shell's task so the lifecycle can be tested without iOS scheduling it. Expiring cancels the
work (and the backend's networking) and waits for it to drain; a drained run that expired never reports
success. The lifecycle's races are the framework's and tested there; RecordsTest keeps this app's cases. -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

/-- `BackgroundSyncScheduler.refreshID` / `processingID` (Info.plist `BGTaskSchedulerPermittedIdentifiers`). -/
def backgroundRefreshID : String := "com.btcswift.winnow.chain-refresh"
def backgroundProcessingID : String := "com.btcswift.winnow.chain-processing"

/-- The time a task of `kind` is given before the run expires itself (`.seconds(120)` for processing,
`.seconds(25)` for refresh). -/
def backgroundBudgetMs (kind : String) : Nat := if kind == "processing" then 120_000 else 25_000

/-- `BackgroundSyncRun`: LeanNative's `BackgroundRun` (`LeanNative.Native.BackgroundRun`) with the task's budget
as its deadline. It completes exactly once, including when iOS expires the task during start-up; once
expired, the work and the backend's cancellation drain before the completion, which then reports no
success. -/
structure BackgroundSyncRun where
  run : LeanNative.Native.BackgroundRun

namespace BackgroundSyncRun

def new (budgetMs : Nat) (work : IO Bool) (cancel : IO Unit) (completion : Bool → IO Unit) : IO BackgroundSyncRun := do
  return ⟨← LeanNative.Native.BackgroundRun.new
    { work, cancel, completion := fun o => completion o.success, deadline := .after budgetMs }⟩

/-- `start()`: the work, and the deadline that expires it. A second start does nothing. -/
def start (r : BackgroundSyncRun) : IO Unit := r.run.start

/-- `expire()`: cancel the work and the backend's networking; the completion follows when the work drains. -/
def expire (r : BackgroundSyncRun) : IO Unit := r.run.expire

end BackgroundSyncRun

/-! ## The backend's half -/

/-- `scanInBackground()`: a ready wallet, the foreground's routing (refused when Automatic would connect
directly after the foreground last used a gateway), the stack, the pool, one bounded scan. -/
def scanInBackground (env : Env) : IO Bool := do
  let cancelled : IO Bool := do return (← env.get).backgroundCancelled
  let c ← env.get
  let (some _, some dir) := (c.wallet, c.dir) | return false
  if ← cancelled then return false
  preparePeerGateways env
  if ← cancelled then return false
  let c ← env.get
  unless backgroundRoutingAllowed c.gatewaySettings.mode c.activeGateways (← readGatewaysUsed dir) do return false
  buildStackIfNeeded env
  if ← cancelled then return false
  let some s := (← env.get).stack | return false
  s.pool.start
  if ← cancelled then return false
  syncOnce env (maxBlocks := some 2_000)

/-- `runBackgroundSync()`: one bounded scan with the foreground's routing, peers and checks, then teardown;
whether it reached the tip. Refused while the scene is active or another check runs. -/
def runBackgroundSync (env : Env) (s : Settings) : IO Bool := do
  let go ← env.modifyGet fun c =>
    if c.active || c.backgroundRunning then (false, c)
    else (true, { c.withSettings s with backgroundRunning := true, backgroundCancelled := false })
  if !go then return false
  let complete ← try scanInBackground env catch _ => pure false
  -- the next foreground resolves routing afresh: Tailscale may have come or gone since this check
  suspendAndStop env false
  env.modify fun c => { c with backgroundRunning := false }
  env.journal "background.completed" [("complete", toString complete)]
  return complete

end WinnowApp.Real
