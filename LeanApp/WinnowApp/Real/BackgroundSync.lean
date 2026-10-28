import WinnowApp.Real.Peers

/-! # Background chain checks (`BackgroundSyncScheduler.swift`, AppModel's `runBackgroundSync`, upstream 66c6a48)

iOS decides when, and whether, a background task runs; an earliest-begin date is a request, never a
promise. Both task kinds (`refreshID`, `processingID`) enter the same single scan: the foreground's
routing, peers and checks, at most 2,000 blocks, then networking stops. Foreground networking and a
background check never run together: the scene becoming active cancels the check first, and a check
does not start while the scene is active.

`BackgroundSyncRun` completes exactly once, including when iOS expires the task during start-up or the
app returns to the foreground; it is kept apart from the shell's task so the lifecycle can be tested
without iOS scheduling it. Expiring cancels the work (and the backend's networking) and waits for it to
drain; a drained run that expired never reports success. -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

/-- `BackgroundSyncScheduler.refreshID` / `processingID` (Info.plist `BGTaskSchedulerPermittedIdentifiers`). -/
def backgroundRefreshID : String := "com.btcswift.winnow.chain-refresh"
def backgroundProcessingID : String := "com.btcswift.winnow.chain-processing"

/-- The time a task of `kind` is given before the run expires itself (`.seconds(120)` for processing,
`.seconds(25)` for refresh). -/
def backgroundBudgetMs (kind : String) : Nat := if kind == "processing" then 120_000 else 25_000

structure BackgroundSyncRun.State where
  running : Option (Task (Except IO.Error Unit)) := none
  started : Bool := false
  expired : Bool := false
  finished : Bool := false

/-- `BackgroundSyncRun`. -/
structure BackgroundSyncRun where
  budgetMs : Nat
  work : IO Bool
  cancel : IO Unit
  completion : Bool → IO Unit
  state : IO.Ref BackgroundSyncRun.State

namespace BackgroundSyncRun

def new (budgetMs : Nat) (work : IO Bool) (cancel : IO Unit) (completion : Bool → IO Unit) : IO BackgroundSyncRun := do
  return { budgetMs, work, cancel, completion, state := ← IO.mkRef {} }

/-- `finish(_:)`: the completion, once. -/
def finish (r : BackgroundSyncRun) (success : Bool) : IO Unit := do
  let go ← r.state.modifyGet fun s => if s.finished then (false, s) else (true, { s with finished := true, running := none })
  if go then r.completion success

/-- `expire()`: cancel the work and the backend's networking; the completion follows when the work drains. -/
def expire (r : BackgroundSyncRun) : IO Unit := do
  let claim ← r.state.modifyGet fun s => if s.finished || s.expired then (none, s) else (some s.running, { s with expired := true })
  let some running := claim | return
  if let some t := running then IO.cancel t
  discard <| IO.asTask (prio := .dedicated) (try r.cancel catch _ => pure ())

/-- `start()`: the work, and the deadline that expires it. A second start does nothing. -/
def start (r : BackgroundSyncRun) : IO Unit := do
  let go ← r.state.modifyGet fun s => if s.started || s.finished then (false, s) else (true, { s with started := true })
  if !go then return
  let t ← IO.asTask (prio := .dedicated) do
    if (← r.state.get).expired then r.finish false; return
    let ok ← try r.work catch _ => pure false
    r.finish (ok && !(← r.state.get).expired)
  r.state.modify fun s => if s.finished then s else { s with running := some t }
  discard <| IO.asTask (prio := .dedicated) do
    let deadline := (← IO.monoMsNow) + r.budgetMs
    repeat
      if (← r.state.get).finished then return
      let now ← IO.monoMsNow
      if now ≥ deadline then break
      IO.sleep (min 50 (deadline - now)).toUInt32
    r.expire

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
