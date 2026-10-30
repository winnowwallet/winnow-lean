import WinnowApp.Real.Send

/-! # Networking controls: start/stop, reconnect, retry, the census line, peers

AppModel.swift: `scenePhaseChanged` (:553: active → `activate`, background → suspend + stop),
`retryPeerDiscovery` (:593), `reconnect` (:2586), `candidateCount` (:2636), `resetPeers` (:2642);
SettingsView's census line (the list each build ships; upstream e5ce950 removed the download and its
Refresh button) and peer rows. -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

/-- `cancelBackgroundSync()`: closing the pool's sockets interrupts pending peer reads; returns once the
check has drained. -/
def cancelBackgroundSync (env : Env) : IO Unit := do
  let c ← env.modifyGet fun c => (c, if c.backgroundRunning then { c with backgroundCancelled := true } else c)
  if !c.backgroundRunning then return
  if let some s := c.stack then s.pool.stop
  repeat
    if !(← env.get).backgroundRunning then break
    IO.sleep 20

/-- The scene became active (`activate`), with these settings. A stack built for other settings
(manual peers, verify-from-genesis) is torn down first so the change takes effect. -/
def startNetworking (env : Env) (s : Settings) : IO Unit := do
  -- foreground networking and a background check never run together
  cancelBackgroundSync env
  let checked ← match (← env.get).dir with
    | some d => readLastCompleteCheck d
    | none => pure none
  env.modify fun c => { c with lastCompleteCheck := checked.or c.lastCompleteCheck }
  let restart ← env.modifyGet fun c =>
    let c := { c.withSettings s with active := true }
    match c.stack, c.network with
    | some st, some n => (st.key != keyFor (some s) n, c)
    | _, _ => (false, c)
  if restart then suspendAndStop env true
  activate env

/-- The scene went to the background: suspend, then stop (nothing of this generation keeps running). -/
def stopNetworking (env : Env) : IO Unit := do
  -- a cold background launch can deliver the scene's phase after its check started: that phase must not
  -- tear down the check's own scan
  if (← env.get).backgroundRunning then
    env.modify fun c => { c with active := false }
    return
  suspendAndStop env false

/-- `reconnect()`: rebuild the stack so changed peer settings take effect. -/
def reconnect (env : Env) (s : Settings) : IO Unit := do
  env.modify fun c => c.withSettings s
  suspendAndStop env true
  env.modify fun c => { c with active := true }
  activate env

/-- `retryPeerDiscovery()`: Automatic routing asks for the gateways again (`reconnect`). -/
def retryPeers (env : Env) : IO Unit := do
  let c ← env.get
  if let some s := c.settings then
    if c.gatewaySettings.mode == "automatic" then return ← reconnect env s
  match c.stack with
  | some s => s.pool.retry
  | none => activate env

/-- `syncNow()`. -/
def syncNow (env : Env) : IO Unit := discard <| syncOnce env

/-- "977 candidates": the entries on the networks the current routing may dial. -/
def candidateCount (c : CensusCatalog) (networks : List PeerNetwork := [.clearnet]) : String :=
  let n := networks.foldl (fun acc net => acc + ((c.networks.find? (·.1 == net.rawValue)).map (·.2.size)).getD 0) 0
  s!"{n} {if n == 1 then "candidate" else "candidates"}"

/-- SettingsView's census line: the list this build ships (`CensusCatalog.bundled`), or the sentence for
a build without one. -/
def catalogStatus (env : Env) : IO String := do
  match ← env.deps.census with
  | some c => return s!"Observed {c.date}: {candidateCount c (← env.get).activeGateways.networks}."
  | none => return "This build carries no peer list. Winnow uses saved peers and, when clearnet is allowed, DNS seeds."

/-- SettingsView's connected-peer rows. -/
def connectedPeers (env : Env) : IO (List PeerInfo) := do
  let some s := (← env.get).stack | return []
  let mut out := #[]
  for p in ← s.pool.connectedPeers do
    out := out.push { endpoint := p.endpoint.description, userAgent := ← p.peerUserAgent,
                      startHeight := (← p.peerStartHeight).toInt, feeFilter := (← p.feeFilter).map natOf
                      network := PeerNetwork.ofHost p.endpoint.host }
  return out.toList

/-- `resetPeers()`: forget learned peers (manual peers and the shipped list stay), avoid the current ones
first next time, and come back up. -/
def resetPeers (env : Env) : IO Unit := do
  let c ← env.get
  let avoid ← match c.stack with
    | some s => (·.map (·.endpoint)) <$> s.pool.connectedPeers
    | none => pure #[]
  env.modify fun c => { c with peersToAvoid := avoid }
  suspendAndStop env true
  try
    match c.stack, c.dir with
    | some s, _ => s.pool.forgetKnownGood
    | none, some d =>
      let f := dirFile d "peers.json"
      if ← f.pathExists then IO.FS.removeFile f
    | none, none => pure ()
  catch e =>
    env.modify fun c => { c with lastSyncError := some (toString e) }
    return
  env.journal "peers.reset" []
  activate env

end WinnowApp.Real
