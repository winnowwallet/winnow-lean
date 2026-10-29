import WinnowApp.Real.Base

/-! # The sync stack: build, activate, suspend, the loops and one sync pass

AppModel.swift: `buildStackIfNeeded` (:725), `makePeerPool` (:708), `openOrRebuildChain` (:697),
`makeBroadcaster` with the quarantine (:805), `chainStart` (:922), `observeBroadcasterFailures` (:907),
`rollBackStores` / `finishRollback` / `resumeInterruptedRollback` (:845–888), `activate` (:569),
`suspendNetworking` (:586) + `stopNetworking` (:2575), `startPhasePolling` / `updateSyncPhase`
(:604–655), `startSyncLoop` (:935), `syncOnce` (:954).

Cancellation: every loop thread belongs to one generation (and the sync loop also to one `loopToken`);
it re-reads the state between short sleeps and exits as soon as its generation is over. Suspending
bumps the generation first, then stops the pool, the broadcaster (which ends the event observer) and
every mempool window (whose consumer streams are cancelled here, since `MempoolWindowIO.stop` does not
end them). Results computed for an older generation are dropped. -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

def rollbackMarkerName : String := "rollback.height"
def quarantinedRelayStoreName : String := "broadcast.damaged.json"

/-- `chainStart()`: where the header chain begins for the wallet we have. -/
def chainStart (w : Option Wallet) (params : NetworkParams) (verifyFromGenesis : Bool) : IO ChainStart := do
  let birthday ← match w with
    | some w => do
      let s ← w.state
      pure (some (min s.creationHeight s.nextScanHeight))
    | none => pure none
  return ChainStart.forWallet birthday params.checkpoint verifyFromGenesis

/-- `openOrRebuildChain`: a start mismatch (the setting changed) rebuilds; any other error is fatal. -/
def openOrRebuildChain (params : NetworkParams) (path : System.FilePath) (start : ChainStart) : NetM HeaderStore := do
  match ← (HeaderStore.open params (some path) start).attempt with
  | .ok s => pure s
  | .error (.headers (.startMismatch ..)) =>
    removeQuietly path
    HeaderStore.open params (some path) start
  | .error e => throw e

/-- `makeBroadcaster`: a damaged relay store is set aside (renamed) and relay starts fresh. -/
def makeBroadcaster (env : Env) (pool : PeerPool) (dir : String) : NetM TxBroadcaster := do
  let path := dirFile dir "broadcast.json"
  match ← (TxBroadcaster.new pool (some path)).attempt with
  | .ok b => pure b
  | .error e@(.broadcastStorage _) =>
    let quarantine := dirFile dir quarantinedRelayStoreName
    removeQuietly quarantine
    match ← (IO.FS.rename path quarantine).toBaseIO with
    | .error _ => throw e
    | .ok () =>
      env.modify fun c => { c with relayStoreQuarantined := some (s!"Pending transactions could not be read ({e.description}). " ++
         s!"The file was set aside as {quarantinedRelayStoreName} and relay started fresh. " ++
         "Your balance and history are unaffected.") }
      TxBroadcaster.new pool (some path)
  | .error e => throw e

/-- `observeBroadcasterFailures`: a relay persistence failure shows as the sync error. The stream ends
when the broadcaster shuts down. -/
def observeBroadcasterFailures (env : Env) (b : TxBroadcaster) (gen : Nat) : IO Unit := do
  let events ← b.events
  env.spawnLoop do
    repeat
      match ← events.next with
      | .value (.persistenceFailed reason) =>
        env.modify fun c => if c.generation == gen then { c with lastSyncError := some reason } else c
      | .value _ => pure ()
      | .finished _ => break

/-! ## Rollback marker -/

def finishRollback (dir : String) : IO Unit := removeQuietly (dirFile dir rollbackMarkerName)

/-- `rollBackStores(to:)`: the target is recorded first; nothing changes if it cannot be. -/
def rollBackStores (env : Env) (dir : Option String) (w : Wallet) (b : TxBroadcaster) (fork : UInt32) : IO Unit := do
  let some dir := dir | failWith .noStorage
  writeAtomic (dirFile dir rollbackMarkerName) (toString fork).toUTF8
  env.walletOp (w.rollBack fork)
  env.hooks.multisigRollBack fork
  -- reactivates any own send whose confirming block fell (#157)
  runNet (b.rollBack fork)

/-- `resumeInterruptedRollback()`: redo a rollback a crash interrupted, before anything scans. -/
def resumeInterruptedRollback (env : Env) (dir : String) (w : Option Wallet) (s : Stack) : IO Unit := do
  let marker := dirFile dir rollbackMarkerName
  let some text ← (try some <$> IO.FS.readFile marker catch _ => pure none) | return
  let some fork := text.trimAscii.copy.toNat? | return
  if fork > 0xFFFF_FFFF then return
  let fork := fork.toUInt32
  if let some w := w then env.walletOp (w.rollBack fork)
  env.hooks.multisigRollBack fork
  runNet (s.broadcaster.rollBack fork)
  if let some f := s.filters then runNet (f.rollBack fork)
  finishRollback dir

/-! ## Building and tearing down -/

/-- Stops what a stack runs: the pool (and its monitor), the broadcaster (and its observers). -/
def Stack.shutdown (s : Stack) : IO Unit := do
  s.pool.stop
  s.broadcaster.shutdown

def Window.close (w : Window) : IO Unit := do
  w.window.stop
  w.events.cancel

/-! ## Peer routing -/

/-- `preparePeerGateways()`: resolve the routing once per networking generation. Direct only is clearnet,
Manual the gateways typed in, Automatic what discovery finds (callers of one generation share one
discovery). A generation that ended meanwhile installs nothing. No discovered address is persisted:
the next generation asks again. The routed HTTP client follows the routing. -/
def preparePeerGateways (env : Env) : IO Unit := do
  let c ← env.get
  let epoch := c.generation
  if c.preparedGatewayGeneration == some epoch then return
  let settings := c.gatewaySettings
  let config ← match settings.mode with
    | "direct" => pure {}
    | "manual" => pure settings.manual
    | _ =>
      match env.deps.discoverGateways with
      | none => pure {}
      | some discover =>
        let p ← IO.Promise.new
        let (mine, t) ← env.modifyGet fun c =>
          match c.gatewayDiscovery with
          | some t => ((false, t), c)
          | none =>
            if c.generation != epoch then ((false, Task.pure none), c)
            else ((true, p.result?), { c with gatewayDiscovery := some p.result?, discoveringGateways := true })
        if mine then
          discard <| IO.asTask (prio := .dedicated) do
            let r ← try discover catch _ => pure {}
            p.resolve r
        pure ((← IO.wait t).getD {})
  let claim ← env.modifyGet fun c =>
    if c.generation != epoch then (none, c) else
    (some (c.active, c.activeGateways == config && c.httpGateways == config, c.http, c.dir),
     { c with preparedGatewayGeneration := some epoch, gatewayDiscovery := none, discoveringGateways := false })
  let some (active, same, old, dir) := claim | return
  if settings.mode == "automatic" && active then
    if let some d := dir then
      try IO.FS.writeFile (gatewaysUsedPath d) (toString !(config.networks.contains .clearnet)) catch _ => pure ()
  if same && !(← old.isCancelled) then return
  let fresh ← RoutedHTTPClient.ofGateways env.deps.fetch config
  let replaced ← env.modifyGet fun c =>
    if c.generation == epoch then (some c.http, { c with activeGateways := config, http := fresh, httpGateways := config }) else (none, c)
  if let some o := replaced then o.cancel

/-- `buildStackIfNeeded()`. Unlike AppModel it does not require `isActive`: the Lean app creates and
imports wallets during onboarding before networking is started (see the module doc of `Real.lean`). -/
partial def buildStackIfNeeded (env : Env) : IO Unit := do
  let claim ← env.modifyGet fun c =>
    if c.stack.isSome then (none, c)
    else if c.buildingStack then (some none, c)
    else match c.dir, c.network with
      | some d, some n => (some (some (d, n, c)), { c with buildingStack := true })
      | _, _ => (none, c)
  match claim with
  | none => return
  | some none =>
    -- `waitForStackBuild`
    repeat
      let c ← env.get
      if c.stack.isSome || !c.buildingStack then break
      IO.sleep 50
  | some (some (dir, network, c)) =>
    let epoch := c.generation
    try
      -- creation, import and activation all wait for the same routing decision
      preparePeerGateways env
      let c ← env.get
      if c.generation != epoch then return
      let params := env.deps.networkParams.getD (NetworkParams.params (Network.net network))
      let key := keyFor c.settings network
      let manual := key.manualPeers.filterMap parsePeerEndpoint
      -- `censusCatalog: network == .mainnet ? CensusCatalog.bundled : nil`
      let catalog ← if network == .mainnet then env.deps.census else pure none
      let pool ← PeerPool.new params (peerCount := env.deps.peerCount) (manualPeers := manual.toArray)
        (peersFile := some (dirFile dir "peers.json")) (relayPreference := true)
        (dialTimeoutMs := if c.activeGateways.networks == [.clearnet] then 5_000 else 30_000)
        (seedResolver := some (SeedResolver.routed c.http)) (censusCatalog := catalog) (gateways := c.activeGateways)
        (avoidOnReset := c.peersToAvoid) (httpFetch := env.deps.fetch)
      let start ← chainStart c.wallet params key.verifyFromGenesis
      let chain ← runNet (openOrRebuildChain params (dirFile dir "headers.bin") start)
      if (← env.get).generation != epoch then pool.stop; return
      let broadcaster ← runNet (makeBroadcaster env pool dir)
      let filters ← match c.wallet with
        | some w => some <$> runNet (FilterSyncIO.new pool chain (← w.nextScanHeight) (some (dirFile dir "filters.json")))
        | none => pure none
      let stack : Stack := { pool, chain, filters, broadcaster, key }
      let installed ← env.modifyGet fun c =>
        if c.generation == epoch && c.stack.isNone then (true, { c with stack := some stack }) else (false, c)
      if !installed then stack.shutdown; return
      observeBroadcasterFailures env broadcaster epoch
      -- Before anything scans; fails closed (the marker stays and the error is shown).
      resumeInterruptedRollback env dir c.wallet stack
    catch e =>
      env.modify fun c => if c.generation == epoch then { c with lastSyncError := some (toString e) } else c
      env.journal "network.stackFailed" [("error", toString e)]
    finally
      env.modify fun c => { c with buildingStack := false }

/-- `suspendNetworking()` + `stopNetworking()`: ends the generation, then stops everything it ran.
`keepActive` is for the rebuilds (`reconnect`, `resetPeers`), which activate again right after. -/
def suspendAndStop (env : Env) (keepActive : Bool) : IO Unit := do
  let routing := (← env.get).activeGateways
  let fresh ← RoutedHTTPClient.ofGateways env.deps.fetch routing
  let (old, stack, windows) ← env.modifyGet fun c =>
    ((c.http, c.stack, c.receiveWindow.toList ++ c.relayWindows.toList.map (·.2)),
     { c with generation := c.generation + 1, active := keepActive && c.active, http := fresh, httpGateways := routing, stack := none,
              gatewayDiscovery := none, discoveringGateways := false,
              receiveWindow := none, relayWindows := #[], syncLoop := none, phaseLoop := none,
              loopToken := c.loopToken + 1, phase := .idle })
  old.cancel
  for w in windows do w.close
  if let some s := stack then s.shutdown

/-! ## The phase -/

/-- `bestAdvertisedTip(in:atLeast:)`. -/
def bestAdvertisedTip (s : Stack) (tip : UInt32) : IO UInt32 := do
  let mut estimate := tip
  for peer in ← s.pool.connectedPeers do
    let advertised ← peer.peerStartHeight
    if advertised > 0 && advertised.toInt.toNat.toUInt32 > estimate then estimate := advertised.toInt.toNat.toUInt32
  return estimate

/-- `journalPeerStatusIfChanged(_:)`: who the pool is connected to (endpoint and user agent, public
connection metadata) and what it held against the endpoints it dropped; journaled only when it changed. -/
def journalPeerStatusIfChanged (env : Env) (s : Stack) (connection : ConnectionStatus) : IO Unit := do
  let mut descriptions : Array String := #[]
  for peer in ← s.pool.connectedPeers do
    -- empty until the peer's version message lands
    let advertised ← peer.peerUserAgent
    descriptions := descriptions.push s!"{peer.endpoint.description} {if advertised.isEmpty then "unknown" else advertised}"
  let rejections := ((← s.pool.rejectionReasons).toArray.map fun (e, reason) => s!"{e.description}: {reason}").qsort (· < ·)
  env.journalIfChanged "peers.status"
    [("connected", toString connection.connected), ("target", toString connection.target),
     ("dialing", toString connection.dialing), ("exhausted", toString connection.exhausted),
     ("peers", ",".intercalate (descriptions.qsort (· < ·)).toList), ("rejected", " | ".intercalate rejections.toList)]
    (·.lastPeerFingerprint) fun c fp => { c with lastPeerFingerprint := fp }

/-- `updateSyncPhase()`'s computation for a stack. -/
def phaseOf (s : Stack) (connection : ConnectionStatus) : IO SyncPhase := do
  if connection.connected == 0 then
    return if connection.exhausted then .peerDiscoveryFailed else .connecting 0 connection.target
  if connection.connected < connection.target && connection.dialing then
    return .connecting connection.connected connection.target
  let tip ← s.chain.height
  let estimate ← bestAdvertisedTip s tip
  if estimate.toNat > tip.toNat + 1 then return .headers tip.toNat estimate.toNat
  match s.filters with
  | some f =>
    let next ← f.nextScanHeight
    return if next > tip then .synced else .filters next.toNat tip.toNat
  | none => return .synced

/-- `updateSyncPhase()`: stored only while the stack it read is still the current one. -/
def updateSyncPhase (env : Env) : IO SyncPhase := do
  let c ← env.get
  match c.stack with
  | none =>
    env.modify fun c' => if c'.generation == c.generation then { c' with phase := .idle } else c'
    return .idle
  | some s =>
    let connection ← s.pool.connectionStatus
    journalPeerStatusIfChanged env s connection
    let p ← phaseOf s connection
    env.modify fun c' => if c'.generation == c.generation then { c' with phase := p } else c'
    return p

/-- `startPhasePolling()`: once a second while this generation lasts. -/
def startPhasePolling (env : Env) (epoch : Nat) : IO Unit := do
  let go ← env.modifyGet fun c =>
    if c.generation != epoch || c.phaseLoop == some epoch then (false, c) else (true, { c with phaseLoop := some epoch })
  if !go then return
  let alive (c : Core) := c.generation == epoch && c.phaseLoop == some epoch
  env.spawnLoop do
    repeat
      if !alive (← env.get) then break
      discard <| updateSyncPhase env
      env.modify fun c => if alive c then { c with phaseTicks := c.phaseTicks + 1 } else c
      if !(← env.sleepWhile env.deps.phaseIntervalMs alive) then break

/-! ## One sync pass -/

/-- `syncOnce()`: the wallet's and its multisig accounts' scripts in one filter stream (an account is
just more watched scripts); matched blocks update the wallet and the accounts and confirm pending
broadcasts; the frontier is recorded either way. -/
def syncOnce (env : Env) (maxBlocks : Option UInt32 := none) : IO Bool := do
  let claim ← env.modifyGet fun c =>
    match c.wallet, c.stack with
    | some w, some s =>
      match s.filters with
      | some f =>
        if c.syncing then (none, c)
        else (some (w, s, f, c.generation, c.dir), { c with syncing := true, syncPasses := c.syncPasses + 1 })
      | none => (none, c)
    | _, _ => (none, c)
  let some (w, s, f, gen, dir) := claim | return false
  try
    let pass : NetM Unit := do
      let scripts := (← WM.toNet w.watchScripts) ++ (← (env.hooks.multisigWatchScripts w.network : IO _))
      let b := s.broadcaster
      f.sync scripts (maxBlocks := maxBlocks) (onReorg := some fun fork => (rollBackStores env dir w b fork : IO Unit)) (onMatch := fun m => do
        let effect ← env.walletOpNet (w.apply m)
        for discarded in effect.discardedReplacements do b.cancel discarded
        for discarded in ← (env.hooks.multisigApply m w.network : IO _) do b.cancel discarded
        let pending ← b.pendingTxids
        for tx in m.block.transactions do
          if pending.contains tx.txid then b.markConfirmed tx.txid m.height)
      env.walletOpNet (w.recordScanHeight (← f.nextScanHeight))
      b.pruneConfirmed (← f.nextScanHeight)
      if let some d := dir then (finishRollback d : IO Unit)
    match ← pass.attempt with
    | .ok () =>
      -- the scan reached the tip: when it did is what Advanced's Sync section shows
      let complete := (← f.nextScanHeight) > (← s.chain.height)
      let now ← unixNow
      let current ← env.modifyGet fun c =>
        if c.generation == gen then
          (true, { c with lastSyncError := none, transientSyncFailures := 0, transientSyncError := none,
                          lastCompleteCheck := if complete then some now else c.lastCompleteCheck })
        else (false, c)
      if complete && current then
        if let some d := dir then
          try IO.FS.writeFile (lastCompleteCheckPath d) (toString now) catch _ => pure ()
      return complete
    | .error e =>
      try env.walletOp (w.recordScanHeight (← f.nextScanHeight)) catch _ => pure ()
      -- a suspend, network switch or expired background check ended this generation: nothing failed
      let transient := isTransientSyncError e
      env.modify fun c => if c.generation == gen then
          { c with lastSyncError := some e.description,
                   transientSyncFailures := if transient then c.transientSyncFailures + 1 else 0,
                   transientSyncError := if transient then some e.description else none }
        else c
      return false
  finally
    env.modify fun c => { c with syncing := false }

/-- `startSyncLoop()`: a pass, then 45 s, until the loop's generation or token is over. -/
def startSyncLoop (env : Env) : IO Unit := do
  let claim ← env.modifyGet fun c =>
    let ready := c.active && c.syncLoop.isNone && c.wallet.isSome && (c.stack.bind (·.filters)).isSome
    if ready then (some (c.generation, c.loopToken), { c with syncLoop := some c.loopToken }) else (none, c)
  let some (gen, token) := claim | return
  let alive (c : Core) := c.generation == gen && c.loopToken == token
  env.spawnLoop do
    try
      repeat
        if !alive (← env.get) then break
        discard <| syncOnce env
        if !(← env.sleepWhile env.deps.syncIntervalMs alive) then break
    finally
      env.modify fun c => if c.syncLoop == some token then { c with syncLoop := none } else c

/-- `activate()`: build the stack if needed, start the phase ticker, the pool, then the sync loop. -/
def activate (env : Env) : IO Unit := do
  let c ← env.get
  if !c.active || c.backgroundRunning || c.dir.isNone then return
  let epoch := c.generation
  buildStackIfNeeded env
  let c ← env.get
  if c.generation != epoch || !c.active then return
  let some s := c.stack | return
  startPhasePolling env epoch
  s.pool.start
  let c ← env.get
  if c.generation != epoch || !c.active then return
  startSyncLoop env

end WinnowApp.Real
