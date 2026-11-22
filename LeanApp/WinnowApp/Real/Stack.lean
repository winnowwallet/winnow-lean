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
def chainStart (w : Option Wallet) (params : NetworkParams) (verifyFromGenesis : Bool) (others : Array UInt32 := #[]) :
    IO ChainStart := do
  let own ← match w with
    | some w => do
      let s ← w.state
      pure (some (min s.creationHeight s.nextScanHeight))
    | none => pure none
  -- the network's chain is every held wallet's: it begins at or below the oldest of them
  let birthday := others.foldl (fun b x => some (match b with | some b => min b x | none => x)) own
  return ChainStart.forWallet birthday params.checkpoint verifyFromGenesis

/-- `openOrRebuildChain`: a start mismatch (the setting changed) rebuilds, and so does a kept chain that went
past the checkpoint on another header (an earlier build did not check it); any other error is fatal. -/
def openOrRebuildChain (params : NetworkParams) (path : System.FilePath) (start : ChainStart) : NetM HeaderStore := do
  match ← (HeaderStore.open params (some path) start).attempt with
  | .ok s => pure s
  | .error (.headers (.startMismatch ..)) | .error (.headers (.checkpointMismatch _)) =>
    removeQuietly path
    HeaderStore.open params (some path) start
  | .error e => throw e

/-- The network's scan from its file. A saved frontier behind every wallet here (the one it was last moved
for is gone, or was left out of passes) is where scanning goes on from: more blocks are scanned, none is
missed. -/
def openNetworkFilters (pool : PeerPool) (chain : HeaderStore) (start : UInt32) (path : System.FilePath) :
    NetM FilterSyncIO := do
  match ← (FilterSyncIO.new pool chain start (some path)).attempt with
  | .ok f => pure f
  | .error (.filterStorage (.frontierBeforeWallet stored _)) => FilterSyncIO.new pool chain stored (some path)
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

/-- The filter frontier mirrored into the wallet file with the hash of the last block scanned, so a backup
names the block its state stands on and another device can check that block is in its own chain. A
frontier that has not moved leaves a recorded hash alone: it is either this chain's already, or one that
came with a restore and is checked before anything is scanned (`anchorFork`), which this must not paper over. -/
def recordFrontier (env : Env) (serial : Nat) (what : String) (w : Wallet) (f : FilterSyncIO) : IO Unit := do
  let (next, hash) ← f.frontier
  let s ← runWM w.state
  if next == s.nextScanHeight && s.scannedThroughHash.isSome then return
  env.walletWrite serial what (w.recordScanHeight next hash)

/-- The open wallet's anchor checked against the chain just synced: the fork to roll back to, if any. -/
def walletAnchorFork (w : Wallet) (chain : HeaderStore) : IO (Option UInt32) := do
  let s ← runWM w.state
  let some anchor := s.scannedThroughHash | return none
  if s.nextScanHeight == 0 then return none
  -- never below where this chain begins: nothing under it can be scanned
  let start ← chain.startHeight
  return (← anchorFork (fun h => chain.blockHash h) (s.nextScanHeight - 1) anchor s.history).map (max start)

/-! ## Rollback marker -/

def finishRollback (dir : String) : IO Unit := removeQuietly (dirFile dir rollbackMarkerName)

/-- `rollBackStores(to:)`: the target is recorded first; nothing changes if it cannot be (backend-test's
step 7e). -/
def rollBackStores (env : Env) (dir : Option String) (w : Wallet) (serial : Nat) (b : TxBroadcaster) (fork : UInt32) :
    IO Unit := do
  let some dir := dir | failWith .noStorage
  writeAtomic (dirFile dir rollbackMarkerName) (toString fork).toUTF8
  env.walletWrite serial "sync.rollBack" (w.rollBack fork)
  env.hooks.multisigRollBack fork
  -- reactivates any own send whose confirming block fell (#157)
  runNet (b.rollBack fork)

/-- `resumeInterruptedRollback()`: redo a rollback a crash interrupted, before anything scans (backend-test's
step 9b). -/
def resumeInterruptedRollback (env : Env) (dir : String) (w : Option Wallet) (serial : Nat) (s : Stack) : IO Unit := do
  let marker := dirFile dir rollbackMarkerName
  let some text ← (try some <$> IO.FS.readFile marker catch _ => pure none) | return
  let some fork := text.trimAscii.copy.toNat? | return
  if fork > 0xFFFF_FFFF then return
  let fork := fork.toUInt32
  if let some w := w then env.walletWrite serial "resume.rollBack" (w.rollBack fork)
  env.hooks.multisigRollBack fork
  for r in (← env.get).riders do
    try
      env.riderWrite r.serial "resume.rollBack" (r.wallet.rollBack fork)
      r.multisig.rollBack fork
    catch _ => pure ()
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

/-- Each added wallet's own stack (0.9.20 to 0.9.23 kept one per slot) folded into the network's, once: its
pending payments join the network's relay file, a rollback it was in the middle of is finished on its wallet
and accounts, and its chain, scan and peers go (the network's serve every wallet; its frontier is its wallet
file's). A file that does not read is left where it is. -/
def migrateSlotStacks (env : Env) (network : WinnowApp.Network) (networkDir : String) : IO Unit := do
  -- every slot's directory, a wallet in it or not (an addition that never finished kept a stack too)
  let base := System.FilePath.mk networkDir / slotsDirName
  let slots ← if ← base.isDir then pure (((← base.readDir).map (·.fileName)).filter validSlot) else pure #[]
  for slot in slots do
    let dir := slotDir networkDir slot
    let marker := dirFile dir rollbackMarkerName
    if let some text ← (try some <$> IO.FS.readFile marker catch _ => pure none) then
      if let some fork := text.trimAscii.copy.toNat? then
        if fork ≤ 0xFFFF_FFFF then
          match ← (Wallet.open (walletPath dir) env.deps.keyStore env.deps.random).run with
          | .ok w => discard <| (w.rollBack fork.toUInt32).run
          | .error _ => pure ()
          try (← env.hooks.multisigAt network dir).rollBack fork.toUInt32 catch _ => pure ()
    let relay := dirFile dir "broadcast.json"
    if ← relay.pathExists then
      let now := (← unixNow).toFloat
      let shared := dirFile networkDir "broadcast.json"
      let theirs ← try pure (TxBroadcaster.decodeStore (← IO.FS.readBinFile relay) now).toOption catch _ => pure none
      let ours ← if ← shared.pathExists then
          try pure (TxBroadcaster.decodeStore (← IO.FS.readBinFile shared) now).toOption catch _ => pure none
        else pure (some {})
      if let (some theirs, some ours) := (theirs, ours) then
        writeAtomic shared (TxBroadcaster.encodeStore (theirs.fold (fun m k v => if m.contains k then m else m.insert k v) ours))
        removeQuietly relay
    for name in oldSlotStackFiles do removeQuietly (dirFile dir name)

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
  | some (some (walletDir, network, c)) =>
    let epoch := c.generation
    -- the stack is the network's, in its own directory, whichever wallet is open
    let dir := networkDirOf walletDir
    try
      migrateSlotStacks env network dir
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
      let start ← chainStart c.wallet params key.verifyFromGenesis (c.held.map (·.birthday))
      let chain ← runNet (openOrRebuildChain params (dirFile dir "headers.bin") start)
      if (← env.get).generation != epoch then pool.stop; return
      let broadcaster ← runNet (makeBroadcaster env pool dir)
      let filters ← match c.wallet with
        -- the network's scan, which may be behind the open wallet (another wallet here is further back, or
        -- the open one took another device's state): it starts no later than the wallet least far on
        | some w => do
          let start := (c.held.map (·.next)).foldl min (← w.nextScanHeight)
          some <$> runNet (openNetworkFilters pool chain start (dirFile dir "filters.json"))
        | none => pure none
      let stack : Stack := { pool, chain, filters, broadcaster, key }
      let installed ← env.modifyGet fun c =>
        if c.generation == epoch && c.stack.isNone then (true, { c with stack := some stack }) else (false, c)
      if !installed then stack.shutdown; return
      observeBroadcasterFailures env broadcaster epoch
      -- Before anything scans; fails closed (the marker stays and the error is shown).
      resumeInterruptedRollback env dir c.wallet c.walletSerial stack
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
  -- under the wallet lock: a wallet write checked against this generation finishes first
  let (old, stack, windows) ← env.withWalletLock <| env.modifyGet fun c =>
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

/-- A restored wallet looks further for cards its backup does not list (issue #94). The scan forward from
the backup's height watched the cards the wallet could have made since (`Wallet.beginCardRestore`). If one
of those was paid there may be more after it, and what was paid to them is in blocks that scan has passed.
So, once the scan has reached the tip: record the next cards, scan the same blocks again for their scripts
alone, and repeat until a round records none. Only then is the mark that the search is unfinished cleared,
so a search a peer or the app's exit cuts short starts again on a later pass.

When no card was paid, which the wallet's file answers, it ends here without a key being read. A range
scan must be able to check what a peer says against a filter checkpoint (every 1,000 blocks), so the range
starts just above the last one at or below the backup's height; when the header chain starts above that
and the range holds none, the search waits for the tip to pass the next one. -/
def finishCardRestore (env : Env) (w : Wallet) (f : FilterSyncIO) (chainStart : UInt32) (serial : Nat)
    (applyMatch : BlockMatch → NetM Unit) : NetM Unit := do
  let some fromHeight ← w.cardRestoreFrom | return
  let finished (rounds : Nat) : NetM Unit := do
    env.walletWriteNet serial "cards.endRestore" w.endCardRestore
    env.journal "cards.restored"
      [("fromHeight", toString fromHeight), ("rounds", toString rounds), ("cards", toString (← w.cards).size)]
  if !(← w.wantsMoreCards) then return ← finished 0
  let some through ← f.lastScannedHeight | return
  if through < fromHeight then return
  let interval := FilterSync.checkpointInterval
  let boundaryBelow := ((fromHeight - 1) / interval) * interval
  let low := max chainStart (if boundaryBelow == 0 then 0 else boundaryBelow + 1)
  if through ≥ interval && low != 0 && (RangeScan.boundary (low - 1) through through).isNone then return
  let mut rounds := 0
  while (← w.wantsMoreCards) do
    let before : Std.HashSet ByteArray := Std.HashSet.ofArray (← WM.toNet w.watchScripts)
    discard <| env.walletWriteNet serial "cards.restore" w.restoreCards
    let fresh := (← WM.toNet w.watchScripts).filter (!before.contains ·)
    if fresh.isEmpty then break
    rounds := rounds + 1
    let outcome ← f.scanRange low through fresh (RangeScanLimits.make (maxBlocks := RangeScanLimits.blocksCeiling))
      none applyMatch
    -- cut short: the cards are recorded and watched from here on; a later pass scans back for them
    unless outcome.isComplete do return
  finished rounds

/-- What one run of an arriving account's catch-up may spend before the forward pass goes on: a minute, and
the filters of about three weeks of mainnet blocks. The next pass takes it up where it stopped. -/
def arrivingScanLimits : RangeScanLimits :=
  RangeScanLimits.make (maxScripts := RangeScanLimits.scriptsCeiling) (maxDurationMs := 60_000)

/-- One wallet a pass scans for: the open one (`rider` none) or a rider. `from` is the first block given to it:
one ahead of the network's scan (state from another device) is given nothing it already has. -/
structure PassWallet where
  wallet : Wallet
  rider : Option Rider := none
  multisig : ProfileMultisig
  scripts : Array ByteArray
  «from» : UInt32

/-- `syncOnce()`: every wallet kept on the network in one filter stream, each with its multisig accounts (an
account is just more watched scripts). The scan is the network's (`filters.json` in its directory): a wallet
behind it (added, restored, or held back by a pass that could not write to it) is first caught up with a range
scan, as an arriving account is, then joins. Matched blocks update each wallet and its accounts and confirm
pending broadcasts; each wallet's frontier is recorded either way. A wallet whose accounts cannot be read now
is left out of the pass, and waits for the next, without holding the others back. -/
def syncOnce (env : Env) (maxBlocks : Option UInt32 := none) : IO Bool := do
  let claim ← env.modifyGet fun c =>
    match c.wallet, c.stack with
    | some w, some s =>
      match s.filters with
      | some f =>
        if c.syncing then (none, c)
        else (some (w, s, f, c.generation, c.walletSerial, c.dir, c.riders), { c with syncing := true, syncPasses := c.syncPasses + 1 })
      | none => (none, c)
    | _, _ => (none, c)
  let some (w, s, f, gen, serial, dir, riders) := claim | return false
  let network := dir.map networkDirOf
  let net := w.network
  let hashes : ChainHashes := fun h => s.chain.blockHash h
  let openCurrent : IO Bool := do return (← env.get).walletSerial == serial
  let riderCurrent (r : Rider) : IO Bool := do return (← env.get).riders.any (·.serial == r.serial)
  let write (p : PassWallet) (what : String) (x : WM Unit) : IO Unit :=
    match p.rider with
    | some r => env.riderWrite r.serial what x
    | none => env.walletWrite serial what x
  let current (p : PassWallet) : IO Bool := match p.rider with
    | some r => riderCurrent r
    | none => openCurrent
  -- a wallet's frontier mirrored, never moved back (one ahead keeps its own), with the hash of its last block
  let record (p : PassWallet) (next : UInt32) : IO Unit := do
    let st ← p.wallet.state
    if next < st.nextScanHeight || (next == st.nextScanHeight && st.scannedThroughHash.isSome) then return
    let hash ← if next == 0 then pure none else hashes (next - 1)
    write p "sync.recordScanHeight" (p.wallet.recordScanHeight next hash)
  try
    let scanner : RangeScanner := fun fromHeight toHeight scripts onMatch => do
      match ← (f.scanRange fromHeight toHeight scripts (limits := arrivingScanLimits)
          (onMatch := fun m => (onMatch m : IO Unit)) (stopAtCaps := true)).attempt with
      | .ok outcome => return (outcome.scannedThrough, outcome.isComplete)
      | .error (.range (.rangeBelowChain ..)) => throw (IO.userError waitingForNewerCopyText)
      | .error e => throw (IO.userError e.description)
    let openMultisig : ProfileMultisig :=
      { watchScripts := env.hooks.multisigWatchScripts, apply := env.hooks.multisigApply,
        rollBack := env.hooks.multisigRollBack, catchUp := env.hooks.multisigCatchUp }
    -- accounts that arrived from another of the person's devices are brought up to this phone's scan first, so
    -- one that is ready is watched by this very pass. Not in a background check, whose minute is the wallet's.
    if maxBlocks.isNone then
      try openMultisig.catchUp net (← f.nextScanHeight) scanner hashes catch _ => pure ()
      for r in riders do
        try r.multisig.catchUp net (← f.nextScanHeight) scanner hashes catch _ => pure ()
    -- the accounts' scripts first, outside the pass: an account file that cannot be read now (a locked phone in
    -- a background launch) leaves its wallet out of the pass, so its scan height stays where the accounts'
    -- payments are, and the next pass reads the file again; it is a transient failure, not the wallet's
    let watchIO (m : ProfileMultisig) : IO (Array ByteArray) := do
      match ← m.watchScripts net with
      | .ok xs => pure xs
      | .error e => throw (IO.userError e.message)
    let mut wallets : Array PassWallet := #[]
    let mut openOut := false
    match ← openMultisig.watchScripts net with
    | .ok scripts => wallets := wallets.push { wallet := w, multisig := openMultisig, scripts, «from» := 0 }
    | .error (.locked msg) =>
      -- a file whose key is locked comes back by itself
      env.modify fun c => if c.generation == gen && c.walletSerial == serial then
          { c with transientSyncFailures := c.transientSyncFailures + 1, transientSyncError := some msg }
        else c
      openOut := true
    | .error (.failed msg) =>
      -- a damaged file waits for the person (Settings → Security → Multisig accounts sets it aside)
      env.modify fun c => if c.generation == gen && c.walletSerial == serial then
          { c with lastSyncError := some msg, transientSyncFailures := 0, transientSyncError := none }
        else c
      openOut := true
    for r in riders do
      match ← r.multisig.watchScripts net with
      | .ok scripts => wallets := wallets.push { wallet := r.wallet, rider := some r, multisig := r.multisig, scripts, «from» := 0 }
      | .error e => env.journal "sync.walletSetAside" [("walletID", r.held.id), ("error", e.message)]
    -- what another device scanned further is taken first, for the blocks this chain already has
    if maxBlocks.isNone then
      try env.hooks.headStart catch _ => pure ()
    -- a wallet behind the network's scan joins it first, by a range scan of the blocks it has not had (not in
    -- a background check); one that cannot be brought all the way waits out this pass
    let frontier ← f.nextScanHeight
    let mut joined : Array PassWallet := #[]
    for p in wallets do
      let next ← p.wallet.nextScanHeight
      if next ≥ frontier then
        joined := joined.push { p with «from» := next }
        continue
      if maxBlocks.isSome then continue
      -- what came from elsewhere names a block this chain must have
      if let some fork ← walletAnchorFork p.wallet s.chain then
        env.journal "sync.anchorMismatch" [("fork", toString fork), ("walletID", p.wallet.id)]
        write p "sync.anchorRollBack" (p.wallet.rollBack fork)
        p.multisig.rollBack fork
      let mut ready := false
      for _ in [0:8] do
        let begin ← p.wallet.nextScanHeight
        if begin ≥ frontier then ready := true; break
        let own ← runWM p.wallet.watchScripts
        let accounts ← watchIO p.multisig
        let applyOne : Net.BlockMatch → IO Unit := fun m => env.withPlaceLock do
          unless ← current p do throw (IO.userError "the wallet changed")
          write p "sync.join" (discard <| p.wallet.apply m)
          discard <| p.multisig.apply m net
        let outcome ← (scanner begin (frontier - 1) (own ++ accounts) applyOne).toBaseIO
        let (through, complete) ← match outcome with
          | .ok r => pure r
          | .error e =>
            env.journal "sync.joinWaiting" [("walletID", p.wallet.id), ("error", toString e)]
            pure (none, false)
        -- a block that paid a new address: the same blocks again for the scripts that grew, from where this began
        let grown := (← runWM p.wallet.watchScripts).size > own.size || (← watchIO p.multisig).size > accounts.size
        if complete && grown then continue
        if let some t := through then record p (if complete then frontier else t + 1)
        if complete then
          env.journal "sync.walletJoined" [("walletID", p.wallet.id), ("from", toString begin), ("through", toString (frontier - 1))]
          ready := true
        break
      if ready then
        joined := joined.push { p with scripts := (← watchIO p.multisig), «from» := ← p.wallet.nextScanHeight }
    if joined.isEmpty then return false
    let openIn := joined.any (·.rider.isNone)
    let multisigScripts := ((joined.find? (·.rider.isNone)).map (·.scripts)).getD #[]
    env.deps.syncScriptsChosen
    let dropped ← IO.mkRef (#[] : Array Nat)
    -- the open wallet is 0 here (a rider's serial never is)
    let isDropped (p : PassWallet) : IO Bool := do return (← dropped.get).contains ((p.rider.map (·.serial)).getD 0)
    let pass : NetM Unit := do
      let mut scripts : Array ByteArray := #[]
      let mut seen : Std.HashSet ByteArray := {}
      for p in joined do
        for x in (← WM.toNet p.wallet.watchScripts) ++ p.scripts do
          unless seen.contains x do
            seen := seen.insert x
            scripts := scripts.push x
      let b := s.broadcaster
      let began ← f.nextScanHeight
      -- a block to every wallet past it, under the place lock: the open wallet's errors end the pass, as
      -- they always did; a rider's leaves it out of the rest of the pass
      let applyAll : BlockMatch → NetM Unit := fun m => do
        let cancelled ← (env.withPlaceLock do
          let mut cancelled : Array ByteArray := #[]
          for p in joined do
            if m.height < p.«from» || (← isDropped p) then continue
            unless ← current p do continue
            match p.rider with
            | none =>
              let effect ← env.walletWrite serial "sync.apply" (w.apply m)
              -- a payment to a card is its person's: said once the coin is the wallet's, and never a reason to stop
              for coin in effect.received do
                if let some card := coin.card then
                  discard <| (env.hooks.cardPayment card (Winnow.displayHex coin.txid)).toBaseIO
              cancelled := cancelled ++ effect.discardedReplacements ++ (← env.hooks.multisigApply m net)
            | some r =>
              match ← (do
                  let effect ← env.riderWrite r.serial "sync.apply" (r.wallet.apply m)
                  return effect.discardedReplacements ++ (← r.multisig.apply m net)).toBaseIO with
              | .ok more => cancelled := cancelled ++ more
              | .error e =>
                dropped.modify (·.push r.serial)
                env.journal "sync.walletSetAside" [("walletID", r.held.id), ("error", toString e)]
          return cancelled : IO _)
        for discarded in cancelled do b.cancel discarded
        let pending ← b.pendingTxids
        for tx in m.block.transactions do
          if pending.contains tx.txid then b.markConfirmed tx.txid m.height
      -- the open wallet alone, for its own range scans below (cards, accounts made during the pass)
      let applyOpen : BlockMatch → NetM Unit := fun m => do
        unless openIn do return
        let effect ← env.walletWriteNet serial "sync.apply" (w.apply m)
        for coin in effect.received do
          if let some card := coin.card then
            discard <| ((env.hooks.cardPayment card (Winnow.displayHex coin.txid) : IO Unit)).toBaseIO
        for discarded in effect.discardedReplacements do b.cancel discarded
        for discarded in ← (env.hooks.multisigApply m net : IO _) do b.cancel discarded
      -- a reorg: every wallet of the pass, its accounts, then the relay
      let onReorg : UInt32 → NetM Unit := fun fork => do
        (env.withPlaceLock do
          if let some d := network then writeAtomic (dirFile d rollbackMarkerName) (toString fork).toUTF8
          for p in joined do
            unless ← current p do continue
            match p.rider with
            | none =>
              env.walletWrite serial "sync.rollBack" (w.rollBack fork)
              env.hooks.multisigRollBack fork
            | some r =>
              try
                env.riderWrite r.serial "sync.rollBack" (r.wallet.rollBack fork)
                r.multisig.rollBack fork
              catch e =>
                dropped.modify (·.push r.serial)
                env.journal "sync.walletSetAside" [("walletID", r.held.id), ("error", toString e)] : IO Unit)
        -- reactivates any own send whose confirming block fell (#157)
        b.rollBack fork
      -- a wallet whose state came from elsewhere names a block this chain must have, checked once the headers
      -- are in: one that does not goes back on its own and joins again at the next pass
      let afterHeaders : NetM (Option UInt32) := do
        -- the chain has its new blocks: what another device scanned of them is taken before any is scanned here
        if maxBlocks.isNone then
          try (env.hooks.headStart : IO Unit) catch _ => pure ()
        for p in joined do
          let some fork ← (walletAnchorFork p.wallet s.chain : IO _) | continue
          env.journal "sync.anchorMismatch" [("fork", toString fork), ("walletID", p.wallet.id)]
          (env.withPlaceLock do
            unless ← current p do return
            write p "sync.anchorRollBack" (p.wallet.rollBack fork)
            p.multisig.rollBack fork : IO Unit)
          match p.rider with
          | some r => dropped.modify (·.push r.serial)
          | none => dropped.modify (·.push 0)
        return none
      -- every wallet here past the scan (each took another device's state): the scan begins where they all are
      let forwardTo : NetM (Option UInt32) := do
        let c ← (env.get : IO Core)
        let mut lowest : Option UInt32 := none
        for pw in c.wallet.toArray ++ c.riders.map (·.wallet) do
          let next ← (pw.nextScanHeight : IO UInt32)
          lowest := some (match lowest with | some l => min l next | none => next)
        if let some low := lowest then
          if low > (← f.nextScanHeight) then env.journal "sync.frontierJumped" [("to", toString low)]
        return lowest
      f.sync scripts (maxBlocks := maxBlocks) (onReorg := some onReorg) (onMatch := applyAll) (afterHeaders := some afterHeaders)
        (forwardTo := some forwardTo)
      let scanned ← f.nextScanHeight
      for p in joined do
        if ← isDropped p then continue
        if ← current p then (record p scanned : IO Unit)
      -- An account made or joined while this pass ran is not among the scripts it began with, and the pass has
      -- moved the frontier past the blocks it scanned: a payment to the account that one of them confirmed
      -- would never be looked for again. Those blocks are scanned once more, for the scripts the pass did not
      -- have, before anything else. A block before the pass began cannot pay an account that did not exist.
      -- What does not finish now (a peer, a limit) is owed, and done for every account's scripts at the next
      -- pass. Applying a block to the accounts again changes nothing for what they already hold.
      if openIn then
        let owed := (← env.get).accountRescanFrom
        let nowScripts ← match ← (env.hooks.multisigWatchScripts net : IO _) with
          | .ok xs => pure xs
          | .error _ => pure multisigScripts
        let known : Std.HashSet ByteArray := multisigScripts.foldl (·.insert ·) {}
        let fresh := nowScripts.filter (!known.contains ·)
        let lowest : Option UInt32 := match owed, (if fresh.isEmpty || scanned ≤ began then none else some began) with
          | some a, some b => some (min a b)
          | some a, none => some a
          | none, b => b
        if let some low := lowest then
          if scanned > low then
            let again := if owed.isSome then nowScripts else fresh
            let applyAccounts : BlockMatch → NetM Unit := fun m => do
              for discarded in ← (env.hooks.multisigApply m net : IO _) do b.cancel discarded
            -- what a run does not finish is owed from where it got, not from where it began: a range longer than
            -- one run can take (a slow link, a long pass) is otherwise begun again at every pass, and never done
            let (done, owedFrom) ← match ← (f.scanRange low (scanned - 1) again (limits := arrivingScanLimits) (onMatch := applyAccounts) (stopAtCaps := true)).attempt with
              | .ok outcome => pure (outcome.isComplete, (outcome.scannedThrough.map (· + 1)).getD low)
              | .error e =>
                env.journal "multisig.rescanWaiting" [("from", toString low), ("error", e.name)]
                pure (false, low)
            if done then env.journal "multisig.rescanned" [("from", toString low), ("through", toString (scanned - 1)), ("scripts", toString again.size)]
            else env.journal "multisig.rescanOwed" [("from", toString owedFrom), ("through", toString (scanned - 1))]
            env.modify fun c => if c.walletSerial == serial then { c with accountRescanFrom := if done then none else some (max low owedFrom) } else c
        -- a restored wallet's search for cards, once the scan is at the tip. What it cannot do now it does on a
        -- later pass, and it is never why a pass fails
        if (← w.cardRestoreFrom).isSome && (← f.nextScanHeight) > (← s.chain.height) then
          match ← (finishCardRestore env w f (← s.chain.startHeight) serial applyOpen).attempt with
          | .ok () => pure ()
          | .error e => env.journal "cards.restoreWaiting" [("error", e.name)]
      b.pruneConfirmed (← f.nextScanHeight)
      if let some d := network then (finishRollback d : IO Unit)
    match ← pass.attempt with
    | .ok () =>
      -- the scan reached the tip: when it did is what Settings → Network → Sync shows
      let complete := (← f.nextScanHeight) > (← s.chain.height)
      let now ← unixNow
      let current ← env.modifyGet fun c =>
        if c.generation == gen && !openOut then
          (true, { c with lastSyncError := none, transientSyncFailures := 0, transientSyncError := none,
                          lastCompleteCheck := if complete then some now else c.lastCompleteCheck })
        else (false, c)
      if complete && current then
        if let some d := network then
          try IO.FS.writeFile (lastCompleteCheckPath d) (toString now) catch _ => pure ()
      return complete && !openOut
    | .error e =>
      let scanned ← f.nextScanHeight
      for p in joined do
        if ← isDropped p then continue
        try if ← current p then record p scanned catch _ => pure ()
      -- a suspend, network switch or expired background check ended this generation, or the wallet was erased or
      -- replaced: nothing failed
      let transient := isTransientSyncError e
      env.modify fun c => if c.generation == gen && c.walletSerial == serial then
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
