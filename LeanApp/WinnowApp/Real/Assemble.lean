import WinnowApp.Real.BackgroundSync

/-! # `Backend.real`: the core half of AppModel behind the `Backend` record

Every field is one AppModel method (file:line in each `Real/*` module's doc). The people and label
fields stay `notPorted` here (the records half plugs them in over this backend, through `Deps.hooks`
for what the core itself needs). -/

namespace WinnowApp
open Winnow Winnow.IO

namespace Real

/-- What a test can observe of the backend beyond its fields: loop threads alive, sync passes
started, phase ticks, and whether a stack is up. -/
structure Diagnostics where
  liveLoops : Nat
  syncPasses : Nat
  phaseTicks : Nat
  hasStack : Bool
  syncing : Bool
  active : Bool
  deriving Repr

def Env.diagnostics (env : Env) : IO Diagnostics := do
  let c ← env.get
  return { liveLoops := c.liveLoops, syncPasses := c.syncPasses, phaseTicks := c.phaseTicks,
           hasStack := c.stack.isSome, syncing := c.syncing, active := c.active }

/-! What the records half reads of the core (its `RecordsCtx`): the open wallet and the routed HTTP
GET. -/

def Env.currentWallet (env : Env) : IO (Option Wallet) := do return (← env.get).wallet

/-- The current generation's routed client (cancelled on suspend). -/
def Env.httpGet (env : Env) (url : String) (maximumBytes : Nat) : IO ByteArray := do
  runNet ((← env.get).http.get url maximumBytes)

def Env.new (deps : Deps) : IO Env := do
  let http ← RoutedHTTPClient.new deps.fetch
  return { deps, core := ← Std.Mutex.new { http }, walletLock := ← Std.Mutex.new () }

def Env.backend (env : Env) : Backend :=
  { Backend.pending with
    openWallet := fun n dir => openWallet env n dir
    createWallet := fun n dir => do
      let (id, _) ← createWallet env n dir
      finishOnboarding env
      return id
    importBundle := fun n dir json => importBundle env n dir json
    finishOnboarding := finishOnboarding env
    updateSettings := fun s => env.modify fun c => { c with settings := some s }
    snapshot := snapshot env
    records := pure {}
    receiveAddress := fun fresh => receiveAddress env fresh
    watchAddress := fun address seen => watchAddress env address seen
    stopWatchingAddress := stopWatchingAddress env
    deleteWallet := deleteWallet env
    startNetworking := fun s => startNetworking env s
    stopNetworking := stopNetworking env
    syncNow := syncNow env
    retryPeers := retryPeers env
    reconnect := fun s => reconnect env s
    resolveFeeRate := fun priority milli => do return milliOf (← resolveRate env priority milli)
    previewSend := fun inputs => previewSend env inputs
    sendPayment := fun inputs p => sendPayment env inputs p
    rawTransactionHex := fun txid => rawTransactionHex env txid
    watchRelay := fun txid report => watchRelay env txid report
    loadPaymentDetails := fun txid => loadPaymentDetails env txid
    pendingFeeRate := fun txid => pendingFeeRate env txid
    previewFeeBump := fun txid milli => previewFeeBump env txid milli
    bumpFee := fun txid p => bumpFee env txid p
    catalogStatus := catalogStatus env
    connectedPeers := connectedPeers env
    resetPeers := resetPeers env
    exportBundle := fun withPhrase => exportBundle env withPhrase
    revealMnemonic := revealMnemonic env
    runBackgroundSync := fun s => runBackgroundSync env s
    cancelBackgroundSync := cancelBackgroundSync env }

end Real

/-- The core half alone over the injected capabilities, with its diagnostics handle (`Real/Full.lean`
adds the records half: `Backend.realWithEnv`). -/
def Backend.coreWithEnv (deps : Real.Deps) : IO (Backend × Real.Env) := do
  let env ← Real.Env.new deps
  return (env.backend, env)

end WinnowApp
