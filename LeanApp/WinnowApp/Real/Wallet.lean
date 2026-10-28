import WinnowApp.Real.Stack

/-! # The wallet's lifecycle and the UI snapshot

AppModel.swift: `boot` / `openPersistedWallet` (:470, :535), `switchNetwork` (:2507: here, opening
another network's directory), `refresh` (:1033), `creationHeightForNewWallet` (:1095), `createWallet`
(:1115), `importWallet` (:1148), `exportWalletBundle` (:1215), `adopt` (:1247), `finishOnboarding`
(:1319), `revealMnemonic` (:1366), `destroyWallet` (:1393), `waitForPeer` (:1445),
`currentReceiveAddress` / `freshReceiveAddress` (:1459, :1468). -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

/-- The network's directory becomes current; another network or directory first ends the old one
(`switchNetwork`: stop, drop the wallet, nothing carried over). -/
def switchTo (env : Env) (n : WinnowApp.Network) (dir : String) : IO Unit := do
  let c ← env.get
  if c.network == some n && c.dir == some dir then return
  suspendAndStop env false
  env.hooks.walletChanged
  let checked ← readLastCompleteCheck dir
  env.modify fun c => { c with network := some n, dir := some dir, wallet := none, reviews := #[], bumps := #[],
                               lastSyncError := none, relayStoreQuarantined := none, phase := .idle,
                               transientSyncFailures := 0, transientSyncError := none, lastCompleteCheck := checked }

def damagedWalletText : String :=
  "Winnow found local wallet data but could not safely read it. The files and protected key were left untouched. Retry; if this continues, restore from a known-good wallet bundle or ask for help before changing anything."

/-- `DefaultsKey.backupPending(walletID)`: the legacy phrase-checklist flag (a file next to the wallet),
which earlier builds left from creation until the words were confirmed written down. Onboarding has no
checklist now (upstream 4228c6b): opening an existing wallet clears it. -/
def backupPendingPath (dir walletID : String) : System.FilePath := dirFile dir s!"backup-pending.{walletID}"

/-- `.opened`, clearing a legacy backup-pending flag (the wallet opens without a phrase checklist). -/
def bootResult (dir walletID : String) : IO BootResult := do
  removeQuietly (backupPendingPath dir walletID)
  return .opened walletID

/-- A `String` as Swift's `debugDescription` quotes it (inside `String(describing:)` of an enum payload). -/
def swiftQuoted (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t" | '\x00' => "\\0"
    | c => if c.toNat < 0x20 || c.toNat == 0x7F then s!"\\u\{{String.mk (Nat.toDigits 16 c.toNat)}}" else c.toString) ++ "\""

/-- `String(describing: error)` of a `KeyStoreError`, as the journal records it. -/
def keyStoreErrorDescribing : Keys.KeyStoreError → String
  | .notFound w => s!"notFound(walletID: {swiftQuoted w})"
  | .alreadyExists w => s!"alreadyExists(walletID: {swiftQuoted w})"
  | .malformedSecret => "malformedSecret"
  | .unsupportedSecretVersion label => s!"unsupportedSecretVersion({swiftQuoted label})"
  | .keychain status => s!"keychain({status})"

/-- `boot()` / `openPersistedWallet(at:)` for `dir`. -/
def openWallet (env : Env) (n : WinnowApp.Network) (dir : String) : IO BootResult := do
  switchTo env n dir
  if let some message ← env.hooks.configure n dir then return .damaged message
  if let some w := (← env.get).wallet then return ← bootResult dir w.id
  let path := walletPath dir
  if !(← path.pathExists) then return .missing
  match ← (Wallet.open path env.deps.keyStore env.deps.random).run with
  | .error _ => return .damaged damagedWalletText
  | .ok w =>
    let installed ← env.modifyGet fun c =>
      if c.dir == some dir && c.wallet.isNone then (true, { c with wallet := some w }) else (false, c)
    if !installed then
      if let some w' := (← env.get).wallet then return ← bootResult dir w'.id
    -- `upgradeKeyProtection`: best effort, attributes only
    match ← (env.deps.keyStore.upgradeProtection w.id).run with
    | .ok true => env.journal "keychain.protectionUpgraded" [("walletID", w.id)]
    | .ok false => pure ()
    | .error e => env.journal "keychain.protectionUpgradeFailed" [("walletID", w.id), ("error", keyStoreErrorDescribing e)]
    return ← bootResult dir w.id

/-! ## The snapshot -/

/-- One history row with its transaction decoded (what the payment screens read). -/
def historyItem (e : HistoryEntry) (owned : Std.HashSet ByteArray) (net : Tx.BitcoinNetwork) : HistoryItem :=
  let outputs : Option (List TxOut) := match e.transaction with
    | .ok (some tx) => some ((List.range tx.outputs.size).zip tx.outputs.toList |>.map fun (i, o) =>
        { index := i, address := AddressDecoder.address o.scriptPubKey net, script := hex o.scriptPubKey,
          amount := natOf o.value, ownedByWallet := owned.contains o.scriptPubKey })
    | _ => none
  { txid := Winnow.displayHex e.txid, height := e.height.toNat, received := e.received.toInt, spent := e.spent.toInt,
    fee := e.fee.map (·.toInt), replacedBy := e.replacedBy.map Winnow.displayHex, outputs,
    fundingAddresses := e.fundingScripts.toList.filterMap (AddressDecoder.address · net) }

/-- `FeePolicy.FloorAggregation`: how the connected peers' BIP133 floors become one. -/
inductive FloorAggregation where
  /-- the highest floor any connected peer reports -/
  | strictest
  /-- the lower median across the configured seats, a missing report counting as zero -/
  | seatMajority
  /-- the lowest floor any connected peer reports; none while a connected peer has not reported -/
  | mostLenient

/-- `feeFilterFloorSatPerVByte(aggregation:)` (sat/vB; feefilter is sat/kvB). -/
def feeFloor (pool : PeerPool) (aggregation : FloorAggregation := .seatMajority) : IO (Option Float) := do
  let mut reports : Array Float := #[]
  let mut unreported := 0
  for peer in ← pool.connectedPeers do
    match ← peer.feeFilter with
    | some f => reports := reports.push (f.toInt.toFloat / 1000)
    | none => unreported := unreported + 1
  return match aggregation with
    | .strictest => reports.foldl (fun acc r => some (max (acc.getD r) r)) none
    | .seatMajority => FeePolicy.seatMajorityFloor reports pool.peerCount
    | .mostLenient => if unreported > 0 then none else reports.foldl (fun acc r => some (min (acc.getD r) r)) none

/-- `feeFilterFloorSatPerVByte()` in thousandths of sat/vB: the seat majority (the floor a quote is priced
against; a lone peer's floor cannot set the wallet's). -/
def feeFloorMilli (pool : PeerPool) : IO (Option Nat) := do
  return (← feeFloor pool .seatMajority).map milliOf

/-- `journalSnapshotIfChanged()`: public facts only (txids, heights, counts),
journaled when they changed. `status.history` is the display order (`historyForDisplay`). -/
def journalSnapshotIfChanged (env : Env) (s : Status) : IO Unit := do
  let some w := (← env.get).wallet | return
  let history := historyForDisplay s.history
  let confirmed := (history.filter (·.height > 0)).map fun e => s!"{e.txid}@{e.height}"
  let pending := (history.filter fun e => e.height == 0 && e.replacedBy.isNone).map (·.txid)
  let replacements := history.filterMap fun e => e.replacedBy.map fun r => s!"{e.txid}>{r}"
  env.journalIfChanged "wallet.snapshot"
    [("walletID", w.id), ("balance", toString s.balance), ("utxoCount", toString s.utxoCount),
     ("historyCount", toString s.history.length), ("nextScanHeight", toString s.nextScanHeight),
     ("tipHeight", toString s.tipHeight), ("peerCount", toString s.peerCount),
     ("confirmedTransactions", ",".intercalate confirmed), ("pendingTransactions", ",".intercalate pending),
     ("replacements", ",".intercalate replacements)]
    (·.lastSnapshotFingerprint) fun c fp => { c with lastSnapshotFingerprint := fp }

/-- `refresh()`'s `Status`, with the phase as the ticker last stored it (re-read now). -/
def snapshot (env : Env) : IO (Status × SyncPhase) := do
  let phase ← updateSyncPhase env
  let c ← env.get
  let mut s : Status := {}
  if let some w := c.wallet then
    let st ← w.state
    -- `ownWatchScripts.union(ownedMultisigScripts)`: an account payment is not a recipient
    let multisigScripts ← try env.hooks.multisigOwnedScripts catch _ => pure #[]
    let owned : Std.HashSet ByteArray :=
      (((← (w.watchScripts).run).toOption.getD #[]) ++ multisigScripts).foldl (·.insert ·) {}
    let utxos := st.utxos
    s := { s with balance := (utxos.foldl (fun (a : Int64) (u : WalletUTXO) => a + u.amount) 0).toInt, utxoCount := utxos.size
                  history := st.history.toList.map (historyItem · owned w.network)
                  feeBumpable := (← w.feeBumpableTxids).toList.map Winnow.displayHex
                  nextScanHeight := st.nextScanHeight.toNat }
    -- the accounts' balance and the one Transactions list (wallet, accounts, transfers, drafts)
    let (accountsBalance, rows) ← try env.hooks.multisigSnapshot owned w.network s.history
      catch _ => pure (0, payments s.history [] [])
    s := { s with accountsBalance, payments := rows }
  if let some stack := c.stack then
    s := { s with peerCount := (← stack.pool.connectedPeers).size, tipHeight := (← stack.chain.height).toNat
                  feeFloorMilli := ← feeFloorMilli stack.pool }
    if let some f := stack.filters then s := { s with nextScanHeight := (← f.nextScanHeight).toNat }
  s := { s with syncing := c.syncing, lastSyncError := c.lastSyncError, relayStoreQuarantined := c.relayStoreQuarantined,
                activeGateways := c.activeGateways, discoveringGateways := c.discoveringGateways,
                transientSyncError := c.transientSyncError, transientSyncFailures := c.transientSyncFailures }
  if let some at_ := c.lastCompleteCheck then
    let now ← unixNow
    s := { s with lastCheckedAgo := some (relativeAgo (now - at_)) }
  journalSnapshotIfChanged env s
  return (s, phase)

/-! ## Creating, adopting, importing -/

/-- `creationHeightForNewWallet()`: the best advertised tip less 500, never below the local tip. -/
def creationHeightForNewWallet (s : Stack) : IO UInt32 := do
  let localTip ← s.chain.height
  let mut advertised : UInt32 := 0
  for peer in ← s.pool.connectedPeers do
    let h ← peer.peerStartHeight
    if h > 0 && h.toInt.toNat.toUInt32 > advertised then advertised := h.toInt.toNat.toUInt32
  let margin : UInt32 := 500
  let peerBirthday := if advertised > margin then advertised - margin else 0
  return max localTip peerBirthday

/-- `adopt(wallet:startSync:)`: the previous wallet's chain-facing files go; an existing stack gets
new filters and a new broadcaster (or is rebuilt from genesis when the wallet is older than it). -/
def adopt (env : Env) (w : Wallet) (startSync : Bool) : IO Unit := do
  let (stack, dir, n) ← env.modifyGet fun c =>
    ((c.stack, c.dir, c.network), { c with loopToken := c.loopToken + 1, syncLoop := none })
  let some dir := dir | failWith .noWallet
  env.hooks.walletChanged
  if let some s := stack then s.broadcaster.shutdown
  for name in ["filters.json", "broadcast.json", "vaults.json", "multisig.json", "receive-labels.json", "cloud-backup.json"] do
    removeQuietly (dirFile dir name)
  if let some n := n then
    if let some message ← env.hooks.configure n dir then failWith (.storageDamaged message)
  env.modify fun c => { c with wallet := some w, stack := none, reviews := #[], bumps := #[] }
  if let some existing := stack then
    if (← existing.chain.startHeight) > (← w.nextScanHeight) then
      -- the windows watch the pool that stops here
      let windows ← env.modifyGet fun c =>
        (c.receiveWindow.toList ++ c.relayWindows.toList.map (·.2), { c with receiveWindow := none, relayWindows := #[] })
      for win in windows do win.close
      existing.pool.stop
      buildStackIfNeeded env
    else
      let filters ← runNet (FilterSyncIO.new existing.pool existing.chain (← w.nextScanHeight) (some (dirFile dir "filters.json")))
      let broadcaster ← runNet (TxBroadcaster.new existing.pool (some (dirFile dir "broadcast.json")))
      let gen ← env.modifyGet fun c => (c.generation, { c with stack := some { existing with filters := some filters, broadcaster } })
      observeBroadcasterFailures env broadcaster gen
  if startSync then startSyncLoop env

def readMnemonic (env : Env) (walletID : String) : IO (Option String) := do
  match ← (env.deps.keyStore.load walletID).run with
  | .ok (.mnemonic words) => return some words
  | .ok (.masterKey _) | .ok (.accountKey ..) => return none
  | .error e => failText (keyStoreErrorText e)

/-- `createWallet()`: a fresh wallet dated at the chain tip, adopted; its id and recovery words (which go
only to the iCloud backup's preparation, never to a screen). -/
def createWallet (env : Env) (n : WinnowApp.Network) (dir : String) : IO (String × String) := do
  switchTo env n dir
  buildStackIfNeeded env
  let some stack := (← env.get).stack | failWith .noStack
  let knownHeight ← creationHeightForNewWallet stack
  let w ← runWM (Wallet.create (Network.tx n) env.deps.keyStore (some (walletPath dir)) (entropy := env.deps.entropy) (creationHeight := knownHeight)
    (random := env.deps.random))
  adopt env w true
  let some words ← readMnemonic env w.id | failWith .mnemonicUnavailable
  env.journal "wallet.created" [("walletID", w.id), ("height", toString knownHeight), ("headersContinueInBackground", "true")]
  return (w.id, words)

/-- `finishOnboarding()`: wallet usability is independent of cloud availability or a manual backup. -/
def finishOnboarding (env : Env) : IO Unit := do
  let c ← env.get
  if let (some dir, some w) := (c.dir, c.wallet) then
    let p := backupPendingPath dir w.id
    let wasBackupPending ← p.pathExists
    if wasBackupPending then IO.FS.removeFile p
    env.journal (if wasBackupPending then "backup.completed" else "import.onboardingCompleted") [("walletID", w.id)]
    let (s, _) ← snapshot env
    env.journal "wallet.ready" [("walletID", w.id), ("balance", toString s.balance), ("utxoCount", toString s.utxoCount),
      ("historyCount", toString s.history.length), ("nextScanHeight", toString s.nextScanHeight)]

/-- `waitForPeer(timeout:)`, polling once a second. -/
def waitForPeer (env : Env) (pool : PeerPool) (ms : Nat) (gen : Nat) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if (← env.get).generation != gen then return false
    if (← pool.randomPeer).isSome then return true
    IO.sleep 1000
  return false

/-- The verification report as OnboardingView lays it out. -/
def reportText (r : ImportReport) : String :=
  let lines := [s!"Scanned from block {r.scannedFromHeight}"] ++
    (match r.scannedToHeight with | some h => [s!"Scanned to block {h}"] | none => []) ++
    [s!"Claimed UTXOs confirmed: {r.confirmedUTXOs.size}", s!"Claimed but spent since: {r.spentSinceBundle.size}",
     s!"Discovered since bundle: {r.discoveredUTXOs.size}"] ++
    (if r.matchesBundle then [] else
      ["Some claimed UTXOs were already spent — the bundle was stale or wrong. The chain won; check the report above."])
  "\n".intercalate lines

/-- What the app shows when `importWallet` returns no report (no peer yet). -/
def verificationWaitingText : String :=
  "Imported. Verification is waiting for Bitcoin peers; the regular sync checks the same blocks once Winnow connects."

/-- A `ScanSource` over the stack's filter sync (`verifyImport(_:using:)`). -/
def scanSource (f : FilterSyncIO) : ScanSource where
  nextScanHeight := f.nextScanHeight
  lastScannedHeight := f.lastScannedHeight
  sync scripts cb := NetM.toWM (f.sync scripts (onMatch := fun m => WM.toNet (cb m)))

/-- What `import.started` and `wallet.exported` say of a bundle (never its phrase). -/
def bundleFields (b : ImportBundle) : List (String × String) :=
  [("bundleVersion", toString b.version), ("seedBearing", toString b.mnemonic.isSome),
   ("lastKnownHeight", toString b.lastKnownHeight), ("utxoCount", toString b.utxos.size),
   ("historyCount", toString b.transactions.size)]

/-- `importWallet(bundle:authenticate:afterCommit:)`: check, seed the wallet, adopt it without the loop,
run `afterCommit` (the iCloud backup's preparation, or a restore's context), then verify by a forward scan
(the loop starts on the way out). The report, or none while no peer was reachable. -/
def importDecoded (env : Env) (n : WinnowApp.Network) (dir : String) (bundle : ImportBundle)
    (afterCommit : String → IO Unit := fun _ => pure ()) : IO (String × Option ImportReport) := do
  unless bundle.network == n.name do failWith (.wrongNetwork bundle.network)
  -- before anything is written: a bundle whose multisig accounts cannot be restored must not replace the
  -- wallet half-way
  env.hooks.multisigValidate (bundle.vaults.getD #[]) (Network.tx n)
  env.hooks.signerValidate (bundle.signers.getD #[]) (Network.tx n)
  env.journal "import.started" (bundleFields bundle)
  switchTo env n dir
  let w ← runWM (Wallet.importing bundle env.deps.keyStore (some (walletPath dir)) env.deps.random)
  adopt env w false
  env.hooks.multisigRestore (bundle.vaults.getD #[])
  env.hooks.signerMerge (bundle.signers.getD #[])
  try
    afterCommit w.id
    buildStackIfNeeded env
    let c ← env.get
    let waiting (reason : String) : IO (String × Option ImportReport) := do
      env.journal "import.verificationWaiting" [("reason", reason)]
      return (w.id, none)
    let some stack := c.stack | waiting "sync stack unavailable"
    let some filters := stack.filters | waiting "sync stack unavailable"
    stack.pool.start
    if !(← waitForPeer env stack.pool 60_000 c.generation) then return ← waiting "public peers unavailable"
    let additional ← env.hooks.multisigWatchScripts (Network.tx n)
    let report ← runWM (w.verifyImport bundle (scanSource filters) additional fun m => do
      discard <| WM.io (env.hooks.multisigApply m (Network.tx n)))
    -- `await refresh()`, then the journal reads the refreshed status
    let (s, _) ← snapshot env
    env.journal "import.verified"
      [("scannedFromHeight", toString report.scannedFromHeight),
       ("scannedToHeight", (report.scannedToHeight.map toString).getD "waiting"),
       ("matchesBundle", toString report.matchesBundle),
       ("confirmedUTXOCount", toString report.confirmedUTXOs.size),
       ("spentSinceBundleCount", toString report.spentSinceBundle.size),
       ("discoveredUTXOCount", toString report.discoveredUTXOs.size),
       ("balance", toString s.balance), ("utxoCount", toString s.utxoCount),
       ("historyCount", toString s.history.length), ("nextScanHeight", toString s.nextScanHeight)]
    return (w.id, some report)
  finally
    startSyncLoop env

/-- `importWallet(bundleJSON:)`: the wallet's id, and the verification report as the import sheet shows it. -/
def importBundle (env : Env) (n : WinnowApp.Network) (dir : String) (json : String)
    (afterCommit : ImportBundle → String → IO Unit := fun _ _ => pure ()) : IO (String × String) := do
  let bundle ← match ImportBundle.decode json with
    | .ok b => pure b
    | .error e => failText (importFailureText e)
  let (id, report) ← importDecoded env n dir bundle (afterCommit bundle)
  return (id, (report.map reportText).getD verificationWaitingText)

/-- `exportWalletBundle(includeMnemonic:)`. -/
def exportBundle (env : Env) (includeMnemonic : Bool) : IO String := do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  if let some f := c.stack.bind (·.filters) then env.walletOp (w.recordScanHeight (← f.nextScanHeight))
  let b ← runWM (w.exportBundle includeMnemonic)
  let accounts ← env.hooks.multisigBackup
  let signers ← env.hooks.signerBackup
  let b := { b with vaults := if accounts.isEmpty then none else some accounts,
                    signers := if signers.isEmpty then none else some signers }
  let serialized := b.serialized
  env.journal "wallet.exported" (bundleFields b)
  return serialized

/-- `revealMnemonic()` (after authentication in `perform`). -/
def revealMnemonic (env : Env) : IO (List String) := do
  let some w := (← env.get).wallet | failWith .noWallet
  let some words ← readMnemonic env w.id | failText WalletError.mnemonicUnavailable.description
  return words.splitOn " "

/-- `destroyWallet()`: networking down, the key first, then the per-wallet files (headers and peers stay). -/
def deleteWallet (env : Env) : IO Unit := do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  env.hooks.walletChanged
  suspendAndStop env false
  match ← (env.deps.keyStore.delete w.id).run with
  | .ok () => pure ()
  | .error e => failText (keyStoreErrorText e)
  if let some dir := c.dir then
    for name in ["wallet.json", "filters.json", "broadcast.json", "vaults.json", "multisig.json", "receive-labels.json", "cloud-backup.json"] do
      removeQuietly (dirFile dir name)
  env.modify fun c => { c with wallet := none, lastSyncError := none, relayStoreQuarantined := none, phase := .idle,
                               reviews := #[], bumps := #[] }
  if let (some n, some dir) := (c.network, c.dir) then
    if let some message ← env.hooks.configure n dir then failWith (.storageDamaged message)
  env.journal "wallet.destroyed" [("walletID", w.id)]

/-! ## Receiving -/

/-- `currentReceiveAddress()` (peeked) or `freshReceiveAddress()` (marks it used, shows the next). -/
def receiveAddress (env : Env) (fresh : Bool) : IO String := do
  let some w := (← env.get).wallet | failWith .noWallet
  if fresh then discard <| env.walletOp w.freshReceiveAddress
  let address ← runWM (w.address .receive (← w.nextReceiveIndex))
  -- `currentReceiveAddress()` journals what it shows; `freshReceiveAddress()` does not
  unless fresh do env.journal "address.receive" [("address", address)]
  return address

end WinnowApp.Real
