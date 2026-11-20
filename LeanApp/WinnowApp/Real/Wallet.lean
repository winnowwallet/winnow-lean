import WinnowApp.Real.Stack
import WinnowApp.Real.RecordsSeal

/-! # The wallet's lifecycle and the UI snapshot

AppModel.swift: `boot` / `openPersistedWallet` (:470, :535), `switchNetwork` (:2507: here, opening
another network's directory), `refresh` (:1033), `creationHeightForNewWallet` (:1095), `createWallet`
(:1115), `importWallet` (:1148), `exportWalletBundle` (:1215), `adopt` (:1247), `finishOnboarding`
(:1319), `revealMnemonic` (:1366), `destroyWallet` (:1393), `waitForPeer` (:1445),
`currentReceiveAddress` / `freshReceiveAddress` (:1459, :1468). -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

/-- How long a switch to another place waits for a sync pass in flight to end. -/
def switchWaitMs : Nat := 5_000

/-- Whether another wallet file on this device, on any network and in any slot, is the wallet `id`. The
Keychain names a wallet's secret by its id alone, which is the master key's fingerprint and says nothing of
the network or the slot: one phrase on mainnet and on signet is one item. The places looked in are this
wallet's network directory and, beside it, the directories named for a network. A wallet file that does not
read counts as one, since a key is not deleted on a guess. -/
def secretInUseElsewhere (env : Env) (dir id : String) : IO Bool := do
  let real (path : String) : IO String := do
    try pure (← IO.FS.realPath (System.FilePath.mk path)).toString catch _ => pure path
  let network := networkDirOf dir
  let beside := match (System.FilePath.mk network).parent with
    | some root => [WinnowApp.Network.mainnet, .signet, .regtest].map fun n => (root / n.name).toString
    | none => []
  let here ← real dir
  let mut looked : List String := []
  for place in network :: beside do
    unless ← (System.FilePath.mk place).isDir do continue
    let place' ← real place
    if looked.contains place' then continue
    looked := place' :: looked
    for slot in ← listSlots place do
      let other := slotDir place slot
      if (← real other) == here then continue
      match ← (Wallet.open (walletPath other) env.deps.keyStore env.deps.random).run with
      | .ok w => if w.id == id then return true
      | .error _ => return true
  return false

/-- The wallets kept for a network, the network's own directory first: each slot's file opened, without its
key, for its id, account key and birthday. A file that does not read is left out here (it is shown as damaged
when it is opened). -/
def heldWalletFiles (env : Env) (networkDir : String) : IO (Array (HeldWallet × Wallet)) := do
  let mut held : Array (HeldWallet × Wallet) := #[]
  for slot in ← listSlots networkDir do
    let dir := slotDir networkDir slot
    match ← (Wallet.open (walletPath dir) env.deps.keyStore env.deps.random).run with
    | .ok w =>
      let s ← w.state
      let name := ((← readProfileName dir).map (·.1)).getD ""
      held := held.push ({ id := w.id, slot, dir, accountKey := w.accountKey,
                           birthday := min s.creationHeight s.nextScanHeight, name }, w)
    | .error _ => pure ()
  return held

def heldWallets (env : Env) (networkDir : String) : IO (Array HeldWallet) := do
  return (← heldWalletFiles env networkDir).map (·.1)

/-- `Core.held` read again from the files, and the riders made from them: every held wallet but the place
that is current, each with its own account store, scanned for in every pass beside the open wallet. After a
wallet is opened, adopted or deleted. Nothing is installed if the place changed meanwhile. -/
def refreshHeld (env : Env) : IO Unit := do
  let c ← env.get
  let (some dir, some n) := (c.dir, c.network) | env.modify fun c => { c with held := #[], riders := #[] }
  let files ← heldWalletFiles env (networkDirOf dir)
  let mut made : Array (HeldWallet × Wallet × ProfileMultisig) := #[]
  for (h, w) in files do
    if h.dir == dir then continue
    made := made.push (h, w, ← env.hooks.multisigAt n h.dir)
  env.withWalletLock <| env.modify fun c =>
    if c.dir != some dir || c.network != some n then c else
    let riders := made.mapIdx fun i (h, w, multisig) => ({ held := h, wallet := w, serial := c.riderSerial + i + 1, multisig } : Rider)
    { c with held := files.map (·.1), riders, riderSerial := c.riderSerial + made.size + 1 }

/-- `Backend.wallets`. -/
def wallets (env : Env) (networkDir : String) : IO (List WalletSummary) := do
  let c ← env.get
  return (← heldWallets env networkDir).toList.map fun h =>
    { id := h.id, slot := h.slot, active := c.wallet.isSome && c.dir == some h.dir, name := h.name }

/-- The longest name a wallet takes, in bytes. -/
def maximumWalletNameBytes : Nat := 64

/-- `Backend.renameWallet`: the open wallet's name, stamped now, so the latest any device gave it wins. -/
def renameWallet (env : Env) (name : String) : IO Unit := do
  let c ← env.get
  let (some _, some dir) := (c.wallet, c.dir) | failWith .noWallet
  let some name := Winnow.DisplayName.normalized name | failText "A name is one line of text."
  unless !name.isEmpty && name.utf8ByteSize ≤ maximumWalletNameBytes do failText "A name is one short line of text."
  writeProfileName dir name ((← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat)
  refreshHeld env

/-- The network's directory becomes current; another network or directory first ends the old one
(`switchNetwork`: stop, drop the wallet, nothing carried over). -/
def switchTo (env : Env) (n : WinnowApp.Network) (dir : String) : IO Unit := do
  let c ← env.get
  if c.network == some n && c.dir == some dir then return
  -- another wallet of the same network: the peers, the chain and the scan are the network's and stay; the open
  -- wallet changes between two blocks of a pass, which from then on writes to neither (`walletSerial`, and
  -- the riders, made again once the next one is open)
  if c.network == some n && c.dir.map networkDirOf == some (networkDirOf dir) && c.stack.isSome then
    env.withPlaceLock do
      env.hooks.walletChanged
      env.withWalletLock <| env.modify fun c =>
        { (c.withWallet none) with dir := some dir, riders := #[], reviews := #[], bumps := #[], lastSyncError := none,
                                   relayStoreQuarantined := none, transientSyncFailures := 0, transientSyncError := none }
    env.journal "wallet.switched" [("slot", slotOf dir)]
    return
  suspendAndStop env false
  -- a pass in flight still calls the stores of the place it began in (an account's coins, a card's payment):
  -- it is let finish, or run out of the peers just stopped, before those stores are pointed elsewhere. Its
  -- writes to the wallet itself are refused either way (`walletSerial`)
  discard <| env.sleepWhile switchWaitMs (·.syncing)
  env.hooks.walletChanged
  let checked ← readLastCompleteCheck (networkDirOf dir)
  env.withWalletLock <| env.modify fun c =>
    { (c.withWallet none) with network := some n, dir := some dir, reviews := #[], bumps := #[],
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

/-- A wallet is open in `dir`: it is the one to open next time, and the wallets kept beside it are read. The
pointer is written only now, so a wallet that failed to open is never the one a launch goes back to. -/
def walletOpened (env : Env) (dir : String) : IO Unit := do
  let network := networkDirOf dir
  -- one wallet in the network's own directory needs no pointer: an install that never adds one never has it
  if slotOf dir != "" || (← (activeSlotPath network).pathExists) then
    try writeActiveSlot network (slotOf dir) catch _ => pure ()
  refreshHeld env

/-- A `String` as Swift's `debugDescription` quotes it (inside `String(describing:)` of an enum payload). -/
def swiftQuoted (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t" | '\x00' => "\\0"
    | c => if c.toNat < 0x20 || c.toNat == 0x7F then s!"\\u\{{String.mk (Nat.toDigits 16 c.toNat)}}" else c.toString) ++ "\""

/-- `String(describing: error)` of a `KeyStoreError`, as the journal records it (backend-test `refusalsFlow`: a
protection upgrade that fails as the wallet opens). -/
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
  if let some w := (← env.get).wallet then
    walletOpened env dir
    return ← bootResult dir w.id
  let path := walletPath dir
  if !(← path.pathExists) then
    -- an empty place (a new install, or a wallet about to be added): the wallets beside it are still read
    refreshHeld env
    return .missing
  match ← (Wallet.open path env.deps.keyStore env.deps.random).run with
  | .error _ => return .damaged damagedWalletText
  | .ok w =>
    let installed ← env.withWalletLock <| env.modifyGet fun c =>
      if c.dir == some dir && c.wallet.isNone then (true, c.withWallet (some w)) else (false, c)
    if !installed then
      if let some w' := (← env.get).wallet then
        walletOpened env dir
        return ← bootResult dir w'.id
    -- `upgradeKeyProtection`: best effort, attributes only
    match ← (env.deps.keyStore.upgradeProtection w.id).run with
    | .ok true => env.journal "keychain.protectionUpgraded" [("walletID", w.id)]
    | .ok false => pure ()
    | .error e => env.journal "keychain.protectionUpgradeFailed" [("walletID", w.id), ("error", keyStoreErrorDescribing e)]
    walletOpened env dir
    return ← bootResult dir w.id

/-- `Backend.personPresent`: a search for cards that has no search key (one begun by a build that read the
wallet's secret in every round) keeps one now, while the secret can be read, so that its rounds in sync
passes go on. A wallet with no such search reads nothing. -/
def personPresent (env : Env) : IO Unit := do
  -- the records' keys a build put behind the person's presence come out from behind it now, while it is
  -- satisfied, and the stores sealed with them are read again
  let moved ← RecordsReal.repairRefusedStoreKeys env.deps.keyStore
  unless moved.isEmpty do
    env.journal "keychain.storeKeysMoved" [("accounts", ",".intercalate moved)]
    let c ← env.get
    if let (some n, some dir) := (c.network, c.dir) then
      try discard <| env.hooks.configure n dir catch _ => pure ()
  let some w := (← env.get).wallet | return
  match ← (runWM w.keepCardSearchKeyIfWaiting).toBaseIO with
  | .ok true => env.journal "cards.searchKeyKept" [("walletID", w.id)]
  | .ok false => pure ()
  | .error e => env.journal "cards.searchKeyWaiting" [("error", toString e)]

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
  s := { s with recordsLocked := !(← RecordsReal.refusedStoreKeys.get).isEmpty }
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
def adopt (env : Env) (w : Wallet) (dir : String) (startSync : Bool) : IO Unit := do
  -- the files that go are the directory's the wallet was written in: were another place current by now (a
  -- switch while the wallet was made), they would be another wallet's
  unless (← env.get).dir == some dir do failWith .walletReplaced
  let (stack, n) ← env.modifyGet fun c =>
    ((c.stack, c.network), { c with loopToken := c.loopToken + 1, syncLoop := none })
  env.hooks.walletChanged
  -- the scan, the chain and the relay are the network's: they go with the wallet only when it is the only one
  -- there, and otherwise it joins the scan the others are at (`syncOnce`)
  let network := networkDirOf dir
  let alone := (← heldWallets env network).all (·.dir == dir)
  if alone then
    if let some s := stack then s.broadcaster.shutdown
    for name in sharedStackFiles do removeQuietly (dirFile network name)
  for name in walletOwnFiles do removeQuietly (dirFile dir name)
  if let some n := n then
    if let some message ← env.hooks.configure n dir then failWith (.storageDamaged message)
  env.withWalletLock <| env.modify fun c => { (c.withWallet (some w)) with stack := none, reviews := #[], bumps := #[] }
  walletOpened env dir
  if let some existing := stack then
    if (← existing.chain.startHeight) > (← w.nextScanHeight) then
      -- the windows watch the pool that stops here
      let windows ← env.modifyGet fun c =>
        (c.receiveWindow.toList ++ c.relayWindows.toList.map (·.2), { c with receiveWindow := none, relayWindows := #[] })
      for win in windows do win.close
      existing.pool.stop
      buildStackIfNeeded env
    else if alone || existing.filters.isNone then
      let filters ← runNet (FilterSyncIO.new existing.pool existing.chain (← w.nextScanHeight) (some (dirFile network "filters.json")))
      let broadcaster ← if alone then runNet (TxBroadcaster.new existing.pool (some (dirFile network "broadcast.json")))
        else pure existing.broadcaster
      let gen ← env.modifyGet fun c => (c.generation, { c with stack := some { existing with filters := some filters, broadcaster } })
      if alone then observeBroadcasterFailures env broadcaster gen
    else
      env.modify fun c => { c with stack := some existing }
  if startSync then startSyncLoop env

def readMnemonic (env : Env) (walletID : String) : IO (Option String) := do
  match ← (env.deps.keyStore.load walletID).run with
  | .ok (.mnemonic words) => return some words
  | .ok (.masterKey _) | .ok (.accountKey ..) => return none
  | .error e => failText e.errorDescription

/-- `createWallet()`: a fresh wallet dated at the chain tip, adopted; its id and recovery words (which go
only to the iCloud backup's preparation, never to a screen). -/
def createWallet (env : Env) (n : WinnowApp.Network) (dir : String) : IO (String × String) := do
  -- a new wallet never takes the place of one: its files would be written over the other's
  if ← holdsWallet dir then failWith .walletAlreadyHere
  switchTo env n dir
  buildStackIfNeeded env
  let some stack := (← env.get).stack | failWith .noStack
  let knownHeight ← creationHeightForNewWallet stack
  env.replacingWallet
  -- a pinned seed (test mode) is the first wallet's: one added beside it is another wallet, made from the
  -- same pin and its slot, so a run that adds a wallet is still the same run every time
  let entropy := match env.deps.entropy, slotOf dir with
    | some pinned, "" => some pinned
    | some pinned, slot => some ((sha256 (pinned ++ slot.toUTF8)).extract 0 16)
    | none, _ => none
  let w ← runWM (Wallet.create (Network.tx n) env.deps.keyStore (some (walletPath dir)) (entropy := entropy) (creationHeight := knownHeight)
    (random := env.deps.random))
  adopt env w dir true
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

/-- A restored wallet's payments no block has taken go back to the broadcaster (a restored phone's has none
of its own), at the rate each was sent at. -/
def relayRestoredPayments (env : Env) (w : Wallet) (b : TxBroadcaster) : IO Unit := do
  for p in (← w.state).pendingSends do
    let .ok tx := Transaction.decode p.rawTransaction | continue
    let vsize := TransactionBuilder.vsize tx
    let rate := if vsize > 0 && p.fee > 0 then some (Float.ofInt p.fee.toInt / vsize.toFloat) else none
    match ← (runNet (b.broadcast p.rawTransaction rate)).toBaseIO with
    | .ok txid => env.journal "transaction.restored" [("txid", Winnow.displayHex txid)]
    | .error e => env.journal "transaction.restoreFailed" [("txid", Winnow.displayHex tx.txid), ("error", toString e)]

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
  -- a wallet this device already keeps for this network, elsewhere than here, is not kept twice: the two
  -- would be one Keychain item with two histories. (Here itself is the wallet's own backup taken again.)
  let id ← runWM (Wallet.importedWalletID bundle)
  for h in ← heldWallets env (networkDirOf dir) do
    if h.id == id && h.dir != dir then failWith .walletAlreadyHeld
  env.journal "import.started" (bundleFields bundle)
  switchTo env n dir
  env.replacingWallet
  let w ← runWM (Wallet.importing bundle env.deps.keyStore (some (walletPath dir)) env.deps.random)
  -- cards made after this backup are not in it: the wallet records the ones it could have made, so the scan
  -- forward watches for them, and a sync pass looks further if one was paid (`finishCardRestore`). A backup
  -- without the phrase or a master key restores a wallet that cannot derive a card
  -- never why a restore fails: the wallet is already written
  -- the phrase the backup carries is the secret just stored: the Keychain is not asked for it back
  match ← (runWM (w.beginCardRestore (bundle.mnemonic.map .mnemonic))).toBaseIO with
  | .ok true =>
    env.journal "cards.restoreBegun" [("fromHeight", toString ((← w.cardRestoreFrom).getD 0)), ("cards", toString (← w.cards).size)]
  | .ok false => pure ()
  | .error e => env.journal "cards.restoreSkipped" [("error", toString e)]
  adopt env w dir false
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
    relayRestoredPayments env w stack.broadcaster
    let some filters := stack.filters | waiting "sync stack unavailable"
    stack.pool.start
    if !(← waitForPeer env stack.pool env.deps.importPeerWaitMs c.generation) then return ← waiting "public peers unavailable"
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
  if let some f := c.stack.bind (·.filters) then
    recordFrontier env c.walletSerial "export.recordScanHeight" w f
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

/-- `destroyWallet()`: networking down, the key first, then the per-wallet files (in the network's own
directory headers, peers, contacts and signers stay; an added wallet's directory goes whole). The wallet is
let go before its files go,
so a write through it still in flight (a sync pass) is refused rather than writing `wallet.json` back
(backend-test `oldWalletWritesFlow`). With `expected`, only that wallet is deleted: the one open may no
longer be the one the person was shown. The key stays while another wallet file on the device is the same
wallet (`secretInUseElsewhere`). -/
def deleteWallet (env : Env) (expected : Option String := none) : IO Unit := do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  if let some id := expected then
    unless w.id == id do failWith .walletReplaced
  let shared ← match c.dir with
    | some dir => secretInUseElsewhere env dir w.id
    | none => pure false
  -- stopped before the stores are told: a round or a pass of this wallet is over before they change
  suspendAndStop env false
  discard <| env.sleepWhile switchWaitMs (·.syncing)
  env.hooks.walletChanged
  if shared then env.journal "wallet.keyKept" [("walletID", w.id)]
  else
    match ← (env.deps.keyStore.delete w.id).run with
    | .ok () => pure ()
    | .error e => failText e.errorDescription
    -- what a restore kept for its search for cards goes with the wallet
    w.forgetCardSearchKey
  env.withWalletLock <| env.modify fun c =>
    { (c.withWallet none) with lastSyncError := none, relayStoreQuarantined := none, phase := .idle,
                               reviews := #[], bumps := #[] }
  if let some dir := c.dir then
    removeQuietly (walletPath dir)
    for name in walletOwnFiles do removeQuietly (dirFile dir name)
    -- the network's scan, chain and relay stay while another wallet is kept there
    let network := networkDirOf dir
    if (← heldWallets env network).isEmpty then
      for name in sharedStackFiles do removeQuietly (dirFile network name)
  if let (some n, some dir) := (c.network, c.dir) then
    if networkDirOf dir == dir then
      if let some message ← env.hooks.configure n dir then failWith (.storageDamaged message)
    else
      -- an added wallet's directory goes whole, with its contacts, signers, headers and peers; no place is
      -- current until a wallet is opened
      discardEmptySlot dir
      env.modify fun c => { c with dir := none }
  let network := c.dir.map networkDirOf
  env.modify fun c => { c with held := #[] }
  if let some network := network then
    let held ← heldWallets env network
    env.modify fun c => { c with held }
  env.journal "wallet.destroyed" [("walletID", w.id)]

/-! ## Receiving -/

/-- `currentReceiveAddress()` (peeked) or `freshReceiveAddress()` (marks it used, shows the next). -/
def receiveAddress (env : Env) (fresh : Bool) : IO String := do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  if fresh then discard <| env.walletWrite c.walletSerial "receive.fresh" w.freshReceiveAddress
  let address ← runWM (w.address .receive (← w.nextReceiveIndex))
  -- `currentReceiveAddress()` journals what it shows; `freshReceiveAddress()` does not
  unless fresh do env.journal "address.receive" [("address", address)]
  return address

end WinnowApp.Real
