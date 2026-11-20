import WinnowApp.Real.CloudBackup
import WinnowApp.Real.CloudAppState
import WinnowApp.Real.Multisig
import Winnow.Wallet.DeviceSync

/-! # Accounts and signers that follow a person between devices: the app's side

Every device of a person keeps an encrypted backup in their iCloud (`CloudBackupController`): its wallet box
holds that device's multisig accounts and its signers, and the key that opens it travels in their iCloud
Keychain. A device keeps in step by reading the wallet boxes of the other backups on its network, deciding
what to take (`Winnow.DeviceSync`, the rules) and doing it to its own stores; its own next backup then carries
the result, with the stamps the other devices decide by (`CloudAppState.sync`).

Nothing is uploaded that a backup did not already hold, apart from those stamps. The recovery words' box is
never opened here: only the wallet box, for its accounts and signers (`CloudWalletBackup.shared`). So no key or phrase reaches a device by
this path, and a device whose wallet is another one sees an account of the first as watch-only.

There is no push: the shell has CloudKit's records and no subscriptions, so a device looks when it comes to
the foreground and then about once a minute while it is open (`SyncApp.start`, a loop of its own). A backup already read is not
downloaded again until its save date changes; one there was nothing to take from is remembered across
launches (`SyncView.settled`).

What this device has done with what it read is `device-sync.json` in the network's directory (`SyncView`), a
wallet's file like `multisig.json`, deleted with the wallet: the stamps of every account and signer it has or
knows removed, and the values those stamps were written for. Removals are written by the app's own Remove
(`noteAccountRemoved`, `noteSignerRemoved`) and by nothing else.

An account taken from another device arrives with that device's coins and history and is brought up to this
device's own scan before it is watched (`ArrivingAccount`, `MultisigApp.catchUp`). -/

namespace WinnowApp.Real
open Winnow Winnow.DeviceSync WinnowApp.RecordsReal SwiftJSON

/-- A signer under one name on every device: the compressed account public keys it holds, sorted. None for a
record whose keys do not read. -/
def signerKey (r : SignerRecord) (network : Tx.BitcoinNetwork) : IO (Option String) := do
  match ← (SignerStore.identities r.keys network).run with
  | .ok ids => return some ("+".intercalate ((ids.map hex).qsort (· < ·)).toList)
  | .error _ => return none

/-- What this device has done with what it read. -/
structure SyncView where
  /-- The wallet these are the accounts of; another wallet begins again. -/
  wallet : String
  /-- This device, as its stamps name it: a number drawn once. -/
  device : Nat
  /-- The latest time of any stamp seen or written. -/
  clock : Nat := 0
  accounts : Array AccountSeen := #[]
  signers : Array SignerSeen := #[]
  /-- Backups there was nothing to take from, by id and save date: not downloaded again until they change. -/
  settled : Array (String × Float) := #[]
  /-- Ledgers (master fingerprints) that came from another device and have not answered on this one. -/
  elsewhere : Array UInt32 := #[]
  deriving Inhabited

namespace SyncView

def fileName : String := "device-sync.json"
def maximumBytes : Nat := 4 * 1_024 * 1_024

def toJV (v : SyncView) : JV :=
  obj [("version", some (ofInt 1)), ("wallet", some (.str v.wallet)), ("deviceID", some (ofInt v.device)),
       ("clock", some (ofInt v.clock)), ("accounts", some (.arr (v.accounts.map AccountSeen.toJV))),
       ("signers", some (.arr (v.signers.map SignerSeen.toJV))),
       ("settled", some (.arr (v.settled.map fun (id, savedAt) => .arr #[.str id, ofDouble savedAt]))),
       ("elsewhere", some (.arr (v.elsewhere.map (ofInt ·.toNat))))]

def ofJV (v : JV) : D SyncView := do
  let kvs ← asObject v
  unless (← key kvs "version" asInt) == 1 do dataCorrupted
  let settled ← key kvs "settled" (asArray fun pair => do
    match pair with
    | .arr #[id, savedAt] => return (← asString id, ← asDouble savedAt)
    | _ => dataCorrupted)
  return { wallet := ← key kvs "wallet" asString, device := (← key kvs "deviceID" (intIn 0 (2 ^ 53))).toNat,
           clock := (← key kvs "clock" (intIn 0 (2 ^ 53))).toNat, accounts := ← key kvs "accounts" (asArray AccountSeen.ofJV),
           signers := ← key kvs "signers" (asArray SignerSeen.ofJV), settled,
           elsewhere := ← key kvs "elsewhere" (asArray asUInt32) }

def account? (v : SyncView) (id : String) : Option AccountSeen := v.accounts.find? (·.stamps.id == id)
def signer? (v : SyncView) (key : String) : Option SignerSeen := v.signers.find? (·.stamps.key == key)

def setAccount (v : SyncView) (e : AccountSeen) : SyncView :=
  match v.accounts.findIdx? (·.stamps.id == e.stamps.id) with
  | some i => { v with accounts := v.accounts.set! i e }
  | none => { v with accounts := v.accounts.push e }

def setSigner (v : SyncView) (e : SignerSeen) : SyncView :=
  match v.signers.findIdx? (·.stamps.key == e.stamps.key) with
  | some i => { v with signers := v.signers.set! i e }
  | none => { v with signers := v.signers.push e }

/-- What the backup carries: the stamps alone. Past `maximumEntries`, the oldest removals go first. -/
def published (v : SyncView) : SyncMeta :=
  let trim {α} (xs : Array α) (removed : α → Stamp) (isRemoved : α → Bool) : Array α :=
    if xs.size ≤ maximumEntries then xs else
      let kept := xs.filter (!isRemoved ·)
      let gone := (xs.filter isRemoved).qsort fun a b => removed b < removed a
      (kept ++ gone).extract 0 maximumEntries
  { device := v.device
    accounts := trim (v.accounts.map (·.stamps)) (·.removed) (·.isRemoved)
    signers := trim (v.signers.map (·.stamps)) (·.removed) (·.isRemoved) }

end SyncView

/-- Why another device's backup was not read in a round. -/
inductive Unread where
  /-- Its key has not arrived from iCloud Keychain: looked for again each round. -/
  | keyMissing
  /-- It does not open with its key, or is not a backup this build reads. It is not fetched again in this
  run of the app unless it is saved again. -/
  | notOpened
  /-- iCloud did not hand it over this time: fetched again next round. -/
  | notFetched
  deriving BEq, Inhabited

/-- How keeping in step stands, for Settings → Backup. -/
structure SyncStatus where
  /-- When the other devices' backups were last read (seconds since 1970). -/
  checkedAt : Option Nat := none
  /-- A round that failed as a whole, in its own words. -/
  message : Option String := none
  /-- The other backups iCloud listed in the last round. -/
  listed : Nat := 0
  /-- Those of them not read, each with when it was saved (seconds since 2001) and why. -/
  unread : Array (Float × Unread) := #[]
  /-- Accounts and signers in the backups read that are of a kind or a shape this build does not keep. -/
  skipped : Nat := 0
  deriving Inhabited

/-- At most this many other backups are read in a round, newest first. -/
def maximumSiblings : Nat := 50

structure SyncApp where
  controller : CloudBackupController
  env : Env
  multisig : MultisigApp
  /-- Never in test mode (`allowsCloudBackup`). -/
  allows : Bool
  /-- One reader or writer of `device-sync.json` at a time. -/
  lock : Std.Mutex Unit
  /-- The backups opened in this run of the app, by id and save date. -/
  opened : IO.Ref (Array (String × Float × Replica × Nat))
  /-- The backups that did not open in this run of the app, by id and save date: not fetched again in it. -/
  unopened : IO.Ref (Array (String × Float))
  /-- Moves when the wallet changes or goes (`reset`): what a round read before then is another wallet's. -/
  epoch : IO.Ref Nat
  running : IO.Ref Bool
  /-- When the last round began (monotonic milliseconds); none before the first. -/
  lastRound : IO.Ref (Option Nat)
  /-- A round at most this often while the app is open. -/
  intervalMs : Nat := 60_000
  /-- Milliseconds since 1970. -/
  nowMs : IO Nat
  status : IO.Ref SyncStatus
  /-- Called when a round changed something here (the backup is scheduled). -/
  changed : IO.Ref (IO Unit)
  /-- The foreground loop's token: a loop ends when it is no longer its own. Whether one is running. -/
  loop : IO.Ref Nat
  looping : IO.Ref Bool
  /-- The accounts and signers as they were when last stamped (`localMark`). -/
  noticed : IO.Ref (Option String)
  /-- The last line written to test mode's journal (`journalOnce`). -/
  journaled : IO.Ref (Option String)

namespace SyncApp

def unixMs : IO Nat := do
  return ((← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val / 1_000_000).toNat

def new (controller : CloudBackupController) (env : Env) (multisig : MultisigApp) (allows : Bool)
    (intervalMs : Nat := 60_000) : IO SyncApp := do
  return { controller, env, multisig, allows, lock := ← Std.Mutex.new (), opened := ← IO.mkRef #[], unopened := ← IO.mkRef #[], epoch := ← IO.mkRef 0,
           running := ← IO.mkRef false, lastRound := ← IO.mkRef none, intervalMs, nowMs := unixMs,
           status := ← IO.mkRef {}, changed := ← IO.mkRef (pure ()), loop := ← IO.mkRef 0, looping := ← IO.mkRef false, noticed := ← IO.mkRef none,
           journaled := ← IO.mkRef none }

def locked {α} (a : SyncApp) (body : IO α) : IO α :=
  a.lock.atomically (m := IO) (liftM body : Std.AtomicT Unit IO α)

/-- The open wallet's id, its network and its directory. -/
def place (a : SyncApp) : IO (Option (String × WinnowApp.Network × System.FilePath)) := do
  let c ← a.env.get
  match c.wallet, c.network, c.dir with
  | some w, some n, some dir => return some (w.id, n, System.FilePath.mk dir)
  | _, _, _ => return none

/-- The view of `wallet` in `dir`, and whether it is new: no file, another wallet's, or one that does not
read (a new view takes nothing for removed, so a lost file removes nothing). -/
def loadView (dir : System.FilePath) (wallet : String) : IO (SyncView × Bool) := do
  let path := dir / SyncView.fileName
  let read : IO (Option SyncView) := do
    unless ← path.pathExists do return none
    let data ← IO.FS.readBinFile path
    unless data.size ≤ SyncView.maximumBytes do return none
    let some text := String.fromUTF8? data | return none
    match decodeText text SyncView.ofJV with
    | .ok v => return if v.wallet == wallet then some v else none
    | .error _ => return none
  match ← (read.toBaseIO : BaseIO _) with
  | .ok (some v) => return (v, false)
  | _ =>
    let bytes ← IO.getRandomBytes 6
    return ({ wallet, device := bytes.foldl (fun n b => n * 256 + b.toNat) 0 }, true)

/-- Written with at most `maximumEntries` accounts and as many signers: past that, the oldest removals go. -/
def saveView (dir : System.FilePath) (v : SyncView) : IO Unit :=
  let kept := v.published
  let v := { v with accounts := v.accounts.filter fun e => kept.accounts.any (·.id == e.stamps.id)
                    signers := v.signers.filter fun e => kept.signers.any (·.key == e.stamps.key) }
  Winnow.IO.writeAtomic (dir / SyncView.fileName) (write v.toJV).toUTF8

/-- Whether the app's own Remove would take this account: every coin spent in a block, no payment awaiting
signatures, none in flight. -/
def removable (r : MultisigAccountRecord) : Bool :=
  r.allUtxos.all (fun u => u.spent.any (·.height.isSome)) && r.draft.isNone && r.inFlight.isEmpty

/-- This device's accounts and signers with their stamps brought up to what the person has done since the
view was written (`stampAccount`, `stampSigner`), and the view with them. -/
def stamped (a : SyncApp) (view : SyncView) (initial : Bool) (fresh : Stamp) :
    IO (SyncView × Array LocalAccount × Array LocalSigner) := do
  let store ← a.multisig.host.read
  let arriving ← a.multisig.host.arrivingAccounts
  let mut view := view
  let mut accounts : Array LocalAccount := #[]
  for r in store.records do
    let seen := stampAccount fresh initial (view.account? r.id) r
    view := view.setAccount seen
    accounts := accounts.push { record := r, seen, removable := removable r }
  for e in arriving do
    if store.records.any (·.id == e.record.id) then continue
    let seen := stampAccount fresh initial (view.account? e.record.id) e.record
    view := view.setAccount seen
    -- not yet watched here: nothing of it is this device's alone to lose
    accounts := accounts.push { record := e.record, seen, removable := true }
  let signerStore ← a.multisig.signers.read
  let mut signers : Array LocalSigner := #[]
  for r in signerStore.records do
    let some key ← signerKey r signerStore.network | continue
    let seen := stampSigner fresh initial (view.signer? key) key r
    view := view.setSigner seen
    signers := signers.push { key, record := r, seen }
  let answered ← a.multisig.answered.get
  view := { view with elsewhere := view.elsewhere.filter (!answered.contains ·) }
  return (view, accounts, signers)

private def sameView (a b : SyncView) : Bool := write a.toJV == write b.toJV

/-- The view read, brought up to date by `body` and written when it changed, under the lock. `body` gets a
stamp for now. Nothing happens without an open wallet, nor once the wallet has changed: `body` writes to
whichever wallet's stores are current, so it runs only while they are still those of the wallet it was
decided for (`since`, the epoch a round began in; the place, read again under the lock, which `reset` takes
before the stores are pointed elsewhere). -/
def withView {α} (a : SyncApp) (none' : α)
    (body : SyncView → (initial : Bool) → Stamp → IO (SyncView × α)) (latest : Nat := 0)
    (since : Option Nat := none) : IO α := do
  let some (wallet, network, dir) ← a.place | return none'
  let began := since.getD (← a.epoch.get)
  a.locked do
    unless (← a.epoch.get) == began && (← a.place) == some (wallet, network, dir) do return none'
    let (loaded, initial) ← loadView dir wallet
    let clock := max loaded.clock latest
    let fresh := Stamp.after clock (← a.nowMs) loaded.device
    let (view, result) ← body { loaded with clock } initial fresh
    -- nothing later may be stamped behind a stamp read or written here
    let view := { view with clock := max clock view.published.latest }
    if initial || !sameView view loaded then saveView dir view
    a.multisig.elsewhere.set view.elsewhere
    return result

/-- What this device's next backup says of its accounts and signers (`CloudAppState.sync`): the stamps, after
whatever the person did since. None without an open wallet, or while the stores cannot be read. -/
def publish (a : SyncApp) : IO (Option SyncMeta) := do
  let store ← a.multisig.host.read
  if store.isDamaged || store.unavailable || (← a.multisig.signers.read).isDamaged then return none
  a.withView none fun view initial fresh => do
    let (view, _, _) ← a.stamped view initial fresh
    return (view, some view.published)

/-- The app's Remove took this account: it is removed on the person's other devices too. -/
def noteAccountRemoved (a : SyncApp) (id : String) : IO Unit := do
  if !a.allows then return
  a.withView () fun view initial fresh => do
    let (view, _, _) ← a.stamped view initial fresh
    let entry := (view.account? id).getD { stamps := { id } }
    return (view.setAccount { entry with stamps := { entry.stamps with removed := fresh } }, ())

/-- The app's Remove took this signer (`key` as `signerKey` gave it before the removal). -/
def noteSignerRemoved (a : SyncApp) (key : String) : IO Unit := do
  if !a.allows then return
  a.withView () fun view initial fresh => do
    let (view, _, _) ← a.stamped view initial fresh
    let entry := (view.signer? key).getD { stamps := { key } }
    return (view.setSigner { entry with stamps := { entry.stamps with removed := fresh } }, ())

/-! ## Reading the other devices' backups -/

/-- Another device's backup as the rules read it, and how many of its accounts and signers were left
out: the key first (it is on this device or it is not, and asking costs nothing), then the record, then its
wallet box opened for its accounts and signers alone (`CloudWalletBackup.shared`, never the words' box, and
not a restore's reading: an older backup holding an account this build does not keep still gives the rest).
Each account and signer is held to the store's own rules, one that fails left out. The stamps are read from
the context by themselves. None when the backup is another network's. -/
def openReplica (a : SyncApp) (id account : String) (network : WinnowApp.Network) :
    IO (Except Unread (Option Replica × Nat)) := do
  let key ← match ← (a.controller.keys.load id).toBaseIO with
    | .ok k => pure k
    | .error e =>
      return .error (if toString e == CloudBackupError.keyUnavailable.description then .keyMissing else .notOpened)
  let backup ← match ← (a.controller.store.load id account).toBaseIO with
    | .ok b => pure b
    | .error e =>
      return .error (if toString e == CloudBackupError.invalidBackup.description then .notOpened else .notFetched)
  unless backup.network == network.name do return .ok (none, 0)
  let shared ← match ← (backup.shared key).run with
    | .ok s => pure s
    | .error _ => return .error .notOpened
  let net := Network.tx network
  let mut skipped := shared.unread
  let mut accounts : Array MultisigAccountRecord := #[]
  for r in shared.accounts do
    if (← (MultisigStore.validate #[r] net).run).toOption.isSome then accounts := accounts.push r
    else skipped := skipped + 1
  let mut signers : Array (String × SignerRecord) := #[]
  for r in shared.signers do
    if (← (SignerStore.validate #[r] net).run).toOption.isNone then
      skipped := skipped + 1
      continue
    let some key ← signerKey r net | skipped := skipped + 1; continue
    unless signers.any (·.1 == key) do signers := signers.push (key, r)
  return .ok (some { id, height := shared.lastKnownHeight, anchor := shared.lastKnownBlockHash, accounts, signers,
                     sync := CloudAppState.syncOf shared.appState }, skipped)

/-- What a round's reading of the other backups came to. -/
structure Reading where
  found : Array Replica := #[]
  /-- Those there is nothing more to take from until they are saved again (id and save date). -/
  read : Array (String × Float) := #[]
  listed : Nat := 0
  unread : Array (Float × Unread) := #[]
  skipped : Nat := 0

/-- The other backups of this network, newest first, each opened once per save date. One whose key has not
arrived, or that iCloud did not hand over, is passed over this time and tried again; one that does not open
is not fetched again in this run of the app unless it is saved again. -/
def replicas (a : SyncApp) (network : WinnowApp.Network) (settled : Array (String × Float)) : IO Reading := do
  let state ← a.controller.get
  let account ← a.controller.store.account
  if let some pinned := state.configuration.bind (·.account) then
    unless pinned == account do CloudBackupError.accountChanged.throw
  let own := state.configuration.map (·.backup.id)
  let listed := ((← a.controller.store.list network.name).filter (some ·.id != own)).extract 0 maximumSiblings
  let mut reading : Reading := { listed := listed.size }
  let mut cache := (← a.opened.get).filter fun (id, savedAt, _, _) => listed.any fun s => s.id == id && s.savedAt == savedAt
  let mut unopened := (← a.unopened.get).filter fun (id, savedAt) => listed.any fun s => s.id == id && s.savedAt == savedAt
  for summary in listed do
    if settled.any fun (id, savedAt) => id == summary.id && savedAt == summary.savedAt then continue
    if unopened.any fun (id, savedAt) => id == summary.id && savedAt == summary.savedAt then
      reading := { reading with unread := reading.unread.push (summary.savedAt, .notOpened) }
      continue
    if let some (_, _, replica, skipped) := cache.find? fun (id, savedAt, _, _) => id == summary.id && savedAt == summary.savedAt then
      reading := { reading with found := reading.found.push replica, read := reading.read.push (summary.id, summary.savedAt),
                                skipped := reading.skipped + skipped }
      continue
    match ← a.openReplica summary.id account network with
    | .ok (some replica, skipped) =>
      cache := cache.push (summary.id, summary.savedAt, replica, skipped)
      reading := { reading with found := reading.found.push replica, read := reading.read.push (summary.id, summary.savedAt),
                                skipped := reading.skipped + skipped }
    -- another network's: nothing to take, now or later
    | .ok (none, _) => reading := { reading with read := reading.read.push (summary.id, summary.savedAt) }
    | .error why =>
      if why == .notOpened then unopened := unopened.push (summary.id, summary.savedAt)
      reading := { reading with unread := reading.unread.push (summary.savedAt, why) }
  a.opened.set cache
  a.unopened.set unopened
  return reading

/-! ## Doing what was decided -/

private def attempt {α} (x : IO α) : IO (Option α) := do
  match ← x.toBaseIO with
  | .ok v => return some v
  | .error _ => return none

/-- A change to an account's record, wherever it is kept: among the watched accounts, or among those arriving. -/
def changeRecord (a : SyncApp) (id : String) (kept : MultisigStore → RM MultisigStore)
    (arriving : MultisigAccountRecord → RM MultisigAccountRecord) : IO Bool := do
  let host := a.multisig.host
  if (← host.read).records.any (·.id == id) then
    return (← attempt (a.multisig.withStore fun s => do return (← kept s, ()))).isSome
  let network := (← host.read).network
  let done ← attempt <| RM.toIO <| host.modifyArriving fun all => do
    let some i := all.findIdx? (·.record.id == id) | throw (.multisig (.invalidState "the account is no longer on this phone"))
    let record ← arriving all[i]!.record
    MultisigStore.validate #[record] network
    return (all.set! i { all[i]! with record }, ())
  return done.isSome

/-- One account's decision carried out. The view, whether anything of this device's changed, and whether
anything is left to do later (a change that could not be made yet). -/
def applyAccount (a : SyncApp) (view : SyncView) (d : AccountDecision) (here : Option LocalAccount)
    (found : Array Replica := #[]) : IO (SyncView × Bool × Bool) := do
  let host := a.multisig.host
  let keys := host.keys
  let writeData := host.writeData
  let entry := (view.account? d.id).getD { stamps := { id := d.id } }
  let known := { entry with stamps := { entry.stamps with added := d.added, removed := d.removed } }
  match d.existence with
  | .adopt record height nameStamp ledgerStamp =>
    let network := (← host.read).network
    let store ← host.read
    let admissible ← attempt <| RM.toIO do
      store.requireReadable
      MultisigStore.validate #[record] network
      unless store.records.size + (← host.arrivingAccounts).size < MultisigStore.maximumAccounts do throw (.multisig .tooMany)
    if admissible.isNone || store.records.any (·.id == d.id) then return (view, false, true)
    let filed ← attempt <| RM.toIO <| host.modifyArriving fun all =>
      -- the copy chosen is anchored to the block its backup names, which this device's chain must have
      let anchor := (found.find? fun r => r.height == height && (r.account? d.id).isSome).bind (·.anchor)
      pure ((all.filter (·.record.id != d.id)).push (ArrivingAccount.ofSnapshot record height anchor), ())
    if filed.isNone then return (view, false, true)
    a.env.journal "multisig.accountArriving" [("id", d.id), ("height", toString height)]
    let seen : AccountSeen :=
      { stamps := { id := d.id, added := d.added, removed := d.removed, name := nameStamp, ledger := ledgerStamp },
        name := record.name, ledger := ledgerMark record.ledger, draft := "" }
    return (view.setAccount seen, true, false)
  | .remove =>
    let gone ← if (← host.read).records.any (·.id == d.id) then
        attempt (a.multisig.withStore fun s => do return (← s.remove keys writeData d.id, ()))
      else attempt <| RM.toIO <| host.modifyArriving fun all => pure (all.filter (·.record.id != d.id), ())
    if gone.isNone then return (view, false, true)
    a.env.journal "multisig.accountRemovedElsewhere" [("id", d.id)]
    return (view.setAccount known, true, false)
  | .reassert => return (view.setAccount known, true, false)
  | .unchanged =>
    let mut entry := known
    let mut changed := false
    let mut pending := false
    let some mine := here | return (if d.isQuiet (view.account? d.id |>.map (·.stamps)) then view else view.setAccount entry, false, false)
    let live := (← host.read).records.any (·.id == d.id)
    for change in d.changes do
      match change with
      | .rename name stamp =>
        if ← a.changeRecord d.id (·.rename keys writeData d.id name) (fun r => do
            unless DisplayName.normalized name == some name && !name.isEmpty do throw (.multisig (.invalidState "an account needs a short, single-line name"))
            pure { r with name }) then
          changed := changed || name != mine.record.name
          entry := { entry with stamps := { entry.stamps with name := stamp }, name }
        else pending := true
      | .raise receive change =>
        if ← a.changeRecord d.id (·.raiseIndices keys writeData d.id receive change) (fun r =>
            pure { r with nextReceiveIndex := max r.nextReceiveIndex receive, nextChangeIndex := max r.nextChangeIndex change }) then
          changed := true
        else pending := true
      | .ledger registration stamp =>
        if ← a.changeRecord d.id (·.setLedger keys writeData d.id registration) (fun r => pure { r with ledger := some registration }) then
          changed := changed || some registration != mine.record.ledger
          entry := { entry with stamps := { entry.stamps with ledger := stamp }, ledger := ledgerMark (some registration) }
        else pending := true
      | .draft value stamp =>
        -- an arriving account's coins are not this device's yet: its payment waits until they are
        if !live then pending := true
        else if (← attempt (a.multisig.withStore fun s => do return (← s.setDraft keys writeData d.id value, ()))).isSome then
          changed := true
          entry := { entry with stamps := { entry.stamps with draft := stamp }, draft := draftMark value }
          a.env.journal "multisig.draftFromElsewhere" [("id", d.id), ("present", toString value.isSome)]
        else pending := true
      | .combine others stamp =>
        if !live then pending := true else
        let some draft := mine.record.draft | continue
        let combined : Option String := do
          let mine ← draft.psbt.toOption
          let theirs := others.filterMap (·.psbt.toOption)
          (← (mine.combined theirs).toOption).base64V0.toOption
        match combined with
        | none => pending := true
        | some text =>
          if text == draft.psbtBase64 then
            entry := { entry with stamps := { entry.stamps with draft := stamp } }
          else
            let next : MultisigSpendDraft := { draft with psbtBase64 := text }
            if (← attempt (a.multisig.withStore fun s => do return (← s.setDraft keys writeData d.id (some next), ()))).isSome then
              changed := true
              entry := { entry with stamps := { entry.stamps with draft := stamp }, draft := draftMark (some next) }
            else pending := true
    return (view.setAccount entry, changed, pending)

/-- One signer's decision carried out, as `applyAccount`. -/
def applySigner (a : SyncApp) (view : SyncView) (d : SignerDecision) (here : Option LocalSigner) :
    IO (SyncView × Bool × Bool) := do
  let signers := a.multisig.signers
  let entry := (view.signer? d.key).getD { stamps := { key := d.key } }
  let known := { entry with stamps := { entry.stamps with added := d.added, removed := d.removed } }
  match d.existence with
  | .adopt record nameStamp =>
    let spare ← uuidString
    let filed ← attempt (a.multisig.withSigners fun s => s.adopt signers.keys signers.writeData record spare)
    let some filed := filed | return (view, false, true)
    a.env.journal "signer.arrived" [("id", filed.id)]
    let view := view.setSigner { stamps := { key := d.key, added := d.added, removed := d.removed, name := nameStamp }, name := filed.name }
    let answered ← a.multisig.answered.get
    let view := match filed.isLedger, filed.masterFingerprint with
      | true, some fp => if answered.contains fp || view.elsewhere.contains fp then view else { view with elsewhere := view.elsewhere.push fp }
      | _, _ => view
    return (view, true, false)
  | .remove =>
    let some mine := here | return (view.setSigner known, false, false)
    let gone ← attempt (a.multisig.withSigners fun s => do return (← s.remove signers.keys signers.writeData mine.record.id, ()))
    if gone.isNone then return (view, false, true)
    a.env.journal "signer.removedElsewhere" [("id", mine.record.id)]
    return (view.setSigner known, true, false)
  | .unchanged =>
    let some mine := here | return (if d.isQuiet (view.signer? d.key |>.map (·.stamps)) then view else view.setSigner known, false, false)
    match d.rename with
    | none => return (view.setSigner known, false, false)
    | some (name, stamp) =>
      if name == mine.record.name then
        return (view.setSigner { known with stamps := { known.stamps with name := stamp } }, false, false)
      let renamed ← attempt (a.multisig.withSigners fun s => do return (← s.rename signers.keys signers.writeData mine.record.id name, ()))
      if renamed.isNone then return (view.setSigner known, false, true)
      return (view.setSigner { stamps := { known.stamps with name := stamp }, name }, true, false)

/-- An arriving account that cannot be caught up from the copy it came with (`waitingForNewerCopyText`) is
begun again from a later copy, when another device has one. -/
def renewWaiting (a : SyncApp) (found : Array Replica) : IO Unit := do
  let network := (← a.multisig.host.read).network
  for entry in ← a.multisig.host.arrivingAccounts do
    unless entry.note.isSome do continue
    let later := found.filterMap fun r => (r.account? entry.record.id).bind fun record =>
      if r.height > entry.scannedThrough then some (record, r.height, r.anchor) else none
    let some (record, height, anchor) := later.foldl (fun best x => match best with
      | some b => if x.2.1 > b.2.1 then some x else some b
      | none => some x) none | continue
    let record := { record with draft := none, name := entry.record.name }
    if (← (MultisigStore.validate #[record] network).run).toOption.isNone then continue
    discard <| attempt <| RM.toIO <| a.multisig.host.modifyArriving fun all =>
      pure (all.map fun e => if e.record.id == entry.record.id then ArrivingAccount.ofSnapshot record height anchor else e, ())

/-- Test mode's journal, once per distinct outcome: a look every minute that finds the same says it once. -/
def journalOnce (a : SyncApp) (name : String) (fields : List (String × String)) : IO Unit := do
  let line := name ++ "|" ++ journalFingerprint fields
  if (← a.journaled.get) == some line then return
  a.journaled.set (some line)
  a.env.journal name fields

/-- One look at the other devices' backups: read what changed, decide, do it, and remember. -/
def round (a : SyncApp) : IO Unit := do
  let began ← a.epoch.get
  let some (wallet, network, dir) ← a.place | return
  -- the backup is pointed at the open wallet a moment after it opens (the app's tick): until then nothing says
  -- which of the backups is this wallet's own, nor whether its automatic backup is on
  unless (← a.controller.get).configuredWalletID == some wallet do return
  unless (← a.controller.get).automaticEnabled do return
  let store ← a.multisig.host.read
  if store.isDamaged || store.unavailable || (← a.multisig.signers.read).isDamaged then return
  let seen := (← loadView dir wallet).1
  -- something this device took is no longer here (a file set aside, an arrival that failed): the backups
  -- there was nothing more to take from are read again
  let arriving ← a.multisig.host.arrivingAccounts
  let signerKeys ← (← a.multisig.signers.read).records.filterMapM (signerKey · (Network.tx network))
  let lacking := seen.accounts.any (fun e => !e.stamps.isRemoved && !store.records.any (·.id == e.stamps.id) &&
      !arriving.any (·.record.id == e.stamps.id)) ||
    seen.signers.any (fun e => !e.stamps.isRemoved && !signerKeys.contains e.stamps.key)
  let settled := if lacking then #[] else seen.settled
  let reading ← a.replicas network settled
  let found := reading.found
  let read := reading.read
  -- the wallet, its place or the network changed while the backups were read
  unless (← a.epoch.get) == began && (← a.place) == some (wallet, network, dir) do return
  a.renewWaiting found
  let latest := found.foldl (fun t r => max t ((r.sync.map (·.latest)).getD 0)) 0
  let changed ← a.withView false (latest := latest) (since := some began) fun view initial fresh => do
    let (before, accounts, signers) ← a.stamped view initial fresh
    let known := (before.accounts.filter fun e => !accounts.any (·.record.id == e.stamps.id)).map (·.stamps)
    let mut view := before
    let mut changed := false
    let mut pending := false
    for d in decideAccounts fresh (·.txid.toOption) accounts known found do
      let (next, did, later) ← a.applyAccount view d (accounts.find? (·.record.id == d.id)) found
      view := next
      changed := changed || did
      pending := pending || later
    let knownSigners := (view.signers.filter fun e => !signers.any (·.key == e.stamps.key)).map (·.stamps)
    for d in decideSigners signers knownSigners found do
      let (next, did, later) ← a.applySigner view d (signers.find? (·.key == d.key))
      view := next
      changed := changed || did
      pending := pending || later
    -- nothing was taken and nothing waits: these backups need no second reading until they are saved again
    let quiet := !changed && !pending && sameView { view with settled := before.settled } before
    let listed := settled.filter fun (id, _) => !read.any (·.1 == id)
    let moved := changed || !sameView { view with settled := before.settled } before
    return (if quiet then { view with settled := listed ++ read } else { view with settled := #[] }, moved)
  a.status.set { checkedAt := some ((← a.nowMs) / 1000), listed := reading.listed, unread := reading.unread, skipped := reading.skipped }
  let count (why : Unread) := toString (reading.unread.filter (·.2 == why)).size
  a.journalOnce "devices.looked" [("listed", toString reading.listed), ("backups", toString found.size),
    ("keyMissing", count .keyMissing), ("notOpened", count .notOpened), ("notFetched", count .notFetched),
    ("skipped", toString reading.skipped), ("changed", toString changed)]
  if changed then
    a.multisig.overviewCache.set none
    (← a.changed.get)

/-- A round when one is due: on coming to the foreground (`force`), and then at most every `intervalMs`
while the app is open. Runs apart from the caller; a failure is said in the status and tried again. -/
def tick (a : SyncApp) (force : Bool := false) : IO Unit := do
  if !a.allows then return
  let c ← a.env.get
  unless c.active && c.wallet.isSome do return
  let now ← IO.monoMsNow
  let due := match ← a.lastRound.get with
    | some last => force || now ≥ last + a.intervalMs
    | none => true
  unless due do return
  if ← a.running.modifyGet fun r => (r, true) then return
  a.lastRound.set (some now)
  discard <| IO.asTask (prio := .dedicated) do
    try
      a.round
    catch e =>
      unless isCancellation e do
        a.status.modify fun s => { s with message := some (toString e) }
        a.journalOnce "devices.lookFailed" [("reason", toString e)]
    finally
      a.running.set false

/-- What `stamped` would look at, in one line: when it is what it was, nothing has been done here since. -/
def localMark (a : SyncApp) : IO String := do
  let store ← a.multisig.host.read
  let signers ← a.multisig.signers.read
  let accounts := store.records.toList.map fun r => s!"{r.id}|{r.name}|{ledgerMark r.ledger}|{draftMark r.draft}"
  let saved := signers.records.toList.map fun r => s!"{r.id}|{r.name}|{r.keys.size}"
  return "\n".intercalate (((← a.place).map (·.1)).getD "" :: accounts ++ saved ++ (← a.multisig.answered.get).toList.map toString)

/-- What the person did here since the last look is stamped now, not when the next backup happens to be saved:
the later of two devices' renames is then the one made later. Nothing is read or written while nothing changed. -/
def noticeChanges (a : SyncApp) : IO Unit := do
  if !a.allows then return
  let mark ← a.localMark
  if (← a.noticed.get) == some mark then return
  discard <| a.publish
  a.noticed.set (some mark)

/-- While the app is in the foreground: what was done here is noticed every second, and the other devices'
backups are looked at when a look is due. Ends when the scene goes or another loop begins. -/
def start (a : SyncApp) : IO Unit := do
  if !a.allows then return
  let token ← a.loop.modifyGet fun t => (t + 1, t + 1)
  a.looping.set true
  discard <| IO.asTask (prio := .dedicated) do
    try
      while (← a.loop.get) == token && (← a.env.get).active do
        try
          a.noticeChanges
          a.tick
        catch _ => pure ()
        for _ in [0:10] do
          if (← a.loop.get) != token then break
          IO.sleep (min 100 (a.intervalMs / 10 + 1)).toUInt32
    finally
      if (← a.loop.get) == token then a.looping.set false

/-- The loop, begun if it is not running: a launch straight into the foreground has no scene change to begin
it, so the app's own tick does (`CloudApp.tick`). -/
def ensureRunning (a : SyncApp) : IO Unit := do
  if !a.allows || (← a.looping.get) then return
  if (← a.env.get).active then a.start

def stop (a : SyncApp) : IO Unit := do
  a.loop.modify (· + 1)
  a.looping.set false

/-- The wallet changed or went: what was read is another wallet's business. -/
def reset (a : SyncApp) : IO Unit := a.locked do
  -- under the lock: a round's writes to the stores are over before they are pointed at another wallet
  a.epoch.modify (· + 1)
  a.opened.set #[]
  a.unopened.set #[]
  a.lastRound.set none
  a.status.set {}
  a.noticed.set none
  a.multisig.elsewhere.set #[]

end SyncApp
end WinnowApp.Real
