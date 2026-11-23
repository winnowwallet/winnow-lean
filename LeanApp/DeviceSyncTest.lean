import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import WinnowApp.Main
import LeanNative.Json
import TestKit.Check
import TestKit.Fixtures
import TestKit.Regtest
import AppTestNames

/-! `device-sync-test`: multisig accounts and signers that follow a person between devices, headless.

* the rules (`Winnow.DeviceSync`): what one device does with what another's backup says, case by case, and
  the forms they travel in;
* devices: two and three phones on a custom signet with an unreachable peer, one in-memory iCloud and one
  in-memory iCloud Keychain between them (`MemoryCloud`, `memoryCloudKeys`, as cloud-backup-test's). Each
  phone is the real backend with its iCloud flows; a test says when a phone saves its backup (`publish`) and
  when it looks at the others' (`look`), so every step is in a known order. Signers and Ledgers follow, are
  renamed and removed; an account arrives, is caught up and watched; removals travel, and do not where coins
  are; nothing follows with backup off, under another Apple Account, or from a backup whose key has not
  arrived; and left alone in the foreground, ticking as the app does, two phones come into step by themselves.

What needs a chain is in backend-test's `devicesFlow` (regtest): an account's coins found by the second
device's own scan, and a payment's signatures made on two devices added up. Real iCloud between two real
devices is not something a test here can reach.

Run from `LeanApp/`. Exits 1 on any failure. -/

open Winnow WinnowApp WinnowApp.RecordsReal Keys TestKit
open Winnow.DeviceSync
open TestKit.Regtest (waitUntil)
open Tx (BitcoinNetwork)

instance : Describe RecordsError := ⟨(·.name), fun e => s!"{e.name}: {e.description}"⟩

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

def fails {α} (x : IO α) : IO Bool := do return (← x.toBaseIO) matches .error _

/-! ## The rules -/

def stampOf (time : Nat) (device : Nat := 1) : Stamp := { time, device }

def account (id : String) (name : String := "Shared") : MultisigAccountRecord :=
  { id, name, descriptor := s!"descriptor-{id}", createdAtHeight := 10 }

def draftOf (text : String) : MultisigSpendDraft := { psbtBase64 := text, createdAtHeight := 10 }

/-- A draft's payment in these tests: the text before its dash ("pay1-a" and "pay1-b" are one payment). -/
def paymentOf (d : MultisigSpendDraft) : Option ByteArray := some ((d.psbtBase64.splitOn "-").head!.toUTF8)

def here (r : MultisigAccountRecord) (stamps : AccountMeta := { id := r.id }) (removable : Bool := true) : LocalAccount :=
  { record := r, seen := { stamps, name := r.name, ledger := ledgerMark r.ledger, draft := draftMark r.draft }, removable }

def replica (accounts : Array MultisigAccountRecord) (stamps : Array AccountMeta := #[]) (height : UInt32 := 100)
    (legacy : Bool := false) (id : String := "R") : Replica :=
  { id, height, accounts, sync := if legacy then none else some { device := 2, accounts := stamps } }

def fresh : Stamp := stampOf 1_000 9

def judge (mine : Option LocalAccount) (known : Option AccountMeta) (replicas : Array Replica) (id : String := "acct") :
    AccountDecision :=
  decideAccount fresh paymentOf id mine known replicas

def stampForms : TM Unit := do
  let s := stampOf 1_763_400_000_123 281_474_976_710_655
  check "a stamp travels as two whole numbers" ((Stamp.ofJV s.toJV).toOption == some s)
  check "a stamp of three numbers is refused" ((Stamp.ofJV (.arr #[SwiftJSON.ofInt 1, SwiftJSON.ofInt 2, SwiftJSON.ofInt 3])).toOption.isNone)
  check "later by time, then by device" (stampOf 1 9 < stampOf 2 1 && stampOf 2 1 < stampOf 2 3 && !(stampOf 2 3 < stampOf 2 3))
  check "a new stamp is later than the clock even when this device's own clock is behind"
    (stampOf 5_000 7 < Stamp.after 5_000 10 1 && (Stamp.after 5_000 9_000 1).time == 9_000)
  let said : SyncMeta :=
    { device := 77
      accounts := #[{ id := "acct", added := stampOf 5, name := stampOf 6 2, draft := stampOf 7 }, { id := "gone", removed := stampOf 9 }]
      signers := #[{ key := "02ab", added := stampOf 3, removed := stampOf 4, name := stampOf 3 }] }
  check "what a backup says of its accounts and signers round-trips" ((SyncMeta.ofJV said.toJV).toOption == some said)
  check "the latest time in it" (said.latest == 9)
  let later := match said.toJV with
    | .obj kvs => SwiftJSON.JV.obj (kvs.map fun (k, v) => if k == "version" then (k, SwiftJSON.ofInt 2) else (k, v))
    | v => v
  check "a later version's is not read" ((SyncMeta.ofJV later).toOption.isNone)
  let many : SyncMeta := { device := 1, accounts := (Array.range (maximumEntries + 1)).map fun i => { id := toString i } }
  check "more accounts than a backup remembers are refused" ((SyncMeta.ofJV many.toJV).toOption.isNone)

def stampingRules : TM Unit := do
  let r := account "acct"
  let first := stampAccount fresh true none r
  check "first run: an account already here is as old as time" (first.stamps == { id := "acct" } && first.name == "Shared")
  let drafted := stampAccount fresh true none { r with draft := some (draftOf "pay1-a") }
  check "first run: a payment awaiting signatures is stamped, to travel" (drafted.stamps.draft == fresh && drafted.stamps.added == {})
  let joined := stampAccount fresh false none r
  check "afterwards: an account that appears was just added and named" (joined.stamps.added == fresh && joined.stamps.name == fresh)
  let later := stampOf 2_000 9
  check "unchanged: no new stamp" (stampAccount later false (some joined) r == joined)
  let renamed := stampAccount later false (some joined) { r with name := "Household" }
  check "a rename is stamped, and nothing else"
    (renamed.stamps.name == later && renamed.stamps.added == fresh && renamed.name == "Household")
  let signed := stampAccount later false (some joined) { r with draft := some (draftOf "pay1-a") }
  check "a new draft is stamped" (signed.stamps.draft == later && signed.draft == draftMark (some (draftOf "pay1-a")))
  let discarded := stampAccount (stampOf 3_000 9) false (some signed) r
  check "a discarded draft is stamped too" (discarded.stamps.draft == stampOf 3_000 9 && discarded.draft == "")
  let removed : AccountSeen := { joined with stamps := { joined.stamps with removed := later } }
  let back := stampAccount (stampOf 3_000 9) false (some removed) r
  check "removed and here again: added again, later than the removal"
    (back.stamps.added == stampOf 3_000 9 && !back.stamps.isRemoved)
  let signer : SignerRecord := { id := "S", kind := .keys, name := "Bob", keys := #["k"], addedAt := 0 }
  check "signers: first run as old as time, then stamped when added and when renamed"
    ((stampSigner fresh true none "02ab" signer).stamps == { key := "02ab" } &&
     (stampSigner fresh false none "02ab" signer).stamps.added == fresh &&
     (stampSigner later false (some (stampSigner fresh false none "02ab" signer)) "02ab" { signer with name := "Rob" }).stamps.name == later)

def existenceRules : TM Unit := do
  let r := account "acct"
  -- not here, there
  let d := judge none none #[replica #[{ r with draft := some (draftOf "pay1-a"), nextReceiveIndex := 3 }] (height := 120)]
  check "not here, on another device: taken, current to that device's block" (match d.existence with
    | .adopt record height _ _ => height == 120 && record.id == "acct" && record.nextReceiveIndex == 3
    | _ => false)
  check "taken without its payment awaiting signatures, which follows once the coins are seen here" (match d.existence with
    | .adopt record _ _ _ => record.draft.isNone | _ => false)
  let two := judge none none
    #[replica #[r] (height := 90) (id := "old"), replica #[{ r with name := "Newer" }] #[{ id := "acct", name := stampOf 50 }] (height := 140) (id := "new")]
  check "from two devices: the copy current to the later block, under the later name" (match two.existence with
    | .adopt record height name _ => height == 140 && record.name == "Newer" && name == stampOf 50 | _ => false)
  let legacy := judge none none #[replica #[r] (legacy := true)]
  check "a backup from before devices kept in step still gives its accounts" (legacy.existence matches .adopt ..)
  -- removed elsewhere
  let removedThere := replica #[] #[{ id := "acct", added := stampOf 10, removed := stampOf 20 }] (id := "B")
  check "not here, removed there, still in an old backup: not taken"
    ((judge none none #[replica #[r] (legacy := true) (id := "old"), removedThere]).existence matches .unchanged)
  check "…and the removal is remembered" ((judge none none #[removedThere]).removed == stampOf 20)
  check "here, removed there, nothing in it: removed here"
    ((judge (some (here r)) none #[removedThere]).existence matches .remove)
  let kept := judge (some (here r (removable := false))) none #[removedThere]
  check "here with coins or a payment in it: it stays, added again later than the removal"
    ((kept.existence matches .reassert) && kept.added == fresh && stampOf 20 < kept.added)
  check "added here later than it was removed there: it stays as it is"
    ((judge (some (here r { id := "acct", added := stampOf 30 })) none #[removedThere]).existence matches .unchanged)
  -- the removal known here beats another device's older copy
  let known : AccountMeta := { id := "acct", added := stampOf 10, removed := stampOf 40 }
  check "removed here: a copy another device added earlier is not taken back"
    ((judge none (some known) #[replica #[r] #[{ id := "acct", added := stampOf 30 }]]).existence matches .unchanged)
  check "removed here: one another device joined again since is taken"
    ((judge none (some known) #[replica #[r] #[{ id := "acct", added := stampOf 50 }]]).existence matches .adopt ..)

def changeRules : TM Unit := do
  let r := account "acct"
  let renamedThere := replica #[{ r with name := "Household" }] #[{ id := "acct", name := stampOf 50 }]
  check "a later name there: renamed here" ((judge (some (here r)) none #[renamedThere]).changes.any fun
    | .rename name stamp => name == "Household" && stamp == stampOf 50 | _ => false)
  check "an earlier name there: this device's stays"
    ((judge (some (here r { id := "acct", name := stampOf 60 })) none #[renamedThere]).changes.isEmpty)
  check "a backup from before never renames" ((judge (some (here r)) none #[replica #[{ r with name := "Old" }] (legacy := true)]).changes.isEmpty)
  let ahead := replica #[{ r with nextReceiveIndex := 7, nextChangeIndex := 2 }]
  check "address counters go to the highest" ((judge (some (here { r with nextReceiveIndex := 4, nextChangeIndex := 5 })) none #[ahead]).changes.any fun
    | .raise receive change => receive == 7 && change == 5 | _ => false)
  check "…and never back" ((judge (some (here { r with nextReceiveIndex := 9, nextChangeIndex := 5 })) none #[ahead]).changes.isEmpty)
  let registration : LedgerRegistration :=
    { policyName := "Shared", policyID := ByteArray.mk #[1], hmac := ByteArray.mk #[2], masterFingerprint := 7, keyPath := #[] }
  let registeredThere := replica #[{ r with ledger := some registration }] #[{ id := "acct", ledger := stampOf 50 }]
  check "a Ledger's registration made there arrives" ((judge (some (here r)) none #[registeredThere]).changes.any fun
    | .ledger got stamp => got == registration && stamp == stampOf 50 | _ => false)
  -- the payment awaiting signatures
  let drafted (text : String) (time : Nat) := replica #[{ r with draft := some (draftOf text) }] #[{ id := "acct", draft := stampOf time }]
  check "a payment started there arrives" ((judge (some (here r)) none #[drafted "pay1-a" 50]).changes.any fun
    | .draft value stamp => value == some (draftOf "pay1-a") && stamp == stampOf 50 | _ => false)
  let mine := here { r with draft := some (draftOf "pay1-a") } { id := "acct", draft := stampOf 40 }
  check "the same payment signed there: its signatures join this device's, whichever is later"
    ((judge (some mine) none #[drafted "pay1-b" 50]).changes.any (fun | .combine others stamp => others == #[draftOf "pay1-b"] && stamp == stampOf 50 | _ => false) &&
     (judge (some mine) none #[drafted "pay1-b" 30]).changes.any (fun | .combine others stamp => others == #[draftOf "pay1-b"] && stamp == stampOf 40 | _ => false))
  check "the same copy there: nothing to do" ((judge (some mine) none #[drafted "pay1-a" 50]).changes.isEmpty)
  check "another payment started there later: it replaces this one"
    ((judge (some mine) none #[drafted "pay2-a" 50]).changes.any fun | .draft value _ => value == some (draftOf "pay2-a") | _ => false)
  check "another payment started there earlier: this one stays" ((judge (some mine) none #[drafted "pay2-a" 30]).changes.isEmpty)
  let discardedThere := replica #[r] #[{ id := "acct", draft := stampOf 50 }]
  check "discarded or sent there later: gone here" ((judge (some mine) none #[discardedThere]).changes.any fun
    | .draft value _ => value.isNone | _ => false)
  check "no draft there, and none stamped: this device's stays"
    ((judge (some mine) none #[replica #[r] (legacy := true)]).changes.isEmpty)

def signerRules : TM Unit := do
  let bob : SignerRecord := { id := "S", kind := .keys, name := "Bob", keys := #["k"], addedAt := 0 }
  let there (name : String) (stamps : SignerMeta) : Replica :=
    { id := "R", height := 1, signers := #[("02ab", { bob with name })], sync := some { device := 2, signers := #[stamps] } }
  let mine : LocalSigner := { key := "02ab", record := bob, seen := { stamps := { key := "02ab", name := stampOf 40 }, name := "Bob" } }
  check "a signer on another device arrives" ((decideSigner "02ab" none none #[there "Bob" { key := "02ab", added := stampOf 5 }]).existence matches .adopt ..)
  check "a later name there renames here"
    ((decideSigner "02ab" (some mine) none #[there "Robert" { key := "02ab", name := stampOf 50 }]).rename == some ("Robert", stampOf 50))
  check "an earlier name there does not"
    ((decideSigner "02ab" (some mine) none #[there "Robert" { key := "02ab", name := stampOf 30 }]).rename.isNone)
  let removedThere : Replica := { id := "R", height := 1, sync := some { device := 2, signers := #[{ key := "02ab", added := stampOf 5, removed := stampOf 60 }] } }
  check "removed there: removed here" ((decideSigner "02ab" (some mine) none #[removedThere]).existence matches .remove)
  check "removed here: not taken back from a device that has not heard"
    ((decideSigner "02ab" none (some { key := "02ab", removed := stampOf 60 }) #[there "Bob" { key := "02ab", added := stampOf 5 }]).existence matches .unchanged)
  check "paired again there since: taken"
    ((decideSigner "02ab" none (some { key := "02ab", removed := stampOf 60 }) #[there "Bob" { key := "02ab", added := stampOf 70 }]).existence matches .adopt ..)

/-! ## Devices -/

/-- A phone on a custom signet with an unreachable peer, its iCloud the memory versions it is given. -/
structure Device where
  backend : Backend
  env : Real.Env
  app : Real.CloudApp
  secrets : IO.Ref Keys.InMemorySecrets
  dir : String
  settings : Settings

open Real in
def device (root : System.FilePath) (name : String) (cloud : MemoryCloud) (cloudKeys : CloudBackupKeys)
    (ledger : IO LedgerSession := noLedger) (devicesIntervalMs : Nat := 60_000)
    (store : Option CloudBackupStore := none) : TM Device := do
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", "devices"), ("WINNOW_E2E_ENTROPY", "04040404040404040404040404040404"),
               ("WINNOW_E2E_PEER", "127.0.0.1:1"), ("WINNOW_E2E_CHALLENGE", "51")]
  let .active mode := WinnowApp.E2E.resolve (fun k => vars.lookup k) | throw "test mode did not resolve"
  let secrets ← IO.mkRef ({} : Keys.InMemorySecrets)
  let deps : Deps := { keyStore := inMemoryKeyStore secrets, networkParams := mode.networkParams, peerCount := 1,
                       importPeerWaitMs := 1_000, fetch := fun _ => throw (.other "offline") }
  let (backend, env, app) ← Backend.realWithCloud deps ledger (store := store.getD cloud.store) (keys := cloudKeys) (scheduleDelayMs := 20)
    (devicesIntervalMs := devicesIntervalMs)
  let dir := (root / name / "signet").toString
  IO.FS.createDirAll dir
  let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
  return { backend, env, app, secrets, dir, settings }

namespace Device

/-- A new wallet, its first backup saved. -/
def create (d : Device) : TM String := do
  discard <| d.backend.openWallet .signet d.dir
  -- the scene is not told it is active: the foreground loop stays off, and a test says when a device looks
  d.backend.startNetworking d.settings
  let id ← d.backend.createWallet .signet d.dir
  unless ← waitUntil 5_000 (every := 10) (do return (← d.app.controller.get).lastSaved.isSome) do throw "the first backup was not saved"
  -- the scheduled update is over: from here a test says when a backup is saved
  discard <| waitUntil 2_000 (every := 10) do
    let s ← d.app.controller.get
    return !s.scheduled && !s.busy
  return id

/-- This device's backup saved now, with what it holds. -/
def publish (d : Device) : IO Unit :=
  Real.CloudM.toIO <| d.app.controller.update do
    let bundle ← d.app.exportedBundle
    return { bundle, appState := some (← d.app.cloudAppState bundle).encoded }

/-- One look at the other devices' backups. -/
def look (d : Device) : IO Unit := Real.CloudM.toIO d.app.follow.round

def overview (d : Device) : IO MultisigOverview := d.backend.multisigOverview

def signerNames (d : Device) : IO (List String) := do return (← d.overview).signers.map (·.name)

/-- The accounts on their way are brought to block `frontier - 1` by a scan that finds nothing. -/
def catchUp (d : Device) (frontier : UInt32) (chain : Real.ChainHashes := fun _ => pure none) : IO Unit :=
  d.app.multisig.catchUp .signet frontier (fun _ toHeight _ _ => pure (some toHeight, true)) chain

/-- The arriving accounts caught up to the block after the one they are current to. -/
def settle (d : Device) : IO Unit := do
  for e in ← d.app.multisig.host.arrivingAccounts do d.catchUp (e.scannedThrough + 2)

def view (d : Device) : IO Real.SyncView := do
  let some (wallet, _, dir) ← d.app.follow.place | throw (IO.userError "no wallet")
  return (← Real.SyncApp.loadView dir wallet).1

def stop (d : Device) : IO Unit := do
  d.backend.cloudScene false
  d.backend.stopNetworking

end Device

/-- A signer key of a test master: `[fp/86'/1'/0']tpub…/<0;1>/*`. -/
def testKey (entropyByte : UInt8) : TM String := do keyExpression (← master entropyByte)

def signersFollow (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "signersA" cloud cloudKeys
  let b ← device root "signersB" cloud cloudKeys
  let walletA ← a.create
  let walletB ← b.create
  check "two devices, two wallets, one iCloud" (walletA != walletB && (← cloud.count) == 2)
  let bob ← a.backend.addSignerKeys "Bob" (← testKey 0xB2)
  a.publish
  check "before it looks, the other device has no such signer" ((← b.signerNames) == [])
  b.look
  check "keys saved on one device are on the other" ((← b.signerNames) == ["Bob"])
  check "…the same keys" (((← b.overview).signers.map (·.keys)) == ((← a.overview).signers.map (·.keys)))
  check "no secret came with them: the device holds its own wallet's, and no other"
    ((← b.secrets.get).size == (← a.secrets.get).size)
  let uploads ← cloud.saves.get
  b.look
  a.look
  check "looking again changes nothing" ((← b.signerNames) == ["Bob"] && (← a.signerNames) == ["Bob"] && (← cloud.saves.get) == uploads)
  -- a rename travels; the later of two wins on both
  a.backend.renameSigner bob "Robert"
  a.publish
  b.look
  check "a rename travels" ((← b.signerNames) == ["Robert"])
  let onB := ((← b.overview).signers.head?.map (·.id)).getD ""
  b.backend.renameSigner onB "Rob"
  b.app.follow.noticeChanges
  IO.sleep 5
  a.backend.renameSigner bob "Bobby"
  a.app.follow.noticeChanges
  a.publish
  b.publish
  a.look
  b.look
  check "renamed on both before either looked: the later name, on both" ((← a.signerNames) == ["Bobby"] && (← b.signerNames) == ["Bobby"])
  a.publish
  b.publish
  a.look
  b.look
  check "…and it stays" ((← a.signerNames) == ["Bobby"] && (← b.signerNames) == ["Bobby"])
  -- a removal travels, and is not undone by the device that has not heard yet
  b.backend.removeSigner onB
  b.publish
  b.look
  check "removed on one device: the other's backup does not bring it back" ((← b.signerNames) == [])
  a.look
  check "removed on one device: removed on the other" ((← a.signerNames) == [])
  a.publish
  b.look
  check "…and it stays removed" ((← b.signerNames) == [] && (← a.signerNames) == [])
  -- saved again, it comes back everywhere
  discard <| a.backend.addSignerKeys "Bob again" (← testKey 0xB2)
  a.publish
  b.look
  check "saved again later: back on both" ((← b.signerNames) == ["Bob again"])
  -- what was read needs no second reading
  b.publish
  a.look
  b.look
  check "a backup there was nothing to take from is remembered, not read again" ((← b.view).settled.size == 1 && (← a.view).settled.size == 1)
  a.stop
  b.stop

def ledgersFollow (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let ledger ← IO.mkRef (Ledger.Simulator.new (← master 0xC3) .signet)
  let a ← device root "ledgerA" cloud cloudKeys (Real.simulatedLedger ledger)
  let b ← device root "ledgerB" cloud cloudKeys (Real.simulatedLedger ledger)
  discard <| a.create
  discard <| b.create
  discard <| a.backend.pairLedger "Nano"
  check "paired here: not marked as another device's" ((← a.overview).ledgers.map (·.elsewhere) == [false])
  a.publish
  b.look
  let onB := (← b.overview).ledgers
  check "a Ledger paired on one device is listed on the other" (onB.map (·.name) == ["Nano"] && onB.map (·.keys) == (← a.overview).ledgers.map (·.keys))
  check "…marked as paired on another device" (onB.map (·.elsewhere) == [true])
  let shown := (LeanNative.Html.toWire (.col (signersSections { (default : Model) with multisig := ← b.overview }))).toJson.compress
  check "the list says so" (contains shown "Paired on another device")
  -- the Ledger answers on this device: pairing it here files nothing new
  discard <| b.backend.pairLedger "Nano"
  let after := (← b.overview).ledgers
  check "once it has answered here the mark goes, and it is still one Ledger" (after.map (·.elsewhere) == [false] && after.length == 1)
  b.publish
  b.look
  check "…for good" ((← b.overview).ledgers.map (·.elsewhere) == [false] && (← b.view).elsewhere.isEmpty)
  a.stop
  b.stop

/-- A 2-of-2 of the device's own key and a test key, built on it. Its id. -/
def sharedAccount (d : Device) (name : String := "Shared") (other : UInt8 := 0xB2) : TM String := do
  let own := (← d.overview).keyExpression.getD ""
  let (id, _, _) ← d.backend.createMultisigAccount name 2 [([own], none), ([← testKey other], none)] none
  return id

/-- An account arrives anchored to the block its backup names. This device's chain agreeing, it is caught up
from there; disagreeing (a reorg the other device saw), it goes back far enough to be scanned again here. -/
def anchoredArrivals (root : System.FilePath) : TM Unit := do
  -- the fork rule itself: a day below the anchor, or below the lowest history entry this chain disagrees with
  let theirs := ByteArray.mk (Array.replicate 32 0xAA)
  let ours := ByteArray.mk (Array.replicate 32 0xBB)
  let chainOf (f : UInt32 → ByteArray) : Real.ChainHashes := fun h => pure (if h ≤ 1_000 then some (f h) else none)
  let entry (height : UInt32) (hash : ByteArray) : HistoryEntry := { txid := ByteArray.mk (Array.replicate 32 1), height, received := 1, spent := 0, blockHash := some hash }
  check "an anchor this chain has: nothing to do" ((← Real.anchorFork (chainOf fun _ => theirs) 900 theirs #[]) == none)
  check "one past this chain's tip: not checked yet" ((← Real.anchorFork (chainOf fun _ => ours) 1_200 theirs #[]) == none)
  check "one this chain does not have: a day back" ((← Real.anchorFork (chainOf fun _ => ours) 900 theirs #[]) == some (900 - Real.anchorRewind))
  check "…or to below the lowest payment in a block this chain does not have"
    ((← Real.anchorFork (chainOf fun _ => ours) 900 theirs #[entry 700 theirs, entry 600 ours, entry 850 theirs]) == some 699)
  check "…never below block zero" ((← Real.anchorFork (chainOf fun _ => ours) 100 theirs #[]) == some 0)
  -- on the devices
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "anchorA" cloud cloudKeys
  let b ← device root "anchorB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  let some w := (← a.env.get).wallet | throw "no wallet on the first device"
  -- the first device scanned to block 499, the last block of which it names (its own stack put away, so
  -- that what it saves is what it recorded)
  a.backend.stopNetworking
  let next : UInt32 := 500
  discard <| (w.recordScanHeight next (some theirs)).run
  let id ← sharedAccount a
  a.publish
  b.look
  let arriving ← b.app.multisig.host.arrivingAccounts
  check "the account arrives with the block its backup names" (arriving.toList.map (·.anchor) == [some theirs])
  let height := arriving[0]!.scannedThrough
  check "…the block before the first device's next" (height + 1 == next)
  -- this chain names another block there: the account goes back a day and is scanned again
  let scanned ← IO.mkRef (#[] : Array UInt32)
  let scanner : Real.RangeScanner := fun fromHeight toHeight _ _ => do
    scanned.modify (·.push fromHeight)
    pure (some toHeight, true)
  b.app.multisig.catchUp .signet (height + 1) scanner (fun h => pure (if h ≤ height then some ours else none))
  let back := if height > Real.anchorRewind then height - Real.anchorRewind else 0
  check "a disagreeing anchor sends it back a day, and it is scanned here from there" ((← scanned.get) == #[back + 1])
  check "…and, scanned again, it joins this device's accounts" ((← b.overview).accounts.map (·.id) == [id])
  -- another account, anchored to a block this chain agrees on: caught up from where it was
  let id2 ← sharedAccount a "Second" 0xB3
  a.publish
  b.look
  let arriving ← b.app.multisig.host.arrivingAccounts
  check "the second arrives anchored" (arriving.toList.map (·.anchor) == [some theirs])
  scanned.set #[]
  b.app.multisig.catchUp .signet (height + 1) scanner (fun h => pure (if h ≤ height then some theirs else none))
  check "an agreeing anchor: nothing below it scanned again" ((← scanned.get).isEmpty)
  check "…and it joins this device's accounts" ((← b.overview).accounts.map (·.id) |>.contains id2)
  a.stop
  b.stop

/-- An added wallet's own stack, as 0.9.20 to 0.9.23 kept one, folds into the network's: its chain, scan and
peers go, and its relay file's pending payments join the network's. -/
def slotStacksFold (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "foldA" cloud cloudKeys
  discard <| a.create
  let slot := Real.slotDir a.dir "1"
  IO.FS.createDirAll slot
  for name in ["filters.json", "headers.bin", "peers.json", "sync.last-complete"] do
    IO.FS.writeFile (System.FilePath.mk slot / name) "old"
  IO.FS.writeBinFile (System.FilePath.mk slot / "broadcast.json") (Winnow.IO.TxBroadcaster.encodeStore {})
  IO.FS.writeFile (System.FilePath.mk slot / "people.json") "kept"
  Real.migrateSlotStacks a.env .signet a.dir
  let gone ← ["filters.json", "headers.bin", "peers.json", "sync.last-complete", "broadcast.json"].allM fun (name : String) =>
    do return !(← (System.FilePath.mk slot / name).pathExists)
  check "the slot's chain, scan, peers and relay file are folded away" gone
  check "…its own files stay" (← (System.FilePath.mk slot / "people.json").pathExists)
  check "…and the network's relay file is there" (← (System.FilePath.mk a.dir / "broadcast.json").pathExists)
  a.stop

/-- A wallet's name travels with its backup: given on one device, the other device holding the same wallet
shows it after a look; the later name wins; a restore takes it. -/
def namesFollow (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "namesA" cloud cloudKeys
  let b ← device root "namesB" cloud cloudKeys
  let idA ← a.create
  -- the second device holds the same wallet, from the first's backup
  discard <| b.backend.openWallet .signet b.dir
  b.backend.startNetworking b.settings
  let (idB, _) ← b.backend.importBundle .signet b.dir (← a.backend.exportBundle true)
  unless ← waitUntil 5_000 (every := 10) (do return (← b.app.controller.get).lastSaved.isSome) do
    throw "the second device's backup was not saved"
  check "the two devices hold the same wallet" (idA == idB)
  check "a name too long is refused" (← fails (a.backend.renameWallet (String.mk (List.replicate 65 'x'))))
  a.backend.renameWallet "Household"
  check "named on the first device" ((← a.backend.wallets a.dir).map (·.label) == ["Household"])
  a.publish
  b.look
  check "the second device shows the name after a look" ((← b.backend.wallets b.dir).map (·.label) == ["Household"])
  IO.sleep 5
  b.backend.renameWallet "Savings"
  b.publish
  a.look
  check "the later name wins on the first device" ((← a.backend.wallets a.dir).map (·.label) == ["Savings"])
  a.publish
  b.look
  check "…and stays on the second" ((← b.backend.wallets b.dir).map (·.label) == ["Savings"])
  a.stop
  b.stop

/-- The network's saved scan behind the open wallet (0.9.24 on a phone whose open wallet had been in a slot of
its own): the stack still opens, and scanning goes on from the saved frontier. -/
def scanBehindWallets (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let d ← device root "scanBehind" cloud cloudKeys
  discard <| d.create
  let added := Real.slotDir d.dir (← Real.freeSlot d.dir)
  IO.FS.createDirAll added
  discard <| d.backend.openWallet .signet added
  d.backend.startNetworking d.settings
  discard <| d.backend.createWallet .signet added
  Real.buildStackIfNeeded d.env
  let some f := (← d.env.get).stack.bind (·.filters) | throw "no scan"
  let saved ← f.nextScanHeight
  let opened (behind : String) : TM Unit := do
    d.backend.stopNetworking
    discard <| d.env.sleepWhile 2_000 (·.syncing)
    d.env.modify fun c => { c with lastSyncError := none }
    Real.buildStackIfNeeded d.env
    let c ← d.env.get
    check s!"the stack opens with the saved scan behind {behind}"
      ((c.stack.bind (·.filters)).isSome && c.lastSyncError.isNone) s!"{c.lastSyncError}"
    if let some f := c.stack.bind (·.filters) then
      check s!"…and scanning goes on from where it was saved ({behind})" ((← f.nextScanHeight) == saved)
  -- the open wallet further on than the saved scan, the other one not
  let some w := (← d.env.get).wallet | throw "no wallet"
  discard <| (w.recordScanHeight (saved + 50)).run
  opened "the open wallet"
  -- every wallet further on than the saved scan
  for r in (← d.env.get).riders do discard <| (r.wallet.recordScanHeight (saved + 50)).run
  opened "every wallet"
  d.stop

def accountsFollow (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "accountsA" cloud cloudKeys
  let b ← device root "accountsB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  let id ← sharedAccount a
  a.publish
  b.look
  let arriving := (← b.overview).arriving
  check "an account built on one device is on its way to the other" (arriving.map (·.id) == [id] && arriving.map (·.name) == ["Shared"])
  check "…and not yet among its accounts" ((← b.overview).accounts.isEmpty)
  let shown := (LeanNative.Html.toWire (multisigSection { (default : Model) with multisig := ← b.overview })).toJson.compress
  check "the list shows it as catching up" (contains shown (Ids.multisigArriving id) && contains shown "Catching up")
  b.look
  check "looking again takes it once" ((← b.overview).arriving.length == 1)
  -- this device's own scan is behind the block the account is current to: it waits
  let current := ((← b.app.multisig.host.arrivingAccounts).map (·.scannedThrough))[0]!
  b.catchUp current
  check "a device whose scan is behind the other's waits" ((← b.overview).arriving.length == 1 && (← b.overview).accounts.isEmpty)
  -- a capped pass keeps what it reached, and the next pass takes it up from the block after
  let asked ← IO.mkRef (#[] : Array UInt32)
  b.app.multisig.catchUp .signet (current + 5)
    (fun fromH _ _ _ => do asked.modify (·.push fromH); pure (some (current + 2), false)) (fun _ => pure none)
  check "a capped catch-up pass advances the arriving account and keeps it arriving"
    ((← b.overview).arriving.length == 1 && (← b.overview).accounts.isEmpty &&
     ((← b.app.multisig.host.arrivingAccounts).map (·.scannedThrough)) == #[current + 2])
  b.app.multisig.catchUp .signet (current + 5)
    (fun fromH toH _ _ => do asked.modify (·.push fromH); pure (some toH, true)) (fun _ => pure none)
  check "the next pass resumes from where the capped one stopped" ((← asked.get) == #[current + 1, current + 3])
  let onB := (← b.overview).accounts
  check "caught up, it is one of this device's accounts" (onB.map (·.id) == [id] && (← b.overview).arriving.isEmpty)
  check "the same account: descriptor, policy and first address"
    (onB.map (·.descriptor) == (← a.overview).accounts.map (·.descriptor) && onB.map (·.policy) == [some "2 of 2"] &&
     onB.map (·.receiveAddress) == (← a.overview).accounts.map (·.receiveAddress))
  check "watch-only there: that device's wallet is not one of its keys" (onB.map (·.watchOnly) == [true])
  check "not watch-only where it was built" ((← a.overview).accounts.map (·.watchOnly) == [false])
  let model : Model := { (default : Model) with multisig := ← b.overview }
  let list := (LeanNative.Html.toWire (multisigSection model)).toJson.compress
  let page := (LeanNative.Html.toWire (.col (multisigAccountSections model id))).toJson.compress
  check "the list and the account's page say watch-only" (contains list "Watch-only on this device" && contains page Ids.multisigWatchOnlyNote)
  -- the address counter goes to the highest, the name to the latest
  a.backend.newMultisigReceiveAddress id
  a.backend.newMultisigReceiveAddress id
  let rename : IO Unit := a.app.multisig.withStore fun s => do
    return (← s.rename a.app.multisig.host.keys a.app.multisig.host.writeData id "Household", ())
  rename
  a.publish
  b.look
  let onB := (← b.overview).accounts
  check "a new address on one device moves the other's counter" (onB.map (·.nextReceiveIndex) == [2])
  check "a rename travels" (onB.map (·.name) == ["Household"])
  b.backend.newMultisigReceiveAddress id
  b.publish
  a.look
  check "…both ways, and never back" ((← a.overview).accounts.map (·.nextReceiveIndex) == [3] && (← a.overview).accounts.map (·.name) == ["Household"])
  -- settled: the backups are saved, both look, and nothing moves again
  a.publish
  b.publish
  a.look
  b.look
  let uploads ← cloud.saves.get
  a.publish
  b.publish
  a.look
  b.look
  check "in step: another save and another look upload nothing" ((← cloud.saves.get) == uploads)
  -- removal: the device that only watches removes it, and it goes where it was built
  b.backend.removeMultisigAccount id
  b.publish
  b.look
  check "removed on one device: the other's backup does not bring it back" ((← b.overview).accounts.isEmpty && (← b.overview).arriving.isEmpty)
  a.look
  check "removed on one device: removed on the other" ((← a.overview).accounts.isEmpty)
  -- joined again later, it is back on both
  let again ← sharedAccount a "Shared again"
  check "the same account, built again" (again == id)
  a.publish
  b.look
  b.settle
  check "built again later: back on both" ((← b.overview).accounts.map (·.name) == ["Shared again"])
  a.stop
  b.stop

/-- A coin of `account` at its first receive address, as a scan would have filed it. -/
def coinOf (descriptor : String) (height : UInt32) : TM WalletUTXO := do
  let account ← need "account" (AnyMultisigAccount.parse descriptor .signet)
  let script ← need "script" (account.scriptPubKey 0 0)
  return { txid := ByteArray.mk (Array.replicate 32 7), vout := 0, amount := 50_000_000, scriptPubKey := script, chain := .receive,
           index := 0, height }

def removalStopsAtCoins (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "coinsA" cloud cloudKeys
  let b ← device root "coinsB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  let id ← sharedAccount a
  a.publish
  b.look
  b.settle
  -- a payment arrives where the account was built, after the other device took it
  let record := (← a.app.multisig.host.read).records[0]!
  let coin ← coinOf record.descriptor 1
  a.app.multisig.restore #[{ record with allUtxos := #[coin], nextReceiveIndex := 1 }]
  check "the first device sees a coin in the account" ((← a.overview).accounts.map (·.balance) == [50_000_000])
  b.backend.removeMultisigAccount id
  b.publish
  a.look
  check "removed on a device that saw it empty: it stays where its coins are" ((← a.overview).accounts.map (·.balance) == [50_000_000])
  a.publish
  b.look
  check "…and comes back to the device that removed it" ((← b.overview).arriving.map (·.id) == [id])
  b.settle
  check "with the coin" ((← b.overview).accounts.map (·.balance) == [50_000_000])
  check "which that device's own Remove now refuses" (← fails (b.backend.removeMultisigAccount id))
  -- the account goes from this device without its Remove (its file set aside, say): it is taken again
  b.publish
  a.look
  b.look
  check "in step, the other device's backup needs no second reading" ((← b.view).settled.size == 1)
  let drop : IO Unit := b.app.multisig.withStore fun s => do
    return (← s.remove b.app.multisig.host.keys b.app.multisig.host.writeData id, ())
  drop
  b.look
  check "an account lost here without being removed is taken again" ((← b.overview).arriving.map (·.id) == [id])
  a.look
  check "…and losing it removed nothing on the other device" ((← a.overview).accounts.map (·.balance) == [50_000_000])
  -- a reorg while an account is on its way: it goes back to the fork with its blocks
  let arriving := (← b.app.multisig.host.arrivingAccounts)[0]!
  let ahead : ArrivingAccount := { arriving with record := { arriving.record with allUtxos := #[← coinOf arriving.record.descriptor 120] },
                                                 scannedThrough := 125, passFrom := 101 }
  let back := ahead.rollBack 110
  check "a reorg below what an arriving account is current to takes it back to the fork"
    (back.scannedThrough == 110 && back.passFrom == 101 && back.record.allUtxos.isEmpty)
  check "…and one above it changes nothing" (ahead.rollBack 130 == ahead)
  a.stop
  b.stop

/-- A copy of `from`'s backup as a build from before devices kept in step saved it: no stamps. Its id. -/
def legacyCopy (cloud : Real.MemoryCloud) (cloudKeys : Real.CloudBackupKeys) (source : Device) : TM String := do
  let bundle ← source.app.exportedBundle
  let words := " ".intercalate (← source.backend.revealMnemonic)
  let state ← source.app.cloudAppState bundle
  let id ← UUIDText.random
  let key ← (Real.CloudM.toIO (cloudKeys.create id) : IO ByteArray)
  let backup ← need "legacy backup"
    (CloudWalletBackup.create { bundle with mnemonic := some words } key (appState := some ({ state with sync := none } : CloudAppState).encoded) (id := some id))
  cloud.records.modify (·.push backup)
  return id

def olderBackups (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "olderA" cloud cloudKeys
  let b ← device root "olderB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  let id ← sharedAccount a
  discard <| a.backend.addSignerKeys "Carol" (← testKey 0xC3)
  -- an install that is gone left a backup of the same things, written before devices kept in step
  let old ← legacyCopy cloud cloudKeys a
  check "the old backup is one more record" ((← cloud.count) == 3)
  b.look
  b.settle
  check "an old build's backup still gives its accounts and signers" ((← b.overview).accounts.map (·.id) == [id] && (← b.signerNames) == ["Carol"])
  -- removed since, on both: the old backup, which nobody updates, does not bring them back
  let carol := ((← a.overview).signers.head?.map (·.id)).getD ""
  a.backend.removeSigner carol
  a.backend.removeMultisigAccount id
  a.publish
  b.look
  check "removed on a device: gone on the other, old backup or not" ((← b.overview).accounts.isEmpty && (← b.signerNames) == [])
  b.publish
  a.look
  b.look
  check "…and it stays so" ((← a.overview).accounts.isEmpty && (← a.signerNames) == [] && (← b.overview).accounts.isEmpty && (← b.overview).arriving.isEmpty)
  -- a third device, new, reads the removal along with the old backup
  let c ← device root "olderC" cloud cloudKeys
  discard <| c.create
  c.look
  check "a new device takes the removal's word over the old backup's" ((← c.overview).accounts.isEmpty && (← c.overview).arriving.isEmpty && (← c.signerNames) == [])
  check "the old backup itself is untouched" ((← cloud.records.get).any (·.id == old))
  a.stop
  b.stop
  c.stop

/-- In an object, the value under `k` changed by `f`. -/
def editKey (k : String) (f : SwiftJSON.JV → SwiftJSON.JV) : SwiftJSON.JV → SwiftJSON.JV
  | .obj kvs => .obj (kvs.map fun (n, v) => if n == k then (n, f v) else (n, v))
  | v => v

/-- A backup as another build may have left it: `source`'s own things, with the bundle's JSON changed by
`bundle` and the app's context replaced by `context`, sealed under a key of its own (or, with `sealWith`,
under one iCloud Keychain does not hold for it). No restore would write these; an older app did. -/
def craftedCopy (cloud : Real.MemoryCloud) (cloudKeys : Real.CloudBackupKeys) (source : Device)
    (bundle : SwiftJSON.JV → SwiftJSON.JV := id) (context : Option ByteArray := none) (sealWith : Option ByteArray := none) :
    TM (String × ByteArray) := do
  let exported ← source.app.exportedBundle
  let id ← UUIDText.random
  let key ← (Real.CloudM.toIO (cloudKeys.create id) : IO ByteArray)
  let savedAt ← referenceDateNow
  let json := obj [("bundle", some (bundle ({ exported with mnemonic := none } : ImportBundle).toJV)),
                             ("appState", context.map SwiftJSON.ofData)]
  let box ← need "the sealed wallet box" (CloudWalletBackup.sealed (sealWith.getD key) (SwiftJSON.write json).toUTF8
    (CloudWalletBackup.context id exported.network (CloudWalletBackup.walletPurpose savedAt)))
  cloud.records.modify (·.push { version := 2, id, network := exported.network, savedAt, sealedPhrase := ByteArray.mk #[0], sealedWallet := box })
  return (id, key)

/-- Backups in forms a restore refuses. An older app's backup may hold an account of a kind this build does
not keep, a signer of another shape, or a context that no longer reads: a restore refuses the whole of it,
and a device keeping in step takes the rest. One that does not open at all is said so, with its date, and
is not fetched again and again. -/
def olderForms (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let gone ← device root "formsGone" cloud cloudKeys
  let b ← device root "formsB" cloud cloudKeys
  discard <| gone.create
  discard <| b.create
  let id ← sharedAccount gone
  discard <| gone.backend.addSignerKeys "Carol" (← testKey 0xC3)
  -- what the older app wrote: the account and the signer, and beside them an account of another kind, an
  -- entry that is no account, a signer of another shape, and a context this build does not read
  let (old, key) ← craftedCopy cloud cloudKeys gone
    (bundle := fun j =>
      let j := editKey "vaults" (fun
        | .arr xs => .arr (xs ++ #[editKey "id" (fun _ => .str "another-kind") (editKey "descriptor" (fun _ => .str "tr(musig(a,b))") (xs[0]?.getD .null)),
                                    .str "not an account"])
        | v => v) j
      editKey "signers" (fun | .arr xs => .arr (xs ++ #[.obj #[("label", .str "an older shape")]]) | v => v) j)
    (context := some "{\"people\":5}".toUTF8)
  -- the install is gone: its own backup with it, the older one left behind
  let own := ((← gone.app.controller.get).configuration.map (·.backup.id)).getD ""
  gone.stop
  cloud.records.modify (·.filter (·.id != own))
  let some backup := (← cloud.records.get).find? (·.id == old) | throw "the older backup is not in iCloud"
  check "a restore's reading refuses the whole backup" ((← (backup.state key).run) matches .error _)
  let shared ← need "the reading a device keeping in step makes" (backup.shared key)
  check "…and a device's reading has the account and the signer, and counts what it left"
    (shared.accounts.any (·.id == id) && shared.signers.size == 1 && shared.unread ≥ 2)
    s!"{shared.accounts.map (·.id)} {shared.signers.size} {shared.unread}"
  b.look
  b.settle
  check "the account and the signer follow from it" ((← b.overview).accounts.map (·.id) == [id] && (← b.signerNames) == ["Carol"])
    s!"{(← b.overview).accounts.map (·.id)} {(← b.overview).arriving.map (·.id)} {← b.signerNames}"
  let status ← b.app.follow.status.get
  check "the three it did not keep are counted, and the backup counts as read"
    (status.listed == 1 && status.unread.isEmpty && status.skipped == 3) s!"{status.listed} {status.unread.size} {status.skipped}"
  let note := ((← b.backend.cloudStatus).devicesNote).getD ""
  check "the backup page says both" (contains note "in step with 1 backup" && contains note "3 accounts or signers in those backups are of a kind this version does not keep") note
  -- one that does not open: sealed under another key than the one iCloud Keychain holds for it
  let (closed, _) ← craftedCopy cloud cloudKeys b (sealWith := some (ByteArray.mk (Array.replicate 32 7)))
  b.look
  let status ← b.app.follow.status.get
  check "a backup that does not open is said so, and the others are still read"
    (status.listed == 2 && status.unread.map (·.2) == #[Real.Unread.notOpened] && (← b.overview).accounts.map (·.id) == [id])
    s!"{status.listed} {status.unread.size}"
  let note := ((← b.backend.cloudStatus).devicesNote).getD ""
  check "the backup page says which, by when it was saved" (contains note "1 of 2 backups read" && contains note "1 backup (saved " && contains note "could not be opened") note
  check "it is not fetched again in this run" ((← b.app.follow.unopened.get).map (·.1) == #[closed])
  b.look
  check "…and is still said at the next look" (((← b.app.follow.status.get).unread.map (·.2)) == #[Real.Unread.notOpened])
  b.stop

/-- A wallet that changes while a round reads the other backups. What the round read was for the wallet that
was open; the stores it would write to are the next one's by the time it is done. It writes nothing. -/
def walletChangesMidRound (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "midA" cloud cloudKeys
  -- the second device's iCloud does something of the test's choosing while its list is read
  let during ← IO.mkRef (pure () : IO Unit)
  let listing : Real.CloudBackupStore := { cloud.store with list := fun n => do (← during.get); cloud.store.list n }
  let b ← device root "midB" cloud cloudKeys (store := some listing)
  discard <| a.create
  discard <| b.create
  discard <| a.backend.addSignerKeys "Dana" (← testKey 0xB2)
  a.publish
  during.set b.app.follow.reset
  b.look
  check "a round whose wallet changed while it read writes nothing" ((← b.signerNames) == [])
  during.set (pure ())
  b.look
  check "the next round, begun for the wallet now open, takes it" ((← b.signerNames) == ["Dana"])
  a.stop
  b.stop

/-- Two wallets on one device. Each has its own view, its own backup and its own signers; and what one adds
reaches the other through iCloud as it would reach another device, since each wallet's backup is one of the
others the open wallet reads. -/
def twoWalletsOneDevice (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let d ← device root "twoWallets" cloud cloudKeys
  let first ← d.create
  let added := Real.slotDir d.dir (← Real.freeSlot d.dir)
  IO.FS.createDirAll added
  check "an empty place beside the first wallet" ((← d.backend.openWallet .signet added) matches .missing)
  d.backend.startNetworking d.settings
  let second ← d.backend.createWallet .signet added
  unless ← waitUntil 5_000 (every := 10) (do return (← d.app.controller.get).lastSaved.isSome) do
    throw "the second wallet's backup was not saved"
  discard <| waitUntil 2_000 (every := 10) do
    let s ← d.app.controller.get
    return !s.scheduled && !s.busy
  check "the second wallet is another wallet, with a backup of its own" (second != first && (← cloud.count) == 2)
  discard <| d.backend.addSignerKeys "Dana" (← testKey 0xB2)
  d.publish
  check "its view is its own, in its own directory"
    ((← d.view).wallet == second && (← (System.FilePath.mk added / "device-sync.json").pathExists))
  -- the first wallet again: before the backup is pointed at it, a round does nothing
  check "the first wallet opens" ((← d.backend.openWallet .signet d.dir) matches .opened _)
  d.look
  check "a round before the backup knows which wallet is open takes nothing" ((← d.signerNames) == [])
  d.app.configureCurrent
  d.look
  check "the first wallet takes what the second added, as from another device" ((← d.signerNames) == ["Dana"])
  check "…into its own view and its own signers" ((← d.view).wallet == first)
  discard <| d.backend.addSignerKeys "Erin" (← testKey 0xC3)
  d.publish
  check "the second wallet opens" ((← d.backend.openWallet .signet added) matches .opened _)
  d.app.configureCurrent
  check "its signers are still only its own" ((← d.signerNames) == ["Dana"])
  d.look
  check "…until it looks, and takes the first wallet's" ((← d.signerNames).length == 2 && (← d.signerNames).contains "Erin")
  check "two wallets, two backups, no more" ((← cloud.count) == 2)
  -- the first, not open, is scanned for: its backup follows its scan, for another device's head start
  let some r := (← d.env.get).riders.find? (·.held.id == first) | throw "the first wallet is not scanned for"
  discard <| (r.wallet.recordScanHeight 500 (some (ByteArray.mk (Array.replicate 32 7)))).run
  d.look
  let heights : Array (UInt32 × Bool) ← (Real.CloudM.toIO do
    (← d.app.controller.store.list "signet").filterMapM fun summary => do
      let b ← d.app.controller.store.load summary.id (← d.app.controller.store.account)
      let key ← cloudKeys.load b.id
      match ← Real.CloudM.io (b.shared key).run with
      | .ok sh => pure (if sh.walletID == some first then some (sh.lastKnownHeight, sh.lastKnownBlockHash.isSome) else none)
      | .error _ => pure none : IO _)
  check "the wallet that is not open keeps its backup current, with the block it stands on" (heights.toList == [(499, true)])
    s!"{heights}"
  check "…in the same backup" ((← cloud.count) == 2)
  d.stop

def whenNothingFollows (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  -- the first device's key reaches the second only when the test says so (iCloud Keychain is its own service)
  let allKeys ← Real.memoryCloudKeys
  let arrived ← IO.mkRef false
  let created ← IO.mkRef (#[] : Array String)
  let late : Real.CloudBackupKeys :=
    { create := fun id => do created.modify (·.push id); allKeys.create id
      load := fun id => do
        if (← created.get).contains id || (← arrived.get) then allKeys.load id else Real.CloudM.throwIssue .keychainUnavailable }
  let a ← device root "nothingA" cloud allKeys
  let b ← device root "nothingB" cloud late
  discard <| a.create
  discard <| b.create
  discard <| a.backend.addSignerKeys "Dana" (← testKey 0xB2)
  a.publish
  -- the backup's key has not arrived
  b.look
  check "a backup whose key has not arrived is passed over" ((← b.signerNames) == [])
  let status ← b.app.follow.status.get
  check "…and it is counted as waiting for its key, to be looked for again"
    (status.listed == 1 && status.unread.map (·.2) == #[Real.Unread.keyMissing] && (← b.view).settled.isEmpty)
  let note := ((← b.backend.cloudStatus).devicesNote).getD ""
  check "…and the backup page says so, with when it was saved and where the key comes from"
    (contains note "0 of 1 backup read" && contains note "Waiting for the key of 1 backup (saved " && contains note "iCloud Keychain") note
  -- automatic backup off: nothing is read
  arrived.set true
  b.backend.setAutomaticCloudBackup false
  b.look
  check "with automatic backup off nothing follows" ((← b.signerNames) == [])
  check "…and the backup page says why" ((← b.backend.cloudStatus).devicesNote.isNone)
  let sheet := (LeanNative.Html.toWire (cloudBackupSheet { (default : Model) with cloud := ← b.backend.cloudStatus } [])).toJson.compress
  check "the backup page has the other devices' section" (contains sheet "Your other devices" && contains sheet "Off while automatic backup is off.")
  b.backend.setAutomaticCloudBackup true
  unless ← waitUntil 5_000 (every := 10) (do return (← b.app.controller.get).lastSaved.isSome) do
    throw s!"turned on again, the backup was not saved: {reprStr (← b.backend.cloudStatus)}"
  -- another Apple Account: this device's backup is bound to the first
  cloud.accountName.set "second-account"
  let refused ← fails b.look
  check "under another Apple Account nothing is read" (refused && (← b.signerNames) == [])
  cloud.accountName.set "first-account"
  -- iCloud unreachable
  cloud.accountUnavailable.set true
  let refused ← fails b.look
  check "without iCloud nothing is read, and nothing is lost" (refused && (← b.signerNames) == [])
  cloud.accountUnavailable.set false
  b.look
  check "back in reach, with the key arrived: it follows" ((← b.signerNames) == ["Dana"])
  check "the backup page says when the others were checked" (((← b.backend.cloudStatus).devicesNote.map (contains · "Other devices checked")) == some true)
  -- a wallet replaced on one device removes nothing on the other
  b.publish
  a.look
  b.backend.deleteWallet
  discard <| b.backend.openWallet .signet b.dir
  discard <| b.backend.createWallet .signet b.dir
  b.publish
  a.look
  check "a wallet deleted on one device removes nothing on the other" ((← a.signerNames) == ["Dana"])
  a.stop
  b.stop

def threeDevices (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "threeA" cloud cloudKeys
  let b ← device root "threeB" cloud cloudKeys
  let c ← device root "threeC" cloud cloudKeys
  for d in [a, b, c] do discard <| d.create
  -- each device does something of its own before any has looked
  let idA ← sharedAccount a "From A" 0xB2
  discard <| b.backend.addSignerKeys "From B" (← testKey 0xC3)
  let idC ← sharedAccount c "From C" 0xA1
  for d in [a, b, c] do d.publish
  -- they look in one order, save, and look in another
  for d in [c, a, b] do d.look
  for d in [a, b, c] do d.settle
  for d in [b, c, a] do d.publish
  for d in [b, a, c] do d.look
  for d in [a, b, c] do d.settle
  let accounts (d : Device) : IO (List String) := do
    return ((← d.overview).accounts.map (·.id)).toArray.qsort (· < ·) |>.toList
  let want := (#[idA, idC].qsort (· < ·)).toList
  check "three devices: every account on every one" ((← accounts a) == want && (← accounts b) == want && (← accounts c) == want)
  check "…and every signer" ((← a.signerNames) == ["From B"] && (← b.signerNames) == ["From B"] && (← c.signerNames) == ["From B"])
  let watching (d : Device) : IO (List String) := do
    return (((← d.overview).accounts.filter (·.watchOnly)).map (·.id)).toArray.qsort (· < ·) |>.toList
  check "each signs for what it built and watches the rest"
    ((← watching a) == [idC] && (← watching c) == [idA] && (← watching b) == want)
  -- one removes an account while another renames a signer; the third hears both
  b.backend.removeMultisigAccount idC
  let signer := ((← a.overview).signers.head?.map (·.id)).getD ""
  a.backend.renameSigner signer "Renamed on A"
  for d in [a, b, c] do d.publish
  for d in [c, b, a] do d.look
  for d in [a, b, c] do d.publish
  for d in [a, c, b] do d.look
  check "a removal on one and a rename on another reach all three"
    ((← accounts a) == [idA] && (← accounts b) == [idA] && (← accounts c) == [idA] &&
     (← a.signerNames) == ["Renamed on A"] && (← b.signerNames) == ["Renamed on A"] && (← c.signerNames) == ["Renamed on A"])
  for d in [a, b, c] do d.stop

/-- Nobody says when: two devices in the foreground, ticking as the app does, come into step by themselves. -/
def leftAlone (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "aloneA" cloud cloudKeys (devicesIntervalMs := 100)
  let b ← device root "aloneB" cloud cloudKeys (devicesIntervalMs := 100)
  discard <| a.create
  discard <| b.create
  -- no scene change is reported: a launch straight into the foreground has none, and the app's tick begins the loop
  let frank ← a.backend.addSignerKeys "Frank" (← testKey 0xB2)
  let both (cond : IO Bool) : IO Bool := waitUntil 20_000 (every := 50) do
    a.backend.cloudTick
    b.backend.cloudTick
    cond
  check "a signer saved on one open device reaches the other by itself" (← both do return (← b.signerNames) == ["Frank"])
  a.backend.renameSigner frank "Frances"
  check "and so does its new name" (← both do return (← b.signerNames) == ["Frances"])
  let onB := ((← b.overview).signers.head?.map (·.id)).getD ""
  b.backend.removeSigner onB
  check "and its removal, the other way" (← both do return (← a.signerNames) == [])
  check "the backup page says when the other devices were checked"
    (((← a.backend.cloudStatus).devicesNote.map (contains · "Other devices checked")) == some true)
  -- in the background nothing looks, whatever ticks
  a.stop
  IO.sleep 300
  discard <| b.backend.addSignerKeys "Gina" (← testKey 0xC3)
  b.publish
  for _ in [0:8] do
    a.backend.cloudTick
    IO.sleep 60
  check "a device in the background does not look" ((← a.signerNames) == [])
  b.stop
  -- test mode's switch for the journey: an absolute directory, or none
  let resolved (cloud : String) : Option String := match E2E.resolve (fun k =>
      [("WINNOW_E2E", "1"), ("WINNOW_E2E_ENTROPY", "04040404040404040404040404040404"), ("WINNOW_E2E_CLOUD", cloud)].lookup k) with
    | .active m => m.cloudDirectory
    | _ => none
  check "test mode takes an absolute directory for its iCloud, and nothing else"
    (resolved "/tmp/icloud" == some "/tmp/icloud" && resolved "icloud" == none)

/-- Test mode's iCloud of files (`WINNOW_E2E_CLOUD`), which the journey gives two launches: it carries a backup
and its key from one device to the other as the memory versions do. -/
def directoryCloud (root : System.FilePath) : TM Unit := do
  let dir := root / "icloud"
  let store := Real.directoryCloudStore dir
  let keys := Real.directoryCloudKeys dir
  let cloud ← Real.MemoryCloud.new
  let asFiles (name : String) : TM Device := do
    let d ← device root name cloud keys
    -- the same phone, its iCloud the directory
    let secrets ← IO.mkRef ({} : Keys.InMemorySecrets)
    let (backend, env, app) ← Backend.realWithCloud { d.env.deps with keyStore := inMemoryKeyStore secrets }
      (store := store) (keys := keys) (scheduleDelayMs := 20)
    return { d with backend, env, app, secrets }
  let a ← asFiles "filesA"
  let b ← asFiles "filesB"
  discard <| a.create
  discard <| b.create
  let id ← sharedAccount a
  discard <| a.backend.addSignerKeys "Hana" (← testKey 0xC3)
  a.publish
  check "two backups and their keys, as files" ((← dir.readDir).size == 4)
  let signetList : Array Real.CloudBackupSummary ← (Real.CloudM.toIO (store.list "signet") : IO _)
  let mainnetList : Array Real.CloudBackupSummary ← (Real.CloudM.toIO (store.list "mainnet") : IO _)
  check "listed newest first, each with its network" (signetList.size == 2 && mainnetList.isEmpty)
  b.look
  check "the directory carries an account and a signer from one device to the other"
    ((← b.overview).arriving.map (·.id) == [id] && (← b.signerNames) == ["Hana"])
    s!"{(← b.app.follow.status.get).message}"
  check "a key that is not there has not arrived"
    ((← (keys.load "00000000-0000-0000-0000-000000000000").run) matches .error (.issue .keychainUnavailable))
  a.stop
  b.stop

/-- The backup's context with the stamps in it, as the formats carry it. -/
def contextForms (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "formsA" cloud cloudKeys
  discard <| a.create
  discard <| a.backend.addSignerKeys "Erin" (← testKey 0xB2)
  let bundle ← a.app.exportedBundle
  let state ← a.app.cloudAppState bundle
  check "a backup's context says when its signers changed" ((state.sync.map (·.signers.size)) == some 1)
  let again ← need "decode" (CloudAppState.decode (some state.encoded) bundle)
  check "the context round-trips with it" (again == some state)
  -- a reader that cannot read the stamps takes the rest
  let text := String.fromUTF8! state.encoded
  let later := text.replace "\"sync\":{" "\"sync\":{\"later\":true,"
  let odd := (later.replace "\"version\":1,\"wallet\"" "\"version\":1,\"wallet\"").replace "\"signers\":[{\"added\"" "\"signers\":[{\"added\""
  let unreadable := odd.replace "\"deviceID\":" "\"deviceID\":\"x\",\"was\":"
  let read ← need "decode" (CloudAppState.decode (some unreadable.toUTF8) bundle)
  check "stamps this build cannot read are left out, and the context still restores"
    ((read.map (·.sync.isNone)) == some true && (read.map (·.people)) == some state.people)
  check "the saved copy does not hold the stamps, or anything else, in the clear" (
    !(← cloud.records.get).any fun b => contains (String.fromUTF8! (SwiftJSON.write b.toJV).toUTF8) "\"sync\"")
  a.stop

/-- Build a minimal canonical transaction and `PendingTx` for relay-file migration checks. -/
def dummyPendingTx (tag : UInt8) (attempt : Nat := 1) (now : Float := 1_700_000_000.0) : ByteArray × Winnow.IO.PendingTx :=
  let tx : Transaction :=
    { version := 2
      inputs := #[{ previousOutput := { txid := ByteArray.mk (Array.replicate 32 tag), vout := 0 },
                    scriptSig := .empty, sequence := 0xFFFF_FFFF, witness := #[] }]
      outputs := #[{ value := 1000, scriptPubKey := ByteArray.mk #[0x51] }]
      locktime := 0 }
  let raw := tx.serialized true
  (tx.txid, { rawTx := raw, transaction := tx, feeRate := some 2.5, attempt, nextAttemptAt := now })

/-- Edge cases of `migrateSlotStacks`: missing `wallets/`, rollback markers (valid with wallet + multisig,
valid without wallet, non-numeric, `> UInt32.max`), broadcast merging (existing key wins, new key added,
corrupt slot file preserved, corrupt shared file leaves slot untouched). -/
def slotStacksEdges (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "foldEdges" cloud cloudKeys
  discard <| a.create
  -- 1. Network dir with no `wallets/` subdirectory is a clean no-op
  let emptyNet := (root / "foldEdgesEmpty" / "signet").toString
  IO.FS.createDirAll emptyNet
  Real.migrateSlotStacks a.env .signet emptyNet
  check "migrateSlotStacks without wallets/ dir is a no-op" (!(← (System.FilePath.mk emptyNet / "broadcast.json").pathExists))

  -- 2. Slot with real wallet + multisig coin rolled back via valid marker
  a.backend.stopNetworking
  discard <| a.env.sleepWhile 2_000 (·.syncing)
  let slot1 := Real.slotDir a.dir "1"
  IO.FS.createDirAll slot1
  discard <| a.backend.openWallet .signet slot1
  discard <| a.backend.createWallet .signet slot1
  let some w1 := (← a.env.get).wallet | throw "no wallet in slot1"
  let recorded ← (w1.recordScanHeight 50).run
  check "slot1 scan height recorded at 50 before rollback" ((recorded matches .ok _) && (← w1.nextScanHeight) == 50)
  let msId ← sharedAccount a "SlotMS" 0xB4
  let rec0 := (← a.app.multisig.host.read).records[0]!
  let coin ← coinOf rec0.descriptor 25
  a.app.multisig.restore #[{ rec0 with allUtxos := #[coin], nextReceiveIndex := 1 }]
  -- switch back to main dir so slot1 is closed before migrating
  discard <| a.backend.openWallet .signet a.dir
  IO.FS.writeFile (System.FilePath.mk slot1 / Real.rollbackMarkerName) "10\n"
  let now := (← Real.unixNow).toFloat
  let (txidA, pA_slot) := dummyPendingTx 0xA1 5 now
  let (txidB, pB_slot) := dummyPendingTx 0xB2 1 now
  let (_, pA_shared) := dummyPendingTx 0xA1 2 now
  let sharedRelay := System.FilePath.mk a.dir / "broadcast.json"
  IO.FS.writeBinFile sharedRelay (Winnow.IO.TxBroadcaster.encodeStore (Std.HashMap.emptyWithCapacity.insert txidA pA_shared))
  let slot1Relay := System.FilePath.mk slot1 / "broadcast.json"
  IO.FS.writeBinFile slot1Relay
    (Winnow.IO.TxBroadcaster.encodeStore ((Std.HashMap.emptyWithCapacity.insert txidA pA_slot).insert txidB pB_slot))

  -- 3. Slot 2: non-numeric marker + corrupt slot broadcast.json (must be preserved)
  let slot2 := Real.slotDir a.dir "2"
  IO.FS.createDirAll slot2
  IO.FS.writeFile (System.FilePath.mk slot2 / Real.rollbackMarkerName) "not-a-number"
  IO.FS.writeFile (System.FilePath.mk slot2 / "broadcast.json") "{corrupt"

  -- 4. Slot 3: overflow (> 0xFFFF_FFFF) marker
  let slot3 := Real.slotDir a.dir "3"
  IO.FS.createDirAll slot3
  IO.FS.writeFile (System.FilePath.mk slot3 / Real.rollbackMarkerName) "5000000000"

  -- 5. Slot 4: valid marker with NO wallet file
  let slot4 := Real.slotDir a.dir "4"
  IO.FS.createDirAll slot4
  IO.FS.writeFile (System.FilePath.mk slot4 / Real.rollbackMarkerName) "7"

  Real.migrateSlotStacks a.env .signet a.dir

  -- Verify slot1 rollback + broadcast merge
  let reopened1 ← (Wallet.open (Real.walletPath slot1) a.env.deps.keyStore a.env.deps.random).run
  let rolledHeight ← match reopened1 with
    | .ok w => some <$> w.nextScanHeight
    | .error _ => pure none
  check "slot rollback marker rewinds slot wallet to fork + 1" (rolledHeight == some 11) s!"{rolledHeight}"
  let slot1Ms ← a.env.hooks.multisigAt .signet slot1
  discard <| slot1Ms.watchScripts .signet
  let merged ← match Winnow.IO.TxBroadcaster.decodeStore (← IO.FS.readBinFile sharedRelay) now with
    | .ok m => pure m
    | .error e => throw s!"decode merged broadcast.json failed: {e.description}"
  check "merge keeps existing shared tx entry and imports new slot tx"
    (merged.size == 2 && (merged[txidA]?.map (·.attempt)) == some 2 && (merged[txidB]?.map (·.attempt)) == some 1 &&
     !(← slot1Relay.pathExists))
    s!"size={merged.size} A={merged[txidA]?.map (·.attempt)} B={merged[txidB]?.map (·.attempt)}"
  check "corrupt slot broadcast.json is left untouched" (← (System.FilePath.mk slot2 / "broadcast.json").pathExists)
  check "rollback markers are cleaned up across slots"
    (!(← (System.FilePath.mk slot1 / Real.rollbackMarkerName).pathExists) &&
     !(← (System.FilePath.mk slot2 / Real.rollbackMarkerName).pathExists) &&
     !(← (System.FilePath.mk slot3 / Real.rollbackMarkerName).pathExists) &&
     !(← (System.FilePath.mk slot4 / Real.rollbackMarkerName).pathExists))

  -- 6. Corrupt shared broadcast.json must leave a valid slot broadcast.json untouched
  let slot5 := Real.slotDir a.dir "5"
  IO.FS.createDirAll slot5
  let slot5Relay := System.FilePath.mk slot5 / "broadcast.json"
  IO.FS.writeBinFile slot5Relay (Winnow.IO.TxBroadcaster.encodeStore (Std.HashMap.emptyWithCapacity.insert txidB pB_slot))
  IO.FS.writeFile sharedRelay "{corrupt-shared"
  Real.migrateSlotStacks a.env .signet a.dir
  check "corrupt shared broadcast.json leaves valid slot relay file intact" (← slot5Relay.pathExists)
  let _ := msId
  a.stop

/-- Edge and guard paths of `syncOnce`: no stack, concurrent `syncing` guard, `joined.isEmpty`,
transient (`.noPeers`) vs non-transient (`.relayOnly`) failure accounting, and `maxBlocks` background mode. -/
def syncOnceGuards (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let d ← device root "syncGuards" cloud cloudKeys
  discard <| d.create
  -- Add a second wallet (rider) so `catchUpArriving` exercises both open and rider loops
  let added := Real.slotDir d.dir (← Real.freeSlot d.dir)
  IO.FS.createDirAll added
  discard <| d.backend.openWallet .signet added
  d.backend.startNetworking d.settings
  discard <| d.backend.createWallet .signet added
  discard <| d.backend.openWallet .signet d.dir
  d.backend.stopNetworking
  -- 1. No stack -> false
  check "syncOnce without stack returns false" (!(← Real.syncOnce d.env))
  -- Build stack (peer 127.0.0.1:1 is unreachable, so connectedPeers is empty -> fast error)
  Real.buildStackIfNeeded d.env
  -- 2. Concurrent `syncing == true` guard -> false, syncPasses unchanged
  let passesBefore := (← d.env.get).syncPasses
  d.env.modify fun c => { c with syncing := true }
  let blocked ← Real.syncOnce d.env
  d.env.modify fun c => { c with syncing := false }
  check "syncOnce while already syncing returns false without claiming" (!blocked && (← d.env.get).syncPasses == passesBefore)
  -- 3. `maxBlocks := none` with unreachable peer -> transient `.noPeers` failure recorded
  let r1 ← Real.syncOnce d.env none
  let c1 ← d.env.get
  check "syncOnce transient noPeers records failure and clears syncing"
    (!r1 && !c1.syncing && c1.lastSyncError.isSome && c1.transientSyncFailures == 1 && c1.transientSyncError.isSome)
    s!"r1={r1} syncing={c1.syncing} tf={c1.transientSyncFailures} err={c1.lastSyncError}"
  -- 4. `maxBlocks := some 1` (background check) with pool in `.relayOnly` -> non-transient failure resets transient counter
  if let some s := c1.stack then
    s.pool.state.modify fun st => { st with mode := .relayOnly }
  let r2 ← Real.syncOnce d.env (some 1)
  let c2 ← d.env.get
  check "syncOnce non-transient relayOnly clears transient failure counter"
    (!r2 && !c2.syncing && c2.lastSyncError.isSome && c2.transientSyncFailures == 0 && c2.transientSyncError.isNone)
    s!"r2={r2} tf={c2.transientSyncFailures} err={c2.lastSyncError}"
  -- 5. `joined.isEmpty` when open wallet's multisig scripts fail and there are no riders
  d.env.modify fun c => { c with riders := #[] }
  let brokenEnv : Real.Env := { d.env with deps := { d.env.deps with hooks := { d.env.hooks with
    multisigWatchScripts := fun _ => pure (.error (.locked "keychain locked")) } } }
  let r3 ← Real.syncOnce brokenEnv none
  check "syncOnce with no joinable wallets returns false cleanly" (!r3 && !(← d.env.get).syncing)
  d.stop

/-- Exercise all paths of `SyncApp.renewWaiting`: empty list, entry without `note`, replicas not ahead,
invalid replica descriptor rejected by validation, and picking the highest of multiple newer replicas
while preserving local name, clearing draft and note, and leaving other arriving entries untouched. -/
def renewWaitingChecks (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "renewA" cloud cloudKeys
  let b ← device root "renewB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  -- 1. Empty arriving list -> clean no-op (exercises `loop.skip`)
  b.app.follow.renewWaiting #[]
  let id1 ← sharedAccount a "KeepQuiet" 0xB2
  let id2 ← sharedAccount a "NeedsRenew" 0xC3
  let recs := (← a.app.multisig.host.read).records
  let some rec1 := recs.find? (·.id == id1) | throw "missing rec1"
  let some rec2 := recs.find? (·.id == id2) | throw "missing rec2"
  let anchorOld := ByteArray.mk (Array.replicate 32 0x11)
  let anchor200 := ByteArray.mk (Array.replicate 32 0x22)
  let e1 : ArrivingAccount := ArrivingAccount.ofSnapshot rec1 100 (some anchorOld)
  let e2 : ArrivingAccount := { ArrivingAccount.ofSnapshot { rec2 with name := "LocalName" } 100 (some anchorOld) with
                                note := some Real.waitingForNewerCopyText }
  (RM.toIO (b.app.multisig.host.modifyArriving fun _ => pure (#[e1, e2], ())) : IO Unit)

  -- 2. Only older/same-height replicas -> e2 stays waiting at 100
  let rOlder : Replica := { id := "r90", height := 90, accounts := #[rec2] }
  let rSame : Replica := { id := "r100", height := 100, accounts := #[rec2] }
  b.app.follow.renewWaiting #[rOlder, rSame]
  let afterOlder := (← b.app.multisig.host.arrivingAccounts).find? (·.record.id == id2)
  check "renewWaiting ignores replicas not ahead of scannedThrough"
    ((afterOlder.map (·.scannedThrough)) == some 100 && (afterOlder.bind (·.note)).isSome)

  -- 3. Newer replica with invalid descriptor -> rejected by MultisigStore.validate, e2 stays waiting
  let badRec2 : MultisigAccountRecord := { rec2 with descriptor := "not-a-valid-descriptor" }
  b.app.follow.renewWaiting #[{ id := "rBad", height := 150, accounts := #[badRec2] }]
  let afterBad := (← b.app.multisig.host.arrivingAccounts).find? (·.record.id == id2)
  check "renewWaiting skips invalid snapshot records"
    ((afterBad.map (·.scannedThrough)) == some 100 && (afterBad.bind (·.note)).isSome)

  -- 4. Three newer replicas (120, 200, 160) -> picks 200, preserves local name, strips draft, clears note, leaves e1 alone
  let r120 : Replica := { id := "r120", height := 120, anchor := some anchorOld,
                          accounts := #[{ rec2 with name := "Remote120", nextReceiveIndex := 2 }] }
  let r200 : Replica := { id := "r200", height := 200, anchor := some anchor200,
                          accounts := #[{ rec2 with name := "Remote200", nextReceiveIndex := 5, draft := some (draftOf "x") }] }
  let r160 : Replica := { id := "r160", height := 160, anchor := some anchorOld,
                          accounts := #[{ rec2 with name := "Remote160", nextReceiveIndex := 3 }] }
  b.app.follow.renewWaiting #[r120, r200, r160]
  let allAfter ← b.app.multisig.host.arrivingAccounts
  let got1 := allAfter.find? (·.record.id == id1)
  let got2 := allAfter.find? (·.record.id == id2)
  check "renewWaiting leaves non-waiting entry untouched" (got1 == some e1)
  check "renewWaiting picks highest valid replica, keeps local name, drops draft, clears note"
    (match got2 with
     | some g => g.scannedThrough == 200 && g.anchor == some anchor200 && g.note.isNone &&
                 g.record.name == "LocalName" && g.record.draft.isNone && g.record.nextReceiveIndex == 5
     | none => false)
    s!"{got2.map fun g => (g.scannedThrough, g.note, g.record.name, g.record.nextReceiveIndex)}"
  a.stop
  b.stop

/-- Build a minimal v0 PSBT spending `coinOf`'s outpoint with one distinct input key-value pair so two copies combine. -/
def testPsbtBase64 (extraKeyByte : UInt8) (extraValByte : UInt8) : String :=
  let unsigned : Transaction :=
    { version := 2
      inputs := #[{ previousOutput := { txid := ByteArray.mk (Array.replicate 32 7), vout := 0 },
                    scriptSig := .empty, sequence := 0xFFFF_FFFF, witness := #[] }]
      outputs := #[{ value := 1000, scriptPubKey := ByteArray.mk #[0x51] }]
      locktime := 0 }
  let p : PSBT :=
    { globals := #[{ key := ByteArray.mk #[0x00], value := unsigned.serialized false }]
      inputs := #[⟨#[{ key := ByteArray.mk #[0xFC, extraKeyByte], value := ByteArray.mk #[extraValByte] }]⟩]
      outputs := #[⟨#[]⟩] }
  p.base64V0.toOption.getD ""

/-- Exercise every arm and guard of `SyncApp.applyAccountChange` (via `applyAccount`):
`rename` (valid/invalid/same-name on arriving & missing), `raise` (arriving & live & missing),
`ledger` (arriving & same-value & live & missing), `draft` (`!live` deferred, `live` set/clear),
and `combine` (`!live` deferred, missing local draft, invalid PSBT, identical PSBT, distinct PSBTs combined). -/
def applyAccountChangeChecks (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "applyA" cloud cloudKeys
  let b ← device root "applyB" cloud cloudKeys
  discard <| a.create
  discard <| b.create
  let id ← sharedAccount a "Initial" 0xB2
  let some rec0 := (← a.app.multisig.host.read).records.find? (·.id == id) | throw "missing rec0"
  let coin ← coinOf rec0.descriptor 10
  a.app.multisig.restore #[{ rec0 with allUtxos := #[coin], nextReceiveIndex := 1 }]
  let some recA := (← a.app.multisig.host.read).records.find? (·.id == id) | throw "missing recA"

  -- Put account into b's arriving list (`live == false`)
  let arr := ArrivingAccount.ofSnapshot recA 10 none
  (RM.toIO (b.app.multisig.host.modifyArriving fun _ => pure (#[arr], ())) : IO Unit)
  let applyChanges (d : Device) (acctId : String) (rec : MultisigAccountRecord) (changes : Array Change) :
      IO (Real.SyncView × Bool × Bool) := do
    let view ← d.view
    let localAcct : LocalAccount := { record := rec, seen := { stamps := { id := acctId }, name := rec.name }, removable := true }
    let dec : AccountDecision := { id := acctId, added := {}, removed := {}, existence := .unchanged, changes }
    d.app.follow.applyAccount view dec (some localAcct)

  -- Construct a valid LedgerRegistration belonging to `recA`'s parsed Taproot account
  let tapAcct ← need "taproot account" (MultisigAccount.parse recA.descriptor .signet)
  let some origin := tapAcct.allKeys.findSome? (·.origin) | throw "no key origin in descriptor"
  let .ok policy := Ledger.WalletPolicy.ofAccount "Shared" tapAcct | throw "ledger policy"
  let reg : LedgerRegistration :=
    { policyName := "Shared", policyID := policy.id, hmac := ByteArray.mk (Array.replicate 32 0x42),
      masterFingerprint := origin.fingerprint, keyPath := origin.path }

  -- 1. Arriving (`!live`): invalid rename refused (pending=true), valid rename/raise/ledger succeed, draft & combine deferred (pending=true)
  let (_, cBad, pBad) ← applyChanges b id recA #[.rename "" (stampOf 10)]
  check "applyAccountChange refuses empty name on arriving account" (!cBad && pBad)
  let (_, cMulti, pMulti) ← applyChanges b id recA #[.rename "Line1\nLine2" (stampOf 11)]
  check "applyAccountChange refuses multiline name on arriving account" (!cMulti && pMulti)
  let (_, cRen, pRen) ← applyChanges b id recA #[.rename "RenamedArriving" (stampOf 12), .raise 4 2, .ledger reg (stampOf 13)]
  let arrAfter := ((← b.app.multisig.host.arrivingAccounts).find? (·.record.id == id)).map (·.record)
  check "applyAccountChange updates rename, raise, and ledger on arriving account"
    (cRen && !pRen && (arrAfter.map fun r => (r.name, r.nextReceiveIndex, r.nextChangeIndex, r.ledger)) ==
      some ("RenamedArriving", 4, 2, some reg))
  let (_, cSame, pSame) ← applyChanges b id (arrAfter.getD recA) #[.rename "RenamedArriving" (stampOf 14), .ledger reg (stampOf 15)]
  check "applyAccountChange reports unchanged when rename/ledger match existing value" (!cSame && !pSame)
  let (_, cDraftDef, pDraftDef) ← applyChanges b id recA #[.draft (some (draftOf "x")) (stampOf 16)]
  let (_, cCombDef, pCombDef) ← applyChanges b id recA #[.combine #[draftOf "x"] (stampOf 17)]
  check "applyAccountChange defers draft and combine while account is arriving"
    (!cDraftDef && pDraftDef && !cCombDef && pCombDef)

  -- 2. Missing account ID -> store errors return pending=true on rename/raise/ledger/draft
  let (_, _, pMissRen) ← applyChanges a "nonexistent-id" recA #[.rename "X" (stampOf 20)]
  let (_, _, pMissRaise) ← applyChanges a "nonexistent-id" recA #[.raise 3 1]
  let (_, _, pMissLed) ← applyChanges a "nonexistent-id" recA #[.ledger reg (stampOf 21)]
  check "applyAccountChange marks pending when target account is missing" (pMissRen && pMissRaise && pMissLed)

  -- 3. Live account (`a`): ledger, draft set/clear, combine (none, invalid, identical, distinct)
  let (_, cLedLive, pLedLive) ← applyChanges a id recA #[.ledger reg (stampOf 30), .raise 2 1]
  check "applyAccountChange updates ledger and indices on live account" (cLedLive && !pLedLive)
  let (_, cCombNone, pCombNone) ← applyChanges a id { recA with draft := none } #[.combine #[draftOf "x"] (stampOf 31)]
  check "applyAccountChange combine without local draft is a clean no-op" (!cCombNone && !pCombNone)
  let (_, cCombBad, pCombBad) ← applyChanges a id { recA with draft := some (draftOf "not-base64!!!") } #[.combine #[draftOf "x"] (stampOf 32)]
  check "applyAccountChange combine with invalid PSBT returns pending" (!cCombBad && pCombBad)

  let psbtA := testPsbtBase64 0x01 0xAA
  let psbtB := testPsbtBase64 0x02 0xBB
  let (_, cDraftSet, pDraftSet) ← applyChanges a id recA #[.draft (some (draftOf psbtA)) (stampOf 33)]
  check "applyAccountChange sets draft on live account" (cDraftSet && !pDraftSet)
  let recWithDraft := ((← a.app.multisig.host.read).records.find? (·.id == id)).getD recA
  let (_, cCombSame, pCombSame) ← applyChanges a id recWithDraft #[.combine #[draftOf psbtA] (stampOf 34)]
  check "applyAccountChange combine with identical PSBT makes no write" (!cCombSame && !pCombSame)
  let (_, cCombDiff, pCombDiff) ← applyChanges a id recWithDraft #[.combine #[draftOf psbtB] (stampOf 35)]
  let recCombined := ((← a.app.multisig.host.read).records.find? (·.id == id)).getD recA
  check "applyAccountChange combines distinct partial PSBTs and stores result"
    (cCombDiff && !pCombDiff && recCombined.draft.map (·.psbtBase64) != some psbtA && recCombined.draft.isSome)
  let (_, cDraftClr, pDraftClr) ← applyChanges a id recCombined #[.draft none (stampOf 36)]
  check "applyAccountChange clears draft on live account"
    (cDraftClr && !pDraftClr && (((← a.app.multisig.host.read).records.find? (·.id == id)).bind (·.draft)).isNone)
  a.stop
  b.stop

/-- Exercise all guard and success paths of `SyncApp.headStartWallet` (via `headStart`):
pending sends guard, cardRestoreFrom guard, no ahead replica, highest-of-multiple-replicas fold,
anchor mismatch refusal, unreadable backup skip, different-wallet skip, not-further-on skip,
local-only-card skip, missing-multisig-account skip, and successful head start advancing height and card index. -/
def headStartWalletChecks (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let cloudKeys ← Real.memoryCloudKeys
  let a ← device root "hsUnitA" cloud cloudKeys
  let b ← device root "hsUnitB" cloud cloudKeys
  let c ← device root "hsUnitC" cloud cloudKeys
  let idA ← a.create
  discard <| c.create
  -- b imports a's seed so both hold the same wallet ID & account key
  discard <| b.backend.openWallet .signet b.dir
  b.backend.startNetworking b.settings
  let (idB, _) ← b.backend.importBundle .signet b.dir (← a.backend.exportBundle true)
  check "headStart unit: b holds the same wallet as a" (idA == idB)
  discard <| waitUntil 2_000 (every := 10) do
    let s ← b.app.controller.get
    return !s.scheduled && !s.busy
  b.backend.stopNetworking
  Real.buildStackIfNeeded b.env
  let some stackB := (← b.env.get).stack | throw "no stack on b"
  let some wA := (← a.env.get).wallet | throw "no wallet on a"
  let some wB := (← b.env.get).wallet | throw "no wallet on b"
  let some genesis ← stackB.chain.blockHash 0 | throw "no genesis hash"
  let wrongAnchor := ByteArray.mk (Array.replicate 32 0xEE)
  let setBState (f : WalletState → WalletState) : IO Unit := do
    let next := f (← wB.state)
    discard <| (wB.persist next).run
    wB.stateRef.set next
  let setAState (f : WalletState → WalletState) : IO Unit := do
    let next := f (← wA.state)
    discard <| (wA.persist next).run
    wA.stateRef.set next

  -- Issue a real card on `a`, advance its cursor to 4 and nextScanHeight to 1, and publish `a` and `c`
  a.backend.stopNetworking
  discard <| (wA.issueCard).run
  setAState fun st => { st with nextScanHeight := 1, cards := st.cards.map fun x => { x with nextIndex := 4 } }
  a.publish
  let some backupA := (← a.app.controller.get).configuration.map (·.backup.id) | throw "no backupA"
  let some card0A := (← wA.state).cards[0]? | throw "no card0A"
  c.publish
  let some backupC := (← c.app.controller.get).configuration.map (·.backup.id) | throw "no backupC"
  -- Crafted backup whose wallet fails Wallet.importing (`lastKnownHeight == 0xFFFF_FFFF`)
  let (badWalletBackup, _) ← craftedCopy cloud cloudKeys a
    (bundle := editKey "lastKnownHeight" (fun _ => SwiftJSON.ofInt 0xFFFF_FFFF))

  -- Put b at nextScanHeight = 0 so replica height 0 satisfies `r.height + 1 > 0`
  setBState fun st => { st with nextScanHeight := 0 }
  let mkRep (bid : String) (h : UInt32 := 0) (anc : Option ByteArray := some genesis) : Replica :=
    { id := bid, height := h, anchor := anc, walletID := some idB }

  -- 1. Pending sends guard -> early return
  let dummyPending : PendingSend :=
    { rawTransaction := ByteArray.mk #[1], selected := #[], changeIndex := none, changeOutputIndex := none, fee := 100 }
  setBState fun st => { st with pendingSends := #[dummyPending] }
  b.app.follow.lastFound.set #[mkRep backupA]
  b.app.follow.headStart
  check "headStartWallet skips while pendingSends is non-empty" ((← b.app.follow.journaled.get).isNone)
  setBState fun st => { st with pendingSends := #[] }

  -- 2. cardRestoreFrom guard -> early return
  setBState fun st => { st with cardRestoreFrom := some 0 }
  b.app.follow.headStart
  check "headStartWallet skips while cardRestoreFrom is active" ((← b.app.follow.journaled.get).isNone)
  setBState fun st => { st with cardRestoreFrom := none }

  -- 3. No ahead replica -> early return
  b.app.follow.lastFound.set #[]
  b.app.follow.headStart
  check "headStartWallet with no ahead replicas is a no-op" ((← wB.nextScanHeight) == 0)

  -- 4. Multiple ahead replicas (0, 2, 1) -> fold picks highest (2), whose anchor disagrees -> refused
  b.app.follow.lastFound.set #[mkRep backupA 0 (some genesis), mkRep backupA 2 (some wrongAnchor), mkRep backupA 1 (some wrongAnchor)]
  b.app.follow.headStart
  check "headStartWallet refuses mismatched anchor on highest replica" ((← wB.nextScanHeight) == 0)

  -- 5. Missing backup/key -> "the backup did not open"
  b.app.follow.lastFound.set #[mkRep "00000000-0000-0000-0000-000000000000"]
  b.app.follow.headStart
  check "headStartWallet skips unreadable backup"
    ((← b.app.follow.journaled.get).any (contains · "the backup did not open"))
    s!"{← b.app.follow.journaled.get}"

  -- 6. Backup whose wallet fails validation -> "the backup's wallet did not read"
  b.app.follow.lastFound.set #[mkRep badWalletBackup]
  b.app.follow.headStart
  check "headStartWallet skips backup whose wallet fails to import"
    ((← b.app.follow.journaled.get).any (contains · "the backup's wallet did not read"))
    s!"{← b.app.follow.journaled.get}"

  -- 7. Different wallet backup -> "another wallet"
  b.app.follow.lastFound.set #[mkRep backupC]
  b.app.follow.headStart
  check "headStartWallet skips backup of another wallet"
    ((← b.app.follow.journaled.get).any (contains · "another wallet"))
    s!"{← b.app.follow.journaled.get}"

  -- 8. Local card handed out here only (`plainToo := false`) -> "a card handed out here only"
  let localOnlyCard : IssuedCard := { index := 7, tweak := ByteArray.mk (Array.replicate 32 0x44), nextIndex := 1, plainToo := false }
  setBState fun st => { st with cards := #[localOnlyCard] }
  b.app.follow.lastFound.set #[mkRep backupA]
  b.app.follow.headStart
  check "headStartWallet skips when a local-only card is missing from backup"
    ((← b.app.follow.journaled.get).any (contains · "a card handed out here only"))
    s!"{← b.app.follow.journaled.get}"

  -- 9. Local multisig account not in backup -> "the accounts here are not all in the backup"
  setBState fun st => { st with cards := #[] }
  let extraId ← sharedAccount b "LocalOnlyAcct" 0xD4
  b.app.follow.headStart
  check "headStartWallet skips when local accounts are absent from backup"
    ((← b.app.follow.journaled.get).any (contains · "the accounts here are not all in the backup"))
    s!"{← b.app.follow.journaled.get}"
  b.backend.removeMultisigAccount extraId

  -- 10. Success: matching card0 (nextIndex 1 -> 4) + plainToo card kept -> advances nextScanHeight 0 -> 1
  let card0B : IssuedCard := { card0A with nextIndex := 1 }
  let plainCard : IssuedCard := { index := 2, tweak := ByteArray.mk (Array.replicate 32 0x55), nextIndex := 2, plainToo := true }
  setBState fun st => { st with cards := #[card0B, plainCard] }
  b.app.follow.headStart
  let finalB ← wB.state
  check "headStartWallet advances scan height and raises matching card nextIndex while keeping plainToo card"
    (finalB.nextScanHeight == 1 &&
     (finalB.cards.find? (·.index == 0)).map (·.nextIndex) == some 4 &&
     (finalB.cards.find? (·.index == 2)).map (·.nextIndex) == some 2)
    s!"next={finalB.nextScanHeight} cards={finalB.cards.map fun x => (x.index, x.nextIndex)}"
  a.stop
  b.stop
  c.stop

def main : IO UInt32 := runMain "device-sync-test" do
  runTest "stampForms" stampForms
  runTest "stampingRules" stampingRules
  runTest "existenceRules" existenceRules
  runTest "changeRules" changeRules
  runTest "signerRules" signerRules
  let root ← IO.FS.createTempDir
  runTest "contextForms" (contextForms root)
  runTest "signersFollow" (signersFollow root)
  runTest "ledgersFollow" (ledgersFollow root)
  runTest "accountsFollow" (accountsFollow root)
  runTest "anchoredArrivals" (anchoredArrivals root)
  runTest "slotStacksFold" (slotStacksFold root)
  runTest "slotStacksEdges" (slotStacksEdges root)
  runTest "syncOnceGuards" (syncOnceGuards root)
  runTest "renewWaitingChecks" (renewWaitingChecks root)
  runTest "applyAccountChangeChecks" (applyAccountChangeChecks root)
  runTest "headStartWalletChecks" (headStartWalletChecks root)
  runTest "namesFollow" (namesFollow root)
  runTest "scanBehindWallets" (scanBehindWallets root)
  runTest "removalStopsAtCoins" (removalStopsAtCoins root)
  runTest "olderBackups" (olderBackups root)
  runTest "olderForms" (olderForms root)
  runTest "walletChangesMidRound" (walletChangesMidRound root)
  runTest "twoWalletsOneDevice" (twoWalletsOneDevice root)
  runTest "whenNothingFollows" (whenNothingFollows root)
  runTest "threeDevices" (threeDevices root)
  runTest "leftAlone" (leftAlone root)
  runTest "directoryCloud" (directoryCloud root)
  try IO.FS.removeDirAll root catch _ => pure ()
