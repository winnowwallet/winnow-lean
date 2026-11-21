import LeanNative.Journey
import WinnowApp.Ids
import WinnowApp.Format
import Journeys.Screens

/-! # Multi-device sync and multi-profile journeys -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- An account and a paired Ledger follow a person from one device to another. Two launches with two seeds are the two
devices, and a directory both are given stands in for their iCloud (`WINNOW_E2E_CLOUD`; test mode has no iCloud
otherwise). The first pairs a simulated Ledger, builds a 2-of-2 with a Core key, is paid, and saves its backup. The
second, a different wallet with no Ledger attached, is told nothing: it lists the account by itself under Watching, with
the balance its own scan confirms and the next address Core derives, says it only watches since its wallet holds none of
the account's keys, lists the paired Ledger as paired on another device, and confirms reading the other device's backup
under iCloud backup. -/
def accountFollowsDevices : Journey := ⟨"accountFollowsDevices", do
  let r ← Run.new "devices"
  let h := r.host
  let run ← randomHex 4
  let core ← h.coreSigner s!"ui-core-devices-{run}"
  let cloud := s!"{h.fixture}/icloud-{run}"
  IO.FS.createDirAll cloud
  r.launch "devicesfirst" [("WINNOW_E2E_CLOUD", cloud), ("WINNOW_E2E_LEDGER", ← randomHex 16)]
  createWallet (bluetooth := true)
  step "Bluetooth, then Not now on the Ledger nearby" Ledger.notNow

  step "the first device pairs a Ledger" do
    Ledger.pair "Nano X"
    backToWalletList

  let descriptor ← step "the first device builds a 2-of-2 of this phone and a Core key" do
    openMultisigAccounts
    Builder.start
    Builder.name "Phone and Core"
    Builder.addPastedMember r core.keyExpression
    waitFor (.beginning "Members · 2") 10
    Builder.create
  let account := accountID descriptor
  h.importAccount core descriptor

  step "the node funds it, and the first device's backup is saved with it" do
    Builder.openAccount
    let first ← h.deriveAddress descriptor 0
    expectEq "the account's first address (Core's)" (← Account.receiveAddress) first
    discard <| h.fund first funding
    waitForBalance funding multisigBalance
    let marker := s!"{cloud}/seen"
    IO.FS.writeFile marker ""
    -- if the scheduled backup already wrote the funded state just before `marker` was touched, one more block
    -- advances `lastKnownHeight` and guarantees a fresh backup digest after `marker` without moving index 1
    h.mine 1
    waitUntil 60 "the first device's backup was not saved after the payment" (every := 0.5) do savedSince cloud marker
    shot "85-devices-first"

  step "a second device, another wallet, the same iCloud: the account is there by itself, under Watching" do
    r.launch "devicessecond" [("WINNOW_E2E_CLOUD", cloud)]
    createWallet
    waitFor homeWatchingRow 120
    scrolled homeWatchingRow
    tap homeWatchingRow
    waitFor (multisigAccount account) 30
    waitFor (multisigWatchOnly account) 10
    expectEq "the account's name" (← text (multisigAccount account)) "Phone and Core"
    shot "86-devices-second-watching"

  step "its page says it only watches, with the balance and Core's next address" do
    openAccountRow account
    waitFor multisigWatchOnlyNote 20
    waitForBalance funding multisigBalance
    expectEq "the next address, the one after the paid one (Core's)" (← Account.receiveAddress) (← h.deriveAddress descriptor 1)
    shot "87-devices-watch-only"

  step "the paired Ledger followed too, marked paired on another device, and iCloud backup confirms reading it" do
    backToWalletList
    openSettings
    scrolled signersButton
    tap signersButton
    waitFor (.button "Nano X") 30
    scrolled (.button "Nano X")
    waitFor (.beginning "Paired on another device.") 10
    scrolled (.beginning "Paired on another device.")
    shot "88-devices-ledger-sync"
    tap .back
    waitFor networkSyncButton 10
    scrolled (.button "iCloud backup")
    tap (.button "iCloud backup")
    waitFor cloudDevicesNote 10
    scrolled cloudDevicesNote
    waitUntil 20 "iCloud backup does not confirm reading the other device's backup" (every := 0.5) do
      let note ← text cloudDevicesNote 1
      return note.startsWith "Other devices checked " && (note.splitOn "in step with 1 backup").length > 1
    tap (.button "Close")
    h.unload [core]⟩

/-- Two profiles on one device. Settings → Profiles adds a second beside the first, through the onboarding there already
is, and Home's profile pill renames it to Savings. Global sync scans for every profile on the device: a payment to the
inactive first profile arrives while Savings stays open and is already there when the first profile is opened. Savings
then builds a 2-of-2 of itself and the first; the node pays it; a payment from it is signed by the profile that is open
and then, with a button and a device check of its own, by the other profile kept on the device; and the node takes a
witness with both signatures. No other device takes part. -/
def twoWalletsOneDevice : Journey := ⟨"twoWalletsOneDevice", do
  let r ← Run.new "wallets"
  let h := r.host
  r.launch "wallets"
  createWallet

  let (firstLabel, firstID, firstReceive, firstKey) ← step "the first profile's receive address and multisig key" do
    waitFor walletNameButton 10
    let firstLabel ← text walletNameButton
    expect (firstLabel.startsWith "Wallet ") s!"unexpected first profile label: {firstLabel}"
    let firstID := (firstLabel.drop 7).copy
    let firstReceive ← Receive.address
    Receive.close
    openMultisigAccounts
    tap multisigAddButton
    waitFor multisigKeyText 10
    let key ← text multisigKeyText
    backToWalletList
    pure (firstLabel, firstID, firstReceive, key)

  step "Settings → Profiles → Add a profile: a second one, made beside the first" do
    openSettings
    scrolled addWalletButton
    shot "90-profiles-one"
    tap addWalletButton
    waitFor cancelAddWalletButton 60
    shot "91-profiles-add"
    tap createWalletButton
    waitFor receiveButton 60
    waitFor balanceText 30

  step "rename the second profile from Home's profile pill to Savings" do
    Profiles.openSheet
    Profiles.rename "Savings"
    waitFor (.text "^Savings$") 10
    waitFor (.text "^Open$") 10
    waitFor (walletRow firstID) 10
    expectEq "the first profile's row" (← text (walletRow firstID)) firstLabel
    shot "92-profiles-two-renamed"
    tap (.button "Done")
    expectGone renameWalletButton 10
    waitFor walletNameButton 10
    expectEq "the open profile's name on Home" (← text walletNameButton) "Savings"

  step "global sync: the node pays the inactive first profile while Savings stays open" do
    let fundingTx ← h.fund firstReceive smallCoin
    let tip ← h.height
    openSettings
    tap networkSyncButton
    let target := s!"block {WinnowApp.groupDigits tip} of {WinnowApp.groupDigits tip}"
    waitUntil 60 s!"Savings did not scan through {target}" (every := 0.5) do
      return (← exists? (.beginning target)) && (← text syncStatus 1) == "Up to date"
    -- back through Settings to Home (Sync shows balanceText too, so not backToWalletList)
    for _ in [0:4] do
      if ← exists? settingsButton then break
      tap .back
      pause 0.5
    waitFor settingsButton 10
    expectEq "Savings's own balance (the coin belongs to the other profile)" (← balance) (some 0)
    Profiles.openSheet
    scrolled (walletRow firstID)
    tap (walletRow firstID)
    waitFor walletNameButton 30
    waitUntil 20 "the first profile did not open" (every := 0.25) do
      return (← text walletNameButton 1) == firstLabel
    waitUntil 15 "the first profile did not already hold the coin synced while inactive" (every := 0.25) do
      return (← balance) == some smallCoin
    waitFor (historyPayment fundingTx) 20
    waitSynced
    shot "93-profiles-inactive-funded"
    Profiles.openSheet
    scrolled (.button "Savings")
    tap (.button "Savings")
    waitFor walletNameButton 30
    waitUntil 20 "Savings did not reopen" (every := 0.25) do
      return (← text walletNameButton 1) == "Savings"
    waitFor balanceText 30

  let descriptor ← step "Savings builds a 2-of-2 of itself and the first profile" do
    openMultisigAccounts
    Builder.start
    Builder.name "Both wallets"
    Builder.addPastedMember r firstKey
    waitFor (.beginning "Members · 2") 10
    Builder.create
  let account := accountID descriptor

  step "the node pays the account" do
    Builder.openAccount
    discard <| h.fund (← Account.receiveAddress) funding
    waitForBalance funding multisigBalance

  let destination ← h.bankAddress
  step "a payment from it: the open profile signs, and one signature is not enough" do
    Send.fromAccount r account destination payment "needs 2 of 2"
    Collect.countIs multisigSignatureCount "1 of 2"
    shot "94-profiles-one-signature"

  step "the other profile kept here holds the second key: the payment goes to it, it opens, and it signs" do
    scrolled (.beginning "Switch to ")
    tap (.beginning "Switch to ")
    waitFor (.nav "Awaiting signatures") 60
    waitFor multisigSignButton 60
    waitUntil 30 "Add this phone's signature did not enable after switching" (every := 0.25) do
      return (← state multisigSignButton).enabled
    Collect.countIs multisigSignatureCount "1 of 2"
    shot "95-profiles-switched"
    tap multisigSignButton
    Collect.countIs multisigSignatureCount "2 of 2" 60
    shot "96-profiles-two-signatures"

  step "the phone broadcasts, and the node takes it" do
    -- from the payment's own page (the Send sheet that began it was the other profile's)
    scrolled multisigBroadcastButton
    let before ← h.mempool
    tap multisigBroadcastButton
    let txid ← h.newMempoolTransaction before 30
    h.expectPays txid destination payment⟩

end WinnowJourneys
