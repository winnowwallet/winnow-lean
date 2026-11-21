import LeanNative.Journey
import WinnowApp.Ids
import Journeys.Screens

/-! # Multi-device sync and multi-profile journeys -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- An account follows a person from one device to another. Two launches with two seeds are the two devices,
and a directory both are given stands in for their iCloud (`WINNOW_E2E_CLOUD`; test mode has no iCloud
otherwise). The first builds a 2-of-2 with a Core key, is paid, and saves its backup. The second, a different
wallet, is told nothing: it lists the account by itself, with the balance its own scan confirms and the next
address Core derives, and says it only watches, since its wallet holds none of the account's keys. -/
def accountFollowsDevices : Journey := ⟨"accountFollowsDevices", do
  let r ← Run.new "devices"
  let h := r.host
  let run ← randomHex 4
  let core ← h.coreSigner s!"ui-core-devices-{run}"
  let cloud := s!"{h.fixture}/icloud-{run}"
  IO.FS.createDirAll cloud
  r.launch "devicesfirst" [("WINNOW_E2E_CLOUD", cloud)]
  createWallet

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
    waitUntil 60 "the first device's backup was not saved after the payment" (every := 0.5) do savedSince cloud marker
    shot "40-devices-first"

  step "a second device, another wallet, the same iCloud: the account is there by itself, under Watching" do
    r.launch "devicessecond" [("WINNOW_E2E_CLOUD", cloud)]
    createWallet
    waitFor homeWatchingRow 120
    scrolled homeWatchingRow
    tap homeWatchingRow
    waitFor (multisigAccount account) 30
    waitFor (multisigWatchOnly account) 10
    expectEq "the account's name" (← text (multisigAccount account)) "Phone and Core"
    shot "41-devices-second-home"

  step "its page says it only watches, with the balance and Core's next address" do
    openAccountRow account
    waitFor multisigWatchOnlyNote 20
    waitForBalance funding multisigBalance
    expectEq "the next address, the one after the paid one (Core's)" (← Account.receiveAddress) (← h.deriveAddress descriptor 1)
    shot "42-devices-watch-only"⟩

/-- Two wallets on one device. Settings → Wallets adds a second beside the first, through the onboarding
there already is. The second builds a 2-of-2 of itself and the first; the node pays it; a payment from it is
signed by the wallet that is open and then, with a button and a device check of its own, by the other wallet
kept on the device; and the node takes a witness with both signatures. No other device takes part. -/
def twoWalletsOneDevice : Journey := ⟨"twoWalletsOneDevice", do
  let r ← Run.new "wallets"
  let h := r.host
  r.launch "wallets"
  createWallet

  let firstKey ← step "the first wallet's key, as it is sent to whoever builds an account" do
    openMultisigAccounts
    tap multisigAddButton
    waitFor multisigKeyText 10
    let key ← text multisigKeyText
    backToWalletList
    pure key

  step "Settings → Profiles → Add a profile: a second one, made beside the first" do
    openSettings
    scrolled addWalletButton
    shot "60-wallets-one"
    tap addWalletButton
    waitFor cancelAddWalletButton 60
    shot "61-wallets-add"
    tap createWalletButton
    waitFor receiveButton 60
    waitFor balanceText 30
    openSettings
    scrolled addWalletButton
    waitUntil 20 "Settings does not list two profiles" do return (← exists? (.text "^Wallet [0-9a-f]{8}$"))
    shot "62-wallets-two"
    backToWalletList

  let descriptor ← step "the second wallet builds a 2-of-2 of itself and the first" do
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
  step "a payment from it: the open wallet signs, and one signature is not enough" do
    Send.fromAccount r account destination payment "needs 2 of 2"
    Collect.countIs multisigSignatureCount "1 of 2"
    shot "63-wallets-one-signature"

  step "the other profile kept here holds the second key: the payment goes to it, it opens, and it signs" do
    scrolled (.beginning "Switch to ")
    tap (.beginning "Switch to ")
    waitFor multisigSignButton 60
    Collect.countIs multisigSignatureCount "1 of 2"
    shot "64-wallets-switched"
    tap multisigSignButton
    Collect.countIs multisigSignatureCount "2 of 2" 60
    shot "65-wallets-two-signatures"

  step "the phone broadcasts, and the node takes it" do
    -- from the payment's own page (the Send sheet that began it was the other profile's)
    scrolled multisigBroadcastButton
    let before ← h.mempool
    tap multisigBroadcastButton
    let txid ← h.newMempoolTransaction before 30
    h.expectPays txid destination payment⟩

end WinnowJourneys
