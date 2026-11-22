import Journeys.Screens

/-! # Journeys in which the shell's answers fail

Headless only (`failNext`): the fake shell answers a capability as the system does when it fails, and the app
must show the failure where the person is, then go on when the next answer is good. Each step is one of the
failure screens `Model.fail` routes to (the journeys' `coverage.json` names the ones still never shown). -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- What the app says when the Keychain answers as a locked device's does (`errSecInteractionNotAllowed`). -/
def keychainLocked : Find := .text "can only be unlocked while Winnow is on screen and the device is unlocked"

/-- With device authentication asked for as on a phone (`WINNOW_E2E_DEVICE_AUTH=1`): the person cancelling it
before creating the wallet, the Keychain refusing the new wallet's key, the person cancelling before the recovery
phrase, the Keychain refusing to read the phrase under the authentication, the person cancelling before the backup
file, and the Keychain refusing to delete the wallet. In a simulator the shell is the real one:
the journey says so and does nothing. -/
def capabilityFailures : Journey := ⟨"capabilityFailures", do
  unless ← headless do
    log "the shell's answers fail only headless"
    return
  let r ← Run.new "capfail"
  r.launch "capfail" [("WINNOW_E2E_DEVICE_AUTH", "1")]

  step "the person cancels the authentication before creating: no wallet, nothing said" do
    waitFor createWalletButton 60
    failNext "auth"
    tap createWalletButton
    waitUntil 10 "Create new wallet is not enabled again" do return (← state createWalletButton).enabled
    expect (!(← exists? receiveButton)) "a wallet was created although the authentication was cancelled"
    expect (!(← exists? keychainLocked)) "a cancelled authentication was reported as a failure"

  step "the Keychain refuses the new wallet's key: onboarding says why, and Create again makes it" do
    failNext "keychain.add"
    tap createWalletButton
    waitFor keychainLocked 20
    shot "fail-01-create"
    createWallet
    expectGone keychainLocked

  step "the person cancels the authentication before the phrase: nothing shown, nothing said" do
    openSettings
    scrolled revealPhraseButton
    failNext "auth"
    tap revealPhraseButton
    waitUntil 10 "Show recovery phrase is not enabled again" do return (← state revealPhraseButton).enabled
    expect (!(← exists? (.nav "Recovery phrase"))) "the phrase was shown although the authentication was cancelled"
    expect (!(← exists? keychainLocked)) "a cancelled authentication was reported as a failure"

  step "the Keychain refuses to read the phrase: the Backup section says why" do
    -- the read made under the authentication, not the app's own reads in the background
    failNext "keychain.get" (when := [("context", "*")])
    tap revealPhraseButton
    waitFor keychainLocked 20
    shot "fail-02-reveal"
    expect (!(← exists? (.nav "Recovery phrase"))) "the phrase was shown although it could not be read"

  step "the person cancels the authentication before a backup file with the phrase: no file, nothing said" do
    scrolled exportBundleButton
    tap exportBundleButton
    -- only a file with the recovery phrase is asked for as showing the phrase is
    tap (.text "^Include recovery phrase$")
    failNext "auth"
    tap (.button "Create backup file")
    tap (.alert "Export with phrase")
    waitUntil 10 "Create backup file is not enabled again" do return (← state (.button "Create backup file")).enabled
    expect (!(← exists? (.text "^Includes your recovery words"))) "a backup file was made although the authentication was cancelled"
    tap (.button "Close")

  step "the Keychain refuses to delete the wallet: the alert says it could not" do
    scrolled (.button "Delete wallet from this device")
    tap (.button "Delete wallet from this device")
    failNext "keychain.delete" (times := 10)
    failNext "keychain.clear" (times := 10)
    tap (.alert "Delete wallet")
    waitFor (.text "^Could not delete the wallet$") 30
    shot "fail-03-delete"
    tap (.alert "OK")⟩

/-- Winnow's own operations made to fail (`Run.fail`, test mode's `WinnowApp.Faults`): a fresh receive address, a
label's save, the backup file and resetting the peers. Each failure is said where the person is, nothing changes,
and the next try works. The control file is the host's, so this runs in a simulator as headless. -/
def backendFailures : Journey := ⟨"backendFailures", do
  let r ← Run.new "backendfail"
  r.launch "backendfail"
  step "create the wallet" do createWallet

  step "a fresh address cannot be made: Receive says why and keeps the address it showed" do
    let shown ← Receive.address
    r.fail "receive.fresh"
    tap freshAddressButton
    waitFor journeyFault 20
    shot "fail-10-receive"
    expectEq "the address Receive shows" (← text receiveAddress) shown
    tap freshAddressButton
    waitUntil 20 "Receive did not show a fresh address" do return (← text receiveAddress) != shown
    expectGone journeyFault

  step "the label cannot be saved: the editor says why, and Save again keeps it" do
    tap (.button "Label this address")
    type receiveAddressLabelField "Rent"
    r.fail "store.write.receive-labels.json"
    tap saveReceiveAddressLabelButton
    waitFor journeyFault 20
    shot "fail-11-label"
    tap saveReceiveAddressLabelButton
    waitFor (.button "Edit label") 20
    Receive.close

  step "the backup file cannot be written: the sheet says why, and Create again makes it" do
    openSettings
    scrolled exportBundleButton
    tap exportBundleButton
    r.fail "export"
    tap (.button "Create backup file")
    waitFor journeyFault 20
    shot "fail-12-export"
    tap (.button "Create backup file")
    waitFor (.text "^Recovery words are not included") 20
    tap (.button "Close")

  step "the peers cannot be reset: the page says why" do
    scrolled networkPeersButton
    tap networkPeersButton
    scrolled (.button "Reset and shuffle peers")
    tap (.button "Reset and shuffle peers")
    r.fail "peers.reset"
    tap (.alert "Reset and shuffle peers")
    waitFor journeyFault 20
    shot "fail-13-peers"⟩

/-- A payment whose broadcast fails (Winnow's `broadcast` point), and its fee bump's: each is said on the screen
the person is on, the node is given nothing, and the next try works. (A payment's details are loaded only for a
send whose outputs the wallet does not hold, one made on another device: `payment.details` is for such a journey.) -/
def paymentFailures : Journey := ⟨"paymentFailures", do
  let r ← Run.new "payfail"
  let h := r.host
  r.launch "payfail"
  createWallet

  step "the node funds the wallet" do
    let address ← Receive.address
    Receive.close
    discard <| h.fund address funding
    waitForBalance funding

  let destination ← h.bankAddress
  let txid ← step "the payment cannot be broadcast: Send says why, the node is given nothing, and Send again sends it" do
    tap openSendButton
    Send.fill r destination payment
    discard <| Send.expectReview destination payment
    let before ← h.mempool
    r.fail "broadcast"
    tap sendButton
    waitFor journeyFault 30
    shot "fail-20-send"
    expectEq "the node's mempool" (← h.mempool) before
    tap (.button "Edit payment")
    tap reviewButton
    waitFor sendButton 30
    discard <| Send.expectReview destination payment
    let txid ← Send.send h
    h.expectPays txid destination payment
    waitFor broadcastPending 30
    pure txid

  step "the fee bump cannot be broadcast: the sheet says why, the payment stays, and Sign again replaces it" do
    backToWalletList
    scrolled (historyPayment txid)
    tap (historyPayment txid)
    Bump.start
    let current := (digits (← text bumpCurrentRate)).getD 1
    discard <| Bump.review (toString (current + 5))
    let before ← h.mempool
    r.fail "broadcast"
    scrolled bumpSignButton
    tap bumpSignButton
    waitFor journeyFault 30
    shot "fail-22-bump"
    expectEq "the node's mempool" (← h.mempool) before
    discard <| Bump.replace h⟩

end WinnowJourneys
