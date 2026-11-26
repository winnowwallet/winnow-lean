import Journeys.Screens

/-! # Targeted journeys for settings, signers/people/send, and multisig lifecycle controls

Walks real user-facing controls that the main happy-path and failure journeys do not reach:
- `settingsAndSyncControls`: onboarding iCloud re-check, Appearance picker, Sync now + diagnostics copy,
  Block explorer presets/custom URL + "What this trades away", Chain verification from genesis, gateway
  re-check, Recovery phrase copy, and Design papers;
- `signersPeopleAndSendControls`: Receive copy/label cancel/save/remove + own display name + external
  explorer confirmation, Signers add/open/rename/remove, Saved recipients add/rename/choose/clear/card/remove,
  Send fee priority + New payment, Payment detail label edit + recipient save/remove + sender label/attach/send/remove;
- `multisigLifecycleAndNestedBuilder`: Bluetooth card skip, Builder multi-key member add/remove, threshold
  and recovery steppers, recovery key paste/remove, nested account pick + member remove + empty account remove,
  New receive address, and reopening/discarding a multisig draft. -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- Settings, network, sync diagnostics, explorer, chain verification from genesis, recovery copy, and papers. -/
def settingsAndSyncControls : Journey := ⟨"settingsAndSyncControls", do
  let r ← Run.new "controls-settings"
  r.launch "controls-settings"

  step "re-check iCloud on onboarding, then create the wallet" do
    waitFor createWalletButton 60
    if ← exists? checkCloudAgainButton 2 then
      waitUntil 10 "Look for iCloud backups again did not enable" do return (← state checkCloudAgainButton).enabled
      tap checkCloudAgainButton
    createWallet
    waitSynced

  step "Appearance switches to Dark and back to System" do
    openSettings
    tap appearancePicker
    tap (.button "Dark")
    waitFor (.text "^Dark$") 10
    tap appearancePicker
    tap (.button "System")
    waitFor (.text "^System$") 10

  step "Settings → Network → Sync: Sync now and Copy sync diagnostics" do
    tap networkSyncButton
    waitUntil 20 "Sync status is not Up to date" do return (← text syncStatus) == "Up to date"
    here syncHeaderTip
    scrolled (.button "Sync now")
    tap (.button "Sync now")
    waitUntil 20 "Sync now did not return to Up to date" do return (← text syncStatus) == "Up to date"
    scrolled copySyncDiagnosticsButton
    tap copySyncDiagnosticsButton
    waitFor (.button "Diagnostics copied") 10
    tap .back
    waitFor networkExplorerButton 10

  step "Settings → Network → Block explorer: presets, custom URL, and What this trades away" do
    scrolled networkExplorerButton
    tap networkExplorerButton
    waitFor (.text "^blockstream\\.info$") 10
    tap (.text "^blockstream\\.info$")
    tap (.button "mempool.space")
    waitFor (.text "^mempool\\.space$") 10
    tap (.text "^mempool\\.space$")
    tap (.button "Custom")
    waitFor (.text "^Esplora-compatible website URL$") 10
    type (.text "^Esplora-compatible website URL$") "https://esplora.example/api"
    waitFor (.beginning "Selected: https://esplora.example/api") 10
    scrolled (.button "What this trades away")
    tap (.button "What this trades away")
    waitFor (.nav "The Read Side") 10
    tap (.button "Done")
    expectGone (.nav "The Read Side") 10
    tap (.text "^Custom$")
    tap (.button "blockstream.info")
    waitFor (.text "^blockstream\\.info$") 10
    tap .back
    waitFor chainVerificationButton 10

  step "Settings → Network → Chain verification: verify from genesis on regtest, then turn off" do
    scrolled chainVerificationButton
    tap chainVerificationButton
    waitFor (.text "^Verify the chain from genesis$") 10
    tap (.text "^Verify the chain from genesis$")
    waitFor (.beginning "Turning this off later") 10
    tap .back
    waitFor networkSyncButton 10
    tap networkSyncButton
    waitUntil 30 "verify-from-genesis sync did not finish" do return (← text syncStatus) == "Up to date"
    tap .back
    waitFor chainVerificationButton 10
    scrolled chainVerificationButton
    tap chainVerificationButton
    tap (.text "^Verify the chain from genesis$")
    expectGone (.beginning "Turning this off later") 10
    tap .back
    waitFor networkPeersButton 10

  step "Settings → Network → Peers and routing: check gateways and reconnect" do
    scrolled networkPeersButton
    tap networkPeersButton
    scrolled checkPeerGateways
    tap checkPeerGateways
    waitUntil 30 "the peers page shows no connected peer after reconnect" (every := 1) do
      scrolled (.button "Refresh")
      tap (.button "Refresh")
      exists? peerEndpoint
    tap .back
    waitFor networkSyncButton 10

  step "Settings → Backup: copy recovery phrase" do
    scrolled revealPhraseButton
    tap revealPhraseButton
    waitFor (.nav "Recovery phrase") 20
    scrolled (.button "Copy recovery phrase")
    tap (.button "Copy recovery phrase")
    waitFor (.button "Copied for 2 minutes") 10
    tap (.button "Close")
    expectGone (.nav "Recovery phrase") 10

  step "Settings → About → Design papers: open a paper and return" do
    scrolled (.button "Design papers")
    tap (.button "Design papers")
    waitFor (.nav "Design papers") 10
    tap (.button "A phone wallet")
    waitFor (.nav "A phone wallet") 10
    tap (.button "Design papers")
    waitFor (.nav "Design papers") 10
    tap (.button "Done")
    expectGone (.nav "Design papers") 10⟩

/-- Receive labels & own name, Signer rename/remove, Saved recipients & priority send, and Payment detail actions. -/
def signersPeopleAndSendControls : Journey := ⟨"signersPeopleAndSendControls", do
  let r ← Run.new "controls-people"
  let h := r.host
  let run ← randomHex 4
  let bob ← h.coreSigner s!"ui-ctrl-bob-{run}"
  try
    r.launch "controls-people"
    createWallet
    waitSynced

    let address ← step "Receive: copy address, cancel/save/remove/re-save label, set own name, cancel explorer alert" do
      let addr ← Receive.address
      tap (.button "Copy")
      waitFor (.button "Copied") 10
      -- cancel a label edit
      scrolled (.button "Label this address")
      tap (.button "Label this address")
      waitFor receiveAddressLabelField 10
      type receiveAddressLabelField "Temporary"
      tap skipReceiveAddressLabelButton
      waitFor (.button "Label this address") 10
      -- save and then remove a label
      tap (.button "Label this address")
      waitFor receiveAddressLabelField 10
      type receiveAddressLabelField "Invoice 1"
      tap saveReceiveAddressLabelButton
      waitFor (.text "^Invoice 1$") 10
      scrolled (.button "Edit label")
      tap (.button "Edit label")
      waitFor (.button "Remove label") 10
      tap (.button "Remove label")
      waitFor (.button "Label this address") 10
      -- save a label to carry onto the incoming payment
      tap (.button "Label this address")
      waitFor receiveAddressLabelField 10
      type receiveAddressLabelField "Salary"
      tap saveReceiveAddressLabelButton
      waitFor (.text "^Salary$") 10
      -- explorer confirmation alert, cancelled
      scrolled (.button "View address")
      tap (.button "View address")
      waitFor (.alert "Cancel") 10
      tap (.alert "Cancel")
      Receive.close
      pure addr

    step "Signers: save keys, open signer detail, rename, and remove" do
      openSettings
      scrolled signersButton
      tap signersButton
      waitFor signersAddKeysButton 10
      scrolled signersAddKeysButton
      tap signersAddKeysButton
      waitFor signerKeysNameField 10
      type signerKeysNameField "Bob"
      r.paste bob.keyExpression signerKeysPasteButton
      waitUntil 10 "Save signer did not enable" do return (← state signerKeysSaveButton).enabled
      tap signerKeysSaveButton
      waitFor (.button "Bob") 20
      tap (.button "Bob")
      waitFor signerNameField 10
      type signerNameField "Robert"
      tap .back
      waitFor (.button "Robert") 20
      tap (.button "Robert")
      waitFor signerRemoveButton 10
      scrolled signerRemoveButton
      tap signerRemoveButton
      expectGone (.button "Robert") 20
      backToWalletList

    let fundTx ← step "fund the labeled receive address" do
      let tx ← h.fund address funding
      waitForBalance funding
      pure tx

    let carolAddr ← h.bankAddress
    let sentTx ← step "Saved recipients: add, rename, card sheet, choose/clear in Send, High priority send, New payment, remove" do
      tap openSendButton
      waitFor savedRecipientsButton 10
      tap savedRecipientsButton
      waitFor addPersonToolbarButton 10
      tap addPersonToolbarButton
      waitFor personPasteButton 10
      r.paste carolAddr personPasteButton
      scrolled personNameField
      type personNameField "Carol"
      scrolled personSaveButton
      waitUntil 10 "Save recipient did not enable" do return (← state personSaveButton).enabled
      tap personSaveButton
      waitFor (.button "Carol") 20
      -- rename Carol -> Caroline
      tap (.button "Rename")
      waitFor personNameField 10
      type personNameField "Caroline"
      scrolled personSaveButton
      tap personSaveButton
      waitFor (.button "Caroline") 20
      -- open Caroline's card sheet and close it
      tap (.button "Make Caroline’s address and card")
      waitFor closeShareCardButton 20
      scrolled ownNameField
      type ownNameField "Alice"
      tap closeShareCardButton
      waitFor (.button "Caroline") 20
      -- choose Caroline, clear, then choose Caroline again
      tap (.button "Caroline")
      waitFor (.button "Change") 10
      tap (.button "Change")
      waitFor destinationField 10
      tap savedRecipientsButton
      waitFor (.button "Caroline") 10
      tap (.button "Caroline")
      waitFor (.button "Change") 10
      -- change fee priority to High
      Send.openFee
      tap (.text "^Normal$")
      tap (.button "High")
      waitFor (.beginning "Fee · High") 10
      scrolled amountField
      type amountField (toString payment)
      scrolled reviewButton
      tap reviewButton
      waitFor sendButton 30
      here (.text "^Caroline$")
      let tx ← Send.send h
      waitFor newPaymentButton 30
      -- New payment resets Send to an empty form
      tap newPaymentButton
      waitFor amountField 10
      -- remove Caroline from Saved recipients
      tap savedRecipientsButton
      waitFor (.button "Caroline") 10
      tap (.button "Remove")
      expectGone (.button "Caroline") 20
      tap (.button "Done")
      tap closeSendButton
      pure tx

    step "Sent payment detail: save recipient and remove from saved recipients" do
      h.mine 1
      waitFor (historyPayment sentTx) 60
      scrolled (historyPayment sentTx)
      tap (historyPayment sentTx)
      scrolled (.button "Save recipient")
      tap (.button "Save recipient")
      waitFor personNameField 10
      type personNameField "Dave"
      scrolled personSaveButton
      tap personSaveButton
      waitFor (.text "^Dave$") 20
      scrolled (.button "Remove from saved recipients")
      tap (.button "Remove from saved recipients")
      waitFor (.button "Save recipient") 20
      tap .back
      waitFor balanceText 10

    step "Received payment detail: edit address label, save sender, attach destination, send to sender, remove sender label" do
      scrolled (historyPayment fundTx)
      tap (historyPayment fundTx)
      scrolled (.button "Edit address label")
      tap (.button "Edit address label")
      waitFor receiveAddressLabelField 10
      type receiveAddressLabelField "Monthly salary"
      tap saveReceiveAddressLabelButton
      waitFor (.text "^Monthly salary$") 20
      scrolled (.button "Save sender as person")
      tap (.button "Save sender as person")
      waitFor personNameField 10
      type personNameField "Employer"
      scrolled personSaveButton
      tap personSaveButton
      waitFor (.text "^Employer$") 20
      -- attach a destination to Employer
      let empAddr ← h.bankAddress
      scrolled (.button "Add destination for Employer")
      tap (.button "Add destination for Employer")
      waitFor personPasteButton 10
      r.paste empAddr personPasteButton
      scrolled personSaveButton
      waitUntil 10 "Save destination did not enable" do return (← state personSaveButton).enabled
      tap personSaveButton
      waitFor (.button "Send to Employer") 20
      tap (.button "Send to Employer")
      waitFor closeSendButton 10
      here (.text "^Employer$")
      tap closeSendButton
      waitFor (.button "Remove sender label") 10
      scrolled (.button "Remove sender label")
      tap (.button "Remove sender label")
      waitFor (.button "Save sender as person") 20
      tap .back
      waitFor balanceText 10
  finally
    h.unload [bob]⟩

/-- Skip-Bluetooth onboarding, Builder multi-key/threshold/recovery-key controls, nested account & removal,
New receive address, and reopening/discarding an account spend draft. -/
def multisigLifecycleAndNestedBuilder : Journey := ⟨"multisigLifecycleAndNestedBuilder", do
  let r ← Run.new "controls-multisig"
  let h := r.host
  let run ← randomHex 4
  let bob ← h.coreSigner s!"ui-ms-bob-{run}"
  let carol ← h.coreSigner s!"ui-ms-carol-{run}"
  let recovery ← h.coreSigner s!"ui-ms-rec-{run}"
  try
    r.launch "controls-multisig" [("WINNOW_E2E_LEDGER", ← randomHex 16)]

    step "skip Bluetooth on onboarding and reach the home" do
      createWallet (bluetooth := true)
      tap skipBluetoothButton
      waitFor receiveButton 20
      waitSynced

    let descVault ← step "Builder: multi-key member add/remove, threshold & recovery steppers, recovery key paste/remove" do
      openMultisigAccounts
      Builder.start
      Builder.name "Vault"
      -- add a second key to member 0 (this phone), then remove it
      r.clipboard carol.keyExpression
      tap (multisigBuildMemberAddKey 0)
      tap signerPickerPasteButton
      expectGone signerPickerPasteButton 10
      waitFor (.inside (multisigBuildMember 0) (.button "−")) 10
      tap (.inside (multisigBuildMember 0) (.button "−"))
      expectGone (.inside (multisigBuildMember 0) (.button "−")) 10
      -- add Bob and Carol as members 1 and 2
      Builder.addPastedMember r bob.keyExpression
      Builder.addPastedMember r carol.keyExpression
      waitFor (.beginning "Members · 3") 10
      -- bump threshold 2 -> 3
      scrolled multisigBuildThresholdStepper
      tap (multisigBuildThresholdStepper ++ "-Increment")
      waitFor (.beginning "Any 3 of 3 members spend") 10
      -- turn on recovery, bump recovery threshold 1 -> 2, switch to recovery key, paste & remove it, turn recovery off
      tap multisigBuildRecoveryToggle
      waitFor multisigBuildRecoveryThresholdStepper 10
      scrolled multisigBuildRecoveryThresholdStepper
      tap (multisigBuildRecoveryThresholdStepper ++ "-Increment")
      waitFor (.beginning "Any 2 of the 3 members") 10
      scrolled multisigRecoveryModePicker
      tap multisigRecoveryModePicker
      tap (.button "A recovery key")
      waitFor multisigBuildPasteRecoveryKeyButton 10
      r.paste recovery.keyExpression multisigBuildPasteRecoveryKeyButton
      waitFor (.button "Remove the recovery key") 10
      tap (.button "Remove the recovery key")
      waitFor multisigBuildPasteRecoveryKeyButton 10
      scrolled multisigBuildRecoveryToggle
      tap multisigBuildRecoveryToggle
      -- step threshold back 3 -> 2 so Vault is a 2-of-3 threshold account (eligible as a threshold nested member)
      scrolled multisigBuildThresholdStepper
      tap (decrement multisigBuildThresholdStepper)
      waitFor (.beginning "Any 2 of 3 members spend") 10
      Builder.create
    let vaultID := accountID descVault

    let addr0 ← step "Account page: New address advances the receive index" do
      Builder.openAccount
      let first ← Account.receiveAddress
      scrolled multisigNewAddressButton
      tap multisigNewAddressButton
      waitUntil 20 "New address did not advance" do return (← Account.receiveAddress) != first
      pure first

    step "Nested account: pick Vault as a member, remove and re-pick it, create, then remove the empty account" do
      -- pop Vault -> Create an account -> Multisig accounts
      for _ in [0:4] do
        if ← exists? multisigBuildButton then break
        tap .back
      waitFor multisigBuildButton 10
      Builder.start
      Builder.name "Nested"
      tap multisigBuildAddMemberButton
      waitFor (signerPickAccount vaultID) 10
      tap (signerPickAccount vaultID)
      waitFor (multisigBuildMemberRemove 0) 10
      tap (multisigBuildMemberRemove 0)
      expectGone (multisigBuildMemberRemove 0) 10
      tap multisigBuildAddMemberButton
      waitFor (signerPickAccount vaultID) 10
      tap (signerPickAccount vaultID)
      waitFor (multisigBuildMemberRemove 0) 10
      Builder.addPastedMember r recovery.keyExpression
      waitFor (.beginning "Members · 2") 10
      discard <| Builder.create
      Builder.openAccount
      waitFor multisigReceiveAddress 20
      scrolled (.button "Remove account")
      tap (.button "Remove account")
      waitFor (.alert "Remove") 10
      tap (.alert "Remove")
      expectGone multisigReceiveAddress 20

    step "Fund Vault, draft a spend, reopen it from the account page, and discard the draft" do
      discard <| h.fund addr0 funding
      backToWalletList
      waitForBalance funding
      let dest ← h.bankAddress
      Send.fromAccount r vaultID dest payment "needs 2 of 3"
      Collect.countIs multisigSignatureCount "1 of 2"
      backToWalletList
      openAccountRow vaultID
      waitFor multisigDraftButton 20
      tap multisigDraftButton
      waitFor multisigDiscardDraftButton 20
      scrolled multisigDiscardDraftButton
      tap multisigDiscardDraftButton
      waitFor (.alert "Discard") 10
      tap (.alert "Discard")
      waitFor (.beginning "This account has no payment awaiting signatures.") 20
      tap .back
      waitFor multisigSendButton 20
  finally
    h.unload [bob, carol, recovery]⟩

end WinnowJourneys
