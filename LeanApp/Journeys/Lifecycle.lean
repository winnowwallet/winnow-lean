import LeanNative.Journey
import Winnow.Wallet.Wallet
import Winnow.Wallet.SpendReview
import WinnowApp.Ids
import Journeys.Screens

/-! # Protection/backup lifecycle, saved people & sender lookup, cross-device multisig sync, and spend controls

Four simulator-safe, real-UI journeys covering:
- `protectionBackupAndRestore`: home protection cards (`hardwareWalletCard`, `multipartyCard`), 2-of-3 Ledger
  setup with recovery key (`Protect.lean`), iCloud backup toggle and Home link, Profiles cancel-add, backup
  file export with recovery phrase, wallet deletion, iCloud restore re-check, and seeded backup file import;
- `savedPeopleAndSenderLookup`: revealed local funding-address selection (`chooseFunding`) with unverified
  funding + reuse review warnings, Taproot key-path sender-lookup consent UI (`askInfer` cancel & confirm
  against a local loopback explorer), `chooseSaved`, destinationless person in Saved recipients, direct
  typing into `personPastedField` / `destinationField`, and sent-payment save & rename (`editRecipient`);
- `crossDeviceMultisigChanges`: two devices sharing `WINNOW_E2E_CLOUD` exercising `DeviceSync.applyAccountChange`
  (`.rename`, `.raise`, `.ledger`, `.draft (some)`, `.combine`, `.draft none`), `applyAccount .remove`, and
  `applySigner` (`.adopt`, `.rename`, `.remove`);
- `multisigSpendAndWatchOnlyControls`: watch-only Taproot 2-of-2 join (`multisigAddWarning`, `setDescriptor`),
  watch-only account and collection controls (`multisigWatchOnlyNote`, empty & malformed PSBT errors,
  `psbtPasteField` typing), finalizing & broadcasting from the watch-only device, and in-flight spend
  Rebroadcast and Give up (`abandonSpend`) with post-confirmation reappearance. -/

namespace WinnowJourneys
open Lean LeanNative LeanNative.Journey WinnowApp.Ids

/-- Waits until a backup in `cloud` is written after a fresh marker and one mined block. -/
private def waitForCloudBackup (h : Host) (cloud tag : String) : UI Unit := do
  let marker := s!"{cloud}/seen-{tag}"
  IO.FS.writeFile marker ""
  h.mine 1
  waitUntil 60 s!"iCloud backup was not saved ({tag})" (every := 0.5) do savedSince cloud marker

/-- Derives a regtest BIP86 wallet from fresh entropy and returns `(words, address0, importBundleJSON)`
dated at `heightBefore`. -/
private def makeSeededBundle (heightBefore : Nat) : IO (String × String × String) := do
  let entropyHex ← randomHex 16
  let some seed := Winnow.Wire.dataOfHex? entropyHex | failure "entropy hex failed"
  let .ok words := Winnow.Keys.BIP39.mnemonic seed | failure "mnemonic generation failed"
  let .ok master := Winnow.Keys.HDKey.ofSeed (Winnow.Keys.BIP39.seed words) | failure "master key failed"
  let .ok acct := Winnow.Keys.BIP86.accountKey master 1 0 | failure "account key failed"
  let origin : Winnow.Descriptor.KeyOrigin :=
    { fingerprint := master.fingerprint, path := #[86, 1, 0].map (· + Winnow.Keys.HDKey.hardenedOffset) }
  let desc := Winnow.Wallet.makeDescriptor acct origin .regtest
  let .ok outs := desc.derived 0 .regtest | failure "descriptor derivation failed"
  let some addr0 := outs[0]?.map (·.address) | failure "missing receive address 0"
  let bundle : Winnow.ImportBundle := {
    version := 2
    network := "regtest"
    descriptor := some desc.serialized
    mnemonic := some words
    lastKnownHeight := heightBefore.toUInt32
  }
  return (words, addr0, bundle.serialized)

/-- Derives the regtest BIP86 multipath key expression (`[fp/86'/1'/0']tpub…/<0;1>/*`) for `entropyHex`. -/
private def regtestKeyExpression (entropyHex : String) : IO String := do
  let some seed := Winnow.Wire.dataOfHex? entropyHex | failure "entropy hex failed"
  let .ok words := Winnow.Keys.BIP39.mnemonic seed | failure "mnemonic generation failed"
  let .ok master := Winnow.Keys.HDKey.ofSeed (Winnow.Keys.BIP39.seed words) | failure "master key failed"
  let .ok acct := Winnow.Keys.BIP86.accountKey master 1 0 | failure "account key failed"
  return s!"[{Winnow.Wallet.hex8 master.fingerprint}/86'/1'/0']{acct.neutered.serialized (Winnow.Wallet.hdNetwork .regtest)}/<0;1>/*"

/-- Starts a multisig spend from the currently open account page (`multisigSendButton`), signs here, and waits for
the signature-collection screen. -/
private def sendFromOpenAccount (r : Run) (destination : String) (sats : Nat) (needs : String) : UI Unit := do
  scrolled multisigSendButton
  tap multisigSendButton
  waitFor sendSourceNote 10
  Send.fill r destination sats
  let signatures ← text reviewSignatures
  expect ((signatures.splitOn needs).length > 1) s!"review: {signatures}"
  scrolled sendButton
  expectEq "the review's button" (← text sendButton) "Sign and continue"
  tap sendButton
  waitUntil 90 "the collection step did not open" do
    return (← exists? multisigSignatureCount) || (← exists? (.nav "Collect signatures"))
  scrolled multisigSignatureCount

/-- Balance protection cards, 2-of-3 Ledger setup with a recovery key, iCloud backup controls/status,
backup file with recovery phrase, wallet deletion, and seeded backup file restore. -/
def protectionBackupAndRestore : Journey := ⟨"protectionBackupAndRestore", do
  let r ← Run.new "protectbackup"
  let h := r.host
  let run ← randomHex 4
  let recovery ← h.coreSigner s!"ui-prot-rec-{run}"
  let cloud := s!"{h.fixture}/icloud-prot-{run}"
  IO.FS.createDirAll cloud
  let highBalance : Nat := 55_000_000
  try
    r.launch "protectbackup" [("WINNOW_E2E_CLOUD", cloud), ("WINNOW_E2E_LEDGER", ← randomHex 16),
                              ("WINNOW_E2E_SYNC_INTERVAL", "1")]
    createWallet (bluetooth := true)
    step "Bluetooth, then Not now on the nearby Ledger" Ledger.notNow

    step "fund above 0.5 BTC so both protection cards appear on Home" do
      let addr ← Receive.address
      Receive.close
      discard <| h.fund addr highBalance
      waitForBalance highBalance
      waitFor dismissHardwareCard 20
      here (.button "Protect it with a Ledger")
      waitFor dismissMultipartyCard 20
      here (.button "Build an account with other people's keys")

    step "protection cards: open builder, dismiss multiparty card, and complete 2-of-3 Ledger setup with recovery key" do
      scrolled (.button "Build an account with other people's keys")
      tap (.button "Build an account with other people's keys")
      waitFor multisigBuildNameField 20
      tap .back
      waitFor dismissMultipartyCard 20
      scrolled dismissMultipartyCard
      tap dismissMultipartyCard
      expectGone dismissMultipartyCard 10
      scrolled (.button "Protect it with a Ledger")
      tap (.button "Protect it with a Ledger")
      waitFor ledgerSetUpButton 10
      tap ledgerSetUpButton
      waitFor ledgerSetupRecoveryToggle 10
      tap ledgerSetupRecoveryToggle
      waitFor (.button "Paste the recovery key") 10
      -- empty recovery key is rejected before pairing starts
      tap ledgerSetupStartButton
      waitFor (.text "^Paste the recovery key first\\.$") 10
      r.paste recovery.keyExpression (.button "Paste the recovery key")
      expectGone (.button "Paste the recovery key") 10
      tap ledgerSetupStartButton
      waitFor ledgerSetupDone 90
      let addr ← text ledgerSetupAddress
      expect (addr.startsWith "bcrt1p") s!"not a regtest Taproot address: {addr}"
      tap ledgerAddressesMatchButton
      waitFor multisigPolicy 20
      expectEq "the 2-of-3 Ledger setup policy" (← text multisigPolicy) "2 of 3"
      tap .back
      expectGone multisigPolicy 20
      waitFor settingsButton 20
      expectGone dismissHardwareCard 10

    step "iCloud backup toggle off, open from Home backup link, toggle back on, cancel Add profile, and export with phrase" do
      -- Home -> Profiles -> Add a profile -> Cancel
      Profiles.openSheet
      tap addWalletButton
      waitFor cancelAddWalletButton 30
      tap cancelAddWalletButton
      waitFor receiveButton 30

      openSettings
      scrolled (.button "iCloud backup")
      tap (.button "iCloud backup")
      waitFor automaticCloudBackupToggle 10
      waitUntil 45 "iCloud backup did not report Backed up" (every := 0.5) do
        return (← text cloudBackupStatus 1).startsWith "Backed up"
      tap automaticCloudBackupToggle
      waitUntil 10 "automatic iCloud backup did not turn off" (every := 0.25) do
        return (← text cloudBackupStatus 1) == "Off"
      tap (.button "Close")
      expectGone automaticCloudBackupToggle 10
      backToWalletList
      waitFor homeCloudBackupButton 20
      scrolled homeCloudBackupButton
      tap homeCloudBackupButton
      waitFor automaticCloudBackupToggle 10
      tap automaticCloudBackupToggle
      waitUntil 45 "iCloud backup did not resume Backed up" (every := 0.5) do
        return (← text cloudBackupStatus 1).startsWith "Backed up"
      tap (.button "Close")
      expectGone automaticCloudBackupToggle 10

      -- Export a backup file including the recovery phrase (stays in Settings for deletion below)
      openSettings
      scrolled exportBundleButton
      tap exportBundleButton
      waitFor exportExplanation 10
      tap exportIncludePhraseToggle
      waitFor (.beginning "This file includes your phone") 10
      scrolled (.button "Create backup file")
      tap (.button "Create backup file")
      waitFor (.alert "Export with phrase") 10
      tap (.alert "Export with phrase")
      waitFor (.text "^Includes your recovery words") 30
      tap (.button "Close")
      expectGone exportExplanation 10

    step "delete the wallet, re-check iCloud restore list, and restore a funded wallet from a seeded backup file" do
      scrolled (.button "Delete wallet from this device")
      tap (.button "Delete wallet from this device")
      waitFor (.alert "Delete wallet") 10
      tap (.alert "Delete wallet")
      waitFor createWalletButton 60

      -- iCloud restore sheet offers the deleted wallet's backup and supports Check again
      waitFor restoreCloudBackupButton 30
      tap restoreCloudBackupButton
      waitFor (.button "Check again") 20
      scrolled (.button "Check again")
      tap (.button "Check again")
      waitUntil 20 "Check again did not settle" do return (← state (.button "Check again")).enabled
      tap (.button "Close")
      expectGone (.button "Check again") 10

      -- Build a fresh seeded bundle dated before funding so verifyImport discovers the coin
      let heightBefore ← h.height
      let (words, importAddr, bundleJson) ← makeSeededBundle heightBefore
      discard <| h.fund importAddr smallCoin
      let firstWord := (words.splitOn " ").head!

      tap importWalletButton
      waitFor importVerifyButton 20
      r.paste bundleJson (.button "Paste from clipboard")
      scrolled importVerifyButton
      waitUntil 10 "Import and verify did not enable" do return (← state importVerifyButton).enabled
      tap importVerifyButton
      waitFor importReportSection 90
      scrolled importContinueButton
      tap importContinueButton
      waitFor receiveButton 60
      waitForBalance smallCoin

      -- Confirm the restored wallet holds the imported recovery phrase
      openSettings
      scrolled revealPhraseButton
      tap revealPhraseButton
      waitFor (.nav "Recovery phrase") 20
      here (.beginning s!"1. {firstWord}")
      tap (.button "Close")
      expectGone (.nav "Recovery phrase") 10
  finally
    h.unload [recovery]⟩

/-- Saved people lifecycle and sender-lookup consent UI: local revealed funding address with review warnings,
Taproot key-path explorer-lookup consent alert (cancel + confirm against a local loopback URL), choosing an
already-saved person as sender, adding a destination to a destinationless person from Saved recipients, typing
into destination/paste fields, and saving + renaming a recipient from a sent payment. -/
def savedPeopleAndSenderLookup : Journey := ⟨"savedPeopleAndSenderLookup", do
  let r ← Run.new "peoplesender"
  let h := r.host
  let run ← randomHex 4
  let p2wpkhSender ← h.coreSigner s!"ui-p2wpkh-sender-{run}"
  let tapSender ← h.coreSigner s!"ui-tap-sender-{run}"
  try
    r.launch "peoplesender" [("WINNOW_E2E_SYNC_INTERVAL", "1")]
    createWallet

    step "set custom loopback explorer URL so sender-lookup consent stays offline/local" do
      openSettings
      scrolled networkExplorerButton
      tap networkExplorerButton
      waitFor (.text "^blockstream\\.info$") 10
      tap (.text "^blockstream\\.info$")
      tap (.button "Custom")
      waitFor esploraURLField 10
      type esploraURLField "http://127.0.0.1:1"
      waitFor (.beginning "Selected: http://127.0.0.1:1") 10
      backToWalletList

    let (p2wpkhTx, frankAddr, tapTx) ← step "receive a P2WPKH payment (10M sats, dismiss hardware card) and a Taproot key-path payment" do
      let addr1 ← Receive.address
      Receive.close
      -- Explicit P2WPKH ("bech32") coin so spending it reveals frankAddr in the witness
      let frankAddr ← h.wallet #["getnewaddress", "", "bech32"] p2wpkhSender.wallet
      discard <| h.fund frankAddr (3 * funding)
      let tx1 ← h.wallet #["sendtoaddress", addr1, TestKit.Regtest.btc (2 * funding)] p2wpkhSender.wallet
      h.mine 1
      waitForBalance (2 * funding)
      waitFor (historyPayment tx1) 30
      -- 10,000,000 sats crosses the hardware-wallet card threshold; dismiss it
      waitFor dismissHardwareCard 20
      here (.button "Protect it with a Ledger")
      scrolled dismissHardwareCard
      tap dismissHardwareCard
      expectGone dismissHardwareCard 10

      -- Second receive address funded from a Taproot key-path coin (reveals no local funding address)
      let shown ← Receive.address
      tap freshAddressButton
      waitUntil 20 "fresh address did not change" do return (← text receiveAddress) != shown
      let addr2 ← text receiveAddress
      Receive.close
      let tapAddr ← h.wallet #["getnewaddress", "", "bech32m"] tapSender.wallet
      discard <| h.fund tapAddr (2 * funding)
      let tx2 ← h.wallet #["sendtoaddress", addr2, TestKit.Regtest.btc recoveryPayment] tapSender.wallet
      h.mine 1
      waitForBalance (2 * funding + recoveryPayment)
      waitFor (historyPayment tx2) 30
      pure (tx1, frankAddr, tx2)

    step "P2WPKH payment: pick revealed local funding address, save sender, and verify funding + reuse warnings on Send review" do
      scrolled (historyPayment p2wpkhTx)
      tap (historyPayment p2wpkhTx)
      scrolled (.button "Save sender as person")
      tap (.button "Save sender as person")
      waitFor (.button frankAddr) 15
      scrolled (.button frankAddr)
      tap (.button frankAddr)
      waitFor personPayToCaption 15
      scrolled personNameField
      type personNameField "Bank"
      scrolled personSaveButton
      waitUntil 10 "Save sender did not enable" do return (← state personSaveButton).enabled
      tap personSaveButton
      expectGone personSaveButton 20
      waitFor (.button "Send to Bank") 20
      scrolled (.button "Send to Bank")
      tap (.button "Send to Bank")
      waitFor amountField 10
      type amountField (toString payment)
      scrolled reviewButton
      tap reviewButton
      waitFor sendButton 30
      scrolled (.beginning "This destination was inferred from transaction funding.")
      here (.beginning "This destination was inferred from transaction funding.")
      scrolled (.beginning "This address has been saved for reuse.")
      here (.beginning "This address has been saved for reuse.")
      tap closeSendButton
      expectGone closeSendButton 10
      tap .back
      waitFor balanceText 10

    step "Taproot payment: sender-lookup consent alert (cancel + confirm), choose saved sender, then save destinationless sender" do
      scrolled (historyPayment tapTx)
      tap (historyPayment tapTx)
      scrolled (.button "Save sender as person")
      tap (.button "Save sender as person")
      waitFor (.button "Find funding addresses with 127.0.0.1") 15
      scrolled (.button "Find funding addresses with 127.0.0.1")
      tap (.button "Find funding addresses with 127.0.0.1")
      waitFor (.alert "Cancel") 10
      here (.beginning "The explorer receives this transaction ID and your IP address")
      tap (.alert "Cancel")
      waitFor (.button "Find funding addresses with 127.0.0.1") 10
      tap (.button "Find funding addresses with 127.0.0.1")
      waitFor (.alert "Look up with 127.0.0.1") 10
      tap (.alert "Look up with 127.0.0.1")
      waitUntil 20 "sender lookup did not settle" do
        return (← exists? (.button "Find funding addresses with 127.0.0.1") 1) &&
          (← state (.button "Find funding addresses with 127.0.0.1")).enabled

      -- Choose already-saved person ("Or choose someone saved" -> chooseSaved)
      scrolled (.button "Bank")
      tap (.button "Bank")
      expectGone personNameField 20
      waitFor (.text "^Bank$") 20

      -- Change sender to a new destinationless person so Saved recipients shows "— add destination"
      scrolled (.button "Change sender")
      tap (.button "Change sender")
      waitFor personNameField 10
      type personNameField "N"
      scrolled personSaveButton
      waitUntil 10 "Save destinationless sender did not enable" do return (← state personSaveButton).enabled
      tap personSaveButton
      expectGone personSaveButton 20
      waitFor (.text "^N$") 20
      here (.text "^This label has no payment destination\\.$")
      backToWalletList

    step "Saved recipients: attach destination to destinationless person by typing, send by typing destination, save + rename recipient" do
      let dest1 ← h.bankAddress
      let dest2 ← h.bankAddress
      tap openSendButton
      waitFor savedRecipientsButton 10
      tap savedRecipientsButton
      waitFor (.button "N — add destination") 15
      tap (.button "N — add destination")
      waitFor personPastedField 10
      type personPastedField dest1
      scrolled personSaveButton
      waitUntil 15 "Save destination did not enable" do return (← state personSaveButton).enabled
      tap personSaveButton
      expectGone personSaveButton 20
      waitFor (.button "N") 20
      tap (.button "Done")
      expectGone addPersonToolbarButton 10

      -- Type a fresh unsaved address directly into destinationField and send
      waitFor destinationField 10
      type destinationField dest2
      type amountField (toString payment)
      scrolled reviewButton
      tap reviewButton
      waitFor sendButton 30
      let sentTx ← Send.send h
      h.mine 1
      waitFor broadcastConfirmed 90
      tap closeSendButton
      expectGone closeSendButton 10

      -- Open the sent payment (recipient not previously saved -> editRecipient none), save, then rename
      waitFor (historyPayment sentTx) 30
      scrolled (historyPayment sentTx)
      tap (historyPayment sentTx)
      scrolled (.button "Save recipient")
      tap (.button "Save recipient")
      waitFor personNameField 10
      type personNameField "Bob"
      scrolled personSaveButton
      tap personSaveButton
      expectGone personSaveButton 20
      waitFor (.text "^Bob$") 20
      scrolled (.button "Rename recipient")
      tap (.button "Rename recipient")
      waitFor personNameField 10
      type personNameField "Bob2"
      scrolled personSaveButton
      tap personSaveButton
      expectGone personSaveButton 20
      waitFor (.text "^Bob2$") 20
  finally
    h.unload [p2wpkhSender, tapSender]⟩

/-- Cross-device multisig sync changes across two devices sharing `WINNOW_E2E_CLOUD`:
account rename, receive-index raise, Ledger registration sync, partial PSBT draft adoption and
cross-device signature combination, draft discard sync, account removal sync, and signer rename + removal sync. -/
def crossDeviceMultisigChanges : Journey := ⟨"crossDeviceMultisigChanges", do
  let r ← Run.new "devsync"
  let h := r.host
  let run ← randomHex 4
  let cloud := s!"{h.fixture}/icloud-devsync-{run}"
  IO.FS.createDirAll cloud
  let dev1Entropy ← randomHex 16
  let dev2Entropy ← randomHex 16
  let ledgerEntropy ← randomHex 16
  let peerKey ← h.coreSigner s!"ui-ds-peer-{run}"
  let dropKey ← h.coreSigner s!"ui-ds-drop-{run}"
  let dev2Key ← regtestKeyExpression dev2Entropy
  try
    let (sharedDesc, sharedID, tempID) ← step "Device 1 sets up iCloud, pairs Ledger, saves signers, and creates Vault + Temp" do
      r.launch "devsync1" [("WINNOW_E2E_CLOUD", cloud), ("WINNOW_E2E_ENTROPY", dev1Entropy),
                           ("WINNOW_E2E_LEDGER", ledgerEntropy), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      createWallet (bluetooth := true)
      Ledger.notNow

      -- Pair Ledger and save two signers (Peer to rename later, Drop to remove later)
      Ledger.pair "Nano"
      for (name, keyExpr) in [("Peer", peerKey.keyExpression), ("Drop", dropKey.keyExpression)] do
        scrolled signersAddKeysButton
        tap signersAddKeysButton
        waitFor signerKeysNameField 10
        type signerKeysNameField name
        r.paste keyExpr signerKeysPasteButton
        waitUntil 10 s!"Save signer {name} did not enable" do return (← state signerKeysSaveButton).enabled
        tap signerKeysSaveButton
        waitFor (.button name) 20
      -- Signers -> Settings -> Multisig accounts
      tap .back
      waitFor multisigAccountsButton 10
      scrolled multisigAccountsButton
      tap multisigAccountsButton
      waitFor multisigBuildButton 10

      -- Create 2-of-3 Vault (Device 1 + Device 2 + Ledger)
      Builder.start
      Builder.name "Vault"
      Builder.addPastedMember r dev2Key
      Builder.addLedgerMember "Nano"
      waitFor (.beginning "Members · 3") 10
      tap multisigBuildCreateButton
      waitFor multisigBuildLedgerRegistered 60
      scrolled multisigCreatedDescriptor
      let sharedDesc ← text multisigCreatedDescriptor
      expect (sharedDesc.startsWith "tr(") s!"not a descriptor: {sharedDesc}"
      let sharedID := accountID sharedDesc
      -- Create -> Multisig accounts
      tap .back
      waitFor multisigBuildButton 10

      -- Create empty 2-of-2 Temp (Device 1 + Peer)
      Builder.start
      Builder.name "Temp"
      tap multisigBuildAddMemberButton
      waitFor (.button "Peer") 10
      tap (.button "Peer")
      waitFor (.beginning "Members · 2") 10
      let tempDesc ← Builder.create
      let tempID := accountID tempDesc
      waitForCloudBackup h cloud "created"
      pure (sharedDesc, sharedID, tempID)

    step "Device 2 creates its wallet offline and joins Vault as Local (before funding), then the node funds index 0" do
      r.launch "devsync2" [("WINNOW_E2E_ENTROPY", dev2Entropy), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      createWallet
      openMultisigAccounts
      tap multisigAddButton
      waitFor multisigNameField 10
      type multisigNameField "Local"
      r.paste sharedDesc multisigDescriptorPasteButton
      waitFor multisigAddPolicy 20
      waitUntil 10 "Save did not enable on Device 2" do return (← state multisigSaveButton).enabled
      tap multisigSaveButton
      waitFor (multisigAccount sharedID) 20
      let addr0 ← h.deriveAddress sharedDesc 0
      discard <| h.fund addr0 funding

    let (addrAfterRaise, destination) ← step "Device 1 sees funding, advances receive index, creates a 1-of-2 spend draft, and backs up" do
      r.launch "devsync1" [("WINNOW_E2E_RESET", "0"), ("WINNOW_E2E_CLOUD", cloud),
                           ("WINNOW_E2E_ENTROPY", dev1Entropy), ("WINNOW_E2E_LEDGER", ledgerEntropy),
                           ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      waitFor receiveButton 60
      waitSynced
      waitForBalance funding balanceText
      openAccountRow sharedID
      waitForBalance funding multisigBalance
      let beforeAddr ← Account.receiveAddress
      scrolled multisigNewAddressButton
      tap multisigNewAddressButton
      waitUntil 20 "New address did not advance on Device 1" do return (← Account.receiveAddress) != beforeAddr
      let addrAfterRaise ← Account.receiveAddress
      let destination ← h.bankAddress
      sendFromOpenAccount r destination payment "needs 2 of 3"
      Collect.countIs multisigSignatureCount "1 of 2"
      waitForCloudBackup h cloud "draft1"
      pure (addrAfterRaise, destination)

    step "Device 2 enables iCloud: syncs rename, raised address, Ledger registration, Temp, and draft; adds 2nd signature" do
      r.launch "devsync2" [("WINNOW_E2E_RESET", "0"), ("WINNOW_E2E_CLOUD", cloud),
                           ("WINNOW_E2E_ENTROPY", dev2Entropy), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      waitFor receiveButton 60
      -- Local renames to Vault via DeviceSync.applyAccountChange .rename
      waitUntil 90 "Vault did not rename from Local" (every := 0.5) do
        if !(← exists? (multisigAccount sharedID) 1) then return false
        return (← text (multisigAccount sharedID) 1) == "Vault"
      -- Temp arrives under Watching
      waitFor homeWatchingRow 60
      openAccountRow sharedID
      waitForBalance funding multisigBalance
      -- Receive index raised to match Device 1
      waitUntil 30 "receive address did not raise via DeviceSync" (every := 0.5) do
        return (← text multisigReceiveAddress 1) == addrAfterRaise
      -- Ledger registration synced
      waitFor multisigLedgerFingerprint 20
      -- Draft adopted -> sign to 2 of 2
      waitFor multisigDraftButton 30
      tap multisigDraftButton
      Collect.countIs multisigSignatureCount "1 of 2"
      scrolled multisigSignButton
      waitUntil 20 "Add this phone's signature did not enable on Device 2" do return (← state multisigSignButton).enabled
      tap multisigSignButton
      Collect.countIs multisigSignatureCount "2 of 2" 60
      waitForCloudBackup h cloud "draft2"

    step "Device 1 combines Device 2's signature via DeviceSync, discards draft, removes Temp, renames Peer, removes Drop" do
      r.launch "devsync1" [("WINNOW_E2E_RESET", "0"), ("WINNOW_E2E_CLOUD", cloud),
                           ("WINNOW_E2E_ENTROPY", dev1Entropy), ("WINNOW_E2E_LEDGER", ledgerEntropy),
                           ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      waitFor receiveButton 60
      waitSynced
      openAccountRow sharedID
      waitFor multisigDraftButton 20
      tap multisigDraftButton
      -- DeviceSync.applyAccountChange .combine merges Device 2's signature into Device 1's 1-of-2 draft
      Collect.countIs multisigSignatureCount "2 of 2" 90
      scrolled multisigDiscardDraftButton
      tap multisigDiscardDraftButton
      waitFor multisigConfirmDiscardButton 10
      tap multisigConfirmDiscardButton
      waitFor (.beginning "This account has no payment awaiting signatures.") 20
      backToWalletList

      -- Remove empty Temp
      openAccountRow tempID
      waitFor multisigReceiveAddress 20
      scrolled (.button "Remove account")
      tap (.button "Remove account")
      waitFor (.button "Remove") 10
      tap (.button "Remove")
      expectGone multisigReceiveAddress 20
      waitFor settingsButton 20

      -- Rename Peer -> Peer2 and remove Drop
      openSettings
      scrolled signersButton
      tap signersButton
      waitFor (.button "Peer") 20
      tap (.button "Peer")
      waitFor signerNameField 10
      type signerNameField "Peer2"
      tap .back
      waitFor (.button "Peer2") 20
      tap (.button "Drop")
      waitFor signerRemoveButton 10
      scrolled signerRemoveButton
      tap signerRemoveButton
      expectGone (.button "Drop") 20
      waitForCloudBackup h cloud "cleanup"

    step "Device 2 syncs draft discard, Temp removal, Peer rename, and Drop removal" do
      let _ := destination
      r.launch "devsync2" [("WINNOW_E2E_RESET", "0"), ("WINNOW_E2E_CLOUD", cloud),
                           ("WINNOW_E2E_ENTROPY", dev2Entropy), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      waitFor receiveButton 60
      -- Temp removed -> Watching row disappears
      expectGone homeWatchingRow 90
      openAccountRow sharedID
      -- Draft discarded -> Send button is back and draft button is gone
      waitFor multisigSendButton 60
      expect (!(← exists? multisigDraftButton)) "discarded draft still shown on Device 2"
      backToWalletList
      -- Signer rename & removal synced
      openSettings
      scrolled signersButton
      tap signersButton
      waitFor (.button "Peer2") 30
      expect (!(← exists? (.button "Drop"))) "removed signer still shown on Device 2"
  finally
    h.unload [peerKey, dropKey]⟩

/-- Watch-only Taproot 2-of-2 controls (recovery-only join warning & descriptor typing, watch-only account
and collection screen via `WINNOW_E2E_CLOUD`, empty & malformed PSBT error handling, typing into PSBT paste
field, combining co-signer PSBTs and broadcasting) plus in-flight multisig spend Rebroadcast and Give up
(`abandonSpend`) with post-mining confirmation. -/
def multisigSpendAndWatchOnlyControls : Journey := ⟨"multisigSpendAndWatchOnlyControls", do
  let r ← Run.new "mswatchspend"
  let h := r.host
  let run ← randomHex 4
  let coreA ← h.coreSigner s!"ui-wo-a-{run}"
  let coreB ← h.coreSigner s!"ui-wo-b-{run}"
  let cloud := s!"{h.fixture}/icloud-wo-{run}"
  IO.FS.createDirAll cloud
  try
    let (account, psbt1, destination, fee) ← step "Device 1 builds 2-of-2 Watch Vault with Core A, funds it, prepares a 1-of-2 PSBT, and backs up" do
      r.launch "mswatchdev1" [("WINNOW_E2E_CLOUD", cloud), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      createWallet
      openMultisigAccounts
      Builder.start
      Builder.name "Watch"
      Builder.addPastedMember r coreA.keyExpression
      waitFor (.beginning "Members · 2") 10
      let desc ← Builder.create
      let account := accountID desc
      h.importAccount coreA desc
      Builder.openAccount
      let first ← h.deriveAddress desc 0
      expectEq "Watch first address" (← Account.receiveAddress) first
      discard <| h.fund first funding
      waitForBalance funding multisigBalance
      -- Build a 1-of-2 PSBT signed by Device 1, capture it, then discard the draft before backing up
      let destination ← h.bankAddress
      sendFromOpenAccount r destination payment "needs 2 of 2"
      Collect.countIs multisigSignatureCount "1 of 2"
      let fee := (← amount multisigFee).getD 0
      expect (fee > 0) "collection screen showed no fee"
      let psbt1 ← Collect.psbt
      scrolled multisigDiscardDraftButton
      tap multisigDiscardDraftButton
      waitFor multisigConfirmDiscardButton 10
      tap multisigConfirmDiscardButton
      waitFor (.beginning "This account has no payment awaiting signatures.") 20
      waitForCloudBackup h cloud "watch"
      pure (account, psbt1, destination, fee)

    step "Device 2 verifies recovery-only join warning + descriptor typing, then opens watch-only Watch" do
      r.launch "mswatchdev2" [("WINNOW_E2E_CLOUD", cloud), ("WINNOW_E2E_SYNC_INTERVAL", "1")]
      createWallet
      -- Test recovery-only join validation (multisig.setDescriptor + multisigAddRecovery + multisigAddWarning)
      openMultisigAccounts
      tap multisigAddButton
      waitFor multisigKeyText 10
      let dev2Key ← text multisigKeyText
      let recDesc ← match Winnow.MultisigAccount.makeDescriptor 2 #[coreA.keyExpression, coreB.keyExpression]
          (some (.separateKeys 1 #[dev2Key] 144)) .regtest with
        | .ok d => pure d.serialized
        | .error e => failure s!"could not build recovery-only descriptor: {reprStr e}"
      scrolled multisigDescriptorField
      type multisigDescriptorField "x"
      r.paste recDesc multisigDescriptorPasteButton
      waitFor multisigAddPolicy 20
      expectEq "recovery-only policy" (← text multisigAddPolicy) "2 of 2"
      here multisigAddRecovery
      here multisigAddWarning
      here (.beginning "This phone is not one of the signers.")
      backToWalletList

      -- Watch Vault arrives from Device 1 under Watching
      waitFor homeWatchingRow 120
      scrolled homeWatchingRow
      tap homeWatchingRow
      waitFor (multisigAccount account) 30
      waitFor (multisigWatchOnly account) 10
      openAccountRow account
      waitFor multisigWatchOnlyNote 20
      waitForBalance funding multisigBalance

    let txid ← step "watch-only account paste errors, watch-only collect screen, combine Core A's signature, and broadcast" do
      -- Empty clipboard error on account page
      r.clipboard ""
      scrolled multisigPastePSBTButton
      tap multisigPastePSBTButton
      waitFor multisigPasteError 15
      -- Malformed PSBT error on account page
      r.clipboard "not-a-psbt"
      tap multisigPastePSBTButton
      waitFor multisigPasteError 15
      -- Valid 1-of-2 PSBT opens the collection screen in watch-only mode
      r.clipboard psbt1
      tap multisigPastePSBTButton
      waitFor multisigSignatureCount 60
      Collect.countIs multisigSignatureCount "1 of 2"
      scrolled multisigWatchOnlyNote
      here multisigWatchOnlyNote
      -- Malformed PSBT typed directly into psbtPasteField shows multisigError
      scrolled psbtPasteField
      type psbtPasteField "bad"
      scrolled addPSBTButton
      tap addPSBTButton
      waitFor multisigError 15
      -- Combine Core A's signature to reach 2 of 2 and broadcast
      let psbt2 ← h.sign coreA psbt1
      Collect.add r psbt2
      Collect.countIs multisigSignatureCount "2 of 2" 30
      scrolled multisigBroadcastButton
      expect (← state multisigBroadcastButton).enabled "2 of 2 did not enable broadcast"
      let before ← h.mempool
      tap multisigBroadcastButton
      waitFor multisigPaymentSent 30
      let txid ← h.newMempoolTransaction before 30
      expectEq "shown txid" (← text "multisigTxid") txid
      h.expectPays txid destination payment
      pure txid

    step "in-flight multisig spend: Rebroadcast, cancel Give up, confirm Give up, verify freed coins, then confirm on chain" do
      backToWalletList
      waitFor (historyPayment txid) 30
      scrolled (historyPayment txid)
      expectEq "pending spend row status" (← text (historyStatus txid)) "Pending"
      tap (historyPayment txid)
      waitFor paymentAccountName 15
      expectEq "payment account name" (← text paymentAccountName) "Watch"
      scrolled rebroadcastSpendButton
      tap rebroadcastSpendButton
      waitFor abandonSpendButton 15
      scrolled abandonSpendButton
      tap abandonSpendButton
      waitFor abandonConfirmButton 10
      -- iOS 26 renders an anchored action sheet as a popover without a Cancel button (tapping outside dismisses it).
      if ← exists? (.button "Cancel") 1 then
        tap (.button "Cancel")
        expectGone abandonConfirmButton 10
        waitFor abandonSpendButton 10
        tap abandonSpendButton
        waitFor abandonConfirmButton 10
      tap abandonConfirmButton
      waitFor (.text "^This payment is no longer in the wallet’s history\\.$") 20
      backToWalletList
      -- Coins are free again on the watch-only account page before mining
      waitFor homeWatchingRow 20
      scrolled homeWatchingRow
      tap homeWatchingRow
      openAccountRow account
      waitForBalance funding multisigBalance
      -- Mining confirms the broadcast spend anyway; the account picks it up on chain
      h.mine 1
      waitForBalance (funding - payment - fee) multisigBalance
      backToWalletList
      waitFor (historyPayment txid) 60
      scrolled (historyPayment txid)
      waitUntil 60 "confirmed spend did not reappear as Confirmed" do
        return (← text (historyStatus txid) 1) == "Confirmed"
  finally
    h.unload [coreA, coreB]⟩

end WinnowJourneys
