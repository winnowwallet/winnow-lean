import Lean.Data.Json
import WinnowApp.Model

/-! What the app needs from the wallet and the network: AppModel's async methods as IO actions. The
real implementation is the Lean WalletCore port (wired in as its areas land); until then `pending`
answers each operation with a plain "still being ported" failure, so the app runs end to end.

Every type here is an app-level summary (strings, numbers, small structures from `Types.lean`); the
backend keeps the WalletCore objects (wallet, stack, transactions being signed) to itself. Mutations of
people and labels answer with the fresh `Records`. -/

namespace WinnowApp

structure Backend where
  /-- Open the wallet of `network` stored under `dir` (wallet.json + the keychain secret). -/
  openWallet : Network → (dir : String) → IO BootResult
  /-- `createWallet()` (after authentication): a wallet, its automatic iCloud backup prepared from the words
in hand, onboarding finished; the wallet's id. No phrase checklist: the words are never shown here. -/
  createWallet : Network → (dir : String) → IO String
  /-- Import a backup bundle (JSON); the wallet's id and the verification report. -/
  importBundle : Network → (dir : String) → (json : String) → IO (String × String)
  finishOnboarding : IO Unit
  snapshot : IO (Status × SyncPhase)
  /-- People, sender and receive labels. -/
  records : IO Records
  receiveAddress : (fresh : Bool) → IO String
  /-- `setReceiveAddressLabel` (an empty label removes it). -/
  setReceiveLabel : (address label : String) → IO Records
  /-- Open the bounded mempool window on `address` (ReceiveView); `seen txid amount` per payment. -/
  watchAddress : (address : String) → (seen : String → Int → IO Unit) → IO Unit
  stopWatchingAddress : IO Unit
  deleteWallet : IO Unit
  startNetworking : Settings → IO Unit
  stopNetworking : IO Unit
  syncNow : IO Unit
  retryPeers : IO Unit
  /-- Tear the stack down and build it again with these settings (`reconnect`). -/
  reconnect : Settings → IO Unit
  /-- `resolvedFeeRate` (thousandths of sat/vB). -/
  resolveFeeRate : (priority : Nat) → (overrideMilli : Option Nat) → IO Nat
  /-- Winnow's `previewSend` (an address or a saved person). -/
  previewSend : SendInputs → IO Preview
  /-- Winnow's `send(preview:)` after authentication: rebuild, sign, check `authorizes`, broadcast,
  commit. The txid (display hex). -/
  sendPayment : SendInputs → Preview → IO SentPayment
  rawTransactionHex : (txid : String) → IO (Option String)
  /-- Follow a broadcast: broadcaster events plus mempool-window echoes, until it confirms. -/
  watchRelay : (txid : String) → (RelayEvent → IO Unit) → IO Unit
  loadPaymentDetails : (txid : String) → IO Unit
  /-- The pending rate in thousandths (shown) and the suggested replacement rate (`suggestedBumpText`, from the
  exact rate). -/
  pendingFeeRate : (txid : String) → IO (Nat × String)
  previewFeeBump : (txid : String) → (milli : Nat) → IO FeeBumpPreview
  /-- After authentication: sign and broadcast the reviewed replacement; its txid. -/
  bumpFee : (txid : String) → FeeBumpPreview → IO String
  /-- SettingsView's census line: "Observed …: N candidates." for the list this build ships, or the
  sentence for a build without one. -/
  catalogStatus : IO String
  connectedPeers : IO (List PeerInfo)
  resetPeers : IO Unit
  /-- The ImportBundle JSON (watch-only unless asked). -/
  exportBundle : (includeMnemonic : Bool) → IO String
  /-- After authentication: the recovery words. -/
  revealMnemonic : IO (List String)
  /-- `ownPersonCard(name:).serialized()`. -/
  ownCard : (name : String) → IO String
  /-- `PersonPaste.parse`. -/
  parsePaste : (text : String) → IO PastePreview
  /-- `addPerson` (+ `labelReceivedSender` when labelling a payment). -/
  addPerson : (name : String) → (paste : Option String) → Option Provenance →
    (source : Option String) → (labelTxid : Option String) → IO Records
  attachDestination : (personID paste : String) → Provenance → (source : Option String) → IO Records
  updateRecipient : (personID : String) → (name : Option String) → (saved : Bool) → IO Records
  labelSender : (txid personID : String) → IO Records
  removeSenderLabel : (txid : String) → IO Records
  /-- The consented explorer lookup of funding addresses. -/
  lookupSender : (txid baseURL : String) → IO (List String)
  -- Multisig accounts (Advanced mode; `Real/Multisig.lean`). Accounts are named by their id, PSBTs travel
  -- as Base64, and every PSBT operation answers with the PSBT in hand reviewed again.
  /-- `multisigAccounts`, `multisigStorageNotice`, `multisigKeyExpression()`. -/
  multisigOverview : IO MultisigOverview
  /-- `multisigAccount(validating:)` of a pasted descriptor. -/
  checkMultisigDescriptor : (text : String) → IO MultisigCheck
  /-- `addMultisigAccount(name:descriptor:)` then `registerPairedLedger`: the new account's id, and the
  paired Ledger's registration (its name, or why it did not register) when one holds a key of it. -/
  addMultisigAccount : (advanced : Bool) → (name descriptor : String) → IO (String × Option (Except String String))
  removeMultisigAccount : (id : String) → IO Unit
  newMultisigReceiveAddress : (id : String) → IO Unit
  /-- `createMultisigAccount(name:threshold:members:recovery:)` (refused outside Advanced mode) then
  `registerPairedLedger`: the account's id and descriptor, and the paired Ledger's registration. -/
  createMultisigAccount : (advanced : Bool) → (name : String) → (threshold : Nat) →
    (members : List (List String × Option Nat)) → Option MultisigRecovery →
    IO (String × String × Option (Except String String))
  /-- `registerLedger(record:)`: the account registered on the Ledger connected now. -/
  registerLedger : (advanced : Bool) → (id : String) → IO Unit
  /-- `pairLedger(name:)`: the Ledger's signer key read over Bluetooth and filed among the signers; the
  signer's id. Nothing is registered on the Ledger. -/
  pairLedger : (advanced : Bool) → (name : String) → IO String
  /-- `addSignerKeys(name:text:)`: keys someone sent, as one signer; its id. -/
  addSignerKeys : (advanced : Bool) → (name text : String) → IO String
  renameSigner : (id name : String) → IO Unit
  removeSigner : (id : String) → IO Unit
  /-- `verifyLedgerAddress(record:index:)`: the address the Ledger showed (the phone's own). -/
  verifyLedgerAddress : (advanced : Bool) → (id : String) → (index : Nat) → IO String
  -- An account's spend (#259): reviewed from Send, filed as the account's draft, its signatures collected
  -- (this phone, the Ledger, a pasted copy), then finalized and broadcast. Every operation changes the
  -- record, which the next overview shows.
  /-- `signAndDraftMultisigSpend(preview:)` after device authentication: the reviewed account spend signed
  here and filed as the draft; the account's id. -/
  signAndDraft : (advanced : Bool) → SendInputs → Preview → IO String
  /-- After device authentication: this phone's signature on the draft. -/
  signDraft : (id : String) → IO Unit
  /-- The Ledger's signature on the draft. -/
  signDraftWithLedger : (advanced : Bool) → (id : String) → IO Unit
  /-- `adoptMultisigDraft(_:record:)`: a pasted PSBT combined into the draft, or adopted as it. -/
  adoptDraft : (id psbt : String) → IO Unit
  /-- `broadcastMultisigDraft(record:)`: finalize, broadcast and record the draft; the txid. -/
  broadcastDraft : (id : String) → IO String
  discardDraft : (id : String) → IO Unit
  /-- A new unsigned spend (`recovery`: the recovery path), filed as the draft. The app's payments start
  from Send (`previewSend` with `accountID`, then `signAndDraft`); the backend test uses this one. -/
  createDraft : (id address : String) → (amount : Int) → (feeRate : Float) → (recovery : Bool) → IO Unit
  /-- `rebroadcastMultisigSpend(record:txid:)`. -/
  rebroadcastSpend : (id txid : String) → IO Unit
  /-- `abandonMultisigSpend(record:txid:)`. -/
  abandonSpend : (id txid : String) → IO Unit
  /-- `runBackgroundSync()`: one bounded background check with these settings; whether it reached the tip.
  Refused (false) while the scene is active. -/
  runBackgroundSync : Settings → IO Bool
  /-- `cancelBackgroundSync()`: stop a running background check and wait for it to drain. -/
  cancelBackgroundSync : IO Unit
  -- Automatic iCloud backup (`Real/CloudApp.lean`)
  /-- `cloudBackups` as the screens read it. -/
  cloudStatus : IO CloudStatus
  /-- Calls `k` with the fresh status after every change. -/
  observeCloud : (CloudStatus → IO Unit) → IO Unit
  /-- `discoverCloudBackups()`: onboarding's search for this network's saved backups. -/
  discoverCloudBackups : IO Unit
  /-- `setAutomaticCloudBackup(_:)`. -/
  setAutomaticCloudBackup : Bool → IO Unit
  /-- `restoreCloudBackup(_:)` (it authenticates itself): the wallet's id, the verification
  (`matchesBundle`, none while no peer answered) and the restored display name and Advanced switch. -/
  restoreCloudBackup : Network → (dir id : String) → IO (String × Option Bool × Option (String × Bool))
  /-- What `refresh()` asks of the iCloud side (an update, a preparation when due). -/
  cloudTick : IO Unit
  /-- The scene became active (true) or went to the background (false). -/
  cloudScene : Bool → IO Unit
  /-- `cloudBackups.suspend()` (a closed restore presentation). -/
  suspendCloud : IO Unit
  /-- The settings changed (the backup's context reads the display name and Advanced switch). -/
  updateSettings : Settings → IO Unit

def notPorted (what : String) : IO α := throw (IO.userError s!"{what}: this part of Winnow is still being ported to Lean.")

def Backend.pending : Backend where
  openWallet := fun _ dir => do
    if ← System.FilePath.pathExists (System.FilePath.mk dir / "wallet.json") then
      pure (.damaged "A wallet file exists, but opening wallets is still being ported to Lean.")
    else pure .missing
  createWallet := fun _ _ => notPorted "Creating a wallet"
  importBundle := fun _ _ _ => notPorted "Importing a backup"
  finishOnboarding := pure ()
  snapshot := pure ({}, .idle)
  records := pure {}
  receiveAddress := fun _ => notPorted "Receiving"
  setReceiveLabel := fun _ _ => notPorted "Receive address labels"
  watchAddress := fun _ _ => pure ()
  stopWatchingAddress := pure ()
  deleteWallet := notPorted "Deleting the wallet"
  startNetworking := fun _ => pure ()
  stopNetworking := pure ()
  syncNow := notPorted "Syncing"
  retryPeers := pure ()
  reconnect := fun _ => pure ()
  resolveFeeRate := fun _ _ => notPorted "Fee rates"
  previewSend := fun _ => notPorted "Previewing a payment"
  sendPayment := fun _ _ => notPorted "Sending"
  rawTransactionHex := fun _ => pure none
  watchRelay := fun _ _ => pure ()
  loadPaymentDetails := fun _ => notPorted "Loading payment details"
  pendingFeeRate := fun _ => notPorted "Fee bumping"
  previewFeeBump := fun _ _ => notPorted "Fee bumping"
  bumpFee := fun _ _ => notPorted "Fee bumping"
  catalogStatus := pure "This build carries no peer list. Winnow uses saved peers and, when clearnet is allowed, DNS seeds."
  connectedPeers := pure []
  resetPeers := notPorted "Resetting peers"
  exportBundle := fun _ => notPorted "Backing up the wallet"
  revealMnemonic := notPorted "Showing the recovery phrase"
  ownCard := fun _ => notPorted "Your card"
  parsePaste := fun _ => notPorted "Reading addresses and cards"
  addPerson := fun _ _ _ _ _ => notPorted "Saving people"
  attachDestination := fun _ _ _ _ => notPorted "Saving people"
  updateRecipient := fun _ _ _ => notPorted "Saving people"
  labelSender := fun _ _ => notPorted "Sender labels"
  removeSenderLabel := fun _ => notPorted "Sender labels"
  lookupSender := fun _ _ => notPorted "Explorer lookups"
  multisigOverview := pure {}
  checkMultisigDescriptor := fun _ => notPorted "Multisig accounts"
  addMultisigAccount := fun _ _ _ => notPorted "Multisig accounts"
  removeMultisigAccount := fun _ => notPorted "Multisig accounts"
  newMultisigReceiveAddress := fun _ => notPorted "Multisig accounts"
  createMultisigAccount := fun _ _ _ _ _ => notPorted "Multisig accounts"
  registerLedger := fun _ _ => notPorted "Ledger signing"
  pairLedger := fun _ _ => notPorted "Ledger signing"
  addSignerKeys := fun _ _ _ => notPorted "Signers"
  renameSigner := fun _ _ => notPorted "Signers"
  removeSigner := fun _ => notPorted "Signers"
  verifyLedgerAddress := fun _ _ _ => notPorted "Ledger signing"
  signAndDraft := fun _ _ _ => notPorted "Multisig accounts"
  signDraft := fun _ => notPorted "Multisig accounts"
  signDraftWithLedger := fun _ _ => notPorted "Ledger signing"
  adoptDraft := fun _ _ => notPorted "Multisig accounts"
  broadcastDraft := fun _ => notPorted "Multisig accounts"
  discardDraft := fun _ => notPorted "Multisig accounts"
  createDraft := fun _ _ _ _ _ => notPorted "Multisig accounts"
  rebroadcastSpend := fun _ _ => notPorted "Multisig accounts"
  abandonSpend := fun _ _ => notPorted "Multisig accounts"
  runBackgroundSync := fun _ => pure false
  cancelBackgroundSync := pure ()
  cloudStatus := pure {}
  observeCloud := fun _ => pure ()
  discoverCloudBackups := pure ()
  setAutomaticCloudBackup := fun _ => pure ()
  restoreCloudBackup := fun _ _ _ => notPorted "Restoring from iCloud"
  cloudTick := pure ()
  cloudScene := fun _ => pure ()
  suspendCloud := pure ()
  updateSettings := fun _ => pure ()

instance : Nonempty Backend := ⟨Backend.pending⟩

end WinnowApp
