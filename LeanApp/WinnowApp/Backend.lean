import Lean.Data.Json
import WinnowApp.Model

/-! What the app needs from the wallet and the network: AppModel's async methods as IO actions.
`Backend` holds the interface (with default/unconfigured stubs on each field) and `Backend.pending`
(`{}`) is the unconfigured base used for the initial `backendRef`, layered builders, the sample UI
harness, and tests.

Every type here is an app-level summary (strings, numbers, small structures from `Types.lean`); the
backend keeps the WalletCore objects (wallet, stack, transactions being signed) to itself. Mutations of
people and labels answer with the fresh `Records`. -/

namespace WinnowApp

def notPorted (what : String) : IO α := throw (IO.userError s!"{what}: this part of Winnow is still being ported to Lean.")

structure Backend where
  /-- Open the wallet of `network` stored under `dir` (wallet.json + the keychain secret). -/
  openWallet : Network → (dir : String) → IO BootResult := fun _ _ => pure .missing
  /-- `createWallet()` (after authentication): a wallet, its automatic iCloud backup prepared from the words
in hand, onboarding finished; the wallet's id. No phrase checklist: the words are never shown here. -/
  createWallet : Network → (dir : String) → IO String := fun _ _ => notPorted "Creating a wallet"
  /-- Import a backup bundle (JSON); the wallet's id and the verification report. -/
  importBundle : Network → (dir : String) → (json : String) → IO (String × String) :=
    fun _ _ _ => notPorted "Importing a backup"
  finishOnboarding : IO Unit := pure ()
  snapshot : IO (Status × SyncPhase) := pure ({}, .idle)
  /-- People, sender and receive labels. -/
  records : IO Records := pure {}
  receiveAddress : (fresh : Bool) → IO String := fun _ => notPorted "Receiving"
  /-- `setReceiveAddressLabel` (an empty label removes it). -/
  setReceiveLabel : (address label : String) → IO Records := fun _ _ => notPorted "Receive address labels"
  /-- Open the bounded mempool window on `address` (ReceiveView); `seen txid amount` per payment. -/
  watchAddress : (address : String) → (seen : String → Int → IO Unit) → IO Unit := fun _ _ => pure ()
  stopWatchingAddress : IO Unit := pure ()
  deleteWallet : IO Unit := notPorted "Deleting the wallet"
  /-- The wallets kept for the network whose directory this is, the first one first. No secret is read. -/
  wallets : (networkDir : String) → IO (List WalletSummary) := fun _ => pure []
  /-- Names the open wallet; the name travels with its backup to the person's other devices. -/
  renameWallet : String → IO Unit := fun _ => pure ()
  startNetworking : Settings → IO Unit := fun _ => pure ()
  stopNetworking : IO Unit := pure ()
  syncNow : IO Unit := notPorted "Syncing"
  retryPeers : IO Unit := pure ()
  /-- Tear the stack down and build it again with these settings (`reconnect`). -/
  reconnect : Settings → IO Unit := fun _ => pure ()
  /-- `resolvedFeeRate` (thousandths of sat/vB). -/
  resolveFeeRate : (priority : Nat) → (overrideMilli : Option Nat) → IO Nat := fun _ _ => notPorted "Fee rates"
  /-- Winnow's `previewSend` (an address or a saved person). -/
  previewSend : SendInputs → IO Preview := fun _ => notPorted "Previewing a payment"
  /-- Winnow's `send(preview:)` after authentication: rebuild, sign, check `authorizes`, broadcast,
  commit. The txid (display hex). -/
  sendPayment : SendInputs → Preview → IO SentPayment := fun _ _ => notPorted "Sending"
  rawTransactionHex : (txid : String) → IO (Option String) := fun _ => pure none
  /-- Follow a broadcast: broadcaster events plus mempool-window echoes, until it confirms. -/
  watchRelay : (txid : String) → (RelayEvent → IO Unit) → IO Unit := fun _ _ => pure ()
  loadPaymentDetails : (txid : String) → IO Unit := fun _ => notPorted "Loading payment details"
  /-- The pending rate in thousandths (shown) and the suggested replacement rate (`suggestedBumpText`, from the
  exact rate). -/
  pendingFeeRate : (txid : String) → IO (Nat × String) := fun _ => notPorted "Fee bumping"
  previewFeeBump : (txid : String) → (milli : Nat) → IO FeeBumpPreview := fun _ _ => notPorted "Fee bumping"
  /-- After authentication: sign and broadcast the reviewed replacement; its txid. -/
  bumpFee : (txid : String) → FeeBumpPreview → IO String := fun _ _ => notPorted "Fee bumping"
  /-- SettingsView's census line: "Observed …: N candidates." for the list this build ships, or the
  sentence for a build without one. -/
  catalogStatus : IO String :=
    pure "This build carries no peer list. Winnow uses saved peers and, when clearnet is allowed, DNS seeds."
  connectedPeers : IO (List PeerInfo) := pure []
  peerIssues : IO (List (String × String)) := pure []
  resetPeers : IO Unit := notPorted "Resetting peers"
  /-- The ImportBundle JSON (watch-only unless asked). -/
  exportBundle : (includeMnemonic : Bool) → IO String := fun _ => notPorted "Backing up the wallet"
  /-- After authentication: the recovery words. -/
  revealMnemonic : IO (List String) := notPorted "Showing the recovery phrase"
  /-- A card for one person only (issue #94): the saved person `personID`, or else the first person named
  `personName` (saved as a contact if there is none), a card code issued for them alone, on a card under
  `ownName`. The first call issues the card and reads the wallet's private key; later calls read it back.
  The card and the records it changed. -/
  personCard : (personID : Option String) → (personName ownName : String) → IO (String × Records) :=
    fun _ _ _ => notPorted "A card for one person"
  /-- An ordinary address for that person, who has a card: what a wallet that does not read cards, or an
  exchange, pays them at. It is the next unpaid address of their card, so the payment is found and named as
  theirs, and it changes once it has been paid. Reads no key. -/
  personAddress : (personID : Option String) → (personName : String) → IO String :=
    fun _ _ => notPorted "An address for one person"
  /-- Whether that person has a card already, so reading it needs no key and no device authentication. -/
  hasPersonCard : (personID : Option String) → (personName : String) → IO Bool := fun _ _ => pure false
  /-- `PersonPaste.parse`. -/
  parsePaste : (text : String) → IO PastePreview := fun _ => notPorted "Reading addresses and cards"
  /-- `addPerson` (+ `labelReceivedSender` when labelling a payment). -/
  addPerson : (name : String) → (paste : Option String) → Option Provenance →
    (source : Option String) → (labelTxid : Option String) → IO Records :=
    fun _ _ _ _ _ => notPorted "Saving people"
  attachDestination : (personID paste : String) → Provenance → (source : Option String) → IO Records :=
    fun _ _ _ _ => notPorted "Saving people"
  updateRecipient : (personID : String) → (name : Option String) → (saved : Bool) → IO Records :=
    fun _ _ _ => notPorted "Saving people"
  labelSender : (txid personID : String) → IO Records := fun _ _ => notPorted "Sender labels"
  removeSenderLabel : (txid : String) → IO Records := fun _ => notPorted "Sender labels"
  /-- The consented explorer lookup of funding addresses. -/
  lookupSender : (txid baseURL : String) → IO (List String) := fun _ _ => notPorted "Explorer lookups"
  -- Multisig accounts (Settings → Security; `Real/Multisig.lean`). Accounts are named by their id, PSBTs travel
  -- as Base64, and every PSBT operation answers with the PSBT in hand reviewed again.
  /-- `multisigAccounts`, `multisigStorageNotice`, `multisigKeyExpression()`. -/
  multisigOverview : IO MultisigOverview := pure {}
  /-- `multisigAccount(validating:)` of a pasted descriptor. -/
  checkMultisigDescriptor : (text : String) → IO MultisigCheck := fun _ => notPorted "Multisig accounts"
  /-- `addMultisigAccount(name:descriptor:)` then `registerPairedLedger`: the new account's id, and the
  paired Ledger's registration (its name, or why it did not register) when one holds a key of it. -/
  addMultisigAccount : (name descriptor : String) → IO (String × Option (Except String String)) :=
    fun _ _ => notPorted "Multisig accounts"
  removeMultisigAccount : (id : String) → IO Unit := fun _ => notPorted "Multisig accounts"
  /-- The damaged multisig account file renamed and kept, and the accounts begun again from none. -/
  setAsideDamagedMultisig : IO Unit := notPorted "Multisig accounts"
  newMultisigReceiveAddress : (id : String) → IO Unit := fun _ => notPorted "Multisig accounts"
  /-- `createMultisigAccount(name:threshold:members:recovery:)` then
  `registerPairedLedger`: the account's id and descriptor, and the paired Ledger's registration. -/
  createMultisigAccount : (name : String) → (threshold : Nat) →
    (members : List (List String × Option Nat)) → Option MultisigRecovery →
    IO (String × String × Option (Except String String)) :=
    fun _ _ _ _ => notPorted "Multisig accounts"
  /-- `registerLedger(record:)`: the account registered on the Ledger connected now. -/
  registerLedger : (id : String) → IO Unit := fun _ => notPorted "Ledger signing"
  /-- `pairLedger(name:)`: the Ledger's signer key read over Bluetooth and filed among the signers; the
  signer's id. Nothing is registered on the Ledger. -/
  pairLedger : (name : String) → IO String := fun _ => notPorted "Ledger signing"
  /-- `addSignerKeys(name:text:)`: keys someone sent, as one signer; its id. -/
  addSignerKeys : (name text : String) → IO String := fun _ _ => notPorted "Signers"
  renameSigner : (id name : String) → IO Unit := fun _ _ => notPorted "Signers"
  removeSigner : (id : String) → IO Unit := fun _ => notPorted "Signers"
  /-- `verifyLedgerAddress(record:index:)`: the address the Ledger showed (the phone's own). -/
  verifyLedgerAddress : (id : String) → (index : Nat) → IO String := fun _ _ => notPorted "Ledger signing"
  -- An account's spend (#259): reviewed from Send, filed as the account's draft, its signatures collected
  -- (this phone, the Ledger, a pasted copy), then finalized and broadcast. Every operation changes the
  -- record, which the next overview shows.
  /-- `signAndDraftMultisigSpend(preview:)` after device authentication: the reviewed account spend signed
  here and filed as the draft; the account's id. -/
  signAndDraft : SendInputs → Preview → IO String := fun _ _ => notPorted "Multisig accounts"
  /-- After device authentication: this phone's signature on the draft. -/
  signDraft : (id : String) → IO Unit := fun _ => notPorted "Multisig accounts"
  /-- The payment being collected, to the same account in another wallet kept on this device (its slot). -/
  handOverDraft : (id slot : String) → IO Unit := fun _ _ => throw (IO.userError "Another wallet is not available here.")
  /-- The Ledger's signature on the draft. -/
  signDraftWithLedger : (id : String) → IO Unit := fun _ => notPorted "Ledger signing"
  /-- `adoptMultisigDraft(_:record:)`: a pasted PSBT combined into the draft, or adopted as it. -/
  adoptDraft : (id psbt : String) → IO Unit := fun _ _ => notPorted "Multisig accounts"
  /-- `broadcastMultisigDraft(record:)`: finalize, broadcast and record the draft; the txid. -/
  broadcastDraft : (id : String) → IO String := fun _ => notPorted "Multisig accounts"
  discardDraft : (id : String) → IO Unit := fun _ => notPorted "Multisig accounts"
  /-- A new unsigned spend (`recovery`: the recovery path), filed as the draft. The app's payments start
  from Send (`previewSend` with `accountID`, then `signAndDraft`); the backend test uses this one. -/
  createDraft : (id address : String) → (amount : Int) → (feeRate : Float) → (recovery : Bool) → IO Unit :=
    fun _ _ _ _ _ => notPorted "Multisig accounts"
  /-- `rebroadcastMultisigSpend(record:txid:)`. -/
  rebroadcastSpend : (id txid : String) → IO Unit := fun _ _ => notPorted "Multisig accounts"
  /-- `abandonMultisigSpend(record:txid:)`. -/
  abandonSpend : (id txid : String) → IO Unit := fun _ _ => notPorted "Multisig accounts"
  /-- `runBackgroundSync()`: one bounded background check with these settings; whether it reached the tip.
  Refused (false) while the scene is active. -/
  runBackgroundSync : Settings → IO Bool := fun _ => pure false
  /-- `cancelBackgroundSync()`: stop a running background check and wait for it to drain. -/
  cancelBackgroundSync : IO Unit := pure ()
  -- Automatic iCloud backup (`Real/CloudApp.lean`)
  /-- `cloudBackups` as the screens read it. -/
  cloudStatus : IO CloudStatus := pure {}
  /-- Calls `k` with the fresh status after every change. -/
  observeCloud : (CloudStatus → IO Unit) → IO Unit := fun _ => pure ()
  /-- `discoverCloudBackups()`: onboarding's search for this network's saved backups. -/
  discoverCloudBackups : IO Unit := pure ()
  /-- `setAutomaticCloudBackup(_:)`. -/
  setAutomaticCloudBackup : Bool → IO Unit := fun _ => pure ()
  /-- `restoreCloudBackup(_:)` (it authenticates itself): the wallet's id, the verification
  (`matchesBundle`, none while no peer answered) and the restored display name and the backup's Advanced switch (kept for the format; the app applies only
  the name). -/
  restoreCloudBackup : Network → (dir id : String) → IO RestoreOutcome :=
    fun _ _ _ => notPorted "Restoring from iCloud"
  /-- What `refresh()` asks of the iCloud side (an update, a preparation when due). -/
  cloudTick : IO Unit := pure ()
  /-- The scene became active (true) or went to the background (false). -/
  cloudScene : Bool → IO Unit := fun _ => pure ()
  /-- `cloudBackups.suspend()` (a closed restore presentation). -/
  suspendCloud : IO Unit := pure ()
  /-- The settings changed (the backup's context reads the display name). -/
  updateSettings : Settings → IO Unit := fun _ => pure ()
  /-- The Ledgers advertising nearby (`ble.scan` for the Ledger services, connecting to none); none when
  Bluetooth is off, not allowed or absent. -/
  scanLedgers : IO (List NearbyLedger) := pure []
  /-- Ask for Bluetooth (`ble.state`: iOS asks the person the first time). -/
  askBluetooth : IO Unit := pure ()
  /-- The person has just authenticated, and the Keychain's reads of the wallet's secret are allowed for the
  action that follows: what has waited for that is done first (a restored wallet's search for cards that has
  no search key keeps one). Never why the action fails. -/
  personPresent : IO Unit := pure ()

/-- Placeholder backend with default/unconfigured handlers; used as the initial `backendRef`,
the base record for layered builders, the sample harness, and test stubs. -/
def Backend.pending : Backend := {}

instance : Nonempty Backend := ⟨Backend.pending⟩

end WinnowApp
