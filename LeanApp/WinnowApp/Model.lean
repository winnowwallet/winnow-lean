import WinnowApp.Types
import WinnowApp.Format

/-! The app's state, messages and commands (AppModel + the views' @State, as one Elm model).

The state of each area is its own structure (Send, Receive, People, …);
user messages are grouped per area (`SendMsg`, `PeopleMsg`, …), host answers are one `Host` type, and
commands one `Cmd` type, because `perform` runs them all. The area modules (`WinnowApp/Send.lean`,
`People.lean`, …) hold each area's `step` and its views. -/

namespace WinnowApp
open Lean

/-! ## Presentations -/

/-- What AddPersonView is for (its initialiser's arguments). -/
structure PersonMode where
  /-- Editing this person (rename, or adding a destination when it has none). -/
  personID : Option String := none
  /-- Labelling the sender of this received payment. -/
  txid : Option String := none
  deriving Repr, BEq, Inhabited

inductive Sheet where
  | send
  | receive
  | importWallet
  /-- CloudRestoreView (onboarding's "Restore your iCloud wallet"). -/
  | cloudRestore
  /-- CloudBackupView (Advanced: Backup → iCloud backup). -/
  | cloudBackup
  | feeBump
  | addPerson
  | savedRecipients
  | shareCard
  /-- PaymentDetailView's "Address label" sheet. -/
  | labelEditor
  | exportBundle
  | revealPhrase
  | papers
  | readSide
  /-- SignerPickerSheet ("Add a member"). -/
  | signerPicker
  deriving Repr, BEq, Inhabited

/-- A pushed screen (NavigationLink destinations). -/
inductive Route where
  | payment (txid : String)
  /-- Beginner mode's Back up page. -/
  | backup
  /-- MultisigRoute (Advanced mode's Wallet tab): join with a descriptor, build, an account, its PSBT screen. -/
  | multisigAdd
  | multisigBuild
  /-- LedgerPairView (Settings → Signers → "Pair a Ledger"). -/
  | ledgerPair
  /-- SignersView, SignerDetailView, SignerKeysAddView (Settings → Signers). -/
  | signers
  | signer (id : String)
  | signerKeysAdd
  | multisigAccount (id : String)
  | multisigPSBT (id : String)
  deriving Repr, BEq, Inhabited

/-- A confirmation the user must answer (alerts and confirmation dialogs). -/
inductive Confirm where
  | advancedMode
  | deleteWallet
  | deleteFailed (message : String)
  | resetPeers
  | exportWithPhrase
  | inferSender
  /-- WarnedExplorerLink / DesignPaperView: an external URL, and what it exposes. -/
  | openExternal (url : String) (exposedItem : String)
  /-- MultisigAccountView's "Remove this account from this phone?". -/
  | removeMultisig (id : String)
  /-- The collection step's "Discard this payment?". -/
  | discardDraft (id : String)
  /-- The payment screen's "Give up on this payment?". -/
  | abandonSpend (id txid : String)
  deriving Repr, BEq, Inhabited

/-- Which clipboard policy a copy uses (`ClipboardPolicy`). -/
inductive ClipPolicy where
  /-- Recovery words: local only, 120 s. -/
  | recoveryPhrase
  /-- Addresses, descriptors, PSBTs, txids: may cross devices, 300 s. -/
  | interchange
  deriving Repr, BEq, Inhabited

/-- Where a Paste button's text goes. -/
inductive PasteTarget where
  | destination
  | person
  | importBundle
  | multisigDescriptor
  /-- SignerPickerSheet's "Paste keys from the clipboard". -/
  | memberKeys
  | multisigRecoveryKey
  | multisigPSBT
  /-- The account page's "Paste a PSBT from a co-signer": filed as the account's draft at once. -/
  | accountPSBT (id : String)
  /-- SignerKeysAddView's "Paste keys". -/
  | signerKeys
  deriving Repr, BEq, Inhabited

/-! ## Area state -/

/-- OnboardingView, ImportBundleView and CloudRestoreView (no phrase checklist: creation finishes onboarding
by itself, upstream 4228c6b). -/
structure Onboarding where
  busy : Bool := false
  error : Option String := none
  importText : String := ""
  importReport : Option String := none
  /-- CloudRestoreView: a restore running, done, and what it said. -/
  restoring : Bool := false
  restored : Bool := false
  restoreError : Option String := none
  deriving Repr, Inhabited

/-- ReceiveAddressLabelEditor, for the receive screen and a payment's labelled outputs. -/
structure LabelEditor where
  address : String := ""
  draft : String := ""
  saving : Bool := false
  error : Option String := none
  deriving Repr, Inhabited

structure Receive where
  address : String := ""
  error : Option String := none
  editingLabel : Bool := false
  changing : Bool := false
  /-- Payments the mempool window saw: txid, amount. -/
  unconfirmed : List (String × Int) := []
  deriving Repr, Inhabited

/-- What a preview was computed for (Winnow's `SendReviewInputs`): any change voids the preview. -/
structure SendInputs where
  destination : String := ""
  amount : String := ""
  priority : Nat := 1
  override : String := ""
  network : Network := .mainnet
  /-- A payment to a saved person, and the index its fresh address is derived at. -/
  personID : Option String := none
  paymentIndex : Option Nat := none
  walletID : Option String := none
  /-- The multisig account the payment comes from (Advanced mode's From); none for the wallet. -/
  accountID : Option String := none
  /-- The account's timelocked recovery path instead of its signers (Advanced, an account with one): only
  coins whose delay has passed are spent. -/
  recovery : Bool := false
  deriving Repr, Inhabited, BEq

/-- `SendPreview.AccountSource`: the account a payment comes from and the PSBT this phone built for it,
which "Sign and continue" signs and files as the account's draft. -/
structure AccountSource where
  id : String
  name : String
  threshold : Nat
  signerCount : Nat
  /-- The unsigned PSBT (Base64) the review was made from. -/
  psbt : String
  /-- Spent on the recovery path. -/
  recovery : Bool := false
  deriving Repr, Inhabited, BEq

structure PreviewRecipient where
  personID : String
  name : String
  derivesFreshAddresses : Bool
  hasUnverifiedFundingDestination : Bool
  deriving Repr, Inhabited, BEq

/-- Winnow's `SendPreview` as the screen shows it. -/
structure Preview where
  recipient : Option PreviewRecipient := none
  destination : String
  /-- `amountSent` -/
  amount : Nat
  fee : Nat
  feeRateMilli : Nat
  inputCount : Nat
  change : Option Nat
  locktimeLagsTip : Bool
  /-- The destination is a silent payment code (BIP352): the chain shows an address derived at signing. -/
  silent : Bool := false
  /-- Set when the source is a multisig account. -/
  account : Option AccountSource := none
  deriving Repr, Inhabited

/-- A broadcast send: its txid, and the addresses its silent payments were derived to (in order). -/
structure SentPayment where
  txid : String
  derivedAddresses : List String := []
  deriving Repr, Inhabited

structure SendState where
  inputs : SendInputs := {}
  preview : Option Preview := none
  reviewing : Bool := false
  sending : Bool := false
  error : Option String := none
  sentTxid : Option String := none
  /-- Where the silent payments of the sent transaction landed on chain (the receipt shows them). -/
  derivedAddresses : List String := []
  rawTransaction : Option String := none
  relayLog : List String := []
  relayedPeers : List String := []
  feeFloorNotice : Bool := false
  confirmedHeight : Option Nat := none
  resolvedRateMilli : Option Nat := none
  /-- The account whose draft is collecting signatures, after "Sign and continue". -/
  collecting : Option String := none
  deriving Repr, Inhabited

structure PaymentDetail where
  loading : Bool := false
  error : Option String := none
  deriving Repr, Inhabited

structure FeeBump where
  txid : String := ""
  currentRateMilli : Option Nat := none
  targetText : String := ""
  /-- The preview and the rate text it was made for (`FeeBumpReviewInputs`). -/
  reviewed : Option (String × FeeBumpPreview) := none
  error : Option String := none
  bumping : Bool := false
  replacement : Option String := none
  deriving Repr, Inhabited

structure SettingsDraft where
  manualPeer : String := ""
  error : Option String := none
  peers : List PeerInfo := []
  resettingPeers : Bool := false
  /-- The census line: "Observed …: N candidates." for the list this build ships, or the no-list sentence. -/
  catalog : Option String := none
  /-- PeerGatewaysSection's staged edits (applied only by Apply routing): the mode (0 Automatic, 1 Direct
  only, 2 Manual), the manual networks and the two gateway addresses as typed. -/
  gatewayMode : Nat := 0
  gatewayNetworks : List Winnow.IO.PeerNetwork := [.clearnet]
  torAddress : String := ""
  i2pAddress : String := ""
  gatewayError : Option String := none
  applyingGateways : Bool := false
  /-- The staged edits were loaded from the settings once (`loaded`): reappearing keeps them. -/
  gatewaysLoaded : Bool := false
  deriving Repr, Inhabited

structure ExportState where
  includeMnemonic : Bool := false
  /-- The staged backup file (ExportStagingFile), shared by path. -/
  file : Option String := none
  error : Option String := none
  busy : Bool := false
  deriving Repr, Inhabited

structure RevealState where
  words : List String := []
  revealing : Bool := false
  error : Option String := none
  copied : Bool := false
  deriving Repr, Inhabited

/-- AddPersonView's state. -/
structure PersonForm where
  mode : PersonMode := {}
  name : String := ""
  pasted : String := ""
  parsed : Option PastePreview := none
  error : Option String := none
  saving : Bool := false
  inferring : Bool := false
  inferredAddresses : List String := []
  inferredSource : Option String := none
  /-- The funding address picked, and where it came from. -/
  selectedFunding : Option (String × Provenance) := none
  /-- The lookup consent: the explorer and generation it was given for. -/
  lookupConsent : Option (String × Nat) := none
  deriving Repr, Inhabited

structure ShareCard where
  card : Option String := none
  error : Option String := none
  deriving Repr, Inhabited

/-- MultisigAddView's state. -/
structure MultisigAddForm where
  name : String := ""
  descriptor : String := ""
  /-- The validation and the trimmed text it was made for (`validation`; none while the text is empty). -/
  check : Option (String × Except String MultisigCheck) := none
  error : Option String := none
  saving : Bool := false
  /-- Saved, but the paired Ledger did not register it: the toolbar says Done. -/
  saved : Bool := false
  deriving Repr, Inhabited

/-- One key of a builder member, with what to call it (`MultisigBuildView.Key`). -/
structure BuildKey where
  key : String
  label : String
  deriving Repr, Inhabited, BEq

/-- `MultisigBuildView.Member`: one signer's keys; a whole account as one member carries its name and,
when it signs with fewer than all its keys, its threshold. -/
structure BuildMember where
  keys : List BuildKey
  name : Option String := none
  threshold : Option Nat := none
  deriving Repr, Inhabited, BEq

def phoneLabel : String := "This phone"

/-- Whether the member signs with fewer than all its keys. -/
def BuildMember.isThreshold (m : BuildMember) : Bool := m.threshold.any (· < m.keys.length)

/-- "This phone + Nano X", each name once; "Family 2-of-3". -/
def BuildMember.title (m : BuildMember) : String :=
  match m.name with
  | some n => if m.isThreshold then s!"{n} {m.threshold.getD 0}-of-{m.keys.length}" else plain
  | none => plain
where
  plain : String := " + ".intercalate (m.keys.foldl (fun acc k => if acc.contains k.label then acc else acc ++ [k.label]) [])

/-- "any 2 of its 3 keys", "2 keys, one signer", or nothing to add. -/
def BuildMember.caption (m : BuildMember) : Option String :=
  if m.isThreshold then some s!"any {m.threshold.getD 0} of its {m.keys.length} keys"
  else if m.keys.length > 1 then some s!"{m.keys.length} keys, one signer" else none

/-- `Member.plan`: the keys and the member's threshold. -/
def BuildMember.plan (m : BuildMember) : List String × Option Nat := (m.keys.map (·.key), m.threshold)

/-- MultisigBuildView's state. -/
structure MultisigBuildForm where
  name : String := ""
  members : List BuildMember := []
  threshold : Nat := 2
  withRecovery : Bool := false
  /-- 0: fewer signers, 1: a recovery key. -/
  recoveryMode : Nat := 0
  recoveryThreshold : Nat := 1
  recoveryKey : String := ""
  /-- The recovery delay in blocks: about six months by default (26,000 blocks; the stepper moves it a
  day, 144 blocks, at a time). -/
  recoveryBlocks : Nat := 26_000
  creating : Bool := false
  error : Option String := none
  /-- The account created: id and descriptor. -/
  created : Option (String × String) := none
  /-- The paired Ledger's registration after Create: its name, or why it did not register. -/
  registration : Option (Except String String) := none
  /-- The preview line: the account these members make, or why they do not (none: fewer than two). -/
  preview : Option (Except String String) := none
  /-- The picker sheet: adding a new member (none) or a key to member `i`. -/
  pickInto : Option Nat := none
  pasteError : Option String := none
  deriving Repr, Inhabited

def MultisigBuildForm.usedKeys (f : MultisigBuildForm) : List String := f.members.flatMap (·.keys.map (·.key))

/-- The paired Ledgers among the members, by name. -/
def MultisigBuildForm.pairedLedgerNames (f : MultisigBuildForm) (ledgers : List SignerInfo) : List String :=
  (ledgers.filter fun l => l.keys.any f.usedKeys.contains).map (·.name)

/-- LedgerPairView's state. -/
structure LedgerPairForm where
  name : String := ""
  pairing : Bool := false
  error : Option String := none
  deriving Repr, Inhabited

/-- SignerKeysAddView's state ("Save keys someone sent"). -/
structure SignerKeysForm where
  name : String := ""
  text : String := ""
  saving : Bool := false
  error : Option String := none
  deriving Repr, Inhabited

/-- SignerDetailView's state: the name being edited (renamed on submit and on leaving). -/
structure SignerDetailForm where
  id : String := ""
  name : String := ""
  error : Option String := none
  deriving Repr, Inhabited

/-- LedgerVerifyAddressButton's state, for the account and receive index it checks. -/
structure LedgerVerify where
  id : String := ""
  index : Nat := 0
  checking : Bool := false
  /-- The result text, and whether it is a failure. -/
  result : Option (String × Bool) := none
  deriving Repr, Inhabited

/-- The signature-collection step (`MultisigSigningSections`, the same from Send, Transactions and the
account page). Nothing of a PSBT is held here: every step changes the account's draft, which the overview
shows. -/
structure CollectForm where
  pasted : String := ""
  error : Option String := none
  busy : Bool := false
  /-- The operation in progress is the Ledger's signature: the person approves on the Ledger's screen. -/
  ledgerSigning : Bool := false
  /-- "Sign and continue" filed the draft and the overview carrying it has not come back yet. -/
  loadingDraft : Bool := false
  /-- The account page's broadcast (from Send, the receipt shows instead). -/
  broadcastTxid : Option String := none
  /-- `SensitivePresentationEpoch`: bumped by each operation and when the screen is left or backgrounded; an
  answer counts only for its epoch. -/
  epoch : Nat := 0
  deriving Repr, Inhabited

/-- The wallet's answer at boot. -/
inductive BootResult where
  | opened (walletID : String)
  | missing
  | damaged (message : String)
  deriving Repr, Inhabited

structure Model where
  /-- While the screen is captured, recovery words are not drawn (ScreenCaptureMonitor). -/
  captured : Bool := false
  stage : Stage := .loading
  settings : Settings := {}
  status : Status := {}
  phase : SyncPhase := .idle
  walletID : Option String := none
  records : Records := {}
  /-- Advanced mode's tab: 0 wallet, 1 send, 2 settings. -/
  tab : Nat := 0
  /-- Test mode's `WINNOW_E2E_NETWORK`: the network cannot be switched away from it. -/
  forcedNetwork : Option Network := none
  /-- Pushed screens of the main navigation (beginner home, or the current tab), innermost last. -/
  routes : List Route := []
  /-- Each Advanced-mode tab's own navigation stack while another tab shows (by tab index; the current
  tab's stack is `routes`). -/
  tabRoutes : List (List Route) := []
  /-- Presented sheets, innermost last (a sheet presents the next one over itself). -/
  sheets : List Sheet := []
  confirm : Option Confirm := none
  /-- Expanded disclosure groups, by key. -/
  expanded : List String := []
  /-- The copy button showing "Copied", by key. -/
  copied : Option String := none
  onboarding : Onboarding := {}
  receive : Receive := {}
  labelEditor : LabelEditor := {}
  settingsDraft : SettingsDraft := {}
  send : SendState := {}
  payment : PaymentDetail := {}
  feeBump : FeeBump := {}
  exportState : ExportState := {}
  reveal : RevealState := {}
  person : PersonForm := {}
  shareCard : ShareCard := {}
  recipientsError : Option String := none
  /-- Multisig accounts (Advanced mode), as the backend last reported them. -/
  multisig : MultisigOverview := {}
  multisigAdd : MultisigAddForm := {}
  multisigBuild : MultisigBuildForm := {}
  /-- MultisigAccountView's error. -/
  multisigAccountError : Option String := none
  ledgerPair : LedgerPairForm := {}
  signerKeys : SignerKeysForm := {}
  signerDetail : SignerDetailForm := {}
  ledgerVerify : LedgerVerify := {}
  /-- LedgerRegisterButton: the account being registered, and the last failure per account. -/
  ledgerRegistering : Option String := none
  ledgerRegisterError : Option (String × String) := none
  collect : CollectForm := {}
  /-- Paper shown in the Design papers sheet. -/
  paper : Option Nat := none
  /-- Bumped on suspend, network switch and rebuild: an answer from an older generation is dropped. -/
  generation : Nat := 0
  /-- The generation this wallet opened at (network switch, delete). The phone's own stores and the Ledger
  outlive a trip to the background, so their answers count from here (`Model.sameWallet`). -/
  walletGeneration : Nat := 0
  /-- `UIApplication.shared.backgroundRefreshStatus == .available` (the shell's `bgtask.refreshStatus`). -/
  backgroundRefreshAvailable : Bool := true
  /-- `cloudBackups` as the backend last reported it. -/
  cloud : CloudStatus := {}
  /-- `SensitivePresentationEpoch`: bumped whenever a sensitive presentation opens, resets or closes,
  and on background. A sensitive answer (phrase, export) counts only for its epoch. -/
  epoch : Nat := 0
  /-- `AppModel.exclusively(.spending)`: one payment is signed and broadcast at a time. -/
  spendingInFlight : Bool := false
  /-- `isActive`: the scene is in the foreground (the shell's scene phase). A cold background launch has no
  active scene, so boot opens the wallet without starting foreground networking. -/
  active : Bool := false
  /-- A background task iOS launched before the wallet was open (id, kind): it runs once boot lands. -/
  pendingBackgroundTask : Option (String × String) := none
  deriving Repr, Inhabited

/-! ## Messages -/

/-- What changed in people or labels, and what the screen does next. -/
inductive Done where
  | none
  | personSaved
  | senderLabeled
  | labelSaved
  deriving Repr, Inhabited, BEq

/-- What the backend (Lean wallet + network, and iOS capabilities) reports. -/
inductive Host where
  /-- Test mode at launch (E2EMode): the forced network and the first tab; sent before `settingsLoaded`. -/
  | launched (forcedNetwork : Option Network) (tab : Nat)
  | settingsLoaded (s : Settings)
  | booted (gen : Nat) (r : BootResult)
  /-- The wallet is created and onboarding finished (its iCloud backup prepared when iCloud allows). -/
  | created (gen : Nat) (walletID : String)
  | imported (gen : Nat) (walletID : String) (report : String)
  /-- The iCloud backup's status changed. -/
  | cloud (s : CloudStatus)
  /-- A restore from iCloud is done: the wallet, the verification (none: no peer yet), the restored display
  name and Advanced switch. -/
  | cloudRestored (gen : Nat) (walletID : String) (matchesBundle : Option Bool) (context : Option (String × Bool))
  | snapshot (gen : Nat) (s : Status) (p : SyncPhase)
  | records (gen : Nat) (r : Records)
  | updated (gen : Nat) (d : Done) (r : Records)
  | receiveAddress (gen : Nat) (address : String)
  | unconfirmed (gen : Nat) (address txid : String) (amount : Int)
  | failed (gen : Nat) (context : String) (message : String)
  | deleted (gen : Nat)
  | resolvedRate (gen : Nat) (forInputs : SendInputs) (milli : Nat)
  | previewed (gen : Nat) (forInputs : SendInputs) (p : Preview)
  | sent (gen : Nat) (txid : String) (derivedAddresses : List String)
  | rawTransaction (gen : Nat) (txid : String) (hex : Option String)
  | relay (gen : Nat) (txid : String) (e : RelayEvent)
  | paymentLoaded (gen : Nat) (txid : String)
  | pendingRate (gen : Nat) (txid : String) (milli : Nat) (suggested : String)
  | bumpPreviewed (gen : Nat) (txid rateText : String) (p : FeeBumpPreview)
  | bumped (gen : Nat) (txid replacement : String)
  | catalogStored (gen : Nat) (stored : String)
  | peers (gen : Nat) (ps : List PeerInfo)
  | peersReset (gen : Nat)
  | exported (gen epoch : Nat) (file : String)
  | revealed (gen epoch : Nat) (words : List String)
  | card (gen : Nat) (name : String) (card : String)
  | pasteParsed (gen : Nat) (text : String) (r : Except String PastePreview)
  | senderLookup (gen : Nat) (txid source : String) (addresses : List String)
  | multisig (gen : Nat) (o : MultisigOverview)
  | multisigChecked (gen : Nat) (text : String) (r : Except String MultisigCheck)
  | multisigAdded (gen : Nat) (id : String) (registration : Option (Except String String))
  | multisigCreated (gen : Nat) (id descriptor : String) (registration : Option (Except String String))
  | ledgerRegistered (gen : Nat) (id : String) (r : Except String Unit)
  | multisigRemoved (gen : Nat) (id : String)
  /-- "Sign and continue" filed the account's draft. -/
  | drafted (gen : Nat) (id : String)
  /-- A step of the collection (sign, Ledger, combine, a new or pasted PSBT, discard) is done; `pasted`:
  the paste field empties. -/
  | collected (gen epoch : Nat) (id : String) (pasted : Bool := false)
  | draftBroadcast (gen epoch : Nat) (id txid : String)
  /-- Rebroadcast or Give up on an in-flight account spend is done. -/
  | spendHandled (gen : Nat) (id txid : String)
  | ledgerPaired (gen : Nat) (id : String)
  | signerSaved (gen : Nat) (id : String)
  | signerRenamed (gen : Nat) (id : String)
  | signerRemoved (gen : Nat) (id : String)
  | ledgerAddressShown (gen : Nat) (id : String) (index : Nat) (r : Except String String)
  | pasted (target : PasteTarget) (text : String)
  | copiedExpired (key : String)
  | scene (active : Bool)
  /-- The scene went inactive (still foreground: a system prompt, the app switcher): nothing changes. -/
  | sceneInactive
  /-- The screen is being recorded or mirrored (UIScreen.isCaptured): phrase grids are hidden. -/
  | captured (on : Bool)
  /-- Background App Refresh is available (`bgtask.refreshStatus`). -/
  | backgroundRefresh (available : Bool)
  /-- iOS launched the background task `id` (`refresh` or `processing`). -/
  | bgtask (id kind : String)
  /-- iOS expired it. -/
  | bgtaskExpired (id kind : String)
  deriving Inhabited

inductive SendMsg where
  | setDestination (s : String)
  | setAmount (s : String)
  | setPriority (i : Nat)
  | setOverride (s : String)
  | pasteDestination
  | openRecipients
  | choosePerson (id : String)
  | clearPerson
  /-- From: the wallet (none) or a multisig account (Advanced mode). -/
  | setSource (account : Option String)
  /-- "Spend with": the signers now, or the account's recovery path (Advanced, an account with one). -/
  | setRecovery (b : Bool)
  | review
  | sendPayment
  | editPayment
  | newPayment
  deriving Inhabited

inductive ReceiveMsg where
  | freshAddress
  | editLabel
  | setLabelDraft (s : String)
  | saveLabel
  | removeLabel
  | finishLabel
  | openCard
  | setOwnName (s : String)
  deriving Inhabited

inductive HomeMsg where
  | openPayment (txid : String)
  | openBackup
  | pop
  | loadPayment
  | editRecipient (address : String) (personID : Option String)
  | removeRecipient (personID : String)
  | editPaymentLabel (address : String)
  | labelSender
  | attachSenderDestination (personID : String)
  | removeSenderLabel
  | sendToPerson (personID : String)
  | openFeeBump
  | setBumpRate (s : String)
  | reviewBump
  | bump
  deriving Inhabited

inductive SettingsMsg where
  | setManualPeer (s : String)
  | addManualPeer
  | removeManualPeer (i : Nat)
  | reconnect
  | setVerifyFromGenesis (b : Bool)
  | setExplorer (i : Nat)
  | setEsploraURL (s : String)
  | openReadSide
  | openPapers
  | openPaper (i : Nat)
  | closePaper
  | refreshPeers
  | askResetPeers
  | resetPeers
  | askDelete
  | deleteWallet
  | dismissTor
  -- PeerGatewaysSection
  | setGatewayMode (i : Nat)
  | setGatewayNetwork (n : Winnow.IO.PeerNetwork) (on : Bool)
  | setTorAddress (s : String)
  | setI2PAddress (s : String)
  | applyGateways
  | checkGateways
  deriving Inhabited

inductive BackupMsg where
  | openExport
  | setIncludeMnemonic (b : Bool)
  | createExport
  | confirmExport
  | reveal
  | copyPhrase
  deriving Inhabited

inductive PeopleMsg where
  | openAdd (mode : PersonMode) (address : String)
  | setName (s : String)
  | setPasted (s : String)
  | paste
  | chooseSaved (personID : String)
  | chooseFunding (address : String) (p : Provenance)
  | askInfer
  | infer
  | save
  | choose (personID : String)
  | rename (personID : String)
  | remove (personID : String)
  deriving Inhabited

inductive SignerMsg where
  | openSigners
  | openSigner (id : String)
  | openKeysAdd
  | setKeysName (s : String)
  | pasteKeys
  | saveKeys
  | setSignerName (s : String)
  | renameSigner
  | removeSigner
  | pop
  deriving Inhabited

inductive MultisigMsg where
  | openAdd
  | openBuild
  | openAccount (id : String)
  | openPSBT (id : String)
  | pop
  -- MultisigAddView
  | setName (s : String)
  | setDescriptor (s : String)
  | pasteDescriptor
  | save
  -- MultisigBuildView
  | buildSetName (s : String)
  /-- "Add a member" (none) or ⊕ on member `i`: the picker. -/
  | openPicker (into : Option Nat)
  | pickSigner (id : String)
  | pickAccount (id : String)
  | pasteMemberKeys
  | removeMemberKey (member key : Nat)
  | removeMember (member : Nat)
  | setThreshold (n : Nat)
  | setWithRecovery (b : Bool)
  | setRecoveryMode (i : Nat)
  | setRecoveryThreshold (n : Nat)
  | pasteRecoveryKey
  | removeRecoveryKey
  | setRecoveryDays (n : Nat)
  | create
  /-- "Register on Ledger" (the builder's created screen, the account screen). -/
  | registerLedger (id : String)
  -- MultisigAccountView
  | newAddress
  | askRemove
  | remove
  /-- "Send from this account": the Send tab, From this account. -/
  | sendFrom (id : String)
  /-- "Paste a PSBT from a co-signer" (the account page). -/
  | pasteForAccount (id : String)
  -- The collection step (MultisigPSBTView while the account has a draft)
  | setPasted (s : String)
  | pastePSBT
  /-- "Use this PSBT" (no draft) or "Combine" (a draft): the account named. -/
  | addPasted (id : String)
  | sign (id : String)
  | signWithLedger (id : String)
  | broadcast (id : String)
  | askDiscard (id : String)
  | discard
  -- PaymentDetailView's Account section
  | rebroadcast (id txid : String)
  | askAbandon (id txid : String)
  | abandon
  -- LedgerPairView, LedgerVerifyAddressButton, the builder's Ledger toggle
  | openLedgerPair
  | setLedgerName (s : String)
  | pairLedger
  | verifyAddress
  deriving Inhabited

/-- CloudBackupView and CloudRestoreView. -/
inductive CloudMsg where
  | openBackup
  | setAutomatic (b : Bool)
  | openRestore
  | restore (id : String)
  | checkAgain
  deriving Inhabited

inductive Msg where
  | createWallet
  | openImport
  | setImportText (s : String)
  | pasteImport
  | importWallet
  | finishOnboarding
  | closeSheet
  | setNetwork (i : Nat)
  | switchNetwork (net : Network)
  | askAdvanced
  | setAdvanced (b : Bool)
  | dismissConfirm
  | selectTab (i : Nat)
  | openReceive
  | openSend
  | copy (key text : String)
  | openExplorer (url exposedItem : String)
  | openURL (url : String)
  | setExpanded (key : String) (b : Bool)
  | syncNow
  | retryPeers
  | retryOpen
  | send (m : SendMsg)
  | receive (m : ReceiveMsg)
  | home (m : HomeMsg)
  | settings (m : SettingsMsg)
  | backup (m : BackupMsg)
  | people (m : PeopleMsg)
  | multisig (m : MultisigMsg)
  | signer (m : SignerMsg)
  | cloud (m : CloudMsg)
  | host (h : Host)
  deriving Inhabited

/-! ## Commands -/

/-- What the app asks of the backend. Wallet and network commands carry the generation they belong to;
sensitive ones also carry the presentation epoch. -/
inductive Cmd where
  | boot
  | saveSettings (s : Settings)
  /-- `boot()` when `isBoot` (launch, Retry), `switchNetwork` otherwise: only a boot journals `app.booted`. -/
  | openWallet (gen : Nat) (network : Network) (isBoot : Bool)
  | createWallet (gen : Nat) (network : Network)
  | importWallet (gen : Nat) (network : Network) (json : String)
  | finishOnboarding (gen : Nat)
  | refresh (gen : Nat)
  | syncNow (gen : Nat)
  | retryPeers (gen : Nat)
  | reconnect (gen : Nat) (settings : Settings)
  | receiveAddress (gen : Nat) (fresh : Bool)
  | watchAddress (gen : Nat) (address : String)
  | stopWatchingAddress
  | setReceiveLabel (gen : Nat) (address label : String)
  | copy (text : String) (policy : ClipPolicy)
  | timer (ms : Nat) (h : Host)
  | openURL (url : String)
  | deleteWallet (gen : Nat)
  | startNetworking (gen : Nat) (settings : Settings)
  | stopNetworking
  | resolveRate (gen : Nat) (inputs : SendInputs) (floor : Option Nat)
  | previewSend (gen : Nat) (inputs : SendInputs)
  | sendPayment (gen : Nat) (inputs : SendInputs) (p : Preview)
  | rawTransaction (gen : Nat) (txid : String)
  | watchRelay (gen : Nat) (txid : String)
  | loadPaymentDetails (gen : Nat) (txid : String)
  | pendingFeeRate (gen : Nat) (txid : String)
  | previewFeeBump (gen : Nat) (txid rateText : String) (milli : Nat)
  | bumpFee (gen : Nat) (txid : String) (p : FeeBumpPreview)
  | catalogStatus (gen : Nat)
  | connectedPeers (gen : Nat)
  | resetPeers (gen : Nat)
  /-- Export and stage the bundle as `fileName` in a fresh `winnow-export-*` directory of tmp. -/
  | exportBundle (gen epoch : Nat) (includeMnemonic : Bool) (fileName : String)
  /-- `ExportStagingFile.remove` for that file: its staging directory goes. -/
  | removeExport (file : String)
  | revealPhrase (gen epoch : Nat)
  | ownCard (gen : Nat) (name : String)
  | parsePaste (gen : Nat) (text : String)
  | addPerson (gen : Nat) (name : String) (paste : Option String)
      (provenance : Option Provenance) (source : Option String) (labelTxid : Option String)
  /-- Rename a person and keep them saved, first attaching a destination when they had none. -/
  | editPerson (gen : Nat) (personID name : String) (attach : Option (String × Provenance × Option String))
  | updateRecipient (gen : Nat) (personID : String) (name : Option String) (saved : Bool) (ctx : String)
  | labelSender (gen : Nat) (txid personID : String)
  | removeSenderLabel (gen : Nat) (txid : String)
  | lookupSender (gen : Nat) (txid baseURL : String)
  | paste (target : PasteTarget)
  /-- Multisig accounts (`Backend.multisig*`). -/
  | multisigOverview (gen : Nat)
  | checkMultisigDescriptor (gen : Nat) (text : String)
  | addMultisigAccount (gen : Nat) (advanced : Bool) (name descriptor : String)
  | removeMultisigAccount (gen : Nat) (id : String)
  | newMultisigAddress (gen : Nat) (id : String)
  | createMultisigAccount (gen : Nat) (advanced : Bool) (name : String) (threshold : Nat)
      (members : List (List String × Option Nat)) (recovery : Option MultisigRecovery)
  | registerLedger (gen : Nat) (advanced : Bool) (id : String)
  | pairLedger (gen : Nat) (advanced : Bool) (name : String)
  | addSignerKeys (gen : Nat) (advanced : Bool) (name text : String)
  | renameSigner (gen : Nat) (id name : String)
  | removeSigner (gen : Nat) (id : String)
  | verifyLedgerAddress (gen : Nat) (advanced : Bool) (id : String) (index : Nat)
  /-- "Sign and continue", after device authentication ("Sign this multisig payment"). -/
  | signAndDraft (gen : Nat) (advanced : Bool) (inputs : SendInputs) (p : Preview)
  /-- After device authentication ("Sign this multisig payment"). -/
  | signDraft (gen epoch : Nat) (id : String)
  | signDraftWithLedger (gen epoch : Nat) (advanced : Bool) (id : String)
  | adoptDraft (gen epoch : Nat) (id psbt : String)
  | broadcastDraft (gen epoch : Nat) (id : String)
  | discardDraft (gen epoch : Nat) (id : String)
  | rebroadcastSpend (gen : Nat) (id txid : String)
  | abandonSpend (gen : Nat) (id txid : String)
  /-- `e2e?.journal(name, fields:)` for what happens in the Model (test mode only; nothing otherwise). -/
  | journal (name : String) (fields : List (String × String))
  /-- Ask the shell whether Background App Refresh is on (`bgtask.refreshStatus`). -/
  | backgroundRefreshStatus
  /-- `discoverCloudBackups()`. -/
  | discoverCloud
  | setAutomaticCloud (enabled : Bool)
  /-- `restoreCloudBackup(_:)` (the backend authenticates). -/
  | restoreCloud (gen : Nat) (network : Network) (id : String)
  /-- `cloudBackups.suspend()` (CloudRestoreView's `cancel()`). -/
  | suspendCloud
  /-- The scene phase, for the iCloud side (a foreground session may prepare once; the background suspends). -/
  | cloudScene (active : Bool)
  /-- `BackgroundSyncScheduler.schedule()`: one refresh and one processing request, each replacing its own. -/
  | scheduleBackgroundTasks
  /-- Run the launched task `id` as one bounded background check (`BackgroundSyncRun`), then complete it. -/
  | runBackgroundTask (id kind : String) (settings : Settings)
  /-- The task's expiration handler: the run is cancelled and completes unsuccessfully once it drains. -/
  | expireBackgroundTask (id : String)
  deriving Inhabited

instance : Lean.ToJson Cmd := ⟨fun _ => Lean.Json.null⟩

/-- `Review payment` is enabled when the amount is a positive number of sats and there is a destination
or a saved person. -/
def canReview (i : SendInputs) : Bool :=
  (i.personID.isSome || !i.destination.trimAscii.isEmpty) &&
  (match i.amount.trimAscii.copy.toNat? with | some n => n > 0 | none => false)

def networks : List Network := [.mainnet, .signet]

def appVersionText : String := "0.1.0 (1)"

/-! ## Small helpers every area uses -/

def Model.topSheet (m : Model) : Option Sheet := m.sheets.getLast?
def Model.hasSheet (m : Model) (s : Sheet) : Bool := m.sheets.contains s
def Model.present (m : Model) (s : Sheet) : Model := { m with sheets := m.sheets ++ [s], confirm := none }
def Model.isExpanded (m : Model) (key : String) : Bool := m.expanded.contains key
def Model.person? (m : Model) (id : String) : Option Person := m.records.people.find? (·.id == id)
/-- The row a payment screen shows for a transaction id: the merged list's, else the wallet's own entry. -/
def Model.historyItem? (m : Model) (txid : String) : Option HistoryItem :=
  match m.status.payments.find? (·.item.txid == txid) with
  | some row => some row.item
  | none => m.status.history.find? (·.txid == txid)

def Model.payment? (m : Model) (txid : String) : Option DisplayedPayment :=
  match m.status.payments.find? (·.item.txid == txid) with
  | some row => some row
  | none => (m.status.history.find? (·.txid == txid)).map fun e => { item := e, source := .wallet }

/-- The saved stack of `tab` (empty when none was saved). -/
def Model.savedRoutes (m : Model) (tab : Nat) : List Route := (m.tabRoutes[tab]?).getD []

/-- Show tab `i`: the leaving tab keeps its stack, the entering tab gets its own back. -/
def Model.switchTab (m : Model) (i : Nat) : Model :=
  if i == m.tab then m else
  let saved := (List.range (max (m.tabRoutes.length) (max m.tab i + 1))).map fun t =>
    if t == m.tab then m.routes else m.savedRoutes t
  { m with tab := i, routes := m.savedRoutes i, tabRoutes := saved.set i [] }

/-- Leave the current wallet/network generation: every answer still in flight is dropped. -/
def Model.nextGeneration (m : Model) : Model :=
  { m with generation := m.generation + 1, epoch := m.epoch + 1, spendingInFlight := false }

/-- Leave the current wallet: answers about its accounts, signers and Ledger are dropped too. -/
def Model.nextWallet (m : Model) : Model :=
  let m := m.nextGeneration
  { m with walletGeneration := m.generation }

/-- An answer that ends an operation on this wallet (a payment, its accounts, signers or Ledger): it counts
across trips to the background (the phone locks while the person approves on the Ledger), not from another
wallet or network. -/
def Model.sameWallet (m : Model) (g : Nat) : Bool := m.walletGeneration ≤ g && g ≤ m.generation

end WinnowApp
