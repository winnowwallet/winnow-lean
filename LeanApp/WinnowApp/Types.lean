import Lean.Data.Json
import Winnow.IO.Gateways

/-! The app-facing view of the wallet: what the screens show, already derived (the Model never holds
WalletCore objects, only these summaries). Mirrors AppModel's `Status`, `SyncPhase`, settings, stage,
and the records (people, labels) the screens read. The `Backend` fills them. -/

namespace WinnowApp
open Lean

inductive Network where
  | mainnet
  | signet
  | regtest
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def Network.name : Network → String
  | .mainnet => "mainnet"
  | .signet => "signet"
  | .regtest => "regtest"

/-- The network as the app names it (a test session can run on a local regtest node, which is not signet). -/
def Network.label : Network → String
  | .mainnet => "Mainnet"
  | .signet => "Signet"
  | .regtest => "Regtest"

inductive Explorer where
  | blockstream
  | mempool
  | custom
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- The settings Winnow keeps per network (#81: a signet peer or explorer must never be used on mainnet). -/
structure NetworkSettings where
  manualPeers : List String := []
  esploraURL : String := ""
  explorer : Explorer := .blockstream
  deriving Repr, Inhabited, BEq, ToJson

instance : ToJson Winnow.IO.PeerGatewaySettings := ⟨Winnow.IO.PeerGatewaySettings.toJson⟩

/-- AppModel's settings (UserDefaults in the original; `settings.json` here). -/
structure Settings where
  network : Network := .mainnet
  advancedMode : Bool := false
  verifyFromGenesis : Bool := false
  ownDisplayName : String := ""
  /-- The removed Tor option was on (shown once, then cleared). -/
  torRemovedNotice : Bool := false
  mainnet : NetworkSettings := {}
  signet : NetworkSettings := {}
  regtest : NetworkSettings := {}
  /-- `peerGatewaySettings` (global, not per network): Automatic, Direct only, or the manual gateways. -/
  peerGatewaySettings : Winnow.IO.PeerGatewaySettings := {}
  deriving Repr, Inhabited, ToJson

/-- Reads every field with its default when absent, so a settings file from an older build still loads. -/
instance : FromJson NetworkSettings where
  fromJson? j := pure
    { manualPeers := (j.getObjValAs? (List String) "manualPeers").toOption.getD []
      esploraURL := (j.getObjValAs? String "esploraURL").toOption.getD ""
      explorer := (j.getObjValAs? Explorer "explorer").toOption.getD
        (if ((j.getObjValAs? String "esploraURL").toOption.getD "").isEmpty then .blockstream else .custom) }

instance : FromJson Settings where
  fromJson? j := pure
    { network := (j.getObjValAs? Network "network").toOption.getD .mainnet
      advancedMode := (j.getObjValAs? Bool "advancedMode").toOption.getD false
      verifyFromGenesis := (j.getObjValAs? Bool "verifyFromGenesis").toOption.getD false
      ownDisplayName := (j.getObjValAs? String "ownDisplayName").toOption.getD ""
      torRemovedNotice := (j.getObjValAs? Bool "torRemovedNotice").toOption.getD false
      mainnet := (j.getObjValAs? NetworkSettings "mainnet").toOption.getD {}
      signet := (j.getObjValAs? NetworkSettings "signet").toOption.getD {}
      regtest := (j.getObjValAs? NetworkSettings "regtest").toOption.getD {}
      -- absent: Automatic; present but unreadable: offline (`PeerGatewaySettings.unreadable`)
      peerGatewaySettings := match j.getObjVal? "peerGatewaySettings" with
        | .ok v => (Winnow.IO.PeerGatewaySettings.ofJson? v).getD Winnow.IO.PeerGatewaySettings.unreadable
        | .error _ => {} }

/-- `networkScopedSettings`: the peers and explorer of the selected network. -/
def Settings.scoped (s : Settings) : NetworkSettings :=
  match s.network with
  | .mainnet => s.mainnet
  | .signet => s.signet
  | .regtest => s.regtest

def Settings.withScoped (s : Settings) (f : NetworkSettings → NetworkSettings) : Settings :=
  match s.network with
  | .mainnet => { s with mainnet := f s.mainnet }
  | .signet => { s with signet := f s.signet }
  | .regtest => { s with regtest := f s.regtest }

def Settings.manualPeers (s : Settings) : List String := s.scoped.manualPeers

/-- One output of a wallet transaction, as the payment screens need it (the backend decodes the
transaction and renders each script; `address` is none for a non-standard script). -/
structure TxOut where
  index : Nat
  address : Option String
  /-- scriptPubKey, hex -/
  script : String
  amount : Nat
  /-- One of the wallet's own watch scripts (receive or change). -/
  ownedByWallet : Bool
  deriving Repr, Inhabited, BEq

/-- One row of the activity list (Winnow's `HistoryEntry`, with the transaction already decoded). -/
structure HistoryItem where
  /-- display hex -/
  txid : String
  height : Nat
  received : Int
  spent : Int
  fee : Option Int
  replacedBy : Option String := none
  /-- The decoded outputs; none while the raw transaction is not stored on this phone. -/
  outputs : Option (List TxOut) := none
  /-- Addresses this payment's inputs reveal (`FundingSources`), already rendered. -/
  fundingAddresses : List String := []
  deriving Repr, Inhabited, BEq

def HistoryItem.net (h : HistoryItem) : Int := h.received - h.spent

/-- `DisplayedPayment.Source`: whose payment a Transactions row is. -/
inductive PaymentSource where
  | wallet
  | account (name : String)
  /-- The same transaction in two histories: `from` paid `to` ("Wallet" or an account's name), `amount` sats. -/
  | transfer («from» to : String) (amount : Nat)
  /-- An account's draft: `signatures` reads "1 of 2". -/
  | draft (name signatures : String)
  deriving Repr, Inhabited, BEq

/-- `DisplayedPayment`: one row of the one Transactions list (wallet, account, transfer or draft). -/
structure DisplayedPayment where
  item : HistoryItem
  source : PaymentSource
  /-- The account whose history `item` comes from; none for the wallet's. -/
  accountID : Option String := none
  deriving Repr, Inhabited, BEq

def DisplayedPayment.isDraft (p : DisplayedPayment) : Bool := p.source matches .draft ..

/-- The account named on the row, if any. -/
def DisplayedPayment.accountName (p : DisplayedPayment) : Option String :=
  match p.source with
  | .wallet => none
  | .account n | .draft n _ => some n
  | .transfer f t _ => some (if f == "Wallet" then t else f)

/-- AppModel's `Status`. -/
structure Status where
  /-- The wallet's own coins. -/
  balance : Int := 0
  /-- The multisig accounts' live coins, which need co-signers to move. -/
  accountsBalance : Int := 0
  utxoCount : Nat := 0
  /-- The wallet's own history. -/
  history : List HistoryItem := []
  /-- The one Transactions list: wallet, accounts, transfers and drafts, newest first (drafts on top). -/
  payments : List DisplayedPayment := []
  feeBumpable : List String := []
  peerCount : Nat := 0
  tipHeight : Nat := 0
  nextScanHeight : Nat := 0
  syncing : Bool := false
  lastSyncError : Option String := none
  relayStoreQuarantined : Option String := none
  feeFloorMilli : Option Nat := none
  /-- `activePeerGateways`: the routing in effect (discovered, manual or clearnet). -/
  activeGateways : Winnow.IO.PeerGatewayConfiguration := {}
  /-- `discoveringGateways`: Automatic is asking the tailnet for its gateways. -/
  discoveringGateways : Bool := false
  /-- `transientSyncError` / `transientSyncFailures`: the message the last dropped or slow peer left and how
  many passes in a row ended so (`simpleSyncError`). -/
  transientSyncError : Option String := none
  transientSyncFailures : Nat := 0
  /-- `lastCompleteCheck`, as "5 min" for "Chain last checked 5 min ago" (none: never fully checked). -/
  lastCheckedAgo : Option String := none
  deriving Repr, Inhabited

/-- One saved iCloud backup of this network (`ICloudBackupSummary`), its date as the screens show it. -/
structure CloudBackupInfo where
  id : String
  savedAtText : String
  deriving Repr, Inhabited, BEq

/-- What the screens say for a build without the iCloud entitlement (the shell's `missingEntitlement`). -/
def cloudMissingEntitlementText : String := "iCloud backup isn't available in this build of Winnow."

/-- `CloudBackupController` as the screens read it (`automaticEnabled`, `enabled`, `statusTitle`,
`lastSaved`, `message`, `busy`, `available`) and AppModel's `cloudRestoreNotice`. -/
structure CloudStatus where
  automaticEnabled : Bool := true
  enabled : Bool := false
  statusTitle : String := "Not backed up"
  lastSavedText : Option String := none
  /-- How long ago that was ("5 min"), for the Settings row. -/
  lastSavedAgo : Option String := none
  message : Option String := none
  busy : Bool := false
  available : List CloudBackupInfo := []
  restoreNotice : Option String := none
  deriving Repr, Inhabited, BEq

/-- AppModel's `SyncPhase`. -/
inductive SyncPhase where
  | idle
  | connecting (connected target : Nat)
  | headers (synced estimate : Nat)
  | filters (scanned tip : Nat)
  | synced
  | peerDiscoveryFailed
  deriving Repr, BEq, Inhabited

inductive SyncSummary where
  | syncing
  | synced
  | peersUnavailable
  deriving Repr, BEq

/-- `SyncPhase.summary`: the one line a beginner reads. -/
def SyncPhase.summary (p : SyncPhase) (syncing : Bool) : SyncSummary :=
  match p with
  | .peerDiscoveryFailed => .peersUnavailable
  | .synced => if syncing then .syncing else .synced
  | _ => .syncing

def SyncPhase.headerTipMayLagNetwork : SyncPhase → Bool
  | .filters .. | .synced => false
  | _ => true

inductive Stage where
  | loading
  | onboarding
  | ready
  | storageDamaged (message : String)
  deriving Repr, BEq, Inhabited

/-! ## People, labels -/

inductive Provenance where
  | supplied
  | localFunding
  | explorerFunding
  deriving Repr, BEq, Inhabited

/-- `PersonRecord`, as the screens read it. -/
structure Person where
  id : String
  name : String
  /-- Whether the person can be paid, and whether each payment derives a fresh address. -/
  payTo : Option Bool := none
  nextPaymentIndex : Nat := 0
  savedRecipient : Option Bool := none
  provenance : Option Provenance := none
  deriving Repr, Inhabited, BEq

def Person.isSavedRecipient (p : Person) : Bool := p.payTo.isSome && p.savedRecipient != some false
def Person.derivesFreshAddresses (p : Person) : Bool := p.payTo == some true
def Person.hasUnverifiedFundingDestination (p : Person) : Bool :=
  p.provenance == some .localFunding || p.provenance == some .explorerFunding

/-- People and local labels, as one snapshot (each mutation answers with a fresh one). -/
structure Records where
  people : List Person := []
  /-- txid (display hex) → person id -/
  senderByTxid : List (String × String) := []
  /-- scriptPubKey hex → person id (`recipientByScript`) -/
  recipientByScript : List (String × String) := []
  /-- address → the owner's note (`ReceiveAddressLabelStore`) -/
  receiveLabels : List (String × String) := []
  peopleStorageNotice : Option String := none
  receiveLabelStorageNotice : Option String := none
  deriving Repr, Inhabited

/-! ## Results of individual operations -/

/-- What `PersonPaste.parse` read from a pasted address or card. -/
structure PastePreview where
  name : Option String := none
  /-- `some fresh` when it can be paid. -/
  payTo : Option Bool := none
  deriving Repr, Inhabited, BEq

/-- A connected peer (SettingsView.PeerInfo). -/
structure PeerInfo where
  endpoint : String
  userAgent : String
  startHeight : Int
  /-- BIP133 feefilter, sat/kvB -/
  feeFilter : Option Nat
  network : Winnow.IO.PeerNetwork := .clearnet
  deriving Repr, Inhabited

/-- `FeeBumpPreview`. -/
structure FeeBumpPreview where
  feeRateMilli : Nat
  fee : Nat
  change : Option Nat
  deriving Repr, Inhabited, BEq

/-- One broadcaster or mempool-window event about a sent transaction. -/
inductive RelayEvent where
  | announced (peerCount : Nat)
  | requested (peer : String)
  | echoed (peer : String)
  | feeFloorExceeded
  | confirmed
  deriving Repr, Inhabited

end WinnowApp

namespace WinnowApp

/-! ## Multisig accounts (Advanced mode) -/

/-- One output of a reviewed spend. -/
structure MultisigOutputLine where
  owned : Bool
  amount : Nat
  /-- The address, or the script in hex. -/
  address : String
  deriving Repr, Inhabited, BEq

/-- `MultisigSigningProgress`. -/
structure MultisigProgress where
  complete : Bool := false
  phoneHolds : Bool := false
  phoneUnsigned : Bool := false
  ledgerHolds : Bool := false
  ledgerUnsigned : Bool := false
  deriving Repr, Inhabited, BEq

def MultisigProgress.signedHere (p : MultisigProgress) : Bool := p.phoneHolds && !p.phoneUnsigned

/-- `MultisigSigningProgress.nextStep`: the signing screen's footer. -/
def MultisigProgress.nextStep (p : MultisigProgress) : String :=
  if p.complete then "Enough signatures verify. Finalize and broadcast."
  else if p.ledgerUnsigned then
    if p.signedHere then "Sign with the Ledger: check the payment on its screen before approving."
    else "Add this phone's signature and the Ledger's, in either order. Check the payment on the Ledger's screen."
  else if p.signedHere then "Share the PSBT below with the other signers, then combine their signed copies here."
  else "Check the payment, then add this phone's signature. Signers can sign in any order."

/-- `MultisigSigningScreen`: the review, the verified signatures per usable path, and the progress. -/
structure MultisigScreen where
  outputs : List MultisigOutputLine
  inputTotal : Nat
  fee : Nat
  /-- Per usable path: is it the recovery path, verified signatures, threshold. -/
  signatures : List (Bool × Nat × Nat)
  /-- Per usable path: the row's title and its UI-test identifier (`signaturesTitle`, `signatureCountIdentifier`). -/
  signatureTitles : List (String × String) := []
  progress : MultisigProgress
  deriving Repr, Inhabited, BEq

def MultisigScreen.recoveryUsable (s : MultisigScreen) : Bool := s.signatures.any (·.1)

/-- An account's draft as the screens show it (`MultisigSigningSections`): the PSBT to share (BIP174 v0),
its txid, its review, and the signatures on its best leaf. -/
structure MultisigDraftInfo where
  psbt : String
  txid : String
  screen : Option MultisigScreen := none
  reviewError : Option String := none
  /-- "1 of 2" (`bestLeafSignatures`). -/
  signatures : String := ""
  deriving Repr, Inhabited, BEq

/-- One live coin of a multisig account, as MultisigAccountView lists it. -/
structure MultisigCoin where
  amount : Nat
  /-- "txid…:vout · receive 3 · block 120" -/
  line : String
  /-- `recoveryUnlockHeight(of:)`. -/
  recoveryFrom : Option Nat := none
  deriving Repr, Inhabited, BEq

/-- A `MultisigAccountRecord` and its account, as the multisig screens show them. -/
structure MultisigInfo where
  id : String
  name : String
  descriptor : String
  balance : Int
  /-- "2 of 3"; none when the descriptor no longer reads as an account. -/
  policy : Option String := none
  /-- `MultisigAccountView.recoveryText`. -/
  recovery : Option String := none
  /-- The paired Ledger's master fingerprint (`%08x`). -/
  ledgerFingerprint : Option String := none
  /-- The registered Ledger as the account screen names it: "Nano X · 5992698d", or the fingerprint. -/
  ledgerName : Option String := none
  /-- `LedgerMultisig.namesALedgerKey` and no registration yet: "Register on Ledger". -/
  needsLedgerRegistration : Bool := false
  isNested : Bool := false
  /-- A nested account's members section: its header and one line per member (or per leaf). -/
  membersHeader : Option String := none
  memberLines : List String := []
  /-- `signerExpressions`, `threshold`, `signers.count`: the builder's picker offers the account as one member. -/
  signerExpressions : List String := []
  threshold : Nat := 0
  signerCount : Nat := 0
  /-- The payment this phone is collecting signatures for. -/
  draft : Option MultisigDraftInfo := none
  /-- Spends this phone broadcast that no block has taken (display-hex txids). -/
  inFlight : List String := []
  nextReceiveIndex : Nat := 0
  receiveAddress : Option String := none
  coins : List MultisigCoin := []
  /-- What a PSBT's review depends on (`TrustedState`: coins and frontiers): a change re-reviews it. -/
  trusted : String := ""
  deriving Repr, Inhabited, BEq

def MultisigInfo.hasRecovery (a : MultisigInfo) : Bool := a.recovery.isSome

/-- A `SignerRecord` as Settings → Signers and the builder's picker show it. -/
structure SignerInfo where
  id : String
  isLedger : Bool
  name : String
  /-- `[fp/path]xpub…/<0;1>/*`, one or more. -/
  keys : List String
  /-- `SignerLabel.keysText`: "5992698d" for a Ledger, "6824f543 · 1a2b3c4d" for saved keys. -/
  keysText : String
  deriving Repr, Inhabited, BEq

/-- `multisigAccounts`, `multisigStorageNotice`, this wallet's key expression (`multisigKeyExpression`),
and the signer list (`signers`, `signerStorageNotice`). -/
structure MultisigOverview where
  accounts : List MultisigInfo := []
  notice : Option String := none
  keyExpression : Option String := none
  /-- `SignerLabel.fingerprint` of this phone's key. -/
  ownFingerprint : Option String := none
  signers : List SignerInfo := []
  signerNotice : Option String := none
  deriving Repr, Inhabited, BEq

def MultisigOverview.ledgers (o : MultisigOverview) : List SignerInfo := o.signers.filter (·.isLedger)
def MultisigOverview.savedKeys (o : MultisigOverview) : List SignerInfo := o.signers.filter (!·.isLedger)

/-- What a pasted descriptor reads as (MultisigAddView's `validation`). -/
structure MultisigCheck where
  policy : String
  firstAddress : Option String
  /-- A paired Ledger holding a key of the account, which approves it after Save. -/
  ledgerName : Option String := none
  deriving Repr, Inhabited, BEq

/-- `MultisigBuildView.recoveryPlan`. -/
inductive MultisigRecovery where
  | fewerSigners (threshold blocks : Nat)
  | separateKey (key : String) (blocks : Nat)
  deriving Repr, Inhabited, BEq

/-- A PSBT in hand: its v2 Base64 (the working copy), the BIP174 v0 text to share, and its review. -/
structure MultisigPSBT where
  psbt : String
  output : Option String
  screen : Option MultisigScreen
  reviewError : Option String := none
  deriving Repr, Inhabited, BEq

end WinnowApp
