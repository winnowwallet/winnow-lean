import Winnow.Wallet.SpendReview
import Winnow.Wallet.CoinSelection
import Winnow.Wallet.PSBTRoles
import Winnow.Wallet.MultisigSpendRecords
import Winnow.Keys.Unicode

/-! # Taproot multisig accounts (port of `Sources/WalletCore/Wallet/MultisigAccount.swift`, upstream d2ca878)

A raw k-of-n script-path account `tr(NUMS, sortedmulti_a(k, XPUB/<0;1>/*, …))` (BIP386, BIP387), optionally
with timelocked recovery leaves beside the signers' leaves (`and_v(v:pk(K),older(N))` or
`and_v(v:multi_a(m,…),older(N))`). The internal key is BIP341's NUMS point (bare, or as Liana's xpub on it),
so the leaves are the only way to spend. A nested account (upstream #256) has several signers' leaves: its
members are groups of keys that sign together (a phone and its Ledger), or a threshold over their keys (a
2-of-3 account that is one member); any `threshold` of the members spend, one leaf per group of that many
members and per way the group meets its thresholds. A key in more than one leaf takes the next
`/<2n;2n+1>/*` pair in each (SEC-019), so a BIP388 signer can register the whole tree. Spends travel as PSBTs
with the BIP371 leaf, origin and signature fields: `createSpend` builds one, `sign` adds a signer's
script-path signatures after reviewing it, `approvals` counts verified signatures on one leaf,
`finalizeSpend` assembles the BIP387 witness of a leaf that is complete.

The account itself, `makeDescriptor` and `reviewSpend` are in `Wallet/SpendReview.lean`, part of the core
library (`WinnowCore`); this module adds the stored record, `signerKey` and creating, signing and finalizing
spends.

Differences of form from the Swift struct:
* Failures are `MultisigFailure`: this module's `MultisigAccountError` (same cases and reason texts), or
  another module's error by its case name (`named`), as `WalletFailure` does.
* Swift `Set`s and dictionaries are arrays here: `approvals` is the positions in ascending order, key
  origins are (x-only key, origin) pairs with the last value per key kept, sets of keys (a leaf, a group)
  are sorted arrays without repeats.
* `descriptor(threshold:signers:…)` is `makeDescriptor`, `descriptor(members:threshold:…)` is
  `makeNestedDescriptor` (over `Member`s; the `[[String]]` overload is `members.map Member.all`).
  `SpendPath.signers` / `.recovery` take the leaf position with 0 as default, for Swift's static
  `.signers` and its `.signers(i)`.
* Randomness is an argument: `createSpend` takes the two anti-fee-sniping draws (Swift's `randomness`
  closure, called once or twice) and the change position (Swift's `Int.random(in: 0 ... n)` inside
  `TransactionBuilder.build`); `sign` takes the BIP340 auxiliary randomness (Swift passes nil, so P256K
  draws it).
* `MultisigAccountRecord.checkLedgerRegistration` needs `LedgerWalletPolicy`, so it is defined with the
  Ledger signer (`Ledger/Multisig.lean`); the record's `ledger` field is carried and coded here. -/

namespace Winnow
open Keys SwiftJSON
open Tx (BitcoinNetwork)

/-! ## Ledger registration (data only; the protocol is Phase C) -/

/-- `LedgerRegistration` (Ledger/LedgerMultisig.swift): what a Ledger returned when it registered the
account. Coded as Swift's synthesized `Codable` (`Data` fields base64). -/
structure LedgerRegistration where
  /-- The name the Ledger shows for the account. -/
  policyName : String
  policyID : ByteArray
  hmac : ByteArray
  masterFingerprint : UInt32
  /-- The Ledger signer's account path, hardened bits included. -/
  keyPath : Array UInt32
  deriving Inhabited, BEq

namespace LedgerRegistration
def toJV (r : LedgerRegistration) : JV :=
  obj [("policyName", some (.str r.policyName)), ("policyID", some (ofData r.policyID)), ("hmac", some (ofData r.hmac)),
    ("masterFingerprint", some (ofInt r.masterFingerprint.toNat)),
    ("keyPath", some (.arr (r.keyPath.map (ofInt ·.toNat))))]

def ofJV (v : JV) : D LedgerRegistration := do
  let kvs ← asObject v
  let policyName ← key kvs "policyName" asString
  let policyID ← key kvs "policyID" asData
  let hmac ← key kvs "hmac" asData
  let masterFingerprint ← key kvs "masterFingerprint" asUInt32
  let keyPath ← key kvs "keyPath" (asArray asUInt32)
  return { policyName, policyID, hmac, masterFingerprint, keyPath }
end LedgerRegistration

/-! ## The stored record -/

/-- One stored multisig account: the descriptor, its address frontiers, the coins the wallet's filter scan
found for it (spent ones kept as tombstones), what happened to them, and the spend this phone is
collecting signatures for or has broadcast. JSON keys match the shared-account Winnow's vault records
(`utxos` for `allUtxos`); a record without history, a draft or in-flight spends encodes exactly as it did
before they existed. -/
structure MultisigAccountRecord where
  /-- The descriptor's BIP380 checksum. -/
  id : String
  name : String
  descriptor : String
  createdAtHeight : UInt32
  nextReceiveIndex : UInt32 := 0
  nextChangeIndex : UInt32 := 0
  allUtxos : Array WalletUTXO := #[]
  /-- Present when a Ledger is one of the signers and has registered this account. -/
  ledger : Option LedgerRegistration := none
  /-- What happened to the account's coins, as the wallet keeps its own: receives and spends the scan
  found, and this phone's broadcasts while they are pending. Absent in records written before. -/
  history : Array HistoryEntry := #[]
  /-- The one spend this phone is collecting signatures for, if any. -/
  draft : Option MultisigSpendDraft := none
  /-- Spends this phone broadcast that no block has confirmed, with the bytes a restored phone needs to
  announce them again. -/
  inFlight : Array InFlightSpend := #[]
  deriving Inhabited, BEq

namespace MultisigAccountRecord
def utxos (r : MultisigAccountRecord) : Array WalletUTXO := r.allUtxos.filter (!·.isSpent)
def balance (r : MultisigAccountRecord) : Int64 := r.utxos.foldl (fun a u => a + u.amount) 0

def toJV (r : MultisigAccountRecord) : JV :=
  obj [("id", some (.str r.id)), ("name", some (.str r.name)), ("descriptor", some (.str r.descriptor)),
    ("createdAtHeight", some (ofInt r.createdAtHeight.toNat)), ("nextReceiveIndex", some (ofInt r.nextReceiveIndex.toNat)),
    ("nextChangeIndex", some (ofInt r.nextChangeIndex.toNat)), ("utxos", some (.arr (r.allUtxos.map WalletUTXO.toJV))),
    ("ledger", r.ledger.map LedgerRegistration.toJV),
    ("history", if r.history.isEmpty then none else some (.arr (r.history.map HistoryEntry.toJV))),
    ("draft", r.draft.map MultisigSpendDraft.toJV),
    ("inFlight", if r.inFlight.isEmpty then none else some (.arr (r.inFlight.map InFlightSpend.toJV)))]

/-- The custom decoder, in declaration order: every key but `ledger`, `history`, `draft` and `inFlight` is
required (the last three absent from records written before they existed). -/
def ofJV (v : JV) : D MultisigAccountRecord := do
  let kvs ← asObject v
  let id ← key kvs "id" asString
  let name ← key kvs "name" asString
  let descriptor ← key kvs "descriptor" asString
  let createdAtHeight ← key kvs "createdAtHeight" asUInt32
  let nextReceiveIndex ← key kvs "nextReceiveIndex" asUInt32
  let nextChangeIndex ← key kvs "nextChangeIndex" asUInt32
  let allUtxos ← key kvs "utxos" (asArray WalletUTXO.ofJV)
  let ledger ← keyIfPresent kvs "ledger" LedgerRegistration.ofJV
  let history := (← keyIfPresent kvs "history" (asArray HistoryEntry.ofJV)).getD #[]
  let draft ← keyIfPresent kvs "draft" MultisigSpendDraft.ofJV
  let inFlight := (← keyIfPresent kvs "inFlight" (asArray InFlightSpend.ofJV)).getD #[]
  return { id, name, descriptor, createdAtHeight, nextReceiveIndex, nextChangeIndex, allUtxos, ledger, history, draft,
           inFlight }
end MultisigAccountRecord

namespace MultisigAccount

/-- `signerKey(_:network:)`: a signer key expression as the builders take it and the app's signer roster
keeps it, `[fp/path]xpub…/<0;1>/*` on `network`. -/
def signerKey (expression : String) (network : BitcoinNetwork) : MAM Descriptor.SingleKey := do
  let text := Keys.Unicode.trimWhitespace expression
  let notParsed : MAM Descriptor.SingleKey := invalid "a signer key expression does not parse"
  -- `Character.isWhitespace`: the Unicode White_Space property (U+200B is not one).
  let isWhitespace (c : Char) := Keys.Unicode.isWhitespaceOrNewline c && c.toNat != 0x200B
  if text.toList.any (fun c => c == '(' || c == ')' || c == ',' || isWhitespace c) then return ← notParsed
  let .ok parsed := Descriptor.parse s!"tr({text})" | notParsed
  let .tr single := parsed.expression | notParsed
  discard (requireAccountKey single network)
  return single

/-! ### Creating a spend -/

def compactSizeLength (value : Nat) : Nat := if value < 0xFD then 1 else if value ≤ 0xFFFF then 3 else 5

/-- Per-input witness bytes for fee estimation on `path`: item count, one 65-byte slot per key of that
leaf, the leaf script and its control block (33 bytes, plus 32 per level above the leaf), each
length-prefixed. On a signers' path the largest signers' leaf: the creator does not know which group will
finish the spend. -/
def witnessBytesPerInput (a : MultisigAccount) (path : SpendPath := .signers) : MAM Int := do
  let candidates := (← a.leaves 0 0).filter (·.isRecovery == path.isRecovery)
  if candidates.isEmpty then refuse "this account has no recovery path"
  let sizes := candidates.map fun leaf =>
    let slots := (a.keysOn leaf.path).size
    let scriptSize := leaf.script.size
    let controlBlockSize := 33 + 32 * leaf.controlBlock.path.size
    1 + slots * 65 + compactSizeLength scriptSize + scriptSize + 1 + controlBlockSize
  return (sizes.foldl max 0 : Nat)

/-- The suffix steps a key expression takes at (choice, index). -/
def suffixSteps (key : Descriptor.SingleKey) (choice : Nat) (index : UInt32) : Array UInt32 :=
  key.derivation.elements.map fun
    | .step s => s
    | .multipath vs => vs[choice]!
    | .wildcard hardened => index + (if hardened then HDKey.hardenedOffset else 0)

/-- BIP371 key origins for every key of every leaf at (choice, index): master fingerprint, the full path
and the leaf hashes the derived key signs for. A signer in several leaves derives a different key in each,
so each entry names one leaf. -/
def keyOrigins (a : MultisigAccount) (choice : Nat) (index : UInt32) : MAM (Array (ByteArray × PSBT.KeyOrigin)) := do
  let mut origins : Array (ByteArray × PSBT.KeyOrigin) := #[]
  let r ← a.resolved choice index
  for leaf in r.leaves do
    let offset := a.keyOffset leaf.path
    for h : position in [0:(a.keysOn leaf.path).size] do
      let key := (a.keysOn leaf.path)[position]
      let some origin := key.origin | continue
      let xonly := r.keys[offset + position]!
      let known := (origins.find? (·.1 == xonly)).map (·.2.leafHashes)
      let leafHashes := match known with
        | some hs => if hs.contains leaf.hash then hs else hs.push leaf.hash
        | none => #[leaf.hash]
      let entry : PSBT.KeyOrigin := { leafHashes, masterFingerprint := origin.fingerprint,
                                      path := origin.path ++ suffixSteps key choice index }
      origins := match origins.findIdx? (·.1 == xonly) with
        | some j => origins.set! j (xonly, entry)
        | none => origins.push (xonly, entry)
  return origins

/-- The coins a spend on `path` may use and the sequence its inputs carry. -/
def spendableCoins (a : MultisigAccount) (utxos : Array WalletUTXO) (path : SpendPath) (chainTip : UInt32) :
    MAM (Array WalletUTXO × UInt32) := do
  -- a coinbase coin short of its hundred blocks is not a coin to spend yet: selected (the largest first), it
  -- would only be refused by the review (`checkInput`), with coins beside it that could have paid
  let mature (u : WalletUTXO) : Bool :=
    !u.isCoinbase || chainTip.toNat ≥ u.height.toNat + Wallet.coinbaseMaturity.toNat - 1
  let utxos := utxos.filter mature
  if !path.isRecovery then return (utxos, TransactionBuilder.defaultSequence)
  let some r := a.recovery | refuse "this account has no recovery path"
  let unlocked := utxos.filter (a.isUnlockedForRecovery · chainTip)
  if unlocked.isEmpty then
    refuse s!"no coin has stayed unmoved for {r.blocks} blocks yet, so none can be recovered"
  return (unlocked, r.blocks)

/-- The internal key, tap tree (right subtree first, as Bitcoin Core lists it) and key origins on the
change output. -/
def describeChange (a : MultisigAccount) (change : Payment) (changeIndex : UInt32) (psbt : PSBT) : MAM PSBT := do
  let leaves ← a.leaves AddressChain.change.rawValue changeIndex
  let origins ← a.keyOrigins AddressChain.change.rawValue changeIndex
  -- Each leaf's depth is the length of its Merkle path.
  let tree := leaves.reverse.map fun l => (l.controlBlock.path.size.toUInt8, l.version, l.script)
  let outputs := psbt.outputs.map fun o =>
    if o.script == some change.scriptPubKey && o.amount == some change.amount then
      ((o.setTapInternalKey (some leaves[0]!.internalKey)).setTapTree (some tree)).setTapBIP32Derivation origins
    else o
  return { psbt with outputs }

/-- Builds the unsigned spend PSBT: coin selection sized for this account's witness on `path`, the
transaction with an anti-fee-sniping locktime from `draws` and the change at `changePosition n` among the
`n` payments, the BIP371 leaves and per-key origins on every input, and the internal key, tap tree and
origins on the change output. -/
def createSpend (a : MultisigAccount) (utxos : Array WalletUTXO) (payments : Array Payment) (changeIndex : UInt32)
    (feeRateSatPerVByte : Float) (chainTip : UInt32) (path : SpendPath := .signers)
    (draws : Float × Float := (0.5, 0.5)) (changePosition : Nat → Nat := fun n => n) : MAM PSBT := do
  for u in utxos do
    unless (← a.scriptPubKey u.index u.chain.rawValue) == u.scriptPubKey do
      fail (.scriptMismatch u.index u.chain.rawValue)
  let (spendable, sequence) ← a.spendableCoins utxos path chainTip
  let changeScript ← a.scriptPubKey changeIndex AddressChain.change.rawValue
  let witness ← a.witnessBytesPerInput path
  let selection ← lift (·.name) (CoinSelection.select spendable payments changeScript feeRateSatPerVByte witness)
  checkFeeCeiling selection.fee (selection.selected.foldl (fun t u => t + u.amount) 0)
  let change : Option Payment := selection.changeAmount.map fun amt => { amount := amt, scriptPubKey := changeScript }
  let locktime := TransactionBuilder.antiFeeSnipingLocktime chainTip draws.1 draws.2
  let tx ← lift (·.name) (TransactionBuilder.build (selection.selected.map (·.outpoint)) payments change
    (randomPosition := changePosition) (sequence := sequence) (locktime := locktime))
  let mut psbt ← lift (·.name) (PSBT.create tx (selection.selected.map fun u => { spentOutput := u.spentOutput })
    (tx.outputs.map fun _ => {}))
  for h : k in [0:selection.selected.size] do
    let u := selection.selected[k]
    let leaves ← a.leaves u.chain.rawValue u.index
    let origins ← a.keyOrigins u.chain.rawValue u.index
    psbt ← lift (·.name) (psbt.attachScriptPaths k (leaves.map fun l => (l.controlBlock, ⟨l.script⟩, l.version)) origins)
  if let some c := change then psbt ← a.describeChange c changeIndex psbt
  return psbt

/-! ### Signing -/

/-- The input's coordinates, from the known coin it spends. -/
def coin (psbt : PSBT) (input : Nat) (knownUTXOs : Array WalletUTXO) : MAM WalletUTXO := do
  let notKnown : MAM WalletUTXO := refuse s!"input {input + 1} is not an available coin of this account"
  let some i := psbt.inputs[input]? | notKnown
  let some txid := i.previousTxid | notKnown
  let some vout := i.outputIndex | notKnown
  let some known := knownUTXOs.find? (·.outpoint == ⟨txid, vout⟩) | notKnown
  return known

/-- Reviews the spend, then adds a script-path signature to every input for each key `key` holds (a master
or a BIP86 account key itself), on every leaf that key is in; `noSignerKey` when an input has none. The PSBT is replaced only when every
input signs. -/
def sign (a : MultisigAccount) (psbt : PSBT) (signingKey : HDKey) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) (auxiliaryRand : ByteArray) : MAM PSBT := do
  discard (a.reviewSpend psbt knownUTXOs ownedOutputCoordinates chainTip)
  -- each of the account's keys `signingKey` holds, with its account key: derived once per key, however
  -- many leaves it is in
  let mut held : Array (Descriptor.SingleKey × HDKey) := #[]
  for signer in a.allKeys do
    let account ← match held.find? (identity ·.1 == identity signer) with
      | some (_, account) => pure (some account)
      | none => accountSecretKey signer signingKey
    if let some account := account then held := held.push (signer, account)
  let mut signed := psbt
  for k in [0:signed.inputs.size] do
    let u ← coin signed k knownUTXOs
    let mut secrets : Array ByteArray := #[]
    for (signer, account) in held do
      let child ← lift (·.name) (account.derivedPath (suffixSteps signer u.chain.rawValue u.index))
      let some secret := child.privateKey | continue
      secrets := secrets.push secret
    if secrets.isEmpty then fail (.noSignerKey k)
    signed ← lift (·.name) (signed.signScriptPath k secrets auxiliaryRand)
  return signed

/-- Which keys of `path`'s leaf (by position among that leaf's keys) have a verified signature on that
leaf of every input, judged by BIP340 verification against the recomputed sighash. Ascending positions. -/
def approvals (a : MultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO) (path : SpendPath := .signers) :
    MAM (Array Nat) := do
  let keys := a.keysOn path
  if keys.isEmpty then return #[]
  let tx ← lift (·.name) psbt.unsignedTransaction
  let spent ← lift (·.name) psbt.spentOutputs
  let mut approved : Option (Array Nat) := none
  for k in [0:psbt.inputs.size] do
    let u ← coin psbt k knownUTXOs
    let r ← a.resolved u.chain.rawValue u.index
    let some leaf := r.leaves.find? (·.path == path) | return #[]
    let verified ← lift (·.name) (psbt.verifiedScriptPathSigners k leaf.hash tx spent)
    let offset := a.keyOffset path
    let mut here : Array Nat := #[]
    for position in [0:keys.size] do
      if verified.contains r.keys[offset + position]! then here := here.push position
    approved := some (match approved with | some prev => prev.filter here.contains | none => here)
  return approved.getD #[]

/-- Finalizes a PSBT with at least the threshold of verified signatures per input and extracts the raw
transaction, after one more review. Returns the finalized PSBT and the transaction. -/
def finalizeSpend (a : MultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) : MAM (PSBT × Transaction) := do
  discard (a.reviewSpend psbt knownUTXOs ownedOutputCoordinates chainTip)
  let finalized ← lift (·.name) psbt.finalize
  let tx ← lift (·.name) finalized.extractedTransaction
  lift (·.name) (Wallet.checkStandardSize tx)
  return (finalized, tx)

end MultisigAccount
end Winnow