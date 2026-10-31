import Winnow.Wallet.Types
import Winnow.Wallet.CoinSelection
import Winnow.Wallet.Descriptor
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

/-! ## Errors -/

inductive MultisigAccountError where
  /-- Not a supported account shape. `reason` is always a literal written here, never input. -/
  | invalidDescriptor (reason : String)
  /-- A coin's scriptPubKey does not match the descriptor at its coordinates. -/
  | scriptMismatch (index : UInt32) (choice : Nat)
  /-- No signer key for this input derives from the loaded key. -/
  | noSignerKey (input : Nat)
  /-- An imported spend is not an exact, safe spend of known account coins. -/
  | invalidSpend (reason : String)
  deriving Inhabited, BEq, Repr

namespace MultisigAccountError
def name : MultisigAccountError → String
  | .invalidDescriptor _ => "invalidDescriptor" | .scriptMismatch .. => "scriptMismatch"
  | .noSignerKey _ => "noSignerKey" | .invalidSpend _ => "invalidSpend"

/-- `errorDescription`. -/
def description : MultisigAccountError → String
  | .invalidDescriptor reason => s!"The multisig descriptor is invalid: {reason}."
  | .scriptMismatch index choice => s!"Multisig key {choice}/{index} does not produce the stored Bitcoin output."
  | .noSignerKey input => s!"This device holds no signer key for input {input + 1}."
  | .invalidSpend reason => s!"This multisig spend is unsafe: {reason}."
end MultisigAccountError

inductive MultisigFailure where
  | account (e : MultisigAccountError)
  /-- An error of another module (descriptor, PSBT, coin selection, BIP32, …), by its case name. -/
  | named (name : String)
  deriving Inhabited, BEq, Repr

def MultisigFailure.name : MultisigFailure → String | .account e => e.name | .named n => n

abbrev MAM := Except MultisigFailure

namespace MultisigAccount
def fail {α} (e : MultisigAccountError) : MAM α := throw (.account e)
def invalid {α} (reason : String) : MAM α := fail (.invalidDescriptor reason)
def refuse {α} (reason : String) : MAM α := fail (.invalidSpend reason)
def lift {ε α} (name : ε → String) (r : Except ε α) : MAM α := r.mapError (.named ∘ name)
end MultisigAccount

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

/-! ## The account -/

/-- `Descriptor.SingleKey`'s synthesized `Equatable` (origin, key, derivation), by the expression text. -/
instance : BEq Descriptor.SingleKey := ⟨fun a b => Descriptor.serializeSingle a == Descriptor.serializeSingle b⟩

namespace MultisigAccount

/-- A descriptor coordinate that may legitimately receive money back into this account. -/
structure OutputCoordinate where
  choice : Int
  index : UInt32
  deriving Inhabited, BEq, Repr

/-- One leaf the account can spend on: the signers' leaf at a position among `signersLeaves`
(`.signers` is the first, every ordinary account's only one), or the timelocked recovery leaf at a
position among `recoveryLeaves` (`.recovery` is the first). Swift's `.signers` / `.signers(i)` are one
function here with the position defaulting to 0, as are `.recovery` / `.recovery(i)`. -/
structure SpendPath where
  /-- The position among the signers' leaves; `none` for a recovery leaf. -/
  signersLeaf : Option Nat
  /-- The position among the recovery leaves; `none` for a signers' leaf. -/
  recoveryLeaf : Option Nat
  deriving Inhabited, BEq, Hashable, Repr

namespace SpendPath
/-- The signers' leaf at `leaf`; `.signers` is the first: any `threshold` of its signers, at once. -/
def signers (leaf : Nat := 0) : SpendPath := ⟨some leaf, none⟩
/-- The recovery leaf at `leaf`; `.recovery` is the first, once each coin is `Recovery.blocks` old. -/
def recovery (leaf : Nat := 0) : SpendPath := ⟨none, some leaf⟩
def isRecovery (p : SpendPath) : Bool := p.signersLeaf.isNone
/-- `description`: `signers(0)`, `recovery`, `recovery(1)`. -/
def description (p : SpendPath) : String :=
  match p.signersLeaf with
  | some leaf => s!"signers({leaf})"
  | none => if p.recoveryLeaf == some 0 then "recovery" else s!"recovery({p.recoveryLeaf.getD 0})"
instance : ToString SpendPath := ⟨description⟩
end SpendPath

structure SpendReview.Output where
  amount : Int64
  scriptPubKey : ByteArray
  isAccountOwned : Bool
  deriving Inhabited, BEq

structure SpendReview where
  outputs : Array SpendReview.Output
  inputTotal : Int64
  outputTotal : Int64
  fee : Int64
  /-- `.recovery` when every input's sequence meets the recovery lock, so the recovery leaf can finish
  it as well as the signers' leaves. -/
  path : SpendPath := .signers
  deriving Inhabited, BEq

/-- One signers' leaf: `sortedmulti_a(threshold, keys…)`. -/
structure SignersLeaf where
  threshold : Int
  keys : Array Descriptor.SingleKey
  /-- Whether the leaf is `sortedmulti_a` (keys sorted in the script). -/
  isSorted : Bool
  deriving Inhabited, BEq

/-- A nested account read back from its leaves: `threshold` of `groups` spend, each group signing with
`thresholds[i]` of its keys. -/
structure Members where
  threshold : Nat
  groups : Array (Array Descriptor.SingleKey)
  /-- How many of each group's keys sign for it, by position in `groups`. -/
  thresholds : Array Nat
  deriving Inhabited, BEq

/-- The positions of the groups that need fewer than all their keys. -/
def Members.thresholdGroups (m : Members) : Array Nat :=
  (Array.range m.groups.size).filter fun i => m.thresholds[i]! < m.groups[i]!.size

/-- One member as the builder takes it: keys, `threshold` of which sign for the member. -/
structure Member where
  keys : Array String
  threshold : Int
  deriving Inhabited, BEq

/-- `Member(keys:)`: every key signs (a phone and its Ledger). -/
def Member.all (keys : Array String) : Member := { keys, threshold := keys.size }

/-- A timelocked leaf, `and_v(v:pk(K),older(N))` or `and_v(v:multi_a(m,…),older(N))`: after a coin has
not moved for N blocks, `threshold` of these keys may spend it without the signers. An ordinary account
has at most one; a nested account whose recovery path is fewer of its members has one per group of them,
all opening after the same N. -/
structure Recovery where
  threshold : Int
  keys : Array Descriptor.SingleKey
  /-- BIP68 relative lock in blocks, 1…65535. -/
  blocks : UInt32
  deriving Inhabited, BEq

/-- How a new account's recovery path is chosen. -/
inductive RecoveryPlan where
  /-- After the delay, `threshold` of the same signers, each on its next derivation pair (`/<2;3>/*` in
  an ordinary account); for a nested account, `threshold` of its members, a timelocked leaf per group. -/
  | fewerSigners (threshold : Int) (blocks : UInt32)
  /-- After the delay, `threshold` of these other keys (`…/<0;1>/*`). -/
  | separateKeys (threshold : Int) (keys : Array String) (blocks : UInt32)
  deriving Inhabited

/-- One leaf at (choice, index), with its control block and the internal key. -/
structure Leaf where
  internalKey : ByteArray
  version : UInt8
  script : ByteArray
  controlBlock : Tx.Taproot.ControlBlock
  path : SpendPath
  deriving Inhabited

/-- One (choice, index) resolved: its output, every leaf in tree order, and the x-only key each of the
account's keys (`allKeys` order) derives there. -/
structure Resolved where
  output : Descriptor.DerivedOutput
  leaves : Array Leaf
  keys : Array ByteArray
  deriving Inhabited

/-- How many indices per choice the account resolves at most once (`resolved`); past them it resolves on
every call. -/
def resolvedSpan : Nat := 64

end MultisigAccount

/-- A raw k-of-n Taproot script-path account `tr(NUMS, sortedmulti_a(k, XPUB/<0;1>/*, …))`, or a nested
one: its members are groups of keys that sign together, any `threshold` of the members spend, and the
tree holds one leaf per group of that many members. A key in more than one leaf takes the next
`/<2n;2n+1>/*` pair in each (SEC-019). -/
structure MultisigAccount where
  descriptor : Descriptor
  network : BitcoinNetwork
  /-- The signers' leaves in tree order: one for an ordinary account. -/
  signersLeaves : Array MultisigAccount.SignersLeaf
  /-- The timelocked recovery leaves in tree order, all opening after the same delay. -/
  recoveryLeaves : Array MultisigAccount.Recovery
  /-- Each leaf's path, in tree order. -/
  leafPaths : Array MultisigAccount.SpendPath
  /-- (choice, index) for the first `resolvedSpan` indices of each choice, each resolved on first use and
  then kept: a spend's review, signing, approvals and finalizing all read the same few. `make` fills it;
  without it every call resolves the descriptor again. -/
  resolvedCache : Array (Thunk (MAM MultisigAccount.Resolved)) := #[]
  deriving Inhabited

namespace MultisigAccount

/-- The longest relative lock accepted: BIP68's 16-bit block count. -/
def maximumRecoveryBlocks : UInt32 := 0xFFFF
/-- The most leaves an account may have, signers' and recovery leaves together. -/
def maximumLeaves : Nat := 32
def maxMoney : Int := 2_100_000_000_000_000

/-- The suffix of a key's `n`th appearance (from 0): `/<2n;2n+1>/*`. -/
def pairSuffix (appearance : Nat) : Array Descriptor.Element :=
  #[.multipath #[(2 * appearance).toUInt32, (2 * appearance + 1).toUInt32], .wildcard false]

def pairSuffixText (appearance : Nat) : String := s!"/<{2 * appearance};{2 * appearance + 1}>/*"

/-- The only signer suffix accepted on a key's first appearance (SEC-019). -/
def signerSuffix : Array Descriptor.Element := pairSuffix 0
/-- A signer's key on its second path, for the recovery leaf of an ordinary account. -/
def recoverySuffix : Array Descriptor.Element := pairSuffix 1

/-- Which appearance a suffix is, or `none` for any other derivation. -/
def appearance? (elements : Array Descriptor.Element) : Option Nat :=
  match elements with
  | #[.multipath #[a, b], .wildcard false] => if a % 2 == 0 && b == a + 1 then some (a / 2).toNat else none
  | _ => none

/-- The first recovery leaf, if the account has one. Every recovery leaf shares its delay. -/
def recovery (a : MultisigAccount) : Option Recovery := a.recoveryLeaves[0]?
/-- The recovery leaves' paths, in tree order. -/
def recoveryPaths (a : MultisigAccount) : Array SpendPath := (Array.range a.recoveryLeaves.size).map (.recovery ·)
/-- Signatures a spend on the first signers' leaf needs. -/
def threshold (a : MultisigAccount) : Int := a.signersLeaves[0]!.threshold
/-- Whether the first leaf is `sortedmulti_a`. -/
def isSorted (a : MultisigAccount) : Bool := a.signersLeaves[0]!.isSorted
/-- Whether the account has more than one signers' leaf. -/
def isNested (a : MultisigAccount) : Bool := a.signersLeaves.size > 1
/-- The signers' leaves' paths, in tree order. -/
def signersPaths (a : MultisigAccount) : Array SpendPath := (Array.range a.signersLeaves.size).map (.signers ·)

def hdNetwork (n : BitcoinNetwork) : HDKey.Network := if n == .mainnet then .mainnet else .testnet

def extendedKey? (k : Descriptor.SingleKey) : Option (HDKey × HDKey.Network) :=
  match k.base with | .extended key n => some (key, n) | _ => none

/-- A key's identity for repeats and reuse: its compressed public key. -/
def identity (k : Descriptor.SingleKey) : ByteArray :=
  match extendedKey? k with | some (key, _) => key.publicKey | none => .empty

/-- The distinct signer keys of the signers' leaves, in the order they first appear. -/
def signers (a : MultisigAccount) : Array Descriptor.SingleKey := Id.run do
  let mut seen : Array ByteArray := #[]
  let mut out := #[]
  for k in a.signersLeaves.flatMap (·.keys) do
    unless seen.contains (identity k) do
      seen := seen.push (identity k)
      out := out.push k
  return out

/-- A signer as accepted here: an extended public key with its origin, on this network, under the fixed
suffix for this appearance; the origin names as many steps as the key is deep and ends at the key's own
child index. Returns the key's identity. -/
def requireAccountKey (single : Descriptor.SingleKey) (network : BitcoinNetwork)
    (suffix : Array Descriptor.Element := signerSuffix) (nested recovery : Bool := false) : MAM ByteArray := do
  let some (key, keyNetwork) := extendedKey? single
    | invalid "every signer must be an extended public key carrying its origin"
  let some origin := single.origin | invalid "every signer must be an extended public key carrying its origin"
  if key.privateKey.isSome then invalid "every signer must be an extended public key carrying its origin"
  unless origin.path.size == key.depth.toNat && (key.depth == 0 || origin.path.back? == some key.childIndex) do
    invalid "a signer's origin path does not match its key"
  unless keyNetwork == hdNetwork network do invalid "a signer's extended key belongs to a different network"
  unless single.derivation.elements == suffix do
    let pair := pairSuffixText ((appearance? suffix).getD 0)
    invalid (if suffix == signerSuffix then
        "every signer must use the /<0;1>/* suffix, so the signers can be shown to be independent"
      else if recovery then s!"a signer reused for recovery must use its {pair} path there"
      else if nested then s!"a signer in more than one leaf must take its {pair} path in the next"
      else "a signer must not appear twice in one leaf")
  return key.publicKey

/-- SEC-020: the bare NUMS key H, or an origin-less xpub on H under the signers' suffix on this network. -/
def isUnspendable (key : Descriptor.SingleKey) (network : BitcoinNetwork) : Bool :=
  if key.origin.isSome then false
  else match key.base with
    | .publicKey raw =>
      key.derivation.elements.isEmpty &&
        (if raw.size == 32 then raw else raw.extract 1 raw.size) == Taproot.unspendableInternalKey
    | .extended xpub keyNetwork =>
      xpub.privateKey.isNone && keyNetwork == hdNetwork network &&
        xpub.publicKey == ByteArray.mk #[0x02] ++ Taproot.unspendableInternalKey &&
        key.derivation.elements == signerSuffix
    | .privateKey .. => false

/-! ### Admission -/

/-- A set of byte strings as a sorted array without repeats, so that set equality is array equality. -/
def asSet (xs : Array ByteArray) : Array ByteArray :=
  (sortBytes id xs).foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The keys' bookkeeping across the leaves: how often each appeared, and the origin it carried (Swift's
dictionaries, as association arrays), and each leaf's key set so no group appears twice. -/
structure AdmittedKeys where
  appearances : Array (ByteArray × Nat) := #[]
  origins : Array (ByteArray × Descriptor.KeyOrigin) := #[]
  groups : Array (Array ByteArray) := #[]
  recoveryGroups : Array (Array ByteArray) := #[]
  deriving Inhabited

namespace AdmittedKeys
def appearancesOf (k : AdmittedKeys) (id : ByteArray) : Nat := ((k.appearances.find? (·.1 == id)).map (·.2)).getD 0
def originOf (k : AdmittedKeys) (id : ByteArray) : Option Descriptor.KeyOrigin := (k.origins.find? (·.1 == id)).map (·.2)
/-- Records one more appearance of `id`, with `origin`. -/
def note (k : AdmittedKeys) (id : ByteArray) (origin : Descriptor.KeyOrigin) : AdmittedKeys :=
  let count := k.appearancesOf id + 1
  { k with
    appearances := match k.appearances.findIdx? (·.1 == id) with
      | some j => k.appearances.set! j (id, count) | none => k.appearances.push (id, count)
    origins := match k.origins.findIdx? (·.1 == id) with
      | some j => k.origins.set! j (id, origin) | none => k.origins.push (id, origin) }
end AdmittedKeys

def treeLeafExpressions : Descriptor.ScriptTree → List Descriptor.Leaf
  | .leaf l => [l]
  | .branch l r => treeLeafExpressions l ++ treeLeafExpressions r

/-- The tree's leaves in order: the signers' leaves, the timelocked recovery leaves, and each leaf's path. -/
def leavesOf (tree : Descriptor.ScriptTree) :
    MAM (Array SignersLeaf × Array Descriptor.Leaf × Array SpendPath) := do
  let leaves := treeLeafExpressions tree
  let mut signersLeaves : Array SignersLeaf := #[]
  let mut recoveryLeaves : Array Descriptor.Leaf := #[]
  let mut paths : Array SpendPath := #[]
  for leaf in leaves do
    match leaf with
    | .sortedMultiA k keys =>
      paths := paths.push (.signers signersLeaves.size)
      signersLeaves := signersLeaves.push { threshold := k, keys, isSorted := true }
    | .multiA k keys =>
      paths := paths.push (.signers signersLeaves.size)
      signersLeaves := signersLeaves.push { threshold := k, keys, isSorted := false }
    | .timelocked .. =>
      paths := paths.push (.recovery recoveryLeaves.size)
      recoveryLeaves := recoveryLeaves.push leaf
    | .pk _ => invalid "a multisig account has multi_a leaves, and timelocked recovery leaves beside them"
  if signersLeaves.isEmpty then invalid "a multisig account has exactly one multi_a leaf"
  unless leaves.length ≤ maximumLeaves do invalid s!"a multisig account has at most {maximumLeaves} leaves"
  return (signersLeaves, recoveryLeaves, paths)

/-- One key of a signers' leaf (SEC-009): admitted on the pair its appearance calls for, not repeated in
the leaf, and keeping one origin across leaves. -/
def admitSigner (signer : Descriptor.SingleKey) (nested : Bool) (network : BitcoinNetwork) (keys : AdmittedKeys)
    (seen : Array ByteArray) : MAM (AdmittedKeys × Array ByteArray) := do
  let id ← requireAccountKey signer network (pairSuffix (keys.appearancesOf (identity signer))) (nested := nested)
  if seen.contains id then
    invalid "the same signing key appears more than once, so this account needs fewer signers than it claims"
  unless (keys.originOf id).isNone || keys.originOf id == signer.origin do
    invalid "a signer in more than one leaf must keep its own fingerprint and path in each"
  let some origin := signer.origin | invalid "every signer must be an extended public key carrying its origin"
  return (keys.note id origin, seen.push id)

/-- Every signers' leaf: at least two keys, a threshold within them, each key admitted. -/
def admit (leaves : Array SignersLeaf) (network : BitcoinNetwork) : MAM AdmittedKeys := do
  let mut keys : AdmittedKeys := {}
  for leaf in leaves do
    unless leaf.keys.size ≥ 2 do invalid "a multisig account needs at least two signers"
    unless 1 ≤ leaf.threshold && leaf.threshold ≤ leaf.keys.size do
      invalid "the threshold must be between one and the number of signers"
    let mut seen : Array ByteArray := #[]
    for signer in leaf.keys do
      (keys, seen) ← admitSigner signer (leaves.size > 1) network keys seen
    if keys.groups.contains (asSet seen) then invalid "the same group of signers appears in two leaves"
    keys := { keys with groups := keys.groups.push (asSet seen) }
  return keys

/-- One recovery key: an extended key not seen before in the leaf; a signer's key keeps that signer's
origin and its next pair, any other key `/<0;1>/*`, then `/<2;3>/*` in a later recovery leaf. -/
def requireRecoveryKey (key : Descriptor.SingleKey) (keys : AdmittedKeys) (seen : Array ByteArray)
    (network : BitcoinNetwork) : MAM (AdmittedKeys × Array ByteArray) := do
  let some (xpub, _) := extendedKey? key | invalid "every recovery key must be an extended public key"
  if seen.contains xpub.publicKey then invalid "the same recovery key appears more than once"
  let knownOrigin := keys.originOf xpub.publicKey
  unless knownOrigin.isNone || key.origin == knownOrigin do
    invalid "a signer reused for recovery must keep its own fingerprint and path there"
  discard (requireAccountKey key network (pairSuffix (keys.appearancesOf xpub.publicKey)) (recovery := true))
  let some origin := key.origin | invalid "every signer must be an extended public key carrying its origin"
  return (keys.note xpub.publicKey origin, seen.push xpub.publicKey)

/-- The recovery leaves' rules: one timelock of 1…65535 blocks that every recovery leaf shares, distinct
keys in each leaf and no key set twice, each key admitted on the pair after its last leaf. -/
def recoveryOf (leaves : Array Descriptor.Leaf) (keys : AdmittedKeys) (network : BitcoinNetwork) :
    MAM (Array Recovery) := do
  let mut keys := keys
  let mut recoveries : Array Recovery := #[]
  for leaf in leaves do
    let .timelocked condition blocks := leaf
      | invalid "a leaf beside the signers' must be a timelocked recovery path"
    unless 1 ≤ blocks && blocks ≤ maximumRecoveryBlocks do invalid "a recovery delay must be 1 to 65535 blocks"
    unless recoveries.all (·.blocks == blocks) do invalid "every recovery leaf must open after the same delay"
    let mut seen : Array ByteArray := #[]
    for key in condition.keys do
      (keys, seen) ← requireRecoveryKey key keys seen network
    if keys.recoveryGroups.contains (asSet seen) then
      invalid "the same group of recovery keys appears in two leaves"
    keys := { keys with recoveryGroups := keys.recoveryGroups.push (asSet seen) }
    recoveries := recoveries.push { threshold := condition.threshold, keys := condition.keys, blocks }
  return recoveries

/-- Every key expression in the account: each signers' leaf's keys in tree order, then each recovery
leaf's. A signer in several leaves is listed once per leaf, each time on that leaf's path. -/
def allKeys (a : MultisigAccount) : Array Descriptor.SingleKey :=
  a.signersLeaves.flatMap (·.keys) ++ a.recoveryLeaves.flatMap (·.keys)

def treeLeaves : Taproot.Tree → List (UInt8 × ByteArray)
  | .leaf v s => [(v, s)]
  | .branch l r => treeLeaves l ++ treeLeaves r

def txControlBlock (c : Taproot.ControlBlock) : Tx.Taproot.ControlBlock :=
  { leafVersion := c.leafVersion, outputKeyParity := c.outputKeyParity, internalKey := c.internalKey, path := c.path.toArray }

/-- (choice, index) resolved from the descriptor: the internal key and tree once, the output and every
leaf's control block from them, and each key of `allKeys` derived. What `resolved` keeps. -/
def resolve (a : MultisigAccount) (choice : Nat) (index : UInt32) : MAM Resolved := do
  unless choice < a.descriptor.multipathCount do throw (.named "indexOutOfRange")
  let (internalKey, tree) ← lift (·.name) (a.descriptor.resolvedTaproot index choice)
  let output ← lift (·.name) (Descriptor.taprootOutput internalKey tree a.network)
  let blocks ← lift (·.name) (Taproot.controlBlocks internalKey tree)
  let scripts := treeLeaves tree
  unless scripts.length == blocks.length && scripts.length == a.leafPaths.size do
    invalid "the account's tree does not resolve to its leaves"
  let leaves := ((scripts.zip blocks).zipIdx.map fun (((v, s), cb), position) =>
    ({ internalKey, version := v, script := s, controlBlock := txControlBlock cb,
       path := a.leafPaths[position]! } : Leaf)).toArray
  let keys ← a.allKeys.mapM fun k => do
    let pub ← lift (·.name) (Descriptor.publicKey k index choice)
    pure (pub.extract 1 pub.size)
  return { output, leaves, keys }

/-- `resolve`, kept in `resolvedCache` for the first `resolvedSpan` indices of each choice. -/
def resolved (a : MultisigAccount) (choice : Nat) (index : UInt32) : MAM Resolved :=
  match (if index.toNat < resolvedSpan then a.resolvedCache[choice * resolvedSpan + index.toNat]? else none) with
  | some t => t.get
  | none => a.resolve choice index

/-- Where `path`'s keys start in `allKeys`. -/
def keyOffset (a : MultisigAccount) (path : SpendPath) : Nat :=
  let signers := a.signersLeaves.foldl (· + ·.keys.size) 0
  match path.signersLeaf, path.recoveryLeaf with
  | some leaf, _ => (a.signersLeaves.extract 0 leaf).foldl (· + ·.keys.size) 0
  | none, some leaf => signers + (a.recoveryLeaves.extract 0 leaf).foldl (· + ·.keys.size) 0
  | none, none => 0

/-- `MultisigAccount(descriptor:network:)`: admission (SEC-009, SEC-019, SEC-020). -/
def make (descriptor : Descriptor) (network : BitcoinNetwork) : MAM MultisigAccount := do
  let .trTree internalKey tree := descriptor.expression | invalid "expected tr(NUMS, sortedmulti_a(k, …))"
  let (signersLeaves, recoveryLeaves, leafPaths) ← leavesOf tree
  unless isUnspendable internalKey network do
    invalid "the internal key can spend on its own, which would bypass the signers it lists"
  let keys ← admit signersLeaves network
  let recoveryLeaves ← recoveryOf recoveryLeaves keys network
  let account : MultisigAccount := { descriptor, network, signersLeaves, recoveryLeaves, leafPaths }
  let slots := descriptor.multipathCount * resolvedSpan
  let resolvedCache := (Array.range slots).map fun slot =>
    Thunk.mk fun _ => account.resolve (slot / resolvedSpan) (slot % resolvedSpan).toUInt32
  return { account with resolvedCache }

/-- `MultisigAccount(_ string:network:)`. -/
def parse (string : String) (network : BitcoinNetwork) : MAM MultisigAccount := do
  make (← lift (·.name) (Descriptor.parse string)) network

/-! ### Building descriptors -/

/-- Liana's unspendable internal key: an xpub on H with chain code SHA-256 of the leaf keys' compressed
public keys in descriptor order, depth 0, no origin, the shared `/<0;1>/*` suffix. -/
def unspendableKeyExpression (leafKeys : Array Descriptor.SingleKey) (network : BitcoinNetwork) : MAM String := do
  let mut concatenated := ByteArray.empty
  for key in leafKeys do
    let some (xpub, _) := extendedKey? key
      | invalid "every signer must be an extended public key carrying its origin"
    concatenated := concatenated ++ xpub.publicKey
  let nums : HDKey := { depth := 0, parentFingerprint := 0, childIndex := 0, chainCode := sha256 concatenated,
                        privateKey := none, publicKey := ByteArray.mk #[0x02] ++ Taproot.unspendableInternalKey }
  return nums.serialized (hdNetwork network) ++ "/<0;1>/*"

/-- The x-only account key of a key expression. -/
def accountKeyIn (expression : String) : MAM ByteArray := do
  let some single := (match Descriptor.parse s!"tr({expression})" with
    | .ok d => match d.expression with | .tr k => some k | _ => none
    | .error _ => none) | invalid "a signer key expression does not parse"
  let some (xpub, _) := extendedKey? single | invalid "a signer key expression does not parse"
  return xpub.publicKey.extract 1 xpub.publicKey.size

/-- Key expressions sorted by their x-only account key, ascending (stable among equal keys). -/
def canonicalOrder (expressions : Array String) : MAM (Array String) := do
  let keyed ← expressions.mapM fun expression => return (← accountKeyIn expression, expression)
  return (keyed.toList.mergeSort (fun a b => !lexPrecedes b.1 a.1)).toArray.map (·.2)

/-- `and_v(v:pk(K),older(N))` for one key, `and_v(v:multi_a(m,…),older(N))` for several, the keys
already on their paths. -/
def timelockedLeaf (threshold : Int) (keys : Array String) (blocks : UInt32) : MAM String := do
  unless 1 ≤ blocks && blocks ≤ maximumRecoveryBlocks do invalid "a recovery delay must be 1 to 65535 blocks"
  unless 1 ≤ threshold && threshold ≤ keys.size do
    invalid "the recovery threshold must be between one and its number of keys"
  if keys.size == 1 then return s!"and_v(v:pk({keys[0]!}),older({blocks}))"
  return s!"and_v(v:multi_a({threshold},{",".intercalate keys.toList}),older({blocks}))"

/-- The recovery leaf's text; reused signers move to their `/<2;3>/*` path. -/
def recoveryLeafText (plan : RecoveryPlan) (signers : Array String) : MAM String := do
  match plan with
  | .fewerSigners m n =>
    let suffix := "/<0;1>/*"
    unless signers.all (·.endsWith suffix) do
      invalid "every signer must use the /<0;1>/* suffix, so the signers can be shown to be independent"
    timelockedLeaf m (signers.map fun s => String.ofList (s.toList.take (s.length - suffix.length)) ++ "/<2;3>/*") n
  | .separateKeys m others n => timelockedLeaf m (← canonicalOrder others) n

/-- `{{a,b},{c,d}}`: leaves paired from the left, halving at each level (`fuel` bounds the depth; the
length of the list is always enough). -/
def nest : (fuel : Nat) → List String → String
  | 0, leaves => leaves.headD ""
  | fuel + 1, leaves =>
    if leaves.length ≤ 1 then leaves.headD ""
    else
      let half := (leaves.length + 1) / 2
      "{" ++ nest fuel (leaves.take half) ++ "," ++ nest fuel (leaves.drop half) ++ "}"

/-- The descriptor over leaves already in their final text and order: a balanced tree of them under the
NUMS extended key, validated. A failure that is not this module's own is an unparsable signer expression. -/
def build (leaves : Array String) (network : BitcoinNetwork) : MAM Descriptor := do
  let tree := nest leaves.size leaves.toList
  let notParsed : MultisigFailure := .account (.invalidDescriptor "a signer key expression does not parse")
  let draft ← (Descriptor.parse s!"tr({hex Taproot.unspendableInternalKey},{tree})").mapError fun _ => notParsed
  let internalKey ← unspendableKeyExpression (draft.allKeys.extract 1 draft.allKeys.size) network
  let descriptor ← (Descriptor.parse s!"tr({internalKey},{tree})").mapError fun _ => notParsed
  discard (make descriptor network)
  return descriptor

/-- `descriptor(threshold:signers:recovery:network:)`: the canonical account descriptor
`tr(NUMS-xpub/<0;1>/*, sortedmulti_a(k, …))` over the given signer key expressions (and recovery plan), in
canonical key order, validated as an account for `network`. -/
def makeDescriptor (threshold : Int) (signers : Array String) (recovery : Option RecoveryPlan := none)
    (network : BitcoinNetwork) : MAM Descriptor := do
  let signers ← canonicalOrder signers
  let mut leaves := #[s!"sortedmulti_a({threshold},{",".intercalate signers.toList})"]
  if let some plan := recovery then leaves := leaves.push (← recoveryLeafText plan signers)
  build leaves network

/-- Every way to choose `size` of the values, in order: those with the first value first. -/
def combinations {α} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, n + 1 => (combinations xs n).map (x :: ·) ++ combinations xs (n + 1)

/-- Every way to take one element from each list, first list varying slowest. -/
def product {α} (lists : List (List α)) : List (List α) :=
  lists.foldl (fun acc list => acc.flatMap fun pre => list.map fun x => pre ++ [x]) [[]]

/-- How many `size`-element subsets `n` values have (`combinations(of:size:).count`). -/
def binomial (n size : Nat) : Nat := (List.range size).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- Swift's `Int.max`. -/
def intMax : Nat := 2 ^ 63 - 1

/-- How many leaves every group of `groupSize` members makes when each member in a group has `choices[i]`
ways to sign: the coefficient of x^groupSize in the product of (1 + choices[i]·x), saturating at
`Int.max` as Swift's overflow-reporting arithmetic does. -/
def leafCount (choices : Array Nat) (groupSize : Nat) : Nat := Id.run do
  let mut coefficients : Array Nat := #[1] ++ Array.replicate groupSize 0
  for choice in choices do
    for step in [0:groupSize] do
      let degree := groupSize - step
      coefficients := coefficients.set! degree (min intMax (coefficients[degree]! + coefficients[degree - 1]! * choice))
  return coefficients[groupSize]!

/-- A member with its keys bare of the `/<0;1>/*` suffix, in canonical order. -/
structure OrderedMember where
  keys : Array String
  threshold : Nat
  deriving Inhabited

/-- How many ways its keys can meet its threshold. -/
def OrderedMember.choices (m : OrderedMember) : Nat := binomial m.keys.size m.threshold

/-- At least two members, each with a key and a threshold within its keys; a threshold within the
members. -/
def checkMembers (members : Array Member) (threshold : Int) : MAM Unit := do
  unless members.size ≥ 2 && members.all (!·.keys.isEmpty) do
    invalid "a nested account needs at least two members, each with a key"
  unless members.all (fun m => 1 ≤ m.threshold && m.threshold ≤ m.keys.size) do
    invalid "a member's threshold must be between one and its number of keys"
  unless 1 ≤ threshold && threshold ≤ members.size do
    invalid "the threshold must be between one and the number of members"

/-- Members with their keys in canonical order and bare of the suffix, ordered by their lowest key. -/
def orderedMembers (members : Array Member) : MAM (Array OrderedMember) := do
  let suffix := pairSuffixText 0
  let keyed ← members.mapM fun member => do
    let sorted ← canonicalOrder member.keys
    let bare ← sorted.mapM fun expression => do
      unless expression.endsWith suffix do
        invalid "every signer must use the /<0;1>/* suffix, so the signers can be shown to be independent"
      pure (String.ofList (expression.toList.take (expression.length - suffix.length)))
    return (← accountKeyIn sorted[0]!, ({ keys := bare, threshold := member.threshold.toNat } : OrderedMember))
  let ordered := (keyed.toList.mergeSort (fun a b => !lexPrecedes b.1 a.1)).toArray.map (·.2)
  let all := ordered.flatMap (·.keys)
  let distinct := all.foldl (fun acc k => if acc.contains k then acc else acc.push k) #[]
  unless distinct.size == all.size do invalid "the same signing key appears in two members"
  return ordered

/-- Refuses a tree of more than `maximumLeaves` leaves before any is written, naming the count. -/
def checkLeafCount (members : Array OrderedMember) (threshold : Nat) (recovery : Option RecoveryPlan) : MAM Unit := do
  let choices := members.map (·.choices)
  let count := leafCount choices threshold + match recovery with
    | none => 0
    | some (.separateKeys ..) => 1
    | some (.fewerSigners m _) => leafCount choices (min m.toNat members.size)
  unless count ≤ maximumLeaves do
    invalid s!"these members would make {count} leaves, and an account has at most {maximumLeaves}"

/-- The x-only account key of a bare key expression, for sorting; already parsed by `orderedMembers`. -/
def bareKey (expression : String) : ByteArray := (accountKeyIn expression).toOption.getD .empty

/-- The key lists of one leaf per group of `groupSize` members and per way the group's members meet their
thresholds, in canonical order, each key on the pair its appearance so far calls for. `appearances` (by
bare key text) carries across the signers' and recovery leaves. -/
def leafKeys (members : Array OrderedMember) (groupSize : Nat) (appearances : Array (String × Nat)) :
    Array (Array String) × Array (String × Nat) := Id.run do
  let mut appearances := appearances
  let mut leaves : Array (Array String) := #[]
  for group in combinations (List.range members.size) groupSize do
    let choices := group.map fun member =>
      let m := members[member]!
      (combinations (List.range m.keys.size) m.threshold).map (·.map (m.keys[·]!))
    for choice in product choices do
      let keys := sortBytes bareKey choice.flatten.toArray
      let mut leaf : Array String := #[]
      for key in keys do
        let seen := ((appearances.find? (·.1 == key)).map (·.2)).getD 0
        leaf := leaf.push (key ++ pairSuffixText seen)
        appearances := match appearances.findIdx? (·.1 == key) with
          | some j => appearances.set! j (key, seen + 1)
          | none => appearances.push (key, seen + 1)
      leaves := leaves.push leaf
  return (leaves, appearances)

/-- `descriptor(members:threshold:recovery:network:)`: a nested account, `threshold` of `members` spend.
One leaf per group of `threshold` members and per way the members of the group meet their own
thresholds, each needing every key it lists; a key in several leaves takes `/<2;3>/*`, `/<4;5>/*`… in
turn, in tree order. Members are written in one canonical order, by their lowest key. When every member
is one key, this is the ordinary account. A recovery path of fewer members is a timelocked leaf per group
of them; separate keys are one leaf. At most `maximumLeaves` leaves. Swift's overload over `[[String]]`
is this over `members.map Member.all`. -/
def makeNestedDescriptor (members : Array Member) (threshold : Int) (recovery : Option RecoveryPlan := none)
    (network : BitcoinNetwork) : MAM Descriptor := do
  checkMembers members threshold
  if members.all (·.keys.size == 1) then
    return ← makeDescriptor threshold (members.map (·.keys[0]!)) recovery network
  unless threshold > 1 || members.all (·.threshold > 1) do
    invalid "a threshold of one member would let a single key spend alone; give every member two keys that sign, or raise it"
  let ordered ← orderedMembers members
  checkLeafCount ordered threshold.toNat recovery
  let (signersKeys, appearances) := leafKeys ordered threshold.toNat #[]
  let mut leaves := signersKeys.map fun keys => s!"sortedmulti_a({keys.size},{",".intercalate keys.toList})"
  match recovery with
  | none => pure ()
  | some (.separateKeys m keys blocks) =>
    leaves := leaves.push (← recoveryLeafText (.separateKeys m (← canonicalOrder keys) blocks) #[])
  | some (.fewerSigners m blocks) =>
    unless 1 ≤ m && m ≤ members.size do
      invalid "the recovery threshold must be between one and the number of members"
    for keys in (leafKeys ordered m.toNat appearances).1 do
      leaves := leaves.push (← timelockedLeaf keys.size keys blocks)
  build leaves network

/-! ### Reading members back -/

/-- Leaves as sets of key identities, for reading members back. -/
structure LeafFamily where
  /-- Key identities in first-appearance order, each with its first key. -/
  order : Array ByteArray
  key : Array (ByteArray × Descriptor.SingleKey)
  leaves : Array (Array ByteArray)
  family : Array (Array ByteArray)
  deriving Inhabited

namespace LeafFamily

def ofLeaves (lists : Array (Array Descriptor.SingleKey)) : LeafFamily := Id.run do
  let mut f : LeafFamily := { order := #[], key := #[], leaves := #[], family := #[] }
  for keys in lists do
    let mut leaf : Array ByteArray := #[]
    for single in keys do
      let id := identity single
      unless f.order.contains id do
        f := { f with order := f.order.push id, key := f.key.push (id, single) }
      leaf := leaf.push id
    let set := asSet leaf
    f := { f with leaves := f.leaves.push set, family := if f.family.contains set then f.family else f.family.push set }
  return f

def keyOf (f : LeafFamily) (id : ByteArray) : Descriptor.SingleKey := ((f.key.find? (·.1 == id)).map (·.2)).getD default

/-- Whether swapping `first` and `second` maps every leaf onto a leaf. -/
def isSymmetric (f : LeafFamily) (first second : ByteArray) : Bool :=
  f.leaves.all fun leaf =>
    if leaf.contains first == leaf.contains second then true
    else
      let swapped := (leaf.filter fun k => k != first && k != second).push (if leaf.contains first then second else first)
      f.family.contains (asSet swapped)

/-- The keys partitioned by symmetry, in first-appearance order. -/
def symmetryClasses (f : LeafFamily) : Array (Array ByteArray) := Id.run do
  let mut classes : Array (Array ByteArray) := #[]
  for id in f.order do
    match classes.findIdx? (fun c => f.isSymmetric c[0]! id) with
    | some j => classes := classes.modify j (·.push id)
    | none => classes := classes.push #[id]
  return classes

/-- How a symmetry class reads: the threshold of one member made of its keys, or `none` to read each key
as a member of its own. -/
def memberThreshold (f : LeafFamily) (keys : Array ByteArray) : Option Nat := do
  let present := (f.leaves.map fun leaf => (leaf.filter keys.contains).size).filter (· > 0)
  let counts := present.foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]
  guard (counts.size == 1)
  let threshold := counts[0]!
  let everywhere := present.size == f.leaves.size
  if (threshold == keys.size && everywhere) || keys.size == f.order.size then none else some threshold

/-- The number of members in every leaf, when it is the same for all. -/
def groupSize (f : LeafFamily) (groups : Array (Array ByteArray)) : Option Nat :=
  let sizes := f.leaves.map fun leaf => (groups.filter fun g => g.any leaf.contains).size
  let distinct := sizes.foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]
  if distinct.size == 1 then some distinct[0]! else none

/-- Whether the leaves are exactly every group of `size` members, each member in every way it meets
`thresholds[i]` of its keys. -/
def matchesGroups (f : LeafFamily) (groups : Array (Array ByteArray)) (thresholds : Array Nat) (size : Nat) : Bool := Id.run do
  let mut expected : Array (Array ByteArray) := #[]
  for group in combinations (List.range groups.size) size do
    let choices := group.map fun member =>
      (combinations (List.range groups[member]!.size) thresholds[member]!).map (·.map (groups[member]![·]!))
    for pick in product choices do
      let set := asSet pick.flatten.toArray
      unless expected.contains set do expected := expected.push set
  return expected.size == f.family.size && expected.all f.family.contains && expected.size == f.leaves.size

end LeafFamily

/-- Members read from leaves that each need every key they list: keys the leaves cannot tell apart belong
to one member, whose threshold is how many of them each leaf holds; keys symmetric only because each is a
member of its own stay single members. The leaves must then be exactly every group of `threshold`
members, each member in every way it meets its own threshold; `none` otherwise. -/
def membersOf (leaves : Array (Int × Array Descriptor.SingleKey)) : Option Members := do
  guard (leaves.all fun (t, ks) => t == ks.size)
  let family := LeafFamily.ofLeaves (leaves.map (·.2))
  let mut groups : Array (Array ByteArray) := #[]
  let mut thresholds : Array Nat := #[]
  for keys in family.symmetryClasses do
    match family.memberThreshold keys with
    | some t =>
      groups := groups.push keys
      thresholds := thresholds.push t
    | none =>
      groups := groups ++ keys.map (#[·])
      thresholds := thresholds ++ keys.map fun _ => 1
  if family.groupSize groups == some 1 then
    -- Any one member spends: a member of which one key signs is the same leaves as that many one-key
    -- members, so read it as them.
    let split := (Array.range groups.size).flatMap fun i =>
      if thresholds[i]! == 1 then groups[i]!.map (#[·]) else #[groups[i]!]
    thresholds := split.map fun g => match groups.findIdx? (· == g) with | some j => thresholds[j]! | none => 1
    groups := split
  let some threshold := family.groupSize groups | none
  guard (family.matchesGroups groups thresholds threshold)
  return { threshold, groups := groups.map (·.map family.keyOf), thresholds }

/-- The members of a nested account, read from its signers' leaves; `none` for an ordinary account or a
tree of another shape. -/
def members (a : MultisigAccount) : Option Members :=
  if a.isNested then membersOf (a.signersLeaves.map fun l => (l.threshold, l.keys)) else none

/-- The members a recovery path of fewer members reads back as, when the account has a timelocked leaf per
group of them; `none` for one leaf. -/
def recoveryMembers (a : MultisigAccount) : Option Members :=
  if a.recoveryLeaves.size > 1 then membersOf (a.recoveryLeaves.map fun l => (l.threshold, l.keys)) else none

/-- ", one of them 2 of 3"; ", two of them 2 of 3, one 1 of 2"; "" when every member signs with all its
keys. -/
def thresholdMembersText (members : Members) : String := Id.run do
  let mut counts : Array (String × Nat) := #[]
  for group in members.thresholdGroups do
    let policy := s!"{members.thresholds[group]!} of {members.groups[group]!.size}"
    match counts.findIdx? (·.1 == policy) with
    | some j => counts := counts.modify j fun (p, c) => (p, c + 1)
    | none => counts := counts.push (policy, 1)
  let words := #["none", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"]
  return String.join (counts.toList.zipIdx.map fun ((policy, count), position) =>
    let word := words[count]?.getD (toString count)
    s!", {word}{if position == 0 then " of them" else ""} {policy}")

/-- "2 of 3" for an ordinary account, "2 of 3 members" for a nested one whose leaves read as members,
"2 of 3 members, one of them 2 of 3" when a member is a threshold over its keys, else how many ways it can
spend. -/
def policySummary (a : MultisigAccount) : String :=
  if !a.isNested then s!"{a.threshold} of {a.signers.size}"
  else match a.members with
    | none => s!"{a.signersLeaves.size} signing groups"
    | some m => s!"{m.threshold} of {m.groups.size} members" ++ thresholdMembersText m

/-- The account's stable identifier: the descriptor's BIP380 checksum. -/
def id (a : MultisigAccount) : String :=
  let s := a.descriptor.serialized
  String.ofList (s.toList.drop (s.length - 8))

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

/-- The signers' key expressions as the builders take them, each on the `/<0;1>/*` suffix whatever path
its leaf gave it: what the app pastes to make a whole account one member of another. -/
def signerExpressions (a : MultisigAccount) : Array String :=
  a.signers.map fun s => Descriptor.serializeSingle { s with derivation := { elements := signerSuffix } }

/-- The keys of `path`'s leaf, in descriptor order; none for a leaf the account does not have. -/
def keysOn (a : MultisigAccount) (path : SpendPath) : Array Descriptor.SingleKey :=
  match path.signersLeaf, path.recoveryLeaf with
  | some leaf, _ => (a.signersLeaves[leaf]?.map (·.keys)).getD #[]
  | none, some leaf => (a.recoveryLeaves[leaf]?.map (·.keys)).getD #[]
  | none, none => #[]

/-- How many of `path`'s keys must sign. -/
def thresholdOn (a : MultisigAccount) (path : SpendPath) : Int :=
  match path.signersLeaf, path.recoveryLeaf with
  | some leaf, _ => (a.signersLeaves[leaf]?.map (·.threshold)).getD 0
  | none, some leaf => (a.recoveryLeaves[leaf]?.map (·.threshold)).getD 0
  | none, none => 0

/-- Whether one key of the account is this account public key, whatever origin label it carries. -/
def includes (a : MultisigAccount) (accountKey : HDKey) : Bool :=
  a.allKeys.any fun k => match extendedKey? k with
    | some (base, _) => base.publicKey == accountKey.publicKey
    | none => false

/-- The signer's account key with its private half, when `key` is that account key itself or the master its
origin descends from; `none` otherwise. -/
def accountSecretKey (single : Descriptor.SingleKey) (key : HDKey) : MAM (Option HDKey) := do
  let some (base, _) := extendedKey? single | return none
  if key.privateKey.isNone then return none
  if key.publicKey == base.publicKey && key.chainCode == base.chainCode then return some key
  let some origin := single.origin | return none
  if origin.fingerprint != key.fingerprint then return none
  let derived ← lift (·.name) (key.derivedPath origin.path)
  unless derived.publicKey == base.publicKey && derived.chainCode == base.chainCode do return none
  return some derived

/-- Whether `key` (a master or BIP86 account key) holds one of the account's keys. -/
def hasSigner (a : MultisigAccount) (key : HDKey) : Bool :=
  a.allKeys.any fun k => match accountSecretKey k key with | .ok (some _) => true | _ => false

/-! ### Watching -/

def derivedOutput (a : MultisigAccount) (index : UInt32) (choice : Nat) : MAM Descriptor.DerivedOutput :=
  return (← a.resolved choice index).output

/-- scriptPubKey at (multipath choice, index): choice 0 receive, 1 change. -/
def scriptPubKey (a : MultisigAccount) (index : UInt32) (choice : Nat := 0) : MAM ByteArray :=
  return (← a.derivedOutput index choice).scriptPubKey

def address (a : MultisigAccount) (index : UInt32) (choice : Nat := 0) : MAM String :=
  return (← a.derivedOutput index choice).address

/-- Both multipath choices for indices `0 ..< count`. -/
def watchScripts (a : MultisigAccount) (count : UInt32) : MAM (Array ByteArray) := do
  let mut scripts := #[]
  for index in [0:count.toNat] do
    for choice in [0:a.descriptor.multipathCount] do
      scripts := scripts.push (← a.derivedOutput index.toUInt32 choice).scriptPubKey
  return scripts

def Leaf.isRecovery (l : Leaf) : Bool := l.path.isRecovery
def Leaf.hash (l : Leaf) : ByteArray := Taproot.leafHash l.version l.script

/-- Every leaf at (choice, index) in tree order, with its control block. -/
def leaves (a : MultisigAccount) (choice : Nat) (index : UInt32) : MAM (Array Leaf) :=
  return (← a.resolved choice index).leaves

/-- The first signers' leaf at (choice, index). -/
def signersLeaf (a : MultisigAccount) (choice : Nat) (index : UInt32) : MAM Leaf := do
  let some l := (← a.leaves choice index).find? (·.path == .signers) | invalid "the account's tree does not resolve to its leaves"
  return l

/-- Whether `coin` may already be spent on the recovery path in the next block. -/
def isUnlockedForRecovery (a : MultisigAccount) (coin : WalletUTXO) (chainTip : UInt32) : Bool :=
  match a.recovery with
  | some r => coin.height > 0 && chainTip ≥ coin.height && chainTip.toNat - coin.height.toNat + 1 ≥ r.blocks.toNat
  | none => false

/-- The first block in which `coin` can be spent on the recovery path; `none` when unconfirmed or past
`UInt32.max`. -/
def recoveryUnlockHeight (a : MultisigAccount) (coin : WalletUTXO) : Option UInt32 := do
  let r ← a.recovery
  guard (coin.height > 0)
  let unlock := coin.height.toNat + r.blocks.toNat
  guard (unlock < 2 ^ 32)
  return unlock.toUInt32

/-! ### Review -/

def inputTxid? (i : PSBT.Input) : Option (ByteArray × UInt32) := do
  let txid ← i.previousTxid
  guard (txid.size == 32)
  return (txid, ← i.outputIndex)

/-- The recovery path when every input's sequence meets the recovery leaf's lock, otherwise the signers'
path. The signers' leaves have no lock, so they can finish either. -/
def spendPath (a : MultisigAccount) (psbt : PSBT) : MAM SpendPath := do
  let some r := a.recovery | return .signers
  let tx ← lift (·.name) psbt.unsignedTransaction
  return if tx.inputs.all (fun i => RelativeLock.isSatisfied r.blocks i.sequence tx.version) then .recovery else .signers

/-- At most 10% of the inputs may go to the miner. -/
def checkFeeCeiling (fee inputTotal : Int64) : MAM Unit := do
  unless fee ≤ inputTotal / 10 do
    refuse s!"the {fee.toInt}-sat fee exceeds the 10% safety limit for these inputs"

def leafKey (l : PSBT.TapLeafScript) : ByteArray := l.controlBlock.serialized ++ l.script

def sameLeaves (xs ys : Array PSBT.TapLeafScript) : Bool :=
  xs.size == ys.size && (xs.zip ys).all fun (x, y) =>
    x.controlBlock == y.controlBlock && x.script == y.script && x.leafVersion == y.leafVersion

def checkInput (a : MultisigAccount) (input : PSBT.Input) (inputIndex : Nat) (known : WalletUTXO) (chainTip : UInt32) :
    MAM Unit := do
  let n := inputIndex + 1
  let claimedOK := match input.witnessUTXO with
    | some c => c.amount == known.amount && c.scriptPubKey == known.scriptPubKey
    | none => false
  unless known.amount > 0 && known.amount.toInt ≤ maxMoney && claimedOK do
    refuse s!"input {n} has the wrong amount or locking script"
  if known.isCoinbase then
    let matureAt := known.height.toNat + Wallet.coinbaseMaturity.toNat - 1
    unless chainTip.toNat ≥ matureAt do
      refuse s!"input {n} spends a coinbase that matures in {matureAt - chainTip.toNat} blocks"
  unless (← a.scriptPubKey known.index known.chain.rawValue) == known.scriptPubKey do
    refuse s!"input {n} does not belong to this descriptor"
  let rawSighash := input.sighashType.getD 0
  unless rawSighash == 0 || rawSighash == 1 do refuse s!"input {n} does not commit to every output"
  let expected ← a.leaves known.chain.rawValue known.index
  let expectedLeaves : Array PSBT.TapLeafScript :=
    expected.map fun l => { controlBlock := l.controlBlock, script := l.script, leafVersion := l.version }
  let attached := sortBytes leafKey input.tapLeafScripts
  unless input.tapInternalKey == (expected[0]?.map (·.internalKey)) &&
      sameLeaves attached (sortBytes leafKey expectedLeaves) do
    refuse s!"input {n} changes the spending policy"

def reviewedInputTotal (a : MultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO) (chainTip : UInt32)
    (path : SpendPath) : MAM Int64 := do
  let mut seen : Array Transaction.Outpoint := #[]
  let mut total : Int := 0
  for h : k in [0:psbt.inputs.size] do
    let input := psbt.inputs[k]
    let some (txid, vout) := inputTxid? input | refuse s!"input {k + 1} has no complete outpoint"
    let outpoint : Transaction.Outpoint := ⟨txid, vout⟩
    if seen.contains outpoint then refuse s!"input {k + 1} repeats an earlier outpoint"
    seen := seen.push outpoint
    let some known := knownUTXOs.find? (·.outpoint == outpoint)
      | refuse s!"input {k + 1} is not an available coin of this account"
    a.checkInput input k known chainTip
    if path.isRecovery && !a.isUnlockedForRecovery known chainTip then
      let unlock := match a.recoveryUnlockHeight known with
        | some h => s!"at block {h}"
        | none => if known.height > 0 then "past the last block height" else "once it confirms"
      refuse s!"input {k + 1} unlocks for recovery only {unlock}"
    let sum := total + known.amount.toInt
    unless sum ≤ maxMoney do refuse "input amounts exceed Bitcoin's supply"
    total := sum
  return Int64.ofInt total

def reviewedOutputs (a : MultisigAccount) (psbt : PSBT) (inputTotal : Int64) (owned : Array OutputCoordinate) :
    MAM (Array SpendReview.Output × Int64) := do
  let mut candidates : Array OutputCoordinate := #[]
  for c in owned do
    if (c.choice == 0 || c.choice == 1) && !candidates.contains c then candidates := candidates.push c
  unless candidates.size ≤ 1_024 do refuse "too many candidate account output paths"
  let ownedScripts ← candidates.mapM fun c => a.scriptPubKey c.index c.choice.toNat
  let mut total : Int := 0
  let mut reviewed : Array SpendReview.Output := #[]
  for h : k in [0:psbt.outputs.size] do
    let output := psbt.outputs[k]
    let some amount := output.amount | refuse s!"output {k + 1} has an invalid amount or script"
    let some script := output.script | refuse s!"output {k + 1} has an invalid amount or script"
    unless amount > 0 && amount.toInt ≤ maxMoney && !script.isEmpty do
      refuse s!"output {k + 1} has an invalid amount or script"
    let sum := total + amount.toInt
    unless sum ≤ maxMoney do refuse "output amounts exceed Bitcoin's supply"
    total := sum
    reviewed := reviewed.push { amount, scriptPubKey := script, isAccountOwned := ownedScripts.contains script }
  unless total ≤ inputTotal.toInt do refuse "outputs exceed its known inputs"
  return (reviewed, Int64.ofInt total)

/-- Validates a PSBT before it is shown, signed, finalized or broadcast (SEC-004): every input a unique
known coin of this account with the exact amount, script, leaves and internal key; every signature
committing to all outputs; valid amounts; a fee of at most 10%. Output ownership comes only from the
caller's coordinates. -/
def reviewSpend (a : MultisigAccount) (psbt : PSBT) (knownUTXOs : Array WalletUTXO)
    (ownedOutputCoordinates : Array OutputCoordinate) (chainTip : UInt32) : MAM SpendReview := do
  if psbt.inputs.isEmpty then refuse "it has no inputs"
  unless !psbt.outputs.isEmpty && psbt.outputs.size ≤ 1_000 do refuse "it has no outputs or more than 1,000"
  unless psbt.txVersion == 1 || psbt.txVersion == 2 do
    refuse s!"transaction version {psbt.txVersion.toInt} is not supported"
  let path ← a.spendPath psbt
  let inputTotal ← a.reviewedInputTotal psbt knownUTXOs chainTip path
  let (outputs, outputTotal) ← a.reviewedOutputs psbt inputTotal ownedOutputCoordinates
  let fee := inputTotal - outputTotal
  checkFeeCeiling fee inputTotal
  return { outputs, inputTotal, outputTotal, fee, path }

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
