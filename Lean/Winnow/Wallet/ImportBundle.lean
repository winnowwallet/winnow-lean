import Winnow.Wallet.Types
import Winnow.Wallet.Characters
import Winnow.Wallet.MultisigAccount
import Winnow.Wallet.SignerRecord

/-! # Import bundles (port of `Sources/WalletCore/Wallet/ImportBundle.swift`, data half)

`ImportBundle` (+ `UTXO`, `KnownTransaction`), its bounded decoding, the pretty-printed export form,
`claimedUTXOs`, `excerpt` and `ImportReport.make`. `Wallet.importing` / `verifyImport` live in
`Winnow.Wallet.Wallet`.

Decoding is the synthesized `Decodable` (properties in declaration order, optionals by
`decodeIfPresent`, so a `null` legacy `silentPaymentTweak` reads as absent here, unlike in the wallet
file). Encoding: absent optionals are omitted; `rawTransaction` is base64. -/

namespace Winnow
open SwiftJSON

structure ImportBundle.UTXO where
  txid : String
  vout : UInt32
  amount : Int64
  scriptPubKey : String
  chain : Int
  index : UInt32
  height : UInt32
  silentPaymentTweak : Option String := none
  isCoinbase : Option Bool := none
  deriving Inhabited, BEq

structure ImportBundle.KnownTransaction where
  txid : String
  height : UInt32
  received : Int64
  spent : Int64
  fee : Option Int64 := none
  replacedBy : Option String := none
  rawTransaction : Option ByteArray := none
  outputs : Option HistoryEntry.Outputs := none
  /-- The block the transaction confirmed in (display hex). -/
  blockHash : Option String := none
  deriving Inhabited, BEq

structure ImportBundle where
  version : Int := 2
  network : String
  descriptor : Option String := none
  mnemonic : Option String := none
  lastKnownHeight : UInt32
  /-- The hash of block `lastKnownHeight` (display hex). -/
  lastKnownBlockHash : Option String := none
  utxos : Array ImportBundle.UTXO := #[]
  transactions : Array ImportBundle.KnownTransaction := #[]
  /-- Multisig accounts, under the key the shared-account Winnow used for all its accounts. Script-path
  k-of-n accounts restore; a bundle carrying any other kind (a MuSig2 one) is refused (`decodeData`). -/
  vaults : Option (Array MultisigAccountRecord) := none
  /-- The signers the phone knows (`SignerRecord`): paired Ledgers and keys other people sent, so a restored
  phone builds its next account from the same list. Public keys only. Old files omit it; the app merges it
  with the phone's own on restore rather than replacing that. -/
  signers : Option (Array SignerRecord) := none
  /-- The wallet's payments no block has taken yet, with the coins they spend: a restore keeps those coins
  reserved and announces the payments again, instead of forgetting a payment that was never confirmed. -/
  pendingSends : Array PendingSend := #[]
  nextReceiveIndex : Option UInt32 := none
  nextChangeIndex : Option UInt32 := none
  deriving Inhabited, BEq

namespace ImportBundle

def currentVersion : Int := 2
def supportedVersions (v : Int) : Bool := 1 ≤ v && v ≤ currentVersion
def maximumSerializedBytes : Nat := 8 * 1024 * 1024
def maximumEntries : Nat := 50_000
def maximumVaults : Nat := 100

/-- What an error may repeat of bundle-supplied text: at most 64 `Character`s. -/
def excerpt (text : String) : String :=
  if Characters.count text ≤ 64 then text else Characters.prefix text 64 ++ "…"

namespace UTXO
def toJV (u : UTXO) : JV :=
  obj [("txid", some (.str u.txid)), ("vout", some (ofInt u.vout.toNat)), ("amount", some (ofInt u.amount.toInt)),
    ("scriptPubKey", some (.str u.scriptPubKey)), ("chain", some (ofInt u.chain)), ("index", some (ofInt u.index.toNat)),
    ("height", some (ofInt u.height.toNat)), ("silentPaymentTweak", u.silentPaymentTweak.map .str),
    ("isCoinbase", u.isCoinbase.map .bool)]

def ofJV (v : JV) : D UTXO := do
  let kvs ← asObject v
  let txid ← key kvs "txid" asString
  let vout ← key kvs "vout" asUInt32
  let amount ← key kvs "amount" asInt64
  let scriptPubKey ← key kvs "scriptPubKey" asString
  let chain ← key kvs "chain" asInt
  let index ← key kvs "index" asUInt32
  let height ← key kvs "height" asUInt32
  let silentPaymentTweak ← keyIfPresent kvs "silentPaymentTweak" asString
  let isCoinbase ← keyIfPresent kvs "isCoinbase" asBool
  return { txid, vout, amount, scriptPubKey, chain, index, height, silentPaymentTweak, isCoinbase }
end UTXO

namespace KnownTransaction
def toJV (t : KnownTransaction) : JV :=
  obj [("txid", some (.str t.txid)), ("height", some (ofInt t.height.toNat)), ("received", some (ofInt t.received.toInt)),
    ("spent", some (ofInt t.spent.toInt)), ("fee", t.fee.map (ofInt ·.toInt)), ("replacedBy", t.replacedBy.map .str),
    ("rawTransaction", t.rawTransaction.map ofData), ("blockHash", t.blockHash.map .str),
    ("outputs", t.outputs.map HistoryEntry.Outputs.toJV)]

def ofJV (v : JV) : D KnownTransaction := do
  let kvs ← asObject v
  let txid ← key kvs "txid" asString
  let height ← key kvs "height" asUInt32
  let received ← key kvs "received" asInt64
  let spent ← key kvs "spent" asInt64
  let fee ← keyIfPresent kvs "fee" asInt64
  let replacedBy ← keyIfPresent kvs "replacedBy" asString
  let rawTransaction ← keyIfPresent kvs "rawTransaction" asData
  let outputs ← keyIfPresent kvs "outputs" HistoryEntry.Outputs.ofJV
  let blockHash ← keyIfPresent kvs "blockHash" asString
  return { txid, height, received, spent, fee, replacedBy, rawTransaction, outputs, blockHash }
end KnownTransaction

def toJV (b : ImportBundle) : JV :=
  obj [("version", some (ofInt b.version)),
    ("network", some (.str b.network)), ("descriptor", b.descriptor.map .str), ("mnemonic", b.mnemonic.map .str),
    ("lastKnownHeight", some (ofInt b.lastKnownHeight.toNat)), ("lastKnownBlockHash", b.lastKnownBlockHash.map .str),
    ("utxos", some (.arr (b.utxos.map UTXO.toJV))),
    ("transactions", some (.arr (b.transactions.map KnownTransaction.toJV))),
    ("nextReceiveIndex", b.nextReceiveIndex.map (ofInt ·.toNat)), ("nextChangeIndex", b.nextChangeIndex.map (ofInt ·.toNat)), ("vaults", b.vaults.map (.arr ∘ Array.map MultisigAccountRecord.toJV)),
    ("signers", b.signers.map (.arr ∘ Array.map SignerRecord.toJV)),
    ("pendingSends", if b.pendingSends.isEmpty then none else some (.arr (b.pendingSends.map PendingSend.toJV)))]

def ofJV (v : JV) : D ImportBundle := do
  let kvs ← asObject v
  let version ← key kvs "version" asInt
  let network ← key kvs "network" asString
  let descriptor ← keyIfPresent kvs "descriptor" asString
  let mnemonic ← keyIfPresent kvs "mnemonic" asString
  let lastKnownHeight ← key kvs "lastKnownHeight" asUInt32
  let lastKnownBlockHash ← keyIfPresent kvs "lastKnownBlockHash" asString
  let utxos ← key kvs "utxos" (asArray UTXO.ofJV)
  let transactions ← key kvs "transactions" (asArray KnownTransaction.ofJV)
  let vaults ← keyIfPresent kvs "vaults" (asArray MultisigAccountRecord.ofJV)
  let signers ← keyIfPresent kvs "signers" (asArray SignerRecord.ofJV)
  let nextReceiveIndex ← keyIfPresent kvs "nextReceiveIndex" asUInt32
  let nextChangeIndex ← keyIfPresent kvs "nextChangeIndex" asUInt32
  let pendingSends := (← keyIfPresent kvs "pendingSends" (asArray PendingSend.ofJV)).getD #[]
  return { version, network, descriptor, mnemonic, lastKnownHeight, lastKnownBlockHash, utxos, transactions, vaults,
           signers, nextReceiveIndex, nextChangeIndex, pendingSends }

/-- Decoding failures: a `WalletError` (`invalidBundle`, `unsupportedWalletData`, …) or a
`DecodingError` case name. -/
inductive Failure where
  | wallet (e : WalletError)
  | decoding (name : String)
  deriving Inhabited

def Failure.name : Failure → String | .wallet e => e.name | .decoding n => n

/-- `checkAccountsAndSigners(of:)`: the multisig accounts and the signer list, bounded and parsed on the
bundle's network before anything of them is kept. -/
def checkAccountsAndSigners (b : ImportBundle) : Except Failure Unit := do
  let vs := b.vaults.getD #[]
  unless vs.size ≤ maximumVaults && vs.foldl (fun t r => t + r.allUtxos.size) 0 ≤ maximumEntries do
    throw (.wallet (.invalidBundle "too many multisig accounts or account coins"))
  unless vs.foldl (fun t r => t + r.history.size) 0 ≤ maximumEntries &&
      vs.all (fun r => ((r.draft.map (·.psbtBase64.utf8ByteSize)).getD 0) ≤ MultisigSpendDraft.maximumBytes) do
    throw (.wallet (.invalidBundle "too many multisig account transactions, or a draft too large"))
  let network := Tx.BitcoinNetwork.ofString? b.network
  -- MuSig2 accounts from the shared-account Winnow have no home here; their coins must not vanish
  -- from a restore, so a bundle with any account that is not a script-path multisig one is refused.
  unless vs.isEmpty do
    let some network := network | throw (.wallet .unsupportedWalletData)
    unless vs.all (fun r => (MultisigAccount.parse r.descriptor network).toOption.isSome) do
      throw (.wallet .unsupportedWalletData)
  -- A signer list that is not one is refused with the file, never restored in part.
  if let some signers := b.signers then
    unless signers.isEmpty do
      let some network := network | throw (.wallet (.invalidBundle s!"signers for an unknown network {b.network}"))
      (SignerRecord.checkShape signers network).mapError .wallet

/-- `decode(_ data:)`: the byte ceiling first, then the JSON, then the entry ceilings. -/
def decodeData (data : ByteArray) : Except Failure ImportBundle := do
  if data.size > maximumSerializedBytes then
    throw (.wallet (.invalidBundle s!"bundle is {data.size} bytes, above the {maximumSerializedBytes}-byte limit"))
  let some text := String.fromUTF8? data | throw (.decoding "dataCorrupted")
  let b ← (decodeText text ofJV).mapError fun e =>
    if e == "unsupportedWalletData" then .wallet .unsupportedWalletData else .decoding e
  if b.utxos.size > maximumEntries then
    throw (.wallet (.invalidBundle s!"bundle declares {b.utxos.size} coins, above the {maximumEntries} limit"))
  if b.transactions.size > maximumEntries then
    throw (.wallet (.invalidBundle s!"bundle declares {b.transactions.size} transactions, above the {maximumEntries} limit"))
  checkAccountsAndSigners b
  return b

/-- `decode(json:)`. -/
def decode (json : String) : Except Failure ImportBundle := decodeData json.toUTF8

/-- Pretty-printed, sorted-key JSON for the share sheet. -/
def serialized (b : ImportBundle) : String := writePretty "" b.toJV

/-- The v2 writer: display-hex txids, coinbase flag only when set. -/
def «export» (descriptor network : String) (lastKnownHeight : UInt32) (utxos : Array WalletUTXO)
    (history : Array HistoryEntry) (nextReceiveIndex nextChangeIndex : UInt32) (mnemonic : Option String := none)
    (lastKnownBlockHash : Option ByteArray := none) (pendingSends : Array PendingSend := #[]) : ImportBundle :=
  { network, descriptor := some descriptor, mnemonic, lastKnownHeight,
    lastKnownBlockHash := lastKnownBlockHash.map displayHex,
    utxos := utxos.map fun u =>
      { txid := displayHex u.txid, vout := u.vout, amount := u.amount, scriptPubKey := hex u.scriptPubKey,
        chain := u.chain.rawValue, index := u.index, height := u.height,
        isCoinbase := if u.isCoinbase then some true else none },
    transactions := history.map fun e =>
      { txid := displayHex e.txid, height := e.height, received := e.received, spent := e.spent, fee := e.fee,
        replacedBy := e.replacedBy.map displayHex, rawTransaction := e.rawTransaction,
        blockHash := e.blockHash.map displayHex, outputs := e.outputs },
    nextReceiveIndex := some nextReceiveIndex, nextChangeIndex := some nextChangeIndex, pendingSends }

def parsedClaimedUTXO (u : UTXO) : Except WalletError WalletUTXO := do
  let some txid := Wire.dataOfHex? u.txid | throw (.invalidBundle s!"bad txid {excerpt u.txid}")
  unless txid.size == 32 do throw (.invalidBundle s!"bad txid {excerpt u.txid}")
  let some scriptPubKey := Wire.dataOfHex? u.scriptPubKey | throw (.invalidBundle s!"bad scriptPubKey {excerpt u.scriptPubKey}")
  let chain ← match u.chain with
    | 0 => pure AddressChain.receive
    | 1 => pure .change
    | c => throw (.invalidBundle s!"bad chain {c}")
  if u.silentPaymentTweak.isSome then throw .unsupportedWalletData
  return { txid := ByteArray.reverse txid, vout := u.vout, amount := u.amount, scriptPubKey, chain, index := u.index,
           height := u.height, isCoinbase := u.isCoinbase.getD false }

/-- The bundle's claimed UTXOs in wallet form, shape- and range-checked. -/
def claimedUTXOs (b : ImportBundle) : Except WalletError (Array WalletUTXO) := do
  let claimed ← b.utxos.mapM parsedClaimedUTXO
  let mut seen : Std.HashSet (ByteArray × UInt32) := {}
  let mut total : Int := 0
  for c in claimed do
    unless c.amount > 0 && c.amount ≤ bitcoinAmountMaximum do throw (.invalidBundle s!"invalid UTXO amount {c.amount.toInt}")
    if c.scriptPubKey.isEmpty then throw (.invalidBundle "empty UTXO scriptPubKey")
    if seen.contains (c.txid, c.vout) then throw (.invalidBundle "duplicate UTXO outpoint")
    seen := seen.insert (c.txid, c.vout)
    let next := total + c.amount.toInt
    if next > bitcoinAmountMaximum.toInt then throw (.invalidBundle "UTXO total exceeds Bitcoin's monetary range")
    total := next
  return claimed

end ImportBundle

/-! ## Verification report -/

structure ImportReport.SpentClaim where
  txid : ByteArray
  vout : UInt32
  spentBy : ByteArray
  height : UInt32
  deriving Inhabited, BEq

structure ImportReport where
  scannedFromHeight : UInt32
  scannedToHeight : Option UInt32
  confirmedUTXOs : Array WalletUTXO
  spentSinceBundle : Array ImportReport.SpentClaim
  discoveredUTXOs : Array WalletUTXO
  deriving Inhabited, BEq

namespace ImportReport

def matchesBundle (r : ImportReport) : Bool := r.spentSinceBundle.isEmpty

/-- The bundle's claims against the effects of every matched block in the scanned range. -/
def make (bundle : ImportBundle) (effects : Array MatchEffect) (finalUTXOs : Array WalletUTXO)
    (scannedFromHeight : UInt32) (scannedToHeight : Option UInt32) : Except WalletError ImportReport := do
  let claimed ← bundle.claimedUTXOs
  let claimedSet : Std.HashSet (ByteArray × UInt32) := claimed.foldl (fun s c => s.insert (c.txid, c.vout)) {}
  let spentClaims := (effects.flatMap (·.spent)).filterMap fun s =>
    if claimedSet.contains (s.txid, s.vout) then some ({ txid := s.txid, vout := s.vout, spentBy := s.spentBy, height := s.height } : SpentClaim)
    else none
  let spentKeys : Std.HashSet (ByteArray × UInt32) := spentClaims.foldl (fun s c => s.insert (c.txid, c.vout)) {}
  let confirmed := finalUTXOs.filter fun u => claimedSet.contains (u.txid, u.vout) && !spentKeys.contains (u.txid, u.vout)
  let discovered := (effects.flatMap (·.received)).filter fun u => !claimedSet.contains (u.txid, u.vout)
  return { scannedFromHeight, scannedToHeight, confirmedUTXOs := confirmed, spentSinceBundle := spentClaims,
           discoveredUTXOs := discovered }

end ImportReport
end Winnow
