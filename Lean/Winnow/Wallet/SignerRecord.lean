import Winnow.Wallet.MultisigAccount

/-! # The signers a phone knows (port of `Sources/WalletCore/Wallet/SignerRecord.swift`, upstream d2ca878)

A signer as the app keeps it under Settings → Signers and as a backup carries it: a Ledger the phone
paired, or keys other people sent. Public keys only, so the list is not a wallet's: it survives deleting
one, and a restore merges it with the phone's own. One list per network.

Coded as Swift's synthesized `Codable` under `JSONEncoder()`'s default strategies: `kind` as its raw
string, `masterFingerprint` omitted when absent, and `addedAt` a `Date` as `.deferredToDate` writes it, a
JSON number of seconds since 2001-01-01 00:00 UTC (`timeIntervalSinceReferenceDate`), in Swift's `Double`
form (`SwiftDouble.jsonText`). -/

namespace Winnow
open SwiftJSON

inductive SignerRecord.Kind where
  /-- A Ledger paired over Bluetooth: its one key, at its BIP87 path. -/
  | ledger
  /-- Keys someone sent: one, or a few that always sign together, such as a phone's with its Ledger's. -/
  | keys
  deriving Inhabited, BEq, Repr

structure SignerRecord where
  /-- Opaque; a UUID string. -/
  id : String
  kind : SignerRecord.Kind
  name : String
  /-- `[fp/path]xpub…/<0;1>/*`, one or more. -/
  keys : Array String
  /-- The Ledger's master fingerprint; `none` for saved keys. -/
  masterFingerprint : Option UInt32 := none
  /-- `Date`: seconds since 2001-01-01 00:00 UTC. -/
  addedAt : Float
  deriving Inhabited, BEq

namespace SignerRecord

/-- A phone keeps at most this many signers. -/
def maximumSigners : Nat := 100
/-- A whole account's keys as one signer, at most. -/
def maximumKeysPerSigner : Nat := 10

/-- Seconds between 1970-01-01 and 2001-01-01, for `Date(timeIntervalSince1970:)`. -/
def unixEpochOffset : Float := 978_307_200

def isLedger (r : SignerRecord) : Bool := r.kind == .ledger

def Kind.rawValue : Kind → String | .ledger => "ledger" | .keys => "keys"

def Kind.ofJV (v : JV) : D Kind := do
  match ← asString v with
  | "ledger" => return .ledger
  | "keys" => return .keys
  | _ => dataCorrupted

def toJV (r : SignerRecord) : JV :=
  obj [("id", some (.str r.id)), ("kind", some (.str r.kind.rawValue)), ("name", some (.str r.name)),
    ("keys", some (.arr (r.keys.map .str))), ("masterFingerprint", r.masterFingerprint.map (ofInt ·.toNat)),
    ("addedAt", some (ofDouble r.addedAt))]

/-- The synthesized decoder, in declaration order. -/
def ofJV (v : JV) : D SignerRecord := do
  let kvs ← asObject v
  let id ← key kvs "id" asString
  let kind ← key kvs "kind" Kind.ofJV
  let name ← key kvs "name" asString
  let keys ← key kvs "keys" (asArray asString)
  let masterFingerprint ← keyIfPresent kvs "masterFingerprint" asUInt32
  let addedAt ← key kvs "addedAt" asDouble
  return { id, kind, name, keys, masterFingerprint, addedAt }

def networkRawValue : Tx.BitcoinNetwork → String
  | .mainnet => "mainnet" | .signet => "signet" | .regtest => "regtest"

/-- `checkShape(_:network:)`: the bounds a backup gets at decode, before anything of it is kept: at most
`maximumSigners` records, each with one to `maximumKeysPerSigner` keys that parse as signers on the
network. The app checks the rest (unique ids, usable names, each key held once, a Ledger's record carrying
its own key) before replacing local state. -/
def checkShape (records : Array SignerRecord) (network : Tx.BitcoinNetwork) : Except WalletError Unit := do
  unless records.size ≤ maximumSigners do
    throw (.invalidBundle s!"bundle declares {records.size} signers, above the {maximumSigners} limit")
  for record in records do
    unless 1 ≤ record.keys.size && record.keys.size ≤ maximumKeysPerSigner do
      throw (.invalidBundle s!"a signer has no keys, or more than {maximumKeysPerSigner}")
    for k in record.keys do
      if (MultisigAccount.signerKey k network).toOption.isNone then
        throw (.invalidBundle s!"a signer key does not parse for {networkRawValue network}")

end SignerRecord
end Winnow
