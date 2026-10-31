import Winnow.Wallet.Types
import Winnow.Tx.PSBT

/-! # A multisig account's spends in progress (port of `Sources/WalletCore/Wallet/MultisigSpendRecords.swift`, upstream d2ca878)

`MultisigSpendDraft`: the one spend a phone is collecting signatures for on an account, kept on the
account record so it survives leaving the screen and travels in every backup. `InFlightSpend`: a spend
this phone broadcast that no block has confirmed yet, with the bytes a restored phone needs to announce
it again. Both are coded as Swift's `Codable` (the draft synthesized, optionals omitted; the in-flight
spend with a display-hex txid and base64 bytes, and refused at decode unless the bytes are the
transaction named).

Errors: as `HistoryEntry.checkedTransaction`, a `WalletError` whole (`.inl`) or the other module's error
(`.inr`). -/

namespace Winnow
open SwiftJSON

/-! ## The draft -/

/-- The one spend a phone is collecting signatures for: the PSBT as the screens pass it around and the
phone shares it, and who is being paid, so a person's address index can advance once the spend is
broadcast. Script-path signatures never change the txid, so the draft's is known from the start. -/
structure MultisigSpendDraft where
  /-- BIP174 (v0), base64. -/
  psbtBase64 : String
  personID : Option String := none
  paymentIndex : Option UInt32 := none
  createdAtHeight : UInt32
  deriving Inhabited, BEq

namespace MultisigSpendDraft

/-- A PSBT carrying every leaf and origin of a 32-leaf account is far under this. -/
def maximumBytes : Nat := 1_024 * 1_024

/-- A draft of `psbt`, its text the BIP174 v0 envelope. Upstream #259 writes `psbt.base64`, the v2
envelope, into the draft, and the app shares the draft's text as "PSBT to share"; v0 is what Bitcoin
Core and most other signers read, and what the app shared before #259 (`base64V0`). Fixed here: every draft is written through this (see PORT.md, "Fixed upstream bugs"). -/
def ofPSBT (psbt : PSBT) (createdAtHeight : UInt32) (personID : Option String := none)
    (paymentIndex : Option UInt32 := none) : Except PSBTError MultisigSpendDraft := do
  return { psbtBase64 := ← psbt.base64V0, personID, paymentIndex, createdAtHeight }

/-- `psbt()`: the PSBT, refused past `maximumBytes` of text. -/
def psbt (d : MultisigSpendDraft) : Except (WalletError ⊕ PSBTError) PSBT := do
  unless d.psbtBase64.utf8ByteSize ≤ maximumBytes do throw (.inl (.invalidBundle "a multisig draft is too large"))
  (PSBT.ofBase64 d.psbtBase64).mapError .inr

/-- `txid()`. -/
def txid (d : MultisigSpendDraft) : Except (WalletError ⊕ PSBTError) ByteArray := do
  return (← ((← d.psbt).unsignedTransaction).mapError .inr).txid

/-- `inputs()`: the coins it spends. -/
def inputs (d : MultisigSpendDraft) : Except (WalletError ⊕ PSBTError) (Array Transaction.Outpoint) := do
  return (← ((← d.psbt).unsignedTransaction).mapError .inr).inputs.map (·.previousOutput)

def toJV (d : MultisigSpendDraft) : JV :=
  obj [("psbtBase64", some (.str d.psbtBase64)), ("personID", d.personID.map .str),
    ("paymentIndex", d.paymentIndex.map (ofInt ·.toNat)), ("createdAtHeight", some (ofInt d.createdAtHeight.toNat))]

/-- The synthesized decoder, in declaration order. -/
def ofJV (v : JV) : D MultisigSpendDraft := do
  let kvs ← asObject v
  let psbtBase64 ← key kvs "psbtBase64" asString
  let personID ← keyIfPresent kvs "personID" asString
  let paymentIndex ← keyIfPresent kvs "paymentIndex" asUInt32
  let createdAtHeight ← key kvs "createdAtHeight" asUInt32
  return { psbtBase64, personID, paymentIndex, createdAtHeight }

end MultisigSpendDraft

/-! ## A broadcast spend -/

/-- A spend this phone broadcast that no block has confirmed yet, with the bytes, witness included, a
restored phone needs to announce it again. -/
structure InFlightSpend where
  /-- Internal byte order; display hex in JSON, as a history entry's. -/
  txid : ByteArray
  rawTransaction : ByteArray
  broadcastHeight : UInt32
  deriving Inhabited, BEq

namespace InFlightSpend

/-- A standard transaction weighs at most 400,000 units, and bytes never exceed weight. -/
def maximumBytes : Nat := 400_000

/-- `init(transaction:broadcastHeight:)`. -/
def ofTransaction (tx : Transaction) (broadcastHeight : UInt32) : InFlightSpend :=
  { txid := tx.txid, rawTransaction := tx.serialized true, broadcastHeight }

/-- `transaction()`: the bytes decoded, and refused unless they are the transaction named. -/
def transaction (s : InFlightSpend) : Except (WalletError ⊕ String) Transaction := do
  unless s.rawTransaction.size ≤ maximumBytes do throw (.inl (.invalidBundle "an in-flight multisig spend is too large"))
  let tx ← (Transaction.decode s.rawTransaction).mapError (.inr ·.name)
  unless tx.txid == s.txid do
    throw (.inl (.invalidBundle "an in-flight multisig spend does not match its transaction ID"))
  return tx

def toJV (s : InFlightSpend) : JV :=
  obj [("txid", some (.str (displayHex s.txid))), ("rawTransaction", some (ofData s.rawTransaction)),
    ("broadcastHeight", some (ofInt s.broadcastHeight.toNat))]

/-- The custom decoder: a 32-byte display-hex txid, then the bytes, which must be that transaction. -/
def ofJV (v : JV) : D InFlightSpend := do
  let kvs ← asObject v
  let txid ← hexField kvs "txid"
  unless txid.size == 32 do dataCorrupted
  let rawTransaction ← key kvs "rawTransaction" asData
  let broadcastHeight ← key kvs "broadcastHeight" asUInt32
  let s : InFlightSpend := { txid := ByteArray.reverse txid, rawTransaction, broadcastHeight }
  discard (s.transaction.mapError fun | .inl e => e.name | .inr n => n)
  return s

end InFlightSpend
end Winnow
