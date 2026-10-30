import Winnow.Wallet.Types

/-! # Coin selection

Port of `Sources/WalletCore/Wallet/CoinSelection.swift`: largest-first selection with Bitcoin Core's
dust rule and exact P2TR key-path fee estimation. The candidates are ordered by amount, largest first,
keeping the given order among equal amounts (Swift's sort is stable, as is `List.mergeSort`). -/

namespace Winnow

inductive CoinSelectionError where
  | noUTXOs
  | insufficientFunds (available required : Int64)
  | invalidFeeRate (rate : Float)
  | dustOutput (value threshold : Int64)
  | transactionTooLarge (vsize limit : Int)
  | invalidAmount (amount : Int64)
  | duplicateUTXO
  | invalidOutpoint
  | emptyScript
  | invalidWitnessSize (size : Int)
  | amountOverflow
  deriving Inhabited

namespace CoinSelectionError
def name : CoinSelectionError → String
  | .noUTXOs => "noUTXOs" | .insufficientFunds .. => "insufficientFunds" | .invalidFeeRate _ => "invalidFeeRate"
  | .dustOutput .. => "dustOutput" | .transactionTooLarge .. => "transactionTooLarge" | .invalidAmount _ => "invalidAmount"
  | .duplicateUTXO => "duplicateUTXO" | .invalidOutpoint => "invalidOutpoint" | .emptyScript => "emptyScript"
  | .invalidWitnessSize _ => "invalidWitnessSize" | .amountOverflow => "amountOverflow"

def description : CoinSelectionError → String
  | .noUTXOs => "There are no spendable coins."
  | .insufficientFunds available required =>
    s!"Insufficient funds: {available.toInt} sats are available, but {required.toInt} sats are required."
  | .invalidFeeRate rate => s!"Invalid fee rate: {SwiftDouble.description rate} sat/vB."
  | .dustOutput value threshold => s!"The {value.toInt}-sat payment is below the {threshold.toInt}-sat relay minimum."
  | .transactionTooLarge vsize limit =>
    s!"Spending these coins takes a {vsize}-vbyte transaction, above the {limit}-vbyte relay " ++
      "maximum. Send a smaller amount, or combine coins into fewer, larger ones first."
  | .invalidAmount amount => s!"Invalid Bitcoin amount: {amount.toInt} sats."
  | .duplicateUTXO => "The wallet contains the same coin more than once. Rescan before spending."
  | .invalidOutpoint => "A wallet coin has an invalid transaction ID. Rescan before spending."
  | .emptyScript => "A payment has no Bitcoin locking script."
  | .invalidWitnessSize size => s!"Invalid transaction witness estimate: {size} bytes."
  | .amountOverflow => "The transaction amounts exceed Bitcoin's monetary range."
end CoinSelectionError

/-- Which coins to spend, the fee, and the change (`none`: no change output, remainder in the fee). -/
structure Selection where
  selected : Array WalletUTXO
  fee : Int64
  changeAmount : Option Int64
  deriving Inhabited

namespace CoinSelection

abbrev M := Except CoinSelectionError

/-- Core's default dust relay feerate, sat/kvB. -/
def defaultDustRelayFeeSatPerKvB : Int64 := 3_000

/-- Core's `GetDustThreshold`: 330 sats for P2TR, 294 for P2WPKH at the default rate. (Swift's `Int64`
product traps on overflow; here it is unbounded.) -/
def dustThreshold (scriptPubKey : ByteArray) (relayFeeSatPerKvB : Int64 := defaultDustRelayFeeSatPerKvB) : Int :=
  let n := scriptPubKey.size
  let outputSize := 8 + TransactionBuilder.compactSizeLength n.toUInt64 + n
  let version := scriptPubKey[0]?.getD 0xFF
  let isWitness := n ≥ 4 && (version == 0x00 || (version ≥ 0x51 && version ≤ 0x60)) &&
    n == 2 + (scriptPubKey[1]?.getD 0).toNat && n ≤ 42
  let spendSize := if isWitness then 32 + 4 + 1 + 107 / 4 + 4 else 32 + 4 + 1 + 107 + 4
  (((outputSize + spendSize : Nat) : Int) * relayFeeSatPerKvB.toInt).tdiv 1000

def maxI : Int := bitcoinAmountMaximum.toInt

def checkedAdd (a b : Int) : M Int := do
  let s := a + b
  if s > maxI then throw .amountOverflow
  return s

def checkArguments (utxos : Array WalletUTXO) (changeScriptPubKey : ByteArray) (rate : Float) (witness : Int) : M Unit := do
  if utxos.isEmpty then throw .noUTXOs
  if changeScriptPubKey.isEmpty then throw .emptyScript
  unless 1 ≤ witness && witness ≤ 100_000 do throw (.invalidWitnessSize witness)
  unless rate.isFinite && rate > 0 && rate ≤ 10_000 do throw (.invalidFeeRate rate)

def paymentTarget (payments : Array Payment) : M Int := do
  let mut target : Int := 0
  for p in payments do
    unless p.amount > 0 && p.amount ≤ bitcoinAmountMaximum do throw (.invalidAmount p.amount)
    if p.scriptPubKey.isEmpty then throw .emptyScript
    let threshold := dustThreshold p.scriptPubKey
    unless p.amount.toInt ≥ threshold do throw (.dustOutput p.amount (Int64.ofInt threshold))
    target ← checkedAdd target p.amount.toInt
  return target

def checkSpendableSet (utxos : Array WalletUTXO) : M Unit := do
  let mut seen : Array Transaction.Outpoint := #[]
  for u in utxos do
    if u.txid.size != 32 then throw .invalidOutpoint
    unless u.amount > 0 && u.amount ≤ bitcoinAmountMaximum do throw (.invalidAmount u.amount)
    if u.scriptPubKey.isEmpty then throw .emptyScript
    if seen.contains u.outpoint then throw .duplicateUTXO
    seen := seen.push u.outpoint

/-- The ceiling-rounded fee of a signed transaction of this shape. -/
def fee (inputCount : Nat) (outputs : Array Transaction.Output) (witness : Int) (rate : Float) : M Int := do
  let vsize := TransactionBuilder.signedVSize inputCount outputs witness
  let calculated := (Float.ofInt vsize * rate).ceil
  unless calculated.isFinite && calculated ≤ Float.ofInt maxI do throw .amountOverflow
  return calculated.toUInt64.toNat

def checkStandardSize (inputCount : Nat) (outputs : Array Transaction.Output) (witness : Int) : M Unit := do
  let vsize := TransactionBuilder.signedVSize inputCount outputs witness
  if vsize > TransactionBuilder.maximumStandardVSize then
    throw (.transactionTooLarge vsize TransactionBuilder.maximumStandardVSize)

/-- Largest-first selection (see the Swift original for the full contract). -/
def select (utxos : Array WalletUTXO) (payments : Array Payment) (changeScriptPubKey : ByteArray)
    (feeRateSatPerVByte : Float) (witnessBytesPerInput : Int := 66) : M Selection := do
  let rate := feeRateSatPerVByte
  let w := witnessBytesPerInput
  checkArguments utxos changeScriptPubKey rate w
  let target ← paymentTarget payments
  checkSpendableSet utxos
  let paymentOutputs : Array Transaction.Output := payments.map fun p => { value := p.amount, scriptPubKey := p.scriptPubKey }
  let changeOutput : Transaction.Output := { value := 0, scriptPubKey := changeScriptPubKey }
  let feeFor (count : Nat) (withChange : Bool) : M Int :=
    fee count (if withChange then paymentOutputs.push changeOutput else paymentOutputs) w rate
  let sorted := (utxos.toList.mergeSort fun a b => !(a.amount < b.amount)).toArray
  let mut selected : Array WalletUTXO := #[]
  let mut total : Int := 0
  for u in sorted do
    selected := selected.push u
    let sum := total + u.amount.toInt
    if sum > maxI then throw .amountOverflow
    total := sum
    let required ← checkedAdd target (← feeFor selected.size true)
    if total ≥ required then break
  let feeWithChange ← feeFor selected.size true
  let requiredWithoutChange ← checkedAdd target (← feeFor selected.size false)
  unless total ≥ requiredWithoutChange do
    throw (.insufficientFunds (Int64.ofInt total) (Int64.ofInt requiredWithoutChange))
  let change := total - target - feeWithChange
  let withChange := change ≥ dustThreshold changeScriptPubKey
  checkStandardSize selected.size (if withChange then paymentOutputs.push changeOutput else paymentOutputs) w
  if withChange then
    return { selected, fee := Int64.ofInt feeWithChange, changeAmount := some (Int64.ofInt change) }
  return { selected, fee := Int64.ofInt (total - target), changeAmount := none }

end CoinSelection
end Winnow
