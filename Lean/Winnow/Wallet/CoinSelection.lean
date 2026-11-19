import Winnow.Wallet.Types

/-! # Coin selection

Port of `Sources/WalletCore/Wallet/CoinSelection.swift`: largest-first selection with Bitcoin Core's
dust rule and exact P2TR key-path fee estimation. The candidates are ordered by amount, largest first,
keeping the given order among equal amounts (Swift's sort is stable, as is `List.mergeSort`).

**The fee is whole-number arithmetic.** A rate arrives as sat/vB in a `Float` (what the screens and the
peers' floors are written in) and is turned once, at the door, into a whole number of sat/kvB (`satPerKvB`).
From there a fee is `⌈vsize · rate / 1000⌉` on integers (`feeAt`, Bitcoin Core's `CFeeRate::GetFee` rounded
up), with no `Float` in it, so what `select` returns can be proved to add up
(`Winnow/Proofs/Selection.lean`): the coins selected are exactly the payments, the fee and the change. The
candidates are gone through by a recursion (`take`), and the payments added up by one (`paymentTargetFrom`),
for the same reason. -/

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

/-- What Send says of a payment coin selection refuses (backend-test `refusalsFlow`: no coins, dust, more than
the wallet holds). -/
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

/-- One payment checked: an amount in Bitcoin's range, a script, and not dust. -/
def checkPayment (p : Payment) : M Unit := do
  unless p.amount > 0 && p.amount ≤ bitcoinAmountMaximum do throw (.invalidAmount p.amount)
  if p.scriptPubKey.isEmpty then throw .emptyScript
  let threshold := dustThreshold p.scriptPubKey
  unless p.amount.toInt ≥ threshold do throw (.dustOutput p.amount (Int64.ofInt threshold))

/-- The payments' amounts added to `target`, each payment checked on the way. -/
def paymentTargetFrom : List Payment → Int → M Int
  | [], target => pure target
  | p :: rest, target => do
    checkPayment p
    paymentTargetFrom rest (← checkedAdd target p.amount.toInt)

/-- What the payments come to. -/
def paymentTarget (payments : Array Payment) : M Int := paymentTargetFrom payments.toList 0

def checkSpendableSet (utxos : Array WalletUTXO) : M Unit := do
  let mut seen : Array Transaction.Outpoint := #[]
  for u in utxos do
    if u.txid.size != 32 then throw .invalidOutpoint
    unless u.amount > 0 && u.amount ≤ bitcoinAmountMaximum do throw (.invalidAmount u.amount)
    if u.scriptPubKey.isEmpty then throw .emptyScript
    if seen.contains u.outpoint then throw .duplicateUTXO
    seen := seen.push u.outpoint

/-- A rate in sat/vB as a whole number of sat/kvB: the one place a `Float` is read. A rate that is a whole
number of thousandths of a sat/vB (what the screens enter, and Bitcoin Core's own unit) is that number; any
other is rounded up to the next, so a fee is never under the rate asked for. For a rate `checkArguments` has
passed (finite, above 0, at most 10,000). -/
def satPerKvB (rate : Float) : Nat :=
  let scaled := rate * 1000
  let nearest := scaled.round
  -- a product such as 0.07 · 1000 comes out a hair off 70: that is 70, not 71
  ((if (scaled - nearest).abs < 1e-6 then nearest else scaled.ceil).toUInt64).toNat

/-- `⌈vsize · rate / 1000⌉`: the fee of `vsize` vbytes at `rate` sat/kvB, rounded up to a whole sat. -/
def feeAt (vsize : Int) (rate : Nat) : Int := (vsize * rate + 999) / 1000

/-- The fee of a signed transaction of this shape at `rate` sat/kvB, from 0 up to Bitcoin's supply. -/
def fee (inputCount : Nat) (outputs : Array Transaction.Output) (witness : Int) (rate : Nat) : M Int := do
  let calculated := feeAt (TransactionBuilder.signedVSize inputCount outputs witness) rate
  unless 0 ≤ calculated && calculated ≤ maxI do throw .amountOverflow
  return calculated

def checkStandardSize (inputCount : Nat) (outputs : Array Transaction.Output) (witness : Int) : M Unit := do
  let vsize := TransactionBuilder.signedVSize inputCount outputs witness
  if vsize > TransactionBuilder.maximumStandardVSize then
    throw (.transactionTooLarge vsize TransactionBuilder.maximumStandardVSize)

/-- Takes candidates in order, each added to `selected` and `total`, until the total covers `target` and
the fee `feeWithChange` asks for that many inputs, or the candidates run out. -/
def take (feeWithChange : Nat → M Int) (target : Int) :
    List WalletUTXO → Array WalletUTXO → Int → M (Array WalletUTXO × Int)
  | [], selected, total => pure (selected, total)
  | u :: rest, selected, total => do
    let sum := total + u.amount.toInt
    if sum > maxI then throw .amountOverflow
    let required ← checkedAdd target (← feeWithChange (selected.size + 1))
    if sum ≥ required then pure (selected.push u, sum) else take feeWithChange target rest (selected.push u) sum

/-- Largest-first selection (see the Swift original for the full contract). -/
def select (utxos : Array WalletUTXO) (payments : Array Payment) (changeScriptPubKey : ByteArray)
    (feeRateSatPerVByte : Float) (witnessBytesPerInput : Int := 66) : M Selection := do
  let w := witnessBytesPerInput
  checkArguments utxos changeScriptPubKey feeRateSatPerVByte w
  let rate := satPerKvB feeRateSatPerVByte
  let target ← paymentTarget payments
  checkSpendableSet utxos
  let paymentOutputs : Array Transaction.Output := payments.map fun p => { value := p.amount, scriptPubKey := p.scriptPubKey }
  let changeOutput : Transaction.Output := { value := 0, scriptPubKey := changeScriptPubKey }
  let feeWithChange (count : Nat) : M Int := fee count (paymentOutputs.push changeOutput) w rate
  let sorted := utxos.toList.mergeSort fun a b => !(a.amount < b.amount)
  let (selected, total) ← take feeWithChange target sorted #[] 0
  let withChangeFee ← feeWithChange selected.size
  let requiredWithoutChange ← checkedAdd target (← fee selected.size paymentOutputs w rate)
  unless total ≥ requiredWithoutChange do
    throw (.insufficientFunds (Int64.ofInt total) (Int64.ofInt requiredWithoutChange))
  let change := total - target - withChangeFee
  let withChange := change ≥ dustThreshold changeScriptPubKey
  checkStandardSize selected.size (if withChange then paymentOutputs.push changeOutput else paymentOutputs) w
  if withChange then
    return { selected, fee := Int64.ofInt withChangeFee, changeAmount := some (Int64.ofInt change) }
  return { selected, fee := Int64.ofInt (total - target), changeAmount := none }

end CoinSelection
end Winnow
