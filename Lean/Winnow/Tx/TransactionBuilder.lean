import Winnow.Tx.Transaction
import Winnow.Tx.AddressDecoder

/-! # TransactionBuilder: unsigned transactions and vsize math

Port of `Sources/WalletCore/Transactions/TransactionBuilder.swift`. The Swift original draws its own
randomness (the anti-fee-sniping lookback, the change position when none is given); here every draw is
an explicit argument. -/

namespace Winnow

inductive TxBuildError where
  | noInputs | noOutputs
  | invalidAmount (amount : Int64)
  | amountOverflow | emptyScript | invalidOutpoint | duplicateInput
  | invalidChangePosition (position : Int)
  deriving Repr, BEq, Inhabited

def TxBuildError.name : TxBuildError → String
  | .noInputs => "noInputs" | .noOutputs => "noOutputs" | .invalidAmount _ => "invalidAmount"
  | .amountOverflow => "amountOverflow" | .emptyScript => "emptyScript" | .invalidOutpoint => "invalidOutpoint"
  | .duplicateInput => "duplicateInput" | .invalidChangePosition _ => "invalidChangePosition"

/-- `BitcoinAmount.maximum`: 21M BTC in sats. -/
def bitcoinAmountMaximum : Int64 := 2_100_000_000_000_000

/-- A payment target: an amount plus its destination scriptPubKey. -/
structure Payment where
  amount : Int64
  scriptPubKey : ByteArray
  deriving Inhabited

/-- `Payment(amount:address:network:)`: pays any standard address type. -/
def Payment.ofAddress (amount : Int64) (address : String) (network : Tx.BitcoinNetwork) : Except AddressError Payment := do
  return { amount, scriptPubKey := ← AddressDecoder.scriptPubKey address network }

namespace TransactionBuilder

/-- Sequence 0xFFFFFFFD: locktime-disabled, opt-in BIP125 replaceable. -/
def defaultSequence : UInt32 := 0xFFFF_FFFD

/-- Confines a draw to `0 ..< 1` (non-finite → 0). -/
def draw (value : Float) : Float :=
  if !value.isFinite then 0 else min (max value 0) 0.999999999

/-- The anti-fee-sniping `nLockTime`: the tip, or (when the first draw is below 0.1) a height up to 99
blocks back, chosen by the second draw. Never above `tip`. -/
def antiFeeSnipingLocktime (tip : UInt32) (first second : Float) : UInt32 :=
  if !(draw first < 0.1) then tip
  else
    let lookback := (draw second * 100).toUInt32
    if tip ≥ lookback then tip - lookback else 0

def checkInputs (inputs : Array Transaction.Outpoint) : Except TxBuildError Unit := do
  if inputs.isEmpty then throw .noInputs
  let mut seen : Array Transaction.Outpoint := #[]
  for i in inputs do
    if i.txid.size != 32 then throw .invalidOutpoint
    if seen.contains i then throw .duplicateInput
    seen := seen.push i

def checkOutputs (outputs : Array Transaction.Output) : Except TxBuildError Unit := do
  if outputs.isEmpty then throw .noOutputs
  let mut total : Int := 0
  for o in outputs do
    unless o.value > 0 && o.value ≤ bitcoinAmountMaximum do throw (.invalidAmount o.value)
    if o.scriptPubKey.isEmpty then throw .emptyScript
    let sum := total + o.value.toInt
    if sum > bitcoinAmountMaximum.toInt then throw .amountOverflow
    total := sum

/-- An unsigned transaction: payments first, the change output inserted at `changePosition`. When that
is `none`, `randomPosition n` picks it from `0…n` (the Swift original uses `Int.random(in: 0 ... n)`). -/
def build (inputs : Array Transaction.Outpoint) (payments : Array Payment) (change : Option Payment := none)
    (changePosition : Option Int := none) (randomPosition : Nat → Nat := id)
    (sequence : UInt32 := defaultSequence) (locktime : UInt32 := 0) : Except TxBuildError Transaction := do
  checkInputs inputs
  let mut outputs : Array Transaction.Output := payments.map fun p => { value := p.amount, scriptPubKey := p.scriptPubKey }
  if let some c := change then
    let position := changePosition.getD (randomPosition outputs.size : Nat)
    unless position ≥ 0 && position ≤ outputs.size do throw (.invalidChangePosition position)
    outputs := outputs.insertIdxIfInBounds position.toNat { value := c.amount, scriptPubKey := c.scriptPubKey }
  checkOutputs outputs
  let txInputs := inputs.map fun o => ({ previousOutput := o, scriptSig := .empty, sequence } : Transaction.Input)
  return { version := 2, inputs := txInputs, outputs, locktime }

/-- `MAX_STANDARD_TX_WEIGHT / 4`. -/
def maximumStandardVSize : Nat := 100_000

def compactSizeLength (value : UInt64) : Nat :=
  if value < 0xFD then 1 else if value ≤ 0xFFFF then 3 else if value ≤ 0xFFFF_FFFF then 5 else 9

/-- Exact vsize of the signed transaction when every input is a P2TR key-path spend (or spends
`witnessBytesPerInput` witness bytes each). Integer arithmetic as Swift's `Int` (truncating division). -/
def signedVSize (inputCount : Nat) (outputs : Array Transaction.Output) (witnessBytesPerInput : Int := 66) : Int :=
  let base0 : Int := 4 + 4 + compactSizeLength inputCount.toUInt64 + compactSizeLength outputs.size.toUInt64
  let base1 := base0 + inputCount * (32 + 4 + 1 + 4)
  let base := outputs.foldl (fun (b : Int) o => b + 8 + compactSizeLength o.scriptPubKey.size.toUInt64 + o.scriptPubKey.size) base1
  let witness := 2 + inputCount * witnessBytesPerInput
  (3 * base + base + witness + 3).tdiv 4

/-- Exact vsize of a fully-signed transaction (witness included). -/
def vsize (tx : Transaction) : Nat :=
  (3 * (tx.serialized false).size + (tx.serialized true).size + 3) / 4

end TransactionBuilder
end Winnow
