import Winnow.Tx.TransactionBuilder

/-! # What a reviewed send authorizes

A person reviews a send (what is paid, to which scripts, from which coins, for what fee, with what change)
and then authenticates. Between the review and the signature the transaction is built again, and what is
signed must be what was reviewed, not something like it: the same coins in the same order, the same fee and
change, and outputs that are exactly the reviewed payments and the change, each once (SEC-007, SEC-018).

This is that check, as a pure function of what was reviewed and the transaction. It is in the core library so
that whoever reviews a spend has it without the wallet, and it is written by structural recursion on lists so
that what it accepts can be proved (`Winnow/Proofs/Spend.lean`): a transaction it accepts has the reviewed
inputs in order and, as a multiset, exactly the reviewed outputs. -/

namespace Winnow

/-- What a person agreed to when they reviewed a send. -/
structure ReviewedSend where
  /-- The payments reviewed, to scripts known at review time. -/
  payments : Array Payment
  /-- The amounts of the BIP352 destinations reviewed, in order. Their scripts exist only once the wallet
  signs, so the wallet hands `authorizesTransaction` the scripts it derived (SEC-018). -/
  silentAmounts : Array Int64 := #[]
  fee : Int64
  changeAmount : Option Int64
  /-- The coins spent, in the order the transaction spends them. -/
  selected : Array Transaction.Outpoint
  change : Option Payment

namespace ReviewedSend

/-- Whether `o` pays `p`: the same amount to the same script. -/
def pays (o : Transaction.Output) (p : Payment) : Bool := o.value == p.amount && o.scriptPubKey == p.scriptPubKey

/-- `outputs` without the first one that pays `p`, or `none` if none does. -/
def takeOutput : List Transaction.Output → Payment → Option (List Transaction.Output)
  | [], _ => none
  | o :: rest, p => if pays o p then some rest else (takeOutput rest p).map (o :: ·)

/-- Whether `outputs` are exactly `expected`: each expected payment by one output of its own, in any order,
and no output over. -/
def outputsAre : List Transaction.Output → List Payment → Bool
  | outputs, [] => outputs.isEmpty
  | outputs, p :: ps =>
    match takeOutput outputs p with
    | some rest => outputsAre rest ps
    | none => false

/-- The payments a transaction's outputs must be: the reviewed ones, the silent payments as the wallet
resolved them, and the change if there is any. -/
def expected (r : ReviewedSend) (resolved : Array Payment) : List Payment :=
  r.payments.toList ++ resolved.toList ++ r.change.toList

/-- `authorizes(transaction:fee:changeAmount:resolvedSilentPayments:)`: whether `tx`, with the fee and change
it was built with, is the send that was reviewed. The fee and change are the reviewed ones; the inputs are
the reviewed coins in order; each resolved silent payment has its reviewed amount; the outputs are exactly
the reviewed payments, the resolved silent payments and the change; and there is a change payment just when
there is a change amount. -/
def authorizesTransaction (r : ReviewedSend) (tx : Transaction) (fee : Int64) (changeAmount : Option Int64)
    (resolved : Array Payment := #[]) : Bool :=
  fee == r.fee && changeAmount == r.changeAmount &&
    tx.inputs.map (·.previousOutput) == r.selected &&
    resolved.map (·.amount) == r.silentAmounts &&
    outputsAre tx.outputs.toList (r.expected resolved) &&
    r.change.isNone == r.changeAmount.isNone

end ReviewedSend
end Winnow
