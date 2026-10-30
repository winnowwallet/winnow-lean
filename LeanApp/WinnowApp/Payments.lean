import WinnowApp.Pure

/-! DisplayedPayment.swift (upstream d2ca878, `AppModel.payments`): the one Transactions list. Every wallet
entry and every multisig account's entry, a transaction in two histories folded into one transfer row when
one side spent and the others only received, drafts first, then the wallet's own ordering
(`historyForDisplay`) over the rest. Pure, over the app's `HistoryItem`s: the backend builds the inputs
(account histories and draft rows) and the screens read the result as `Status.payments`. -/

namespace WinnowApp

/-- `DisplayedPayment.walletName`. -/
def walletName : String := "Wallet"

/-- `foldTransfers(_:names:)`: rows sharing a txid where exactly one spent and the others only received
become one transfer row carrying the spender's entry; the receivers' rows go. -/
def foldTransfers (rows : List DisplayedPayment) (names : List (String × String)) : List DisplayedPayment := Id.run do
  let arr := rows.toArray
  let nameOf (row : DisplayedPayment) : String := (row.accountID.bind (lookup names ·)).getD walletName
  let mut result := arr
  let mut folded : Array Nat := #[]
  -- the txids in first-appearance order, each group once
  let mut seen : Array String := #[]
  for row in arr do
    if !seen.contains row.item.txid then seen := seen.push row.item.txid
  for txid in seen do
    let positions := (List.range arr.size).filter fun i => arr[i]!.item.txid == txid
    if positions.length ≤ 1 then continue
    let spenders := positions.filter fun i => arr[i]!.item.spent > 0
    let receivers := positions.filter fun i => arr[i]!.item.spent == 0 && arr[i]!.item.received > 0
    match spenders, receivers with
    | [spender], receiver :: _ =>
      if receivers.length != positions.length - 1 then continue
      let amount := receivers.foldl (fun t i => t + arr[i]!.item.received.toNat) 0
      result := result.modify spender fun r =>
        { r with source := .transfer (nameOf arr[spender]!) (nameOf arr[receiver]!) amount }
      folded := folded ++ receivers.toArray
    | _, _ => continue
  return (result.toList.zipIdx.filter fun (_, i) => !folded.contains i).map (·.1)

/-- `AppModel.payments(wallet:accounts:drafts:)`: wallet rows, each account's rows named, transfers
folded, ordered as `historyForDisplay` orders their entries (a txid ranked at its first position, ties
by account id, the wallet's first), drafts on top. `accounts` are (id, name, history). -/
def payments (wallet : List HistoryItem) (accounts : List (String × String × List HistoryItem))
    (drafts : List DisplayedPayment) : List DisplayedPayment :=
  let rows := wallet.map (fun e => ({ item := e, source := .wallet } : DisplayedPayment)) ++
    accounts.flatMap fun (id, name, history) =>
      history.map fun e => ({ item := e, source := .account name, accountID := some id } : DisplayedPayment)
  let names := accounts.map fun (id, name, _) => (id, name)
  let rows := foldTransfers rows names
  let order := historyForDisplay (rows.map (·.item))
  let rank (txid : String) : Nat := (order.findIdx? (·.txid == txid)).getD order.length
  let sorted := rows.mergeSort fun a b =>
    let ra := rank a.item.txid
    let rb := rank b.item.txid
    if ra != rb then ra < rb else (a.accountID.getD "") ≤ (b.accountID.getD "")
  drafts ++ sorted

/-- `displayedPayment(txid:)`: the merged list's row for a transaction id, else the wallet's own entry. -/
def Status.displayedPayment? (s : Status) (txid : String) : Option DisplayedPayment :=
  match s.payments.find? (·.item.txid == txid) with
  | some row => some row
  | none => (s.history.find? (·.txid == txid)).map fun e => { item := e, source := .wallet }

end WinnowApp
