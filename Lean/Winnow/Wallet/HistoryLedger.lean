import Winnow.Wallet.Types
import Winnow.Tx.FundingSources

/-! # The history rules the wallet and a multisig account share (port of `Sources/WalletCore/Wallet/HistoryLedger.swift`, upstream d2ca878)

Pure functions over `Array HistoryEntry`: what a confirmed transaction records, how a pending entry
confirms in place, which outputs are change or external, and what a reorg re-pends or drops. `Wallet`
keeps fee-rate sampling, pending sends and replacement reconciliation around these; the app's
`MultisigStore` keeps coins, drafts and in-flight spends. Swift's `inout` history is an argument and a
returned array here; its `Set<Data>` of re-pended txids is an array in history order (txids are unique
in a history). -/

namespace Winnow.HistoryLedger

/-- The fee a spend paid, known only when every input was ours (the BIP341 sighash commits to amounts, so
our own spends qualify): inputs minus outputs, and only when that is positive. -/
def exactFee (spent : Int64) (tx : Transaction) (allInputsOurs : Bool) : Option Int64 :=
  if !allInputsOurs || !(spent > 0) then none
  else
    let candidate := spent - tx.outputs.foldl (fun a o => a + o.value) 0
    if candidate > 0 then some candidate else none

/-- The breakdown an entry may keep once its bytes are known. A breakdown that arrived without bytes, an
imported entry's display metadata, is dropped when the real transaction contradicts it, rather than
persisted: `HistoryEntry` refuses to decode an entry whose metadata disagrees with its transaction. -/
def agreeing (outputs : Option HistoryEntry.Outputs) (tx : Transaction) : Option HistoryEntry.Outputs :=
  outputs.filter fun o => (o.validateAgainst tx).toOption.isSome

/-- Confirms `tx` into `history`. A known entry, a pending spend reaching its block or a re-pended one,
takes the height, the block hash, its bytes and funding scripts, and keeps a breakdown only while it still
describes those bytes; an unknown transaction is appended without a breakdown. Also returns whether the
entry was known. -/
def record (history : Array HistoryEntry) (tx : Transaction) (txid : ByteArray) (height : UInt32)
    (blockHash : ByteArray) (received spent : Int64) (fee : Option Int64) : Array HistoryEntry × Bool :=
  let raw := tx.serialized false
  let funding := FundingSources.fundingScripts tx
  match history.findIdx? (·.txid == txid) with
  | some k =>
    (history.modify k fun e =>
      { e with height, blockHash := some blockHash, rawTransaction := some raw, fundingScripts := funding,
               outputs := agreeing e.outputs tx }, true)
  | none =>
    (history.push { txid, height, received, spent, fee, rawTransaction := some raw, fundingScripts := funding,
                    blockHash := some blockHash }, false)

/-- Positive outputs classified by whose script they pay: the owner's change vouts, external recipients in
transaction order, and the owner's receive outputs left out. -/
def classifyOutputs (tx : Transaction) (chain : ByteArray → Option AddressChain) : HistoryEntry.Outputs := Id.run do
  let mut result : HistoryEntry.Outputs := {}
  for h : vout in [0:tx.outputs.size] do
    let o := tx.outputs[vout]
    if !(o.value > 0) then continue
    match chain o.scriptPubKey with
    | some .change => result := { result with change := result.change.push vout.toUInt32 }
    | some .receive => continue
    | none =>
      let external : HistoryEntry.ExternalOutput := { vout := vout.toUInt32, amount := o.value, scriptPubKey := o.scriptPubKey }
      result := { result with external := result.external.push external }
  return result

/-- A reorg below `forkHeight`. A disconnected spender is straight back in every mempool that saw it, so
its entry re-pends (height 0, no block hash) and its txid is returned so the caller keeps its input
reservations (#157); a pure receive drops with its coins, and the rescan from the fork re-finds whichever
survive. A pure function of the fork height, so a repeat changes nothing. -/
def rewind (history : Array HistoryEntry) (forkHeight : UInt32) : Array HistoryEntry × Array ByteArray := Id.run do
  let mut repended : Array ByteArray := #[]
  let mut history := history
  for k in [0:history.size] do
    let e := history[k]!
    if e.height > forkHeight && e.spent > 0 then
      repended := repended.push e.txid
      history := history.set! k { e with height := 0, blockHash := none }
  return (history.filter fun e => !(e.height > forkHeight), repended)

end Winnow.HistoryLedger
