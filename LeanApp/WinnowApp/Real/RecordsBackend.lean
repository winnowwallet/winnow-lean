import WinnowApp.Backend
import WinnowApp.Real.Records

/-! # The records fields of `Backend`, ready to plug in

`RecordsCtx` bundles what the records operations need from the core (the current store, the open
wallet, the HTTP getter); each
definition below has exactly the type of the `Backend` field of the same name, so the core writes
`records := ctx.records, addPerson := ctx.addPerson, …`. Failures surface as `IO.userError` with the
description the screens show. -/

namespace WinnowApp.RecordsReal
open Winnow

structure RecordsCtx where
  /-- The records of the current network (the core swaps it on a network switch). -/
  store : IO RecordsStore
  wallet : IO (Option Wallet)
  /-- The explorer GET (`url`, `maximumBytes`), e.g. `routedGetter httpClient`. -/
  http : String → Nat → IO ByteArray
  /-- `e2e?.journal(_:fields:)` (test mode); a no-op otherwise. -/
  journal : String → List (String × String) → IO Unit := fun _ _ => pure ()

namespace RecordsCtx

def needWallet (c : RecordsCtx) : RM Wallet := do
  let some w ← RM.io c.wallet | throw (.app .noWallet)
  return w

def run {α} (c : RecordsCtx) (f : RecordsStore → Option Wallet → RM α) : IO α := RM.toIO do
  f (← RM.io c.store) (← RM.io c.wallet)

def runW {α} (c : RecordsCtx) (f : RecordsStore → Wallet → RM α) : IO α := RM.toIO do
  f (← RM.io c.store) (← c.needWallet)

def records (c : RecordsCtx) : IO Records := do RecordsReal.records (← c.store) (← c.wallet)

def setReceiveLabel (c : RecordsCtx) (address label : String) : IO Records :=
  c.runW fun s w => RecordsReal.setReceiveLabel s w address label

def ownCard (c : RecordsCtx) (name : String) : IO String :=
  c.runW fun _ w => do return (← ownPersonCard w name).serialized

def parsePaste (c : RecordsCtx) (text : String) : IO PastePreview :=
  c.run fun s _ => RecordsReal.parsePaste s.network text

def addPerson (c : RecordsCtx) (name : String) (paste : Option String) (provenance : Option Provenance)
    (source : Option String) (labelTxid : Option String) : IO Records :=
  c.run fun s w => RecordsReal.addPerson s w name paste provenance source labelTxid

def attachDestination (c : RecordsCtx) (personID paste : String) (provenance : Provenance) (source : Option String) :
    IO Records :=
  c.run fun s w => RecordsReal.attachDestination s w personID paste provenance source

def updateRecipient (c : RecordsCtx) (personID : String) (name : Option String) (saved : Bool) : IO Records :=
  c.run fun s w => RecordsReal.updateRecipient s w personID name saved

def labelSender (c : RecordsCtx) (txid personID : String) : IO Records :=
  c.run fun s w => RecordsReal.labelSender s w txid personID

def removeSenderLabel (c : RecordsCtx) (txid : String) : IO Records :=
  c.run fun s w => RecordsReal.removeSenderLabel s w txid

/-- `URL.host` of an explorer base URL: no scheme, user, port or path ("" when there is none). -/
def urlHost (url : String) : String :=
  match url.splitOn "://" with
  | _ :: rest@(_ :: _) =>
    let afterScheme := "://".intercalate rest
    let authority := (afterScheme.takeWhile fun ch => ch != '/' && ch != '?' && ch != '#').toString
    let hostPort := (authority.splitOn "@").getLast!
    if hostPort.startsWith "[" then ((hostPort.drop 1).takeWhile (· != ']')).toString
    else (hostPort.takeWhile (· != ':')).toString
  | _ => ""

def lookupSender (c : RecordsCtx) (txid baseURL : String) : IO (List String) := do
  let addresses ← c.run fun s _ => RecordsReal.lookupSender c.http s.network txid baseURL
  c.journal "sender.lookupOnline" [("txid", txid), ("explorer", urlHost baseURL)]
  return addresses

/-- The records fields of `base` replaced by these. -/
def install (c : RecordsCtx) (base : Backend) : Backend :=
  { base with
    records := c.records, setReceiveLabel := c.setReceiveLabel, ownCard := c.ownCard, parsePaste := c.parsePaste,
    addPerson := c.addPerson, attachDestination := c.attachDestination, updateRecipient := c.updateRecipient,
    labelSender := c.labelSender, removeSenderLabel := c.removeSenderLabel, lookupSender := c.lookupSender }

end RecordsCtx
end WinnowApp.RecordsReal
