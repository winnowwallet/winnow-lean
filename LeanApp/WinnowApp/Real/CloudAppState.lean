import WinnowApp.Real.RecordsStores
import WinnowApp.Real.SignerStore
import Winnow.Wallet.CloudWalletBackup

/-! # The wallet context inside an iCloud backup (`Sources/WinnowApp/CloudAppState.swift`, upstream d2ca878)

Private context carried only inside the encrypted recovery copy (`CloudWalletBackup`'s app data): the
address book, receive-address notes, the display name and the Advanced switch. Connection settings stay
on the device. JSON with sorted keys and escaped slashes (`JSONEncoder` with `.sortedKeys`), the
optionals (`descriptor`, `signers`) omitted when absent; `version` is required on the way in (a `var`
with a default is still decoded by the synthesized `init(from:)`).

`signers` is the list of paired Ledgers and saved keys a context carried while only the iCloud copy held
them; new contexts leave it out (the bundle carries them, `ImportBundle.signers`). An old context's list
is held to `SignerStore.validateBackup` (the signer file's own rules and its 1 MiB ceiling) and merged on
restore (`SignerStore.planRestore`, then `restore`). -/

namespace WinnowApp.RecordsReal
open Winnow SwiftJSON
open Tx (BitcoinNetwork)

structure CloudAppState where
  version : Int := 1
  network : String
  descriptor : Option String := none
  people : PeopleStore.Backup
  /-- Canonical script hex → note (a dictionary). -/
  receiveLabels : Array (String × String) := #[]
  ownDisplayName : String
  advancedMode : Bool
  signers : Option (Array SignerRecord) := none
  deriving Inhabited

namespace CloudAppState

/-- `SignerStore.maximumFileBytes`. -/
def maximumSignerFileBytes : Nat := 1_024 * 1_024

private def sortedLabels (labels : Array (String × String)) : Array (String × String) :=
  (labels.toList.mergeSort fun a b => !(b.1 < a.1)).toArray

/-- Swift's synthesized `==` (dictionaries compared as dictionaries). -/
def same (a b : CloudAppState) : Bool :=
  a.version == b.version && a.network == b.network && a.descriptor == b.descriptor && a.people == b.people &&
    sortedLabels a.receiveLabels == sortedLabels b.receiveLabels && a.ownDisplayName == b.ownDisplayName &&
    a.advancedMode == b.advancedMode && a.signers == b.signers

instance : BEq CloudAppState := ⟨same⟩

def toJV (c : CloudAppState) : JV :=
  obj [("version", some (ofInt c.version)), ("network", some (.str c.network)), ("descriptor", c.descriptor.map .str),
    ("people", some c.people.toJV), ("receiveLabels", some (PeopleStore.labelsJV c.receiveLabels)),
    ("ownDisplayName", some (.str c.ownDisplayName)), ("advancedMode", some (.bool c.advancedMode)),
    ("signers", c.signers.map (.arr ∘ Array.map SignerRecord.toJV))]

def ofJV (v : JV) : D CloudAppState := do
  let kvs ← asObject v
  return { version := ← key kvs "version" asInt, network := ← key kvs "network" asString,
           descriptor := ← keyIfPresent kvs "descriptor" asString, people := ← key kvs "people" PeopleStore.Backup.ofJV,
           receiveLabels := ← key kvs "receiveLabels" PeopleStore.asStringMap,
           ownDisplayName := ← key kvs "ownDisplayName" asString, advancedMode := ← key kvs "advancedMode" asBool,
           signers := ← keyIfPresent kvs "signers" (asArray SignerRecord.ofJV) }

/-- `encoded()`: sorted keys, escaped slashes. -/
def encoded (c : CloudAppState) : ByteArray := (write c.toJV).toUTF8

def mismatch {α} (reason : String) : RM α := throw (.named "invalidBundle" reason)

/-- `validate(for:)`: the same wallet and network as the bundle, every store's own rules, and the app-data
ceiling on its own encoding. -/
def validate (c : CloudAppState) (bundle : ImportBundle) : RM Unit := do
  unless c.version == 1 && c.network == bundle.network && c.descriptor == bundle.descriptor do
    mismatch "cloud wallet context does not match"
  let some network := BitcoinNetwork.ofString? c.network | mismatch "cloud wallet context does not match"
  unless c.ownDisplayName.utf8ByteSize ≤ 1024 do mismatch "cloud wallet context does not match"
  PeopleStore.validateBackup c.people network
  if let some signers := c.signers then SignerStore.validateBackup signers network
  discard <| LabelStore.validatedBackup c.receiveLabels network
  unless c.encoded.size ≤ CloudWalletBackup.maximumAppStateBytes do mismatch "cloud wallet context is too large"

/-- `decode(_:for:)`: none for an older backup without app data; otherwise bounded, decoded, validated. -/
def decode (data : Option ByteArray) (bundle : ImportBundle) : RM (Option CloudAppState) := do
  let some data := data | return none
  unless data.size ≤ CloudWalletBackup.maximumAppStateBytes do mismatch "cloud wallet context is too large"
  let some text := String.fromUTF8? data | throw (.named "dataCorrupted" "The cloud wallet context is not valid JSON.")
  let c ← match decodeText text ofJV with
    | .ok c => pure c
    | .error e => throw (.named e "The cloud wallet context could not be decoded.")
  c.validate bundle
  return some c

end CloudAppState
end WinnowApp.RecordsReal
