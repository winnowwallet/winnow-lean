import Winnow.Ledger.WalletPolicy

/-! # The client-command interpreter

Port of `LedgerClientCommandInterpreter` (`Sources/WalletCore/Ledger/LedgerClientCommands.swift`,
upstream 1cf93fb): the phone's side of the app's interactive protocol. While a command runs, the
device interrupts with status 0xE000 and a client command; the interpreter answers from data the
phone committed to, and nothing else. Swift's dictionaries are arrays of pairs here (a later entry
under the same key replaces the earlier one, as a dictionary assignment does). -/

namespace Winnow.Ledger

/-- `LedgerClientCommandInterpreter`. -/
structure Interpreter where
  yielded : Array ByteArray := #[]
  preimages : Array (ByteArray × ByteArray) := #[]
  trees : Array (ByteArray × Array ByteArray) := #[]
  queue : Array ByteArray := #[]
  deriving Inhabited

namespace Interpreter

/-- The client commands (`Code`). -/
def yieldCode : UInt8 := 0x10
def getPreimage : UInt8 := 0x40
def getMerkleLeafProof : UInt8 := 0x41
def getMerkleLeafIndex : UInt8 := 0x42
def getMoreElements : UInt8 := 0xA0

/-- Every answer must fit one APDU response. -/
def maximumResponse : Nat := 255

def assign {β} (xs : Array (ByteArray × β)) (k : ByteArray) (v : β) : Array (ByteArray × β) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.set! i (k, v)
  | none => xs.push (k, v)

def lookup? {β} (xs : Array (ByteArray × β)) (k : ByteArray) : Option β := (xs.find? (·.1 == k)).map (·.2)

/-- A preimage the device may ask for by its SHA-256. -/
def addKnownPreimage (i : Interpreter) (preimage : ByteArray) : Interpreter :=
  { i with preimages := assign i.preimages (sha256 preimage) preimage }

/-- A committed list: each element is served as 0x00 ‖ element under its element hash, and the
tree of element hashes under its root. -/
def addKnownList (i : Interpreter) (elements : Array ByteArray) : Interpreter := Id.run do
  let mut preimages := i.preimages
  let mut leaves : Array ByteArray := #[]
  for element in elements do
    let leaf := Merkle.elementHash element
    preimages := assign preimages leaf (ByteArray.mk #[0x00] ++ element)
    leaves := leaves.push leaf
  return { i with preimages, trees := assign i.trees (Merkle.root leaves) leaves }

/-- A committed map: its sorted keys and its values as two lists. -/
def addKnownMapping (i : Interpreter) (pairs : Array PSBT.KeyValue) : Interpreter :=
  let sorted := Merkle.sortedPairs pairs
  (i.addKnownList (sorted.map (·.key))).addKnownList (sorted.map (·.value))

/-- Parsing a request: a short or overlong one is `protocolViolation "a malformed client command"`,
as every non-Ledger error inside `execute` becomes in Swift. -/
abbrev P := ExceptT LedgerError Reader

def lift {α} (r : Reader α) : P α := ExceptT.lift r

def requireEnd : P Unit := do
  if (← lift Reader.remaining) != 0 then throw (.protocolViolation "a malformed client command")

def runP {α} (p : P α) (body : ByteArray) : Except LedgerError α :=
  match (p.run).run body with
  | .ok (.ok a, _) => .ok a
  | .ok (.error e, _) => .error e
  | .error _ => .error (.protocolViolation "a malformed client command")

def requestBeforeAnswer : LedgerError := .protocolViolation "a request before the last answer was read"

def preimage (i : Interpreter) (body : ByteArray) : Except LedgerError (Interpreter × ByteArray) := do
  let hash ← runP (do
    unless (← lift Reader.u8) == 0 do throw (.protocolViolation "an unsupported preimage request")
    let hash ← lift (Reader.bytes 32)
    requireEnd
    return hash) body
  unless i.queue.isEmpty do throw requestBeforeAnswer
  let some preimage := lookup? i.preimages hash
    | throw (.protocolViolation "a preimage this phone never committed to")
  let mut response := compactSize preimage.size.toUInt64
  let payload := min (maximumResponse - response.size - 1) preimage.size
  response := (response.push payload.toUInt8) ++ preimage.extract 0 payload
  let queue := (preimage.extract payload preimage.size).data.map fun b => ByteArray.mk #[b]
  return ({ i with queue }, response)

def leafProof (i : Interpreter) (body : ByteArray) : Except LedgerError (Interpreter × ByteArray) := do
  let (root, size, index) ← runP (do
    let root ← lift (Reader.bytes 32)
    let size ← lift Reader.compact
    let index ← lift Reader.compact
    requireEnd
    return (root, size, index)) body
  unless i.queue.isEmpty do throw requestBeforeAnswer
  let some leaves := lookup? i.trees root
    | throw (.protocolViolation "a proof for a tree this phone never committed to")
  unless leaves.size.toUInt64 == size && index < size do
    throw (.protocolViolation "a proof for a tree this phone never committed to")
  let proof := Merkle.proof leaves index.toNat
  let sent := min ((maximumResponse - 32 - 1 - 1) / 32) proof.size
  let mut response := (leaves[index.toNat]!.push proof.size.toUInt8).push sent.toUInt8
  for hash in proof.extract 0 sent do response := response ++ hash
  return ({ i with queue := proof.extract sent proof.size }, response)

def leafIndex (i : Interpreter) (body : ByteArray) : Except LedgerError ByteArray := do
  let (root, leaf) ← runP (do
    let root ← lift (Reader.bytes 32)
    let leaf ← lift (Reader.bytes 32)
    requireEnd
    return (root, leaf)) body
  let some leaves := lookup? i.trees root
    | throw (.protocolViolation "a leaf search in a tree this phone never committed to")
  match leaves.findIdx? (· == leaf) with
  | some index => return ByteArray.mk #[1] ++ compactSize index.toUInt64
  | none => return ByteArray.mk #[0] ++ compactSize 0

def moreElements (i : Interpreter) (body : ByteArray) : Except LedgerError (Interpreter × ByteArray) := do
  runP requireEnd body
  let notQueued := LedgerError.protocolViolation "a request for elements that were never queued"
  let some first := i.queue[0]? | throw notQueued
  let length := first.size
  unless i.queue.all (·.size == length) && length > 0 do throw notQueued
  let mut taken := 0
  let mut total := 0
  for next in i.queue do
    if total + next.size ≤ maximumResponse - 2 then
      total := total + next.size
      taken := taken + 1
    else break
  let mut response := ByteArray.mk #[taken.toUInt8, length.toUInt8]
  for element in i.queue.extract 0 taken do response := response ++ element
  return ({ i with queue := i.queue.extract taken i.queue.size }, response)

/-- `execute(_:)`: answers one client command. -/
def execute (i : Interpreter) (request : ByteArray) : Except LedgerError (Interpreter × ByteArray) := do
  let some code := request[0]? | throw (.protocolViolation "an unknown client command")
  let body := request.extract 1 request.size
  if code == yieldCode then return ({ i with yielded := i.yielded.push body }, .empty)
  else if code == getPreimage then i.preimage body
  else if code == getMerkleLeafProof then i.leafProof body
  else if code == getMerkleLeafIndex then return (i, ← i.leafIndex body)
  else if code == getMoreElements then i.moreElements body
  else throw (.protocolViolation "an unknown client command")

end Interpreter

/-- `LedgerWalletPolicy.register(in:)`: everything the device may ask for while it works with this
policy. -/
def WalletPolicy.registerIn (p : WalletPolicy) (i : Interpreter) : Interpreter :=
  ((i.addKnownList (p.keys.map (·.toUTF8))).addKnownPreimage p.serialized).addKnownPreimage p.template.toUTF8

end Winnow.Ledger
