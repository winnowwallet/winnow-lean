import Winnow.Crypto
import Winnow.Tx.Wire

/-! # Transaction: the raw transaction model

Port of `Sources/WalletCore/Network/Protocol/Transaction.swift`: parse, re-serialize (with and without
witness) and hash. txid = SHA256d of the legacy serialization, wtxid = SHA256d of the segwit one
(BIP141/144). Hashes are in internal byte order. -/

namespace Winnow

namespace Transaction

structure Outpoint where
  txid : ByteArray -- 32 bytes, internal order
  vout : UInt32
  deriving Inhabited

instance : BEq Outpoint := ⟨fun a b => a.txid == b.txid && a.vout == b.vout⟩

structure Input where
  previousOutput : Outpoint
  scriptSig : ByteArray
  sequence : UInt32
  witness : Array ByteArray := #[]
  deriving Inhabited

instance : BEq Input := ⟨fun a b => a.previousOutput == b.previousOutput && a.scriptSig == b.scriptSig &&
  a.sequence == b.sequence && a.witness == b.witness⟩

structure Output where
  value : Int64
  scriptPubKey : ByteArray
  deriving Inhabited

instance : BEq Output := ⟨fun a b => a.value == b.value && a.scriptPubKey == b.scriptPubKey⟩

end Transaction

structure Transaction where
  version : Int32
  inputs : Array Transaction.Input
  outputs : Array Transaction.Output
  locktime : UInt32
  deriving Inhabited

instance : BEq Transaction := ⟨fun a b => a.version == b.version && a.inputs == b.inputs &&
  a.outputs == b.outputs && a.locktime == b.locktime⟩

namespace Transaction
open Wire

def isSegwit (tx : Transaction) : Bool := tx.inputs.any (!·.witness.isEmpty)

def serialized (tx : Transaction) (includeWitness : Bool) : ByteArray := Id.run do
  let mut d := appendInt32 .empty tx.version
  let useWitness := includeWitness && tx.isSegwit
  if useWitness then d := (d.push 0).push 1
  d := appendCompactSize d tx.inputs.size.toUInt64
  for i in tx.inputs do
    d := d ++ i.previousOutput.txid
    d := appendUInt32 d i.previousOutput.vout
    d := appendVarData d i.scriptSig
    d := appendUInt32 d i.sequence
  d := appendCompactSize d tx.outputs.size.toUInt64
  for o in tx.outputs do
    d := appendInt64 d o.value
    d := appendVarData d o.scriptPubKey
  if useWitness then
    for i in tx.inputs do
      d := appendCompactSize d i.witness.size.toUInt64
      for item in i.witness do d := appendVarData d item
  d := appendUInt32 d tx.locktime
  return d

/-- txid in internal byte order (SHA256d of the no-witness serialization). -/
def txid (tx : Transaction) : ByteArray := sha256d (tx.serialized false)
/-- wtxid in internal byte order (SHA256d of the witness serialization). -/
def wtxid (tx : Transaction) : ByteArray := sha256d (tx.serialized true)

/-- The bound on a serialized script field (not `MAX_SCRIPT_SIZE`, see the Swift original). -/
def maxSerializedScript : Nat := 4_000_000

open ByteReader in
def decodeInputs (count : Nat) : ByteReader.M (Array Input) := do
  let mut inputs := Array.emptyWithCapacity count
  for _ in [0:count] do
    let txid ← readBytes 32
    let vout ← readUInt32
    let scriptSig ← readVarData maxSerializedScript
    let sequence ← readUInt32
    inputs := inputs.push { previousOutput := ⟨txid, vout⟩, scriptSig, sequence }
  return inputs

open ByteReader in
def decodeOutputs : ByteReader.M (Array Output) := do
  let outputCount ← readVarInt
  if outputCount == 0 then throw (.malformed "tx has no outputs")
  -- an output is ≥ 9 bytes (8 value + 1 script length)
  if outputCount.toNat > (← remainingM) / 9 then throw (.malformed s!"tx output count {outputCount}")
  let mut outputs := Array.emptyWithCapacity outputCount.toNat
  for _ in [0:outputCount.toNat] do
    let value ← readInt64
    let scriptPubKey ← readVarData maxSerializedScript
    outputs := outputs.push { value, scriptPubKey }
  return outputs

open ByteReader in
/-- BIP144 witness stacks, one per input, in input order. -/
def decodeWitnesses (inputs : Array Input) : ByteReader.M (Array Input) := do
  let mut inputs := inputs
  for idx in [0:inputs.size] do
    let itemCount ← readVarInt
    if itemCount > 1_000 then throw (.malformed s!"witness items {itemCount}")
    let mut items : Array ByteArray := #[]
    for _ in [0:itemCount.toNat] do items := items.push (← readVarData 4_000_000)
    inputs := inputs.modify idx fun i => { i with witness := i.witness ++ items }
  return inputs

open ByteReader in
/-- Parses from a reader positioned at the transaction start; consumes exactly the transaction's
bytes (no end check). Handles legacy and segwit (BIP144) serializations. -/
def decodeFrom : ByteReader.M Transaction := do
  let version ← readInt32
  let mut inputCount ← readVarInt
  let mut segwit := false
  if inputCount == 0 then
    -- marker 0x00 must be followed by a nonzero flag (BIP144)
    let flag ← readUInt8
    if flag == 0 then throw (.malformed "tx flag 0")
    segwit := true
    inputCount ← readVarInt
  if inputCount == 0 then throw (.malformed "tx has no inputs")
  -- a non-witness input is ≥ 41 bytes
  if inputCount.toNat > (← remainingM) / 41 then throw (.malformed s!"tx input count {inputCount}")
  let mut inputs ← decodeInputs inputCount.toNat
  let outputs ← decodeOutputs
  if segwit then inputs ← decodeWitnesses inputs
  let locktime ← readUInt32
  return { version, inputs, outputs, locktime }

/-- Parses a whole buffer: exactly one transaction, nothing after it. -/
def decode (data : ByteArray) : Except WireError Transaction := decodeFrom.runAll data

end Transaction
end Winnow
