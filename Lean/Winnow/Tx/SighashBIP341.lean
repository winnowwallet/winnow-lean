import Winnow.Tx.Transaction
import Winnow.Tx.Taproot

/-! # SighashBIP341: the Taproot signature hash

Port of `Sources/WalletCore/Transactions/SighashBIP341.swift`: key path (ext_flag 0) and script path
(ext_flag 1, the BIP342 extension), with the optional annex commitment. -/

namespace Winnow

inductive SighashError where
  | invalidHashType (raw : UInt8)
  | inputIndexOutOfRange (index : Int) (count : Nat)
  | spentOutputCountMismatch (inputs spentOutputs : Nat)
  | singleWithoutCorrespondingOutput (index : Int)
  deriving Repr, BEq, Inhabited

def SighashError.name : SighashError → String
  | .invalidHashType _ => "invalidHashType" | .inputIndexOutOfRange .. => "inputIndexOutOfRange"
  | .spentOutputCountMismatch .. => "spentOutputCountMismatch"
  | .singleWithoutCorrespondingOutput _ => "singleWithoutCorrespondingOutput"

namespace SighashBIP341
open Wire

/-- The output spent by an input. -/
structure SpentOutput where
  amount : Int64
  scriptPubKey : ByteArray
  deriving Inhabited

instance : BEq SpentOutput := ⟨fun a b => a.amount == b.amount && a.scriptPubKey == b.scriptPubKey⟩

/-- A BIP341 hash_type byte. -/
structure HashType where
  rawValue : UInt8
  deriving BEq, Inhabited

namespace HashType
def «default» : HashType := ⟨0x00⟩
def all : HashType := ⟨0x01⟩
def none : HashType := ⟨0x02⟩
def single : HashType := ⟨0x03⟩
def baseType (h : HashType) : UInt8 := h.rawValue &&& 0x03
def isValid (h : HashType) : Bool := h.rawValue == 0 || (h.baseType != 0 && h.rawValue &&& 0x7C == 0)
def isAnyoneCanPay (h : HashType) : Bool := h.rawValue &&& 0x80 != 0
def commitsToAllOutputs (h : HashType) : Bool := h.rawValue == 0x00 || h.rawValue == 0x01
def anyoneCanPay (h : HashType) : HashType := ⟨h.rawValue ||| 0x80⟩
end HashType

/-- The BIP342 common signature message extension (ext_flag = 1). -/
structure ScriptPath where
  tapleafHash : ByteArray
  keyVersion : UInt8 := 0x00
  codeseparatorPosition : UInt32 := 0xFFFF_FFFF
  deriving Inhabited

namespace ScriptPath
def tapscriptKeyVersion : UInt8 := 0x00
def noCodeseparator : UInt32 := 0xFFFF_FFFF
/-- The extension for spending a tapscript leaf (default key version, no code separator). -/
def ofLeaf (leafScript : Script) (leafVersion : UInt8 := Tx.Taproot.leafVersion) : ScriptPath :=
  { tapleafHash := Tx.Taproot.leafHash leafVersion leafScript }
end ScriptPath

structure CommonHashes where
  prevouts : ByteArray
  amounts : ByteArray
  scriptPubKeys : ByteArray
  sequences : ByteArray
  outputs : ByteArray
  deriving Inhabited

def commonHashes (tx : Transaction) (spentOutputs : Array SpentOutput) : Except SighashError CommonHashes := do
  if tx.inputs.size != spentOutputs.size then throw (.spentOutputCountMismatch tx.inputs.size spentOutputs.size)
  let mut prevouts := ByteArray.empty
  let mut sequences := ByteArray.empty
  for i in tx.inputs do
    prevouts := appendUInt32 (prevouts ++ i.previousOutput.txid) i.previousOutput.vout
    sequences := appendUInt32 sequences i.sequence
  let mut amounts := ByteArray.empty
  let mut spks := ByteArray.empty
  for o in spentOutputs do
    amounts := appendInt64 amounts o.amount
    spks := appendVarData spks o.scriptPubKey
  let mut outputs := ByteArray.empty
  for o in tx.outputs do
    outputs := appendVarData (appendInt64 outputs o.value) o.scriptPubKey
  return { prevouts := sha256 prevouts, amounts := sha256 amounts, scriptPubKeys := sha256 spks,
           sequences := sha256 sequences, outputs := sha256 outputs }

def checkArguments (tx : Transaction) (inputIndex : Int) (spentOutputs : Array SpentOutput) (hashType : HashType) :
    Except SighashError Unit := do
  unless hashType.isValid do throw (.invalidHashType hashType.rawValue)
  unless inputIndex ≥ 0 && inputIndex < tx.inputs.size do throw (.inputIndexOutOfRange inputIndex tx.inputs.size)
  if tx.inputs.size != spentOutputs.size then throw (.spentOutputCountMismatch tx.inputs.size spentOutputs.size)

/-- m = 0x00 ‖ SigMsg(hash_type, ext_flag). `annex` is the full annex including its 0x50 prefix. -/
def signatureMessage (tx : Transaction) (inputIndex : Int) (spentOutputs : Array SpentOutput) (hashType : HashType)
    (scriptPath : Option ScriptPath := .none) (annex : Option ByteArray := .none) : Except SighashError ByteArray := do
  checkArguments tx inputIndex spentOutputs hashType
  let idx := inputIndex.toNat
  let common ← commonHashes tx spentOutputs
  let mut m := ByteArray.mk #[0x00, hashType.rawValue]
  m := appendUInt32 (appendInt32 m tx.version) tx.locktime
  if !hashType.isAnyoneCanPay then
    m := m ++ common.prevouts ++ common.amounts ++ common.scriptPubKeys ++ common.sequences
  if hashType.baseType != HashType.none.baseType && hashType.baseType != HashType.single.baseType then
    m := m ++ common.outputs
  m := m.push ((if scriptPath.isSome then 2 else 0) ||| (if annex.isSome then 1 else 0))
  if hashType.isAnyoneCanPay then
    let input := tx.inputs[idx]!
    let spent := spentOutputs[idx]!
    m := appendUInt32 (m ++ input.previousOutput.txid) input.previousOutput.vout
    m := appendVarData (appendInt64 m spent.amount) spent.scriptPubKey
    m := appendUInt32 m input.sequence
  else
    m := appendUInt32 m idx.toUInt32
  if let some a := annex then m := m ++ sha256 (varBytes a)
  if hashType.baseType == HashType.single.baseType then
    unless idx < tx.outputs.size do throw (.singleWithoutCorrespondingOutput inputIndex)
    let o := tx.outputs[idx]!
    m := m ++ sha256 (appendVarData (i64LE o.value) o.scriptPubKey)
  if let some sp := scriptPath then
    m := appendUInt32 ((m ++ sp.tapleafHash).push sp.keyVersion) sp.codeseparatorPosition
  return m

/-- TaggedHash("TapSighash", 0x00 ‖ SigMsg). -/
def sighash (tx : Transaction) (inputIndex : Int) (spentOutputs : Array SpentOutput)
    (hashType : HashType := HashType.default) (scriptPath : Option ScriptPath := .none)
    (annex : Option ByteArray := .none) : Except SighashError ByteArray := do
  return taggedHash "TapSighash" (← signatureMessage tx inputIndex spentOutputs hashType scriptPath annex)

end SighashBIP341
end Winnow
