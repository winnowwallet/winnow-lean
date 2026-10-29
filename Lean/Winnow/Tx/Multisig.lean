import Winnow.Tx.Script

/-! # Multisig: BIP387 `multi_a` / `sortedmulti_a` tapscripts and timelocked leaves

Port of `Sources/WalletCore/Script/Multisig.swift` at upstream 1cf93fb: the k-of-n `multi_a` leaf, the two
timelocked miniscript leaves a recovery path uses (`and_v(v:pk(K),older(N))` and
`and_v(v:multi_a(k,…),older(N))`), their parser (`parsePolicy`, canonical forms only) and the BIP68/BIP112
block-based relative-lock rule (`RelativeLock`). -/

namespace Winnow

inductive MultisigError where
  | invalidThreshold | tooManyKeys | invalidKey | invalidTimelock
  deriving Repr, BEq, Inhabited

def MultisigError.name : MultisigError → String
  | .invalidThreshold => "invalidThreshold" | .tooManyKeys => "tooManyKeys" | .invalidKey => "invalidKey"
  | .invalidTimelock => "invalidTimelock"

/-- A script-path leaf this wallet can sign and finalize: any `threshold` of these x-only keys (in script
order, the order signatures follow in the witness), optionally only once the coin is `relativeLock` blocks
old. -/
structure LeafPolicy where
  threshold : Int
  keys : Array ByteArray
  relativeLock : Option UInt32
  deriving Inhabited, BEq

namespace Multisig

def maxKeys : Nat := 999

def checkedKeys (k : Int) (keys : Array ByteArray) (sorted : Bool) : Except MultisigError (Array ByteArray) := do
  unless k ≥ 1 && k ≤ keys.size do throw .invalidThreshold
  unless keys.size ≤ maxKeys do throw .tooManyKeys
  unless keys.all (·.size == 32) do throw .invalidKey
  return if sorted then sortBytes id keys else keys

/-- Miniscript's `older(N)` range: 1 to 2^31 − 1. -/
def checkLock (blocks : UInt32) : Except MultisigError Unit := do
  unless blocks ≥ 1 && blocks < 0x8000_0000 do throw .invalidTimelock

def appendKeys (s : Script) (keys : Array ByteArray) : Script := Id.run do
  let mut s := s
  for h : i in [0:keys.size] do
    s := (s.appendPush keys[i]).appendOpcode (if i == 0 then Script.Op.checkSig else Script.Op.checkSigAdd)
  return s

/-- `<KEY_1> OP_CHECKSIG <KEY_2> OP_CHECKSIGADD … <KEY_n> OP_CHECKSIGADD <k> OP_NUMEQUAL` from 32-byte
x-only keys, sorted lexicographically first when `sorted`. -/
def script (k : Int) (keys : Array ByteArray) (sorted : Bool) : Except MultisigError Script := do
  let ordered ← checkedKeys k keys sorted
  return Script.build fun s => ((appendKeys s ordered).appendScriptNumber k.toNat).appendOpcode Script.Op.numEqual

/-- `and_v(v:multi_a(k,…),older(N))`: the multi_a script with OP_NUMEQUALVERIFY, then
`<N> OP_CHECKSEQUENCEVERIFY`. -/
def timelockedMultiScript (k : Int) (keys : Array ByteArray) (blocks : UInt32) : Except MultisigError Script := do
  let ordered ← checkedKeys k keys false
  checkLock blocks
  return Script.build fun s =>
    ((((appendKeys s ordered).appendScriptNumber k.toNat).appendOpcode Script.Op.numEqualVerify).appendScriptNumber
      blocks.toNat).appendOpcode Script.Op.checkSequenceVerify

/-- `and_v(v:pk(K),older(N))`: `<K> OP_CHECKSIGVERIFY <N> OP_CHECKSEQUENCEVERIFY`. -/
def timelockedKeyScript (key : ByteArray) (blocks : UInt32) : Except MultisigError Script := do
  unless key.size == 32 do throw .invalidKey
  checkLock blocks
  return Script.build fun s =>
    (((s.appendPush key).appendOpcode Script.Op.checkSigVerify).appendScriptNumber blocks.toNat).appendOpcode
      Script.Op.checkSequenceVerify

/-- A positive, minimally encoded script number at `offset`: OP_1…OP_16 or a push of at most five bytes
(a push of a value of 16 or less is not minimal). The value and the offset just past it. -/
def scriptNumber (b : ByteArray) (offset : Nat) : Option (Nat × Nat) := do
  guard (offset < b.size)
  let head := b[offset]!
  if 0x51 ≤ head && head ≤ 0x60 then return (head.toNat - 0x50, offset + 1)
  let length := head.toNat
  guard (1 ≤ length && length ≤ 5 && offset + 1 + length ≤ b.size)
  let number := b.extract (offset + 1) (offset + 1 + length)
  let top := number[length - 1]!
  guard (top &&& 0x80 == 0)
  if top == 0 then guard (length > 1 && number[length - 2]! &&& 0x80 != 0)
  let value := (List.range length).foldr (fun i acc => acc * 256 + number[i]!.toNat) 0
  guard (value > 16)
  return (value, offset + 1 + length)

/-- Any leaf shape this module builds, in exactly the canonical form it emits: `multi_a`, timelocked
`multi_a` and timelocked `pk`; `none` for anything else. -/
def parsePolicy (s : Script) : Option LeafPolicy := Id.run do
  let bytes := s.bytes
  if bytes.size ≥ 34 && bytes[0]! == 0x20 && bytes[33]! == Script.Op.checkSigVerify then
    let some (blocks, stop) := scriptNumber bytes 34 | return none
    unless stop + 1 == bytes.size && bytes[stop]! == Script.Op.checkSequenceVerify && blocks ≥ 1 &&
        blocks < 0x8000_0000 do return none
    return some { threshold := 1, keys := #[bytes.extract 1 33], relativeLock := some blocks.toUInt32 }
  let mut keys : Array ByteArray := #[]
  let mut offset := 0
  while offset + 34 ≤ bytes.size && bytes[offset]! == 0x20 do
    let expected := if keys.isEmpty then Script.Op.checkSig else Script.Op.checkSigAdd
    unless bytes[offset + 33]! == expected && keys.size < maxKeys do return none
    keys := keys.push (bytes.extract (offset + 1) (offset + 33))
    offset := offset + 34
  if keys.isEmpty then return none
  let some (threshold, after) := scriptNumber bytes offset | return none
  unless threshold ≥ 1 && threshold ≤ keys.size && after < bytes.size do return none
  let op := bytes[after]!
  if op == Script.Op.numEqual then
    unless after + 1 == bytes.size do return none
    return some { threshold, keys, relativeLock := none }
  if op == Script.Op.numEqualVerify then
    let some (blocks, stop) := scriptNumber bytes (after + 1) | return none
    unless stop + 1 == bytes.size && bytes[stop]! == Script.Op.checkSequenceVerify && blocks ≥ 1 &&
        blocks < 0x8000_0000 do return none
    return some { threshold, keys, relativeLock := some blocks.toUInt32 }
  return none

/-- Threshold and keys, in script order, of a `multi_a`/`sortedmulti_a` tapscript; `none` for any other
script, timelocked leaves included. -/
def parse (s : Script) : Option (Int × Array ByteArray) :=
  match parsePolicy s with
  | some p => if p.relativeLock.isNone then some (p.threshold, p.keys) else none
  | none => none

end Multisig

/-! BIP68/BIP112 relative timelocks, block-based only. -/
namespace RelativeLock

/-- Whether an input with `sequence`, in a transaction of `txVersion`, satisfies
`<blocks> OP_CHECKSEQUENCEVERIFY`. -/
def isSatisfied (blocks sequence : UInt32) (txVersion : Int32) : Bool :=
  let disable : UInt32 := 0x8000_0000
  let typeFlag : UInt32 := 0x40_0000
  blocks &&& disable == 0 && blocks &&& typeFlag == 0 && txVersion ≥ 2 && sequence &&& disable == 0 &&
    sequence &&& typeFlag == 0 && sequence &&& 0xFFFF ≥ blocks &&& 0xFFFF

end RelativeLock
end Winnow
