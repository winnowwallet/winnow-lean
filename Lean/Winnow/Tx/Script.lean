import Winnow.Tx.Wire

/-! # Script: the minimal script model for tapscript leaves

Port of `Sources/WalletCore/Script/Script.swift` (not an interpreter): raw bytes, hex in and out, the
opcode constants Winnow uses, minimal pushes and small script numbers. -/

namespace Winnow

/-- `Data.lexicographicallyPrecedes`: bytewise, a proper prefix first. -/
def bytesLt (a b : ByteArray) : Bool := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

/-- Sort byte strings with `bytesLt` (stable). -/
def sortBytes {α} (key : α → ByteArray) (xs : Array α) : Array α :=
  (xs.toList.mergeSort fun a b => !bytesLt (key b) (key a)).toArray

structure Script where
  bytes : ByteArray
  deriving Inhabited

instance : BEq Script := ⟨fun a b => a.bytes == b.bytes⟩

namespace Script

def empty : Script := ⟨.empty⟩

/-- `Script(hex:)`: whitespace-trimmed, an optional `0x` prefix, non-empty and even. -/
def ofHex? (s : String) : Option Script :=
  let t := Wire.trimWhitespace s
  let t := if t.startsWith "0x" then String.ofList (t.toList.drop 2) else t
  (Wire.bytesOfHexChars t.toList).map Script.mk

def hex (s : Script) : String := Winnow.hex s.bytes

namespace Op
def zero : UInt8 := 0x00
def pushData1 : UInt8 := 0x4c
def pushData2 : UInt8 := 0x4d
def pushData4 : UInt8 := 0x4e
def oneNegate : UInt8 := 0x4f
def checkSig : UInt8 := 0xac
def checkSigAdd : UInt8 := 0xba
def numEqual : UInt8 := 0x9c
def numEqualVerify : UInt8 := 0x9d
def checkSigVerify : UInt8 := 0xad
/-- OP_CHECKSEQUENCEVERIFY (BIP112). -/
def checkSequenceVerify : UInt8 := 0xb2
def greaterThanOrEqual : UInt8 := 0xa2
/-- OP_1 through OP_16 (0x51…0x60); the Swift original traps outside 1…16. -/
def n (value : Nat) : UInt8 := 0x50 + value.toUInt8
end Op

def appendOpcode (s : Script) (opcode : UInt8) : Script := ⟨s.bytes.push opcode⟩

/-- A data push with the minimal PUSHDATA encoding. -/
def appendPush (s : Script) (data : ByteArray) : Script :=
  let c := data.size
  let head :=
    if c < 0x4c then ByteArray.mk #[c.toUInt8]
    else if c ≤ 0xFF then ByteArray.mk #[Op.pushData1, c.toUInt8]
    else if c ≤ 0xFFFF then ByteArray.mk #[Op.pushData2] ++ u16LE c.toUInt16
    else ByteArray.mk #[Op.pushData4] ++ u32LE c.toUInt32
  ⟨s.bytes ++ head ++ data⟩

/-- OP_0 / OP_1…OP_16 for 0…16, otherwise a minimally-encoded script number push (non-negative only;
the Swift original traps on a negative value). -/
def appendScriptNumber (s : Script) (value : Nat) : Script :=
  if value == 0 then s.appendOpcode Op.zero
  else if value ≤ 16 then s.appendOpcode (Op.n value)
  else Id.run do
    let mut v := value
    let mut enc := ByteArray.empty
    while v > 0 do
      enc := enc.push (v % 256).toUInt8
      v := v / 256
    if enc[enc.size - 1]! &&& 0x80 != 0 then enc := enc.push 0
    return s.appendPush enc

/-- `Script.build`: run a body over the empty script. -/
def build (body : Script → Script) : Script := body empty

end Script
end Winnow
