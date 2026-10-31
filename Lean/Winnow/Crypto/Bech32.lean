import Winnow.Bytes

/-! # Bech32 / Bech32m (BIP173 / BIP350) and segwit addresses -/

namespace Winnow

inductive Bech32Error where
  | invalidCharacter | mixedCase | missingSeparator | emptyHRP | invalidChecksum | tooLong
  | invalidDataValue | invalidWitnessVersion | invalidProgramLength | invalidPadding | invalidHRP
  deriving Repr, BEq

def Bech32Error.name : Bech32Error → String
  | .invalidCharacter => "invalidCharacter" | .mixedCase => "mixedCase"
  | .missingSeparator => "missingSeparator" | .emptyHRP => "emptyHRP"
  | .invalidChecksum => "invalidChecksum" | .tooLong => "tooLong"
  | .invalidDataValue => "invalidDataValue" | .invalidWitnessVersion => "invalidWitnessVersion"
  | .invalidProgramLength => "invalidProgramLength" | .invalidPadding => "invalidPadding"
  | .invalidHRP => "invalidHRP"

inductive Bech32Encoding where
  | bech32
  | bech32m
  deriving Repr, BEq

namespace Bech32

def checksumConstant : Bech32Encoding → UInt32
  | .bech32 => 1
  | .bech32m => 0x2bc830a3

def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

def polymod (values : List UInt8) : UInt32 := Id.run do
  let gen : Array UInt32 := #[0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
  let mut chk : UInt32 := 1
  for v in values do
    let top := chk >>> 25
    chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v.toUInt32
    for i in [0:5] do
      if (top >>> i.toUInt32) &&& 1 == 1 then chk := chk ^^^ gen[i]!
  return chk

def hrpExpand (hrp : List UInt8) : List UInt8 := hrp.map (fun b : UInt8 => b >>> 5) ++ [(0 : UInt8)] ++ hrp.map (fun b : UInt8 => b &&& 31)

def asciiLower (c : Char) : Char := if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def encode (hrp : String) (data : List UInt8) (enc : Bech32Encoding) (maxLength : Nat := 90) :
    Except Bech32Error String := do
  if hrp.isEmpty || !hrp.toUTF8.toList.all (fun b => 33 ≤ b ∧ b ≤ 126) then throw .emptyHRP
  let hrpBytes := (String.ofList (hrp.toList.map asciiLower)).toUTF8.toList
  let mod := polymod (hrpExpand hrpBytes ++ data ++ List.replicate 6 0) ^^^ checksumConstant enc
  let check := (List.range 6).map fun i => ((mod >>> (5 * (5 - i)).toUInt32) &&& 31).toUInt8
  let combined := data ++ check
  if hrpBytes.length + 1 + combined.length > maxLength then throw .tooLong
  return String.ofList (hrpBytes.map (fun b => Char.ofNat b.toNat) ++ ['1'] ++ combined.map (fun v => charset[v.toNat]!))

def decode (s : String) (maxLength : Nat := 90) : Except Bech32Error (String × List UInt8 × Bech32Encoding) := do
  let cs := s.toList
  if cs.length > maxLength then throw .tooLong
  if cs.any (fun c => 'A' ≤ c ∧ c ≤ 'Z') && cs.any (fun c => 'a' ≤ c ∧ c ≤ 'z') then throw .mixedCase
  let lowered := cs.map asciiLower
  unless lowered.all (fun c => 33 ≤ c.toNat ∧ c.toNat ≤ 126) do throw .invalidCharacter
  let some sep := (lowered.zipIdx.filter (·.1 == '1')).getLast?.map (·.2) | throw .missingSeparator
  let hrp := lowered.take sep
  if hrp.isEmpty then throw .emptyHRP
  let dataPart := lowered.drop (sep + 1)
  if dataPart.length < 6 then throw .invalidChecksum
  let mut values : List UInt8 := []
  for c in dataPart do
    let some v := charset.idxOf? c | throw .invalidCharacter
    values := values ++ [v.toUInt8]
  let hrpBytes := (String.ofList hrp).toUTF8.toList
  let k := polymod (hrpExpand hrpBytes ++ values)
  let enc ← if k == checksumConstant .bech32 then pure Bech32Encoding.bech32
    else if k == checksumConstant .bech32m then pure .bech32m else throw .invalidChecksum
  return (String.ofList hrp, values.take (values.length - 6), enc)

end Bech32

namespace SegwitAddress

def convertBits (input : List UInt8) (frm to : Nat) (pad : Bool) : Except Bech32Error (List UInt8) := do
  let mut acc := 0
  let mut bits := 0
  let mut out : Array UInt8 := #[]
  let maxV := 2 ^ to - 1
  let maxAcc := 2 ^ (frm + to - 1) - 1
  for v in input do
    if v.toNat >>> frm != 0 then throw .invalidDataValue
    acc := ((acc <<< frm) ||| v.toNat) &&& maxAcc
    bits := bits + frm
    while bits ≥ to do
      bits := bits - to
      out := out.push ((acc >>> bits) &&& maxV).toUInt8
  if pad then
    if bits > 0 then out := out.push ((acc <<< (to - bits)) &&& maxV).toUInt8
  else
    if bits ≥ frm then throw .invalidPadding
    if (acc <<< (to - bits)) &&& maxV != 0 then throw .invalidPadding
  return out.toList

def encode (hrp : String) (version : Nat) (program : ByteArray) : Except Bech32Error String := do
  if version > 16 then throw .invalidWitnessVersion
  if program.size < 2 || program.size > 40 then throw .invalidProgramLength
  if version == 0 && program.size != 20 && program.size != 32 then throw .invalidProgramLength
  let data := version.toUInt8 :: (← convertBits program.toList 8 5 true)
  Bech32.encode hrp data (if version == 0 then .bech32 else .bech32m)

def decode (s : String) (expectedHRP : Option String := none) : Except Bech32Error (Nat × ByteArray) := do
  let (hrp, values, enc) ← Bech32.decode s
  if let some e := expectedHRP then if hrp != e then throw .invalidHRP
  let some first := values.head? | throw .invalidWitnessVersion
  if first > 16 then throw .invalidWitnessVersion
  let program ← convertBits values.tail 5 8 false
  if program.length < 2 || program.length > 40 then throw .invalidProgramLength
  if first == 0 then
    if enc != .bech32 then throw .invalidChecksum
    if program.length != 20 && program.length != 32 then throw .invalidProgramLength
  else if enc != .bech32m then throw .invalidChecksum
  return (first.toNat, ⟨program.toArray⟩)

end SegwitAddress
end Winnow
