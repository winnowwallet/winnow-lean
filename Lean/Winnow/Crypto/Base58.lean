import Winnow.Crypto.Sha2

/-! # Base58 and Base58Check (BIP32 extended keys, legacy addresses) -/

namespace Winnow

inductive Base58Error where
  | invalidCharacter (c : Char)
  | invalidChecksum
  | invalidLength
  deriving Repr, BEq

def Base58Error.name : Base58Error → String
  | .invalidCharacter _ => "invalidCharacter"
  | .invalidChecksum => "invalidChecksum"
  | .invalidLength => "invalidLength"

namespace Base58

def alphabet : String := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def alphabetBytes : ByteArray := alphabet.toUTF8

def encode (data : ByteArray) : String := Id.run do
  let zeros := (data.toList.takeWhile (· == 0)).length
  let mut digits : Array Nat := #[]
  for byte in data.toList.drop zeros do
    let mut carry := byte.toNat
    for i in [0:digits.size] do
      carry := carry + digits[i]! * 256
      digits := digits.set! i (carry % 58)
      carry := carry / 58
    while carry > 0 do
      digits := digits.push (carry % 58)
      carry := carry / 58
  let mut out := String.ofList (List.replicate zeros '1')
  for d in digits.reverse do out := out.push (alphabet.toList[d]!)
  return out

def decode (s : String) : Except Base58Error ByteArray := do
  let cs := s.toList
  let ones := (cs.takeWhile (· == '1')).length
  let mut bytes : Array Nat := #[]
  for c in cs.drop ones do
    let some v := alphabet.toList.idxOf? c | throw (.invalidCharacter c)
    let mut carry := v
    for i in [0:bytes.size] do
      carry := carry + bytes[i]! * 58
      bytes := bytes.set! i (carry % 256)
      carry := carry / 256
    while carry > 0 do
      bytes := bytes.push (carry % 256)
      carry := carry / 256
  return ⟨(Array.replicate ones (0 : UInt8)) ++ bytes.reverse.map (·.toUInt8)⟩

end Base58

namespace Base58Check

def encode (payload : ByteArray) : String := Base58.encode (payload ++ (sha256d payload).extract 0 4)

def decode (s : String) : Except Base58Error ByteArray := do
  let d ← Base58.decode s
  if d.size < 4 then throw .invalidLength
  let payload := d.extract 0 (d.size - 4)
  unless (sha256d payload).extract 0 4 == d.extract (d.size - 4) d.size do throw .invalidChecksum
  return payload

end Base58Check
end Winnow
