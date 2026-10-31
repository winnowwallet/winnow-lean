/-! # Bytes, hex and big-endian integers -/

namespace Secp

/-- A big-endian byte string as a number. -/
def fromBE (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `n mod 2^256` as 32 big-endian bytes. -/
def toBE32 (n : Nat) : ByteArray :=
  ⟨(List.range 32).toArray.map fun i => UInt8.ofNat (n / 2^(8 * (31 - i)))⟩

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def ofHex? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList
  if cs.length % 2 != 0 then return none
  let mut out := ByteArray.empty
  let mut rest := cs
  while true do
    match rest with
    | a :: b :: tl =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => out := out.push (UInt8.ofNat (16 * x + y)); rest := tl
      | _, _ => return none
    | _ => break
  return some out

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList
  String.ofList (b.toList.flatMap fun x => [d[x.toNat / 16]!, d[x.toNat % 16]!])

end Secp
