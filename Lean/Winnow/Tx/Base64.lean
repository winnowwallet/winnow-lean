import Winnow.Bytes

/-! # Base64 as Foundation does it

`Data.base64EncodedString()` (standard alphabet, `=` padding) and `Data(base64Encoded:)`, which PSBT's
text form goes through. Foundation's decoder is laxer than RFC 4648, and this mirrors it as measured
(every string over `{/, B, Q, =, *}` up to 9 characters, and random PSBT texts):

* the empty string decodes to nothing; any other string shorter than 4 characters is refused;
* the text is read in groups of 4. A group of 4 alphabet characters gives 3 bytes. The first group that
  contains `=` must be `xx==` (1 byte), `xxx=` (2 bytes), `xx=x` (2 bytes: the first byte and the 6-bit
  value of the last character — the middle byte is dropped), or `====` (one zero byte when it is the
  first group, nothing otherwise); everything after it must be `=`;
* when no group contains `=`, the 1–3 characters after the last group must all be `=`;
* any other character (whitespace included) refuses the text. Non-zero padding bits are accepted. -/

namespace Winnow.Base64

def alphabet : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

def encode (d : ByteArray) : String := Id.run do
  let a := alphabet.toList.toArray
  let mut out := ""
  let mut i := 0
  while i + 3 ≤ d.size do
    let n := (d[i]!.toNat <<< 16) ||| (d[i+1]!.toNat <<< 8) ||| d[i+2]!.toNat
    out := out.push a[n >>> 18]! |>.push a[(n >>> 12) &&& 63]! |>.push a[(n >>> 6) &&& 63]! |>.push a[n &&& 63]!
    i := i + 3
  let rest := d.size - i
  if rest == 1 then
    let n := d[i]!.toNat <<< 16
    out := out.push a[n >>> 18]! |>.push a[(n >>> 12) &&& 63]! |>.push '=' |>.push '='
  else if rest == 2 then
    let n := (d[i]!.toNat <<< 16) ||| (d[i+1]!.toNat <<< 8)
    out := out.push a[n >>> 18]! |>.push a[(n >>> 12) &&& 63]! |>.push a[(n >>> 6) &&& 63]! |>.push '='
  return out

def value? (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- `Data(base64Encoded:)` (see the module note for the exact acceptance rule). -/
def decode? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  if 0 < n && n < 4 then return none
  let mut out := ByteArray.emptyWithCapacity (n / 4 * 3)
  let mut i := 0
  let allPad (from_ : Nat) : Bool := (cs.extract from_ n).all (· == '=')
  while i + 4 ≤ n do
    let c0 := cs[i]!; let c1 := cs[i+1]!; let c2 := cs[i+2]!; let c3 := cs[i+3]!
    match value? c0, value? c1, value? c2, value? c3 with
    | some x0, some x1, some x2, some x3 =>
      out := out.push ((x0 <<< 2 ||| x1 >>> 4) &&& 255).toUInt8
        |>.push ((x1 <<< 4 ||| x2 >>> 2) &&& 255).toUInt8 |>.push ((x2 <<< 6 ||| x3) &&& 255).toUInt8
      i := i + 4
    | _, _, _, _ =>
      if c0 == '=' && c1 == '=' && c2 == '=' && c3 == '=' then
        if i == 0 then out := out.push 0
      else
        match value? c0, value? c1 with
        | some x0, some x1 =>
          let b0 := ((x0 <<< 2 ||| x1 >>> 4) &&& 255).toUInt8
          if c2 == '=' && c3 == '=' then out := out.push b0
          else if c2 == '=' then
            match value? c3 with
            | some x3 => out := (out.push b0).push x3.toUInt8
            | none => return none
          else if c3 == '=' then
            match value? c2 with
            | some x2 => out := (out.push b0).push ((x1 <<< 4 ||| x2 >>> 2) &&& 255).toUInt8
            | none => return none
          else return none
        | _, _ => return none
      return if allPad (i + 4) then some out else none
  return if allPad i then some out else none

end Winnow.Base64
