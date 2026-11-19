/-! # A signature as Bitcoin's scripts want it written: DER (BIP 66)

`der` writes the 64 bytes `r`, `s` of an ECDSA signature the one way BIP 66 allows, and `parseDer` reads
that form and no other. Bytes in and bytes out: nothing here knows the curve, and every byte read is
in-bounds by construction. -/

namespace Secp.Ecdsa

/-- A number's 32 bytes as DER writes an integer: the tag, the length, and the number with no zero bytes in
front, but for one put back where the first bit would otherwise read as a minus sign. -/
def derInteger (number : ByteArray) : ByteArray :=
  let digits := number.toList.dropWhile (· == 0)
  let body := match digits with
    | [] => [0]
    | first :: _ => if first ≥ 0x80 then 0 :: digits else digits
  ByteArray.mk (#[0x02, body.length.toUInt8] ++ body.toArray)

/-- The signature `r`, `s` (64 bytes) in DER, as BIP66 lays it down: a sequence of the two integers. At
most 72 bytes, so every length fits in one byte. -/
def der (signature : ByteArray) : ByteArray :=
  let r := derInteger (signature.extract 0 32)
  let s := derInteger (signature.extract 32 64)
  ByteArray.mk #[0x30, (r.size + s.size).toUInt8] ++ r ++ s

/-- One DER integer at `offset`, as BIP66 allows it: the tag, a length of at least one, not negative, no zero
byte in front that the sign does not need, and a value of at most 32 bytes. The value as 32 bytes and the
offset just past it. -/
def parseDerInteger (b : ByteArray) (offset : Nat) : Option (ByteArray × Nat) :=
  if h1 : offset + 2 ≤ b.size then do
    guard (b[offset]'(by omega) == 0x02)
    let length := (b[offset + 1]'(by omega)).toNat
    if h2 : 1 ≤ length ∧ offset + 2 + length ≤ b.size then
      let b0 := b[offset + 2]'(by omega)
      guard (b0 &&& 0x80 == 0)
      if h3 : 1 < length then
        if b0 == 0 then guard ((b[offset + 3]'(by omega)) &&& 0x80 != 0)
      let digits := if b0 == 0 then b.extract (offset + 3) (offset + 2 + length)
                    else b.extract (offset + 2) (offset + 2 + length)
      guard (digits.size ≤ 32)
      return (ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits, offset + 2 + length)
    else none
  else none

/-- The 64 bytes `r`, `s` of a signature in DER, read strictly (BIP66): exactly the form `der` writes, and
nothing after it. -/
def parseDer (b : ByteArray) : Option ByteArray :=
  if h : 8 ≤ b.size ∧ b.size ≤ 72 then do
    guard (b[0]'(by omega) == 0x30 && (b[1]'(by omega)).toNat == b.size - 2)
    let (r, afterR) ← parseDerInteger b 2
    let (s, afterS) ← parseDerInteger b afterR
    guard (afterS == b.size)
    return r ++ s
  else none

end Secp.Ecdsa
