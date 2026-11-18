/-! # A signature as Bitcoin's scripts want it written: DER (BIP 66)

`der` writes the 64 bytes `r`, `s` of an ECDSA signature the one way BIP 66 allows, and `parseDer` reads
that form and no other. Bytes in and bytes out: nothing here knows the curve. -/

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
most 70 bytes, so every length fits in one byte. -/
def der (signature : ByteArray) : ByteArray :=
  let r := derInteger (signature.extract 0 32)
  let s := derInteger (signature.extract 32 64)
  ByteArray.mk #[0x30, (r.size + s.size).toUInt8] ++ r ++ s

/-- One DER integer at `offset`, as BIP66 allows it: the tag, a length of at least one, not negative, no zero
byte in front that the sign does not need, and a value of at most 32 bytes. The value as 32 bytes and the
offset just past it. -/
def parseDerInteger (b : ByteArray) (offset : Nat) : Option (ByteArray × Nat) := do
  guard (offset + 2 ≤ b.size && b[offset]! == 0x02)
  let length := b[offset + 1]!.toNat
  guard (length ≥ 1 && offset + 2 + length ≤ b.size)
  let body := b.extract (offset + 2) (offset + 2 + length)
  guard (body[0]! &&& 0x80 == 0)
  if length > 1 && body[0]! == 0 then guard (body[1]! &&& 0x80 != 0)
  let digits := if body[0]! == 0 then body.extract 1 length else body
  guard (digits.size ≤ 32)
  return (ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits, offset + 2 + length)

/-- The 64 bytes `r`, `s` of a signature in DER, read strictly (BIP66): exactly the form `der` writes, and
nothing after it. -/
def parseDer (b : ByteArray) : Option ByteArray := do
  guard (b.size ≥ 8 && b.size ≤ 72 && b[0]! == 0x30 && b[1]!.toNat == b.size - 2)
  let (r, afterR) ← parseDerInteger b 2
  let (s, afterS) ← parseDerInteger b afterR
  guard (afterS == b.size)
  return r ++ s

end Secp.Ecdsa
