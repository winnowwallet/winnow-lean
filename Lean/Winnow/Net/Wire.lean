import Winnow.Bytes
import Winnow.Tx.Wire

/-! # Wire reading for the P2P protocol messages

The reader and its errors are the Tx area's port of `Network/Protocol/Wire.swift` (`Winnow.ByteReader`,
`Winnow.WireError`), shared so that a message embedding a transaction parses it in the same pass. This
module gives Net short names for it. -/

namespace Winnow.Net

abbrev WireError := Winnow.WireError
abbrev Wire := ByteReader.M

namespace Wire

/-- Run over the whole buffer from the start, without requiring it to be consumed. -/
def eval {α} (r : Wire α) (b : ByteArray) : Except WireError α := (·.1) <$> ByteReader.M.run r (ByteReader.init b)
/-- Run, returning the value and the offset reached. -/
def run {α} (r : Wire α) (b : ByteArray) : Except WireError (α × Nat) :=
  (fun (a, rd) => (a, rd.offset)) <$> ByteReader.M.run r (ByteReader.init b)

def remaining : Wire Nat := ByteReader.remainingM
def offset : Wire Nat := do return (← get).offset
def bytes (n : Nat) : Wire ByteArray := ByteReader.readBytes n
def u8 : Wire UInt8 := ByteReader.readUInt8
def u16 : Wire UInt16 := ByteReader.readUInt16
def u32 : Wire UInt32 := ByteReader.readUInt32
def u64 : Wire UInt64 := ByteReader.readUInt64
def i32 : Wire Int32 := ByteReader.readInt32
def i64 : Wire Int64 := ByteReader.readInt64
def varInt : Wire UInt64 := ByteReader.readVarInt
def varData (maxLength : Nat := 4_000_000) : Wire ByteArray := ByteReader.readVarData maxLength
def varString (maxLength : Nat := 1_000) : Wire String := ByteReader.readVarString maxLength
def requireEnd : Wire Unit := ByteReader.requireEnd

end Wire

def utf8Lossy (b : ByteArray) : String := ByteReader.decodeUTF8Lossy b

/-! ## Writing (the `Data.append…` helpers) -/

def varString (s : String) : ByteArray := varBytes s.toUTF8

/-- Swift's `UInt32(String)`: an optional `+`/`-` sign, then ASCII digits; `-` only for zero. -/
def parseUInt32? (s : String) : Option UInt32 :=
  let cs := s.toList
  let (neg, digits) := match cs with
    | '+' :: t => (false, t)
    | '-' :: t => (true, t)
    | t => (false, t)
  if digits.isEmpty || !digits.all Char.isDigit then none
  else
    let v := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if neg then (if v == 0 then some 0 else none)
    else if v > 0xFFFFFFFF then none else some v.toUInt32

/-- `Data(displayHex:)` and `displayHex`: hashes are shown byte-reversed. -/
def ofDisplayHex! (s : String) : ByteArray := Winnow.ByteArray.reverse (ofHex! s)
def displayHex (b : ByteArray) : String := hex (Winnow.ByteArray.reverse b)

end Winnow.Net
