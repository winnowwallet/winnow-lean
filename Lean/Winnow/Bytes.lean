import Secp.Bytes

/-! # Bytes: hex, fixed-width integers, CompactSize, and a reader

`ByteArray` is Winnow's `Data`. Integers are written little-endian unless the name says `BE`. -/

namespace Winnow

abbrev Bytes := ByteArray

def hex (b : ByteArray) : String := Secp.toHex b
def ofHex? (s : String) : Option ByteArray := Secp.ofHex? s
def ofHex! (s : String) : ByteArray := (ofHex? s).getD .empty

def ByteArray.ofList (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

def u16LE (n : UInt16) : ByteArray := ⟨#[n.toUInt8, (n >>> 8).toUInt8]⟩
def u32LE (n : UInt32) : ByteArray := ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩
def u64LE (n : UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 8
  for i in [0:8] do b := b.push (n >>> (8 * i).toUInt64).toUInt8
  return b
def u32BE (n : UInt32) : ByteArray := ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩
def i32LE (n : Int32) : ByteArray := u32LE n.toUInt32
def i64LE (n : Int64) : ByteArray := u64LE n.toUInt64

/-- Bitcoin's CompactSize (varint). -/
def compactSize (n : UInt64) : ByteArray :=
  if n < 0xfd then ⟨#[n.toUInt8]⟩
  else if n ≤ 0xffff then ⟨#[0xfd]⟩ ++ u16LE n.toUInt16
  else if n ≤ 0xffffffff then ⟨#[0xfe]⟩ ++ u32LE n.toUInt32
  else ⟨#[0xff]⟩ ++ u64LE n

/-- A length-prefixed byte string. -/
def varBytes (b : ByteArray) : ByteArray := compactSize b.size.toUInt64 ++ b

def readLE (b : ByteArray) (off n : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:n] do v := v ||| ((b.get! (off + i)).toUInt64 <<< (8 * i).toUInt64)
  return v

def readBE (b : ByteArray) (off n : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:n] do v := (v <<< 8) ||| (b.get! (off + i)).toUInt64
  return v

def ByteArray.reverse (b : ByteArray) : ByteArray := ⟨b.data.reverse⟩

def ByteArray.take (b : ByteArray) (n : Nat) : ByteArray := b.extract 0 n
def ByteArray.drop (b : ByteArray) (n : Nat) : ByteArray := b.extract n b.size

/-- Constant-shape equality of two byte strings. -/
def ByteArray.eq (a b : ByteArray) : Bool := a.data == b.data

instance : BEq ByteArray := ⟨ByteArray.eq⟩

/-! ## Reading -/

/-- A cursor over bytes; every read fails with a message rather than panicking. -/
abbrev Reader := StateT Nat (ExceptT String (ReaderM ByteArray))

namespace Reader

def run {α} (r : Reader α) (b : ByteArray) : Except String (α × Nat) := ((StateT.run r 0).run).run b

/-- Run and require that every byte was consumed. -/
def runAll {α} (r : Reader α) (b : ByteArray) (what : String := "data") : Except String α := do
  let (a, pos) ← r.run b
  if pos != b.size then throw s!"{what}: {b.size - pos} trailing bytes"
  pure a

def remaining : Reader Nat := do return (← read).size - (← get)

def bytes (n : Nat) : Reader ByteArray := do
  let b ← read
  let pos ← get
  if pos + n > b.size then throw s!"unexpected end of data (need {n} bytes at {pos}, have {b.size - pos})"
  set (pos + n)
  return b.extract pos (pos + n)

def u8 : Reader UInt8 := do
  let b ← bytes 1
  return b.get! 0

def le (n : Nat) : Reader UInt64 := do
  let b ← bytes n
  return readLE b 0 n

def u16 : Reader UInt16 := return (← le 2).toUInt16
def u32 : Reader UInt32 := return (← le 4).toUInt32
def u64 : Reader UInt64 := le 8
def i32 : Reader Int32 := return (← u32).toInt32
def i64 : Reader Int64 := return (← u64).toInt64

/-- CompactSize, rejecting non-canonical encodings (as Bitcoin Core does). -/
def compact : Reader UInt64 := do
  let tag ← u8
  if tag < 0xfd then return tag.toUInt64
  else if tag == 0xfd then
    let v ← le 2
    if v < 0xfd then throw "non-canonical CompactSize"
    return v
  else if tag == 0xfe then
    let v ← le 4
    if v ≤ 0xffff then throw "non-canonical CompactSize"
    return v
  else
    let v ← le 8
    if v ≤ 0xffffffff then throw "non-canonical CompactSize"
    return v

def varBytes (max : Nat := 4_000_000) : Reader ByteArray := do
  let n ← compact
  if n.toNat > max then throw s!"length {n} above {max}"
  bytes n.toNat

end Reader
end Winnow
