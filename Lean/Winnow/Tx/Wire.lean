import Winnow.Bytes

/-! # Wire: the byte-level helpers of the P2P wire format

Port of `Sources/WalletCore/Network/Protocol/Wire.swift`: `WireError`, the sequential little-endian
`ByteReader` (CompactSize refusing non-minimal encodings, bounded var data, UTF-8 strings decoded the
way Swift's `String(decoding:as:)` does), the `Data.append…` writers, and `Data(hex:)` / `Data.hex`.

`ByteReader.M` is the reader as a state monad; `ByteReader.M.run` hands back the value and the reader
(its offset says how much was consumed), so another module can parse a prefix and continue. -/

namespace Winnow

/-- Errors thrown while decoding Bitcoin P2P wire data (`WireError`). -/
inductive WireError where
  | truncated (expected remaining : Nat)
  | trailingBytes (count : Nat)
  | invalidVarInt
  | malformed (reason : String)
  deriving Repr, BEq, Inhabited

def WireError.name : WireError → String
  | .truncated .. => "truncated"
  | .trailingBytes _ => "trailingBytes"
  | .invalidVarInt => "invalidVarInt"
  | .malformed _ => "malformed"

/-- Sequential little-endian reader over a byte buffer. -/
structure ByteReader where
  data : ByteArray
  offset : Nat := 0
  deriving Inhabited

namespace ByteReader

def init (data : ByteArray) : ByteReader := ⟨data, 0⟩

def remaining (r : ByteReader) : Nat := r.data.size - r.offset

/-- A computation over a reader, failing with `ε` (a `WireError` unless lifted). -/
abbrev M (α : Type) := StateT ByteReader (Except WireError) α

def M.run {α} (m : M α) (r : ByteReader) : Except WireError (α × ByteReader) := StateT.run m r

/-- Run over a whole buffer, requiring every byte to be consumed (`requireEnd`). -/
def M.runAll {α} (m : M α) (data : ByteArray) : Except WireError α := do
  let (a, r) ← m.run (init data)
  if r.remaining != 0 then throw (.trailingBytes r.remaining)
  pure a

def remainingM : M Nat := do return (← get).remaining

def readBytes (count : Nat) : M ByteArray := do
  let r ← get
  if r.remaining < count then throw (.truncated count r.remaining)
  set { r with offset := r.offset + count }
  return r.data.extract r.offset (r.offset + count)

def readUInt8 : M UInt8 := do
  let r ← get
  if r.remaining < 1 then throw (.truncated 1 r.remaining)
  set { r with offset := r.offset + 1 }
  return r.data.get! r.offset

def readLE (n : Nat) : M UInt64 := do
  let b ← readBytes n
  return Winnow.readLE b 0 n

def readUInt16 : M UInt16 := return (← readLE 2).toUInt16
def readUInt32 : M UInt32 := return (← readLE 4).toUInt32
def readUInt64 : M UInt64 := readLE 8
def readInt32 : M Int32 := return (← readUInt32).toInt32
def readInt64 : M Int64 := return (← readUInt64).toInt64

/-- CompactSize; a wider prefix than the value needs is refused (`invalidVarInt`). -/
def readVarInt : M UInt64 := do
  let first ← readUInt8
  if first < 0xFD then return first.toUInt64
  else if first == 0xFD then
    let v := (← readUInt16).toUInt64
    if v < 0xFD then throw .invalidVarInt
    return v
  else if first == 0xFE then
    let v := (← readUInt32).toUInt64
    if v < 0x1_0000 then throw .invalidVarInt
    return v
  else
    let v ← readUInt64
    if v < 0x1_0000_0000 then throw .invalidVarInt
    return v

/-- CompactSize-prefixed bytes; a length above `maxLength` is `malformed` before it is `truncated`. -/
def readVarData (maxLength : Nat := 4_000_000) : M ByteArray := do
  let length ← readVarInt
  if length.toNat > maxLength then throw (.malformed s!"var data length {length} exceeds {maxLength}")
  readBytes length.toNat

/-- `String(decoding:as: UTF8.self)`: ill-formed sequences become U+FFFD, one per maximal subpart. -/
def decodeUTF8Lossy (b : ByteArray) : String := Id.run do
  let n := b.size
  let cont (i : Nat) (lo hi : UInt8) : Bool := i < n && lo ≤ b[i]! && b[i]! ≤ hi
  let mut out := ""
  let mut i := 0
  while i < n do
    let b0 := b[i]!
    if b0 < 0x80 then
      out := out.push (Char.ofNat b0.toNat); i := i + 1
    else
      -- (sequence length, allowed range of the second byte)
      let spec : Option (Nat × UInt8 × UInt8) :=
        if 0xC2 ≤ b0 && b0 ≤ 0xDF then some (2, 0x80, 0xBF)
        else if b0 == 0xE0 then some (3, 0xA0, 0xBF)
        else if b0 == 0xED then some (3, 0x80, 0x9F)
        else if 0xE1 ≤ b0 && b0 ≤ 0xEF then some (3, 0x80, 0xBF)
        else if b0 == 0xF0 then some (4, 0x90, 0xBF)
        else if b0 == 0xF4 then some (4, 0x80, 0x8F)
        else if 0xF1 ≤ b0 && b0 ≤ 0xF3 then some (4, 0x80, 0xBF)
        else none
      match spec with
      | none => out := out.push '�'; i := i + 1
      | some (len, lo, hi) =>
        -- how many bytes of the sequence are well-formed so far
        let mut good := 1
        if cont (i + 1) lo hi then
          good := 2
          if len ≥ 3 && cont (i + 2) 0x80 0xBF then
            good := 3
            if len ≥ 4 && cont (i + 3) 0x80 0xBF then good := 4
        if good == len then
          let mask : Nat := if len == 2 then 0x1F else if len == 3 then 0x0F else 0x07
          let mut cp := b0.toNat &&& mask
          for k in [1:len] do cp := cp * 64 + (b[i + k]!.toNat &&& 0x3F)
          out := out.push (Char.ofNat cp)
          i := i + len
        else
          out := out.push '�'; i := i + good
  return out

/-- CompactSize-prefixed UTF-8 string. -/
def readVarString (maxLength : Nat := 1_000) : M String := do
  return decodeUTF8Lossy (← readVarData maxLength)

/-- Throws `trailingBytes` unless the buffer was consumed exactly. -/
def requireEnd : M Unit := do
  let r ← get
  if r.remaining != 0 then throw (.trailingBytes r.remaining)

end ByteReader

/-! ## Writing (`Data.append…`) -/

namespace Wire

def appendUInt8 (d : ByteArray) (v : UInt8) : ByteArray := d.push v
def appendUInt16 (d : ByteArray) (v : UInt16) : ByteArray := d ++ u16LE v
def appendUInt32 (d : ByteArray) (v : UInt32) : ByteArray := d ++ u32LE v
def appendUInt64 (d : ByteArray) (v : UInt64) : ByteArray := d ++ u64LE v
def appendInt32 (d : ByteArray) (v : Int32) : ByteArray := d ++ i32LE v
def appendInt64 (d : ByteArray) (v : Int64) : ByteArray := d ++ i64LE v
def appendCompactSize (d : ByteArray) (v : UInt64) : ByteArray := d ++ compactSize v
def appendVarData (d : ByteArray) (b : ByteArray) : ByteArray := d ++ varBytes b
def appendVarString (d : ByteArray) (s : String) : ByteArray := appendVarData d s.toUTF8

/-- `CharacterSet.whitespacesAndNewlines`: general category Z*, U+0009–U+000D, U+0085 and U+200B (as Foundation has it). -/
def isWhitespaceOrNewline (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 || n == 0x1680 ||
  (0x2000 ≤ n && n ≤ 0x200B) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

def trimWhitespace (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWhitespaceOrNewline).reverse.dropWhile isWhitespaceOrNewline).reverse

/-- `UInt8(_:radix: 16)` on a two-character string: an optional sign (`-` only before a zero value). -/
def parseHexPair (a b : Char) : Option UInt8 :=
  match Secp.hexDigit? a, Secp.hexDigit? b with
  | some x, some y => some (UInt8.ofNat (16 * x + y))
  | none, some y => if a == '+' then some (UInt8.ofNat y) else if a == '-' && y == 0 then some 0 else none
  | _, _ => none

/-- Hex digits (whitespace-trimmed, non-empty, even length) to bytes; shared by `Data(hex:)` and
`Script(hex:)`. -/
def bytesOfHexChars (cs : List Char) : Option ByteArray := Id.run do
  if cs.length % 2 != 0 || cs.isEmpty then return none
  let mut out := ByteArray.emptyWithCapacity (cs.length / 2)
  let mut rest := cs
  while true do
    match rest with
    | a :: b :: tl =>
      match parseHexPair a b with
      | some v => out := out.push v; rest := tl
      | none => return none
    | _ => break
  return some out

/-- `Data(hex:)`: raw byte order. -/
def dataOfHex? (s : String) : Option ByteArray := bytesOfHexChars (trimWhitespace s).toList

/-- `Data.hex`: lowercase, raw byte order. -/
def dataHex (d : ByteArray) : String := hex d

end Wire
end Winnow
