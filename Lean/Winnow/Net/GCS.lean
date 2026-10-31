import Winnow.Crypto
import Std.Data.HashSet

/-! # BIP158 Golomb-coded sets (`Crypto/GCSFilter.swift`)

Basic filters use P = 19, M = 784931, keyed with SipHash by the first 16 bytes of the block hash.
Every hot loop runs on `UInt64` values and bit offsets over the encoded `ByteArray`. -/

namespace Winnow.Net

inductive GCSError where
  | emptyKey
  | invalidParameters
  | tooManyElements (n : UInt32)
  | encodedFilterTooLarge (n : Nat)
  | truncatedEncoding
  | nonCanonicalEncoding
  | decodedValueOverflow
  deriving Repr, BEq, Inhabited

def GCSError.name : GCSError → String
  | .emptyKey => "emptyKey"
  | .invalidParameters => "invalidParameters"
  | .tooManyElements _ => "tooManyElements"
  | .encodedFilterTooLarge _ => "encodedFilterTooLarge"
  | .truncatedEncoding => "truncatedEncoding"
  | .nonCanonicalEncoding => "nonCanonicalEncoding"
  | .decodedValueOverflow => "decodedValueOverflow"

structure GCSFilter where
  p : UInt8
  m : UInt32
  /-- 16-byte SipHash key (k0 ‖ k1, little-endian). -/
  key : ByteArray
  /-- Number of items in the hashed set. -/
  n : UInt32
  /-- Golomb-Rice bitstream, without the N prefix. -/
  encoded : ByteArray
  deriving Inhabited

namespace GCSFilter

def defaultP : UInt8 := 19
def defaultM : UInt32 := 784_931
def maxElementCount : UInt32 := 1_000_000
def maxEncodedSize : Nat := 4_000_000

/-- High 64 bits of the 128-bit product (`multipliedFullWidth(by:).high`). -/
@[inline] def mulHi (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& 0xffffffff) + (p10 &&& 0xffffffff)
  p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)

@[inline] def keyWords (key : ByteArray) : UInt64 × UInt64 := (readLE key 0 8, readLE key 8 8)

/-- Bit `i` of the stream, most significant bit of each byte first. -/
@[inline] def bitAt (b : ByteArray) (i : Nat) : Bool :=
  ((b.get! (i >>> 3)) >>> (7 - (i &&& 7)).toUInt8) &&& 1 == 1

/-- Builds a filter from byte-string items (callers pre-filter them, as BIP158 blocks do). -/
def build (items : Array ByteArray) (p : UInt8 := defaultP) (m : UInt32 := defaultM) (key : ByteArray) :
    Except GCSError GCSFilter := do
  if key.size != 16 then throw .emptyKey
  let unique : Std.HashSet ByteArray := items.foldl (·.insert ·) {}
  let n := unique.size.toUInt32
  if n == 0 then return { p, m, key, n, encoded := .empty }
  let (k0, k1) := keyWords key
  let f := n.toUInt64 * m.toUInt64
  let hashed := (unique.toArray.map fun item => mulHi (sipHash k0 k1 item) f).qsort (· < ·)
  let pp := p.toUInt64
  let mask := (1 <<< pp) - 1
  let mut out := ByteArray.emptyWithCapacity (hashed.size * (p.toNat + 2) / 8 + 1)
  let mut cur : UInt8 := 0
  let mut used : Nat := 0 -- bits used in `cur`
  let mut last : UInt64 := 0
  for value in hashed do
    let delta := value - last
    last := value
    let quotient := delta >>> pp
    -- unary quotient (ones), then a zero
    let mut q := quotient
    while q > 0 do
      cur := cur ||| ((1 : UInt8) <<< (7 - used).toUInt8)
      used := used + 1
      if used == 8 then out := out.push cur; cur := 0; used := 0
      q := q - 1
    used := used + 1
    if used == 8 then out := out.push cur; cur := 0; used := 0
    let remainder := delta &&& mask
    let mut i := p.toNat
    while i > 0 do
      i := i - 1
      if (remainder >>> i.toUInt64) &&& 1 == 1 then cur := cur ||| ((1 : UInt8) <<< (7 - used).toUInt8)
      used := used + 1
      if used == 8 then out := out.push cur; cur := 0; used := 0
  if used > 0 then out := out.push cur
  return { p, m, key, n, encoded := out }

/-- Leading one bits of each byte value (a table, so unary runs are counted a byte at a time). -/
def leadingOnes : ByteArray := Id.run do
  let mut t := ByteArray.emptyWithCapacity 256
  for v in [0:256] do
    let mut c := 0
    let mut b := v
    while b &&& 0x80 != 0 do c := c + 1; b := (b <<< 1) &&& 0xff
    t := t.push c.toUInt8
  return t

/-- `k ≤ 63` bits at bit offset `pos`, most significant first; bytes past the end read as zero. -/
@[inline] def readBits (enc : ByteArray) (pos k : Nat) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  let mut i := pos
  let mut rem := k
  while rem > 0 do
    let off := i &&& 7
    let avail := 8 - off
    let take := if avail < rem then avail else rem
    let idx := i >>> 3
    let byte : UInt8 := if idx < enc.size then enc.get! idx else 0
    let chunk := ((byte >>> (avail - take).toUInt8).toUInt64) &&& ((1 <<< take.toUInt64) - 1)
    acc := (acc <<< take.toUInt64) ||| chunk
    i := i + take
    rem := rem - take
  return acc

/-- Length of the run of one bits starting at `pos`, stopping at the end of the stream. -/
@[inline] def onesRun (enc : ByteArray) (pos : Nat) : Nat := Id.run do
  let size := enc.size
  let mut i := pos
  let mut count := 0
  let mut done := false
  while !done do
    let idx := i >>> 3
    if idx ≥ size then done := true
    else
      let off := i &&& 7
      let shifted := (enc.get! idx) <<< off.toUInt8
      let c := (leadingOnes.get! shifted.toNat).toNat
      let avail := 8 - off
      if c ≥ avail then
        count := count + avail; i := i + avail
      else
        count := count + c; done := true
  return count

/-- The whole stream, validated once at the hostile-input boundary: every codeword (unary quotient,
then P remainder bits, refusing truncation exactly where the stream ran out and any overflow), then
canonical padding (fewer than 8 bits left, all zero). -/
def validateEncoding (p : UInt8) (n : UInt32) (encoded : ByteArray) : Except GCSError Unit := Id.run do
  if n == 0 then
    return if encoded.size != 0 then .error .nonCanonicalEncoding else .ok ()
  let minimumBits := n.toNat * (p.toNat + 1)
  if encoded.size * 8 < minimumBits then return .error .truncatedEncoding
  let total := encoded.size * 8
  let pn := p.toNat
  let pu := p.toUInt64
  let qmax : UInt64 := (0xFFFFFFFFFFFFFFFF : UInt64) >>> pu
  let mut pos := 0
  let mut value : UInt64 := 0
  for _ in [0:n.toNat] do
    let ones := onesRun encoded pos
    pos := pos + ones
    if pos ≥ total then return .error .truncatedEncoding
    pos := pos + 1
    if pos + pn > total then return .error .truncatedEncoding
    let quotient := ones.toUInt64
    if quotient > qmax then return .error .decodedValueOverflow
    let delta := (quotient <<< pu) ||| readBits encoded pos pn
    pos := pos + pn
    let next := value + delta
    if next < value then return .error .decodedValueOverflow
    value := next
  if total - pos ≥ 8 then return .error .nonCanonicalEncoding
  if total - pos > 0 && readBits encoded pos (total - pos) != 0 then return .error .nonCanonicalEncoding
  return .ok ()

/-- A filter received from a peer (`init(p:m:key:n:encoded:)`). -/
def decode (p : UInt8 := defaultP) (m : UInt32 := defaultM) (key : ByteArray) (n : UInt32) (encoded : ByteArray) :
    Except GCSError GCSFilter := do
  if key.size != 16 then throw .emptyKey
  if !(p < 64 && m > 0) then throw .invalidParameters
  if n > maxElementCount then throw (.tooManyElements n)
  if encoded.size > maxEncodedSize then throw (.encodedFilterTooLarge encoded.size)
  validateEncoding p n encoded
  return { p, m, key, n, encoded }

/-- Serialized form: compactSize(N) ‖ bitstream (BIP158 `NBytes`). -/
def serialized (f : GCSFilter) : ByteArray := compactSize f.n.toUInt64 ++ f.encoded

@[inline] def hashedValue (f : GCSFilter) (item : ByteArray) : UInt64 :=
  let (k0, k1) := keyWords f.key
  mulHi (sipHash k0 k1 item) (f.n.toUInt64 * f.m.toUInt64)

/-- Next codeword on the non-throwing path (reads past the end are zero bits). -/
@[inline] def nextDelta (enc : ByteArray) (p : UInt8) (pos : Nat) : UInt64 × Nat :=
  let ones := onesRun enc pos
  let pos := pos + ones + 1
  ((ones.toUInt64 <<< p.toUInt64) + readBits enc pos p.toNat, pos + p.toNat)

def contains (f : GCSFilter) (item : ByteArray) : Bool := Id.run do
  if f.n == 0 then return false
  let target := f.hashedValue item
  let mut pos := 0
  let mut last : UInt64 := 0
  for _ in [0:f.n.toNat] do
    let (d, pos') := nextDelta f.encoded f.p pos
    pos := pos'
    let value := last + d
    if value == target then return true
    if value > target then return false
    last := value
  return false

/-- BIP158 `MatchAny`: hash and sort the queries once, then one merge pass over the set. -/
def matchAny (f : GCSFilter) (items : Array ByteArray) : Bool := Id.run do
  if f.n == 0 || items.isEmpty then return false
  let targets := (items.map f.hashedValue).qsort (· < ·)
  let mut pos := 0
  let mut value : UInt64 := 0
  let mut index := 0
  for _ in [0:f.n.toNat] do
    let (d, pos') := nextDelta f.encoded f.p pos
    pos := pos'
    value := value + d
    while index < targets.size && targets[index]! < value do index := index + 1
    if index == targets.size then return false
    if targets[index]! == value then return true
  return false

def containsAny (f : GCSFilter) (items : Array ByteArray) : Bool := f.matchAny items

/-- BIP158 filter hash and header chain: SHA256d(SHA256d(filter) ‖ previousHeader). -/
def filterHash (serializedFilter : ByteArray) : ByteArray := sha256d serializedFilter
def filterHeader (serializedFilter previousHeader : ByteArray) : ByteArray :=
  sha256d (filterHash serializedFilter ++ previousHeader)

end GCSFilter
end Winnow.Net
