import Winnow.Bytes

/-! # 256-bit unsigned integers for proof-of-work targets and chainwork (`Network/Headers/UInt256.swift`)

A `UInt256` is a natural number below 2^256 (GMP-backed `Nat`), with the Swift type's operations:
wrapping add/subtract/multiply, shifts, long division, the compact ("bits") encoding and block work. -/

namespace Winnow.Net

structure UInt256 where
  val : Nat
  deriving BEq, Inhabited, Repr, DecidableEq

namespace UInt256

def modulus : Nat := 2 ^ 256
def ofNat (n : Nat) : UInt256 := ⟨n % modulus⟩
def zero : UInt256 := ⟨0⟩
def max : UInt256 := ⟨modulus - 1⟩

instance : LT UInt256 := ⟨fun a b => a.val < b.val⟩
instance : LE UInt256 := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : UInt256) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : UInt256) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))
instance : Min UInt256 := ⟨fun a b => if a.val ≤ b.val then a else b⟩

/-- From 32 bytes, big-endian (display order). -/
def ofBigEndian (b : ByteArray) : UInt256 := ⟨b.foldl (fun acc x => acc * 256 + x.toNat) 0⟩
/-- From 32 bytes, little-endian (internal hash order). -/
def ofLittleEndian (b : ByteArray) : UInt256 := ⟨b.data.foldr (fun x acc => acc * 256 + x.toNat) 0⟩

/-- Big-endian 32-byte representation. -/
def bigEndianData (x : UInt256) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:32] do out := out.push (x.val >>> (8 * (31 - i))).toUInt8
  return out

def isZero (x : UInt256) : Bool := x.val == 0

/-- Wrapping (mod 2^256) addition and subtraction. -/
instance : Add UInt256 := ⟨fun a b => ofNat (a.val + b.val)⟩
instance : Sub UInt256 := ⟨fun a b => ofNat (a.val + modulus - b.val)⟩

def shiftedLeft (x : UInt256) (bits : Nat) : UInt256 := ofNat (x.val <<< bits)
def shiftedRight (x : UInt256) (bits : Nat) : UInt256 := ⟨x.val >>> bits⟩
/-- Wrapping multiplication by a 32-bit factor, like Core's arith_uint256. -/
def multiplied (x : UInt256) (factor : UInt32) : UInt256 := ofNat (x.val * factor.toNat)

def bitWidth (x : UInt256) : Nat := if x.val == 0 then 0 else Nat.log2 x.val + 1

/-- Positive target encoding, including Core's sign-bit normalization. -/
def compact (x : UInt256) : UInt32 :=
  let size := (x.bitWidth + 7) / 8
  let word : Nat := if size ≤ 3 then (x.val % 2 ^ 64) <<< (8 * (3 - size)) else (x.val >>> (8 * (size - 3))) % 2 ^ 64
  let (word, size) := if word &&& 0x800000 != 0 then (word >>> 8, size + 1) else (word, size)
  word.toUInt32 ||| (size.toUInt32 <<< 24)

/-- Long division (the divisor must be nonzero). -/
def quotientAndRemainder (x d : UInt256) : UInt256 × UInt256 := (⟨x.val / d.val⟩, ⟨x.val % d.val⟩)

/-- Decodes compact bits into a target, refusing negative and overflowing encodings (Core's SetCompact). -/
def target (bits : UInt32) : Option UInt256 :=
  let size := (bits >>> 24).toNat
  let word := (bits &&& 0x007FFFFF).toNat
  if bits &&& 0x00800000 != 0 then none
  else if word != 0 && (size > 34 || (word > 0xFF && size > 33) || (word > 0xFFFF && size > 32)) then none
  else if size ≤ 3 then some ⟨word >>> (8 * (3 - size))⟩
  else some ((⟨word⟩ : UInt256).shiftedLeft (8 * (size - 3)))

/-- Work of one block at `target` (Core's GetBlockProof): ~target / (target + 1) + 1; none for zero. -/
def blockWork (t : UInt256) : Option UInt256 :=
  if t.isZero then none
  else
    let num := max - t
    let den := t + ⟨1⟩
    if den.isZero then none -- unreachable from the chain (targets sit below powLimit); Swift traps
    else some ((num.quotientAndRemainder den).1 + ⟨1⟩)

end UInt256
end Winnow.Net
