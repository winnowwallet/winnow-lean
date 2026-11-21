/-! # Words: arithmetic that does the same thing whatever the numbers are

`SecpCt` is secp256k1 for where a key must not show in how long the work takes, or in which memory it
touches: a signer that someone else can ask for signatures as often as they like, timing every one. So
nothing in `SecpCt` may branch on a secret or use one to pick where to read. This file is the vocabulary that
makes that possible.

A secret is only ever held in `UInt64`s, which compile to machine words, and only ever meets `+ - * &&& |||
^^^ ~~~` and shifts by amounts that are not secret. A carry is computed from the top bits of the operands,
not by comparing. A choice between two values is made by masking both and combining them, not by `if`.

A secret never becomes a `Nat`: Lean stores small and large naturals differently and its arithmetic takes a
different road for each.

Whether compiled code keeps to this can only be checked on the compiled code, for each compiler and target it
is built for; the source can only make it possible. SECURITY.md ("Timing side channels") says where that has
been checked and where it has not. -/

namespace SecpCt

/-- The carry out of `a + b + carry in`, given the sum `s` (as 0 or 1). -/
@[inline] def carryOf (a b s : UInt64) : UInt64 := ((a &&& b) ||| ((a ||| b) &&& ~~~s)) >>> 63

/-- `a + b + k` for a carry `k` of 0 or 1: the sum and the carry out. -/
@[inline] def adc (a b k : UInt64) : UInt64 × UInt64 :=
  let s := a + b + k
  (s, carryOf a b s)

/-- The borrow out of `a - b - borrow in`, given the difference `d` (as 0 or 1). -/
@[inline] def borrowOf (a b d : UInt64) : UInt64 := ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)) >>> 63

/-- `a - b - k` for a borrow `k` of 0 or 1: the difference and the borrow out. -/
@[inline] def sbb (a b k : UInt64) : UInt64 × UInt64 :=
  let d := a - b - k
  (d, borrowOf a b d)

def low32 : UInt64 := 0xFFFFFFFF

/-- `a · b` as (high word, low word), from four 32-bit products. -/
@[inline] def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& low32; let a1 := a >>> 32
  let b0 := b &&& low32; let b1 := b >>> 32
  let p00 := a0 * b0; let p01 := a0 * b1; let p10 := a1 * b0; let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& low32) + (p10 &&& low32)
  ((p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)), ((p00 &&& low32) + (mid <<< 32)))

/-- `a · b + c + d` as (high word, low word); it always fits in two words. -/
@[inline] def mulAdd (a b c d : UInt64) : UInt64 × UInt64 :=
  let (h, l) := mulWide a b
  let (l, k1) := adc l c 0
  let (l, k2) := adc l d 0
  (h + k1 + k2, l)

/-- All ones for a bit of 1, all zeros for a bit of 0. -/
@[inline] def mask (bit : UInt64) : UInt64 := 0 - bit

/-- `a` where the mask is all ones, `b` where it is all zeros. -/
@[inline] def select (m a b : UInt64) : UInt64 := (a &&& m) ||| (b &&& ~~~m)

/-- 1 if `x` is not zero, else 0. -/
@[inline] def nonzero (x : UInt64) : UInt64 := (x ||| (0 - x)) >>> 63

/-- `a · (u0..u3) + (r0..r3)` in five words, least significant first. -/
@[inline] def mulRow (a u0 u1 u2 u3 r0 r1 r2 r3 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (k, s0) := mulAdd a u0 r0 0
  let (k, s1) := mulAdd a u1 r1 k
  let (k, s2) := mulAdd a u2 r2 k
  let (hi, s3) := mulAdd a u3 r3 k
  (s0, s1, s2, s3, hi)

/-- The eight bytes at `offset`, most significant first, as a word (0 if out of range). -/
@[inline] def wordAt (b : ByteArray) (offset : Nat) : UInt64 :=
  if h : offset + 8 ≤ b.size then
    ((b[offset]'(by omega)).toUInt64 <<< 56) ||| ((b[offset + 1]'(by omega)).toUInt64 <<< 48) |||
    ((b[offset + 2]'(by omega)).toUInt64 <<< 40) ||| ((b[offset + 3]'(by omega)).toUInt64 <<< 32) |||
    ((b[offset + 4]'(by omega)).toUInt64 <<< 24) ||| ((b[offset + 5]'(by omega)).toUInt64 <<< 16) |||
    ((b[offset + 6]'(by omega)).toUInt64 <<< 8) ||| (b[offset + 7]'(by omega)).toUInt64
  else 0

/-- `out` with the word `w` appended, most significant byte first. -/
@[inline] def pushWord (out : ByteArray) (w : UInt64) : ByteArray :=
  out.push (w >>> 56).toUInt8 |>.push (w >>> 48).toUInt8 |>.push (w >>> 40).toUInt8 |>.push (w >>> 32).toUInt8
    |>.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 8).toUInt8 |>.push w.toUInt8

end SecpCt
