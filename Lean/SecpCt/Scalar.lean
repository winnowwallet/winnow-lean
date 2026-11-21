import SecpCt.Word

/-! # Scalars: numbers modulo N, the number of points on the curve

A secret key is a scalar, and so is the secret number each signature is made with. Like a field element, a
scalar is four words, least significant first, always the representative below N, and every operation does
the same register sequence whatever the scalar is (no heap arrays, no secret-dependent branches). -/

namespace SecpCt

structure Sc where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  deriving Inhabited

namespace Sc

/-- N, least significant word first. -/
def n0 : UInt64 := 0xBFD25E8CD0364141
def n1 : UInt64 := 0xBAAEDCE6AF48A03B
def n2 : UInt64 := 0xFFFFFFFFFFFFFFFE
def n3 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- `2²⁵⁶ − N = c0 + 2⁶⁴·c1 + 2¹²⁸`, least significant word first (129 bits). -/
def c0 : UInt64 := 0x402DA1732FC9BEBF
def c1 : UInt64 := 0x4551231950B75FC4

def zero : Sc := ⟨0, 0, 0, 0⟩

/-- `u − N` and whether `u < N` (1 or 0), for `u < 2²⁵⁶`. -/
@[inline] def lessN (u0 u1 u2 u3 : UInt64) : Sc × UInt64 :=
  let (t0, b) := sbb u0 n0 0
  let (t1, b) := sbb u1 n1 b
  let (t2, b) := sbb u2 n2 b
  let (t3, b) := sbb u3 n3 b
  (⟨t0, t1, t2, t3⟩, b)

/-- `u + k·2²⁵⁶ mod N`, for a value below 2N: N is taken away when there is a carry or `u` is N or more. -/
@[inline] def reduceOnce (u0 u1 u2 u3 k : UInt64) : Sc :=
  let (t, below) := lessN u0 u1 u2 u3
  let m := mask (k ||| (below ^^^ 1))
  ⟨select m t.a0 u0, select m t.a1 u1, select m t.a2 u2, select m t.a3 u3⟩

def add (a b : Sc) : Sc :=
  let (s0, k) := adc a.a0 b.a0 0
  let (s1, k) := adc a.a1 b.a1 k
  let (s2, k) := adc a.a2 b.a2 k
  let (s3, k) := adc a.a3 b.a3 k
  reduceOnce s0 s1 s2 s3 k

/-- 1 if the scalar is zero, else 0. -/
def isZero (a : Sc) : UInt64 := nonzero (a.a0 ||| a.a1 ||| a.a2 ||| a.a3) ^^^ 1

/-- `−a`: N − a, and zero for zero. -/
def neg (a : Sc) : Sc :=
  let (t0, b) := sbb n0 a.a0 0
  let (t1, b) := sbb n1 a.a1 b
  let (t2, b) := sbb n2 a.a2 b
  let (t3, _) := sbb n3 a.a3 b
  let m := mask (isZero a ^^^ 1)
  ⟨t0 &&& m, t1 &&& m, t2 &&& m, t3 &&& m⟩

/-- `a` where the mask is all ones, `b` where it is all zeros. -/
def choose (m : UInt64) (a b : Sc) : Sc :=
  ⟨select m a.a0 b.a0, select m a.a1 b.a1, select m a.a2 b.a2, select m a.a3 b.a3⟩

/-- `−a` if `bit` is 1, `a` if it is 0. -/
def negIf (bit : UInt64) (a : Sc) : Sc := choose (mask bit) (neg a) a

/-- Eight-word product `(t0..t7)` of two four-word scalars, in registers. -/
@[inline] def mulWide4 (a b : Sc) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (t0, r1, r2, r3, r4) := mulRow a.a0 b.a0 b.a1 b.a2 b.a3 0 0 0 0
  let (t1, r2, r3, r4, r5) := mulRow a.a1 b.a0 b.a1 b.a2 b.a3 r1 r2 r3 r4
  let (t2, r3, r4, r5, r6) := mulRow a.a2 b.a0 b.a1 b.a2 b.a3 r2 r3 r4 r5
  let (t3, t4, t5, t6, t7) := mulRow a.a3 b.a0 b.a1 b.a2 b.a3 r3 r4 r5 r6
  (t0, t1, t2, t3, t4, t5, t6, t7)

/-- First fold: 512 bits → 7 words (< 2³⁸⁶) via `2²⁵⁶ ≡ c0 + 2⁶⁴·c1 + 2¹²⁸ (mod N)`. -/
@[inline] def fold1 (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (f0, u1, u2, u3, u4) := mulRow c0 t4 t5 t6 t7 t0 t1 t2 t3
  let (f1, v2, v3, v4, v5) := mulRow c1 t4 t5 t6 t7 u1 u2 u3 u4
  let (f2, k) := adc v2 t4 0
  let (f3, k) := adc v3 t5 k
  let (f4, k) := adc v4 t6 k
  let (f5, f6) := adc v5 t7 k
  (f0, f1, f2, f3, f4, f5, f6)

/-- Second fold: 7 words (< 2³⁸⁶) → 5 words (< 2²⁶⁰). -/
@[inline] def fold2 (f0 f1 f2 f3 f4 f5 f6 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (g0, u1, u2, u3, u4) := mulRow c0 f4 f5 f6 0 f0 f1 f2 f3
  let (g1, v2, v3, v4, _)  := mulRow c1 f4 f5 f6 0 u1 u2 u3 u4
  let (g2, k) := adc v2 f4 0
  let (g3, k) := adc v3 f5 k
  let (g4, _) := adc v4 f6 k
  (g0, g1, g2, g3, g4)

/-- Reduce an 8-word product modulo N in three register folds and one conditional subtraction. -/
@[inline] def reduceWide (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) : Sc :=
  let (f0, f1, f2, f3, f4, f5, f6) := fold1 t0 t1 t2 t3 t4 t5 t6 t7
  let (g0, g1, g2, g3, g4) := fold2 f0 f1 f2 f3 f4 f5 f6
  let (q0, q1, q2, q3, q4) := mulRow g4 c0 c1 1 0 g0 g1 g2 g3
  reduceOnce q0 q1 q2 q3 q4

def mul (a b : Sc) : Sc :=
  let (t0, t1, t2, t3, t4, t5, t6, t7) := mulWide4 a b
  reduceWide t0 t1 t2 t3 t4 t5 t6 t7

/-- The scalar 32 bytes stand for, most significant first, reduced modulo N. -/
def ofBytes (b : ByteArray) : Sc := reduceOnce (wordAt b 24) (wordAt b 16) (wordAt b 8) (wordAt b 0) 0

/-- Whether 32 bytes are a secret key as they stand: a number from 1 to N − 1 (1 or 0). -/
def isKey (b : ByteArray) : UInt64 :=
  let (u0, u1, u2, u3) := (wordAt b 24, wordAt b 16, wordAt b 8, wordAt b 0)
  (lessN u0 u1 u2 u3).2 &&& nonzero (u0 ||| u1 ||| u2 ||| u3)

/-- Whether 32 bytes are a number below N as they stand (1 or 0). -/
def isBelowN (b : ByteArray) : UInt64 := (lessN (wordAt b 24) (wordAt b 16) (wordAt b 8) (wordAt b 0)).2

/-- The scalar as 32 bytes, most significant first. -/
def bytes (a : Sc) : ByteArray :=
  pushWord (pushWord (pushWord (pushWord (ByteArray.emptyWithCapacity 32) a.a3) a.a2) a.a1) a.a0

def one : Sc := ⟨1, 0, 0, 0⟩

/-- `a` to a power that is not a secret, given as four words, least significant first: the exponent's bits
decide what is done, and the scalar's do not. -/
def power (a : Sc) (e0 e1 e2 e3 : UInt64) : Sc := Id.run do
  let mut r := one
  for word in [e3, e2, e1, e0] do
    for i in [0:64] do
      r := mul r r
      if (word >>> (63 - i).toUInt64) &&& 1 == 1 then r := mul r a
  return r

/-- `1/a` modulo N, as `a` to the power N − 2; zero for zero. ECDSA divides by the secret number a signature
is made with, and this is how: the same squarings and multiplications whatever that number is. -/
def inv (a : Sc) : Sc :=
  power a 0xBFD25E8CD036413F 0xBAAEDCE6AF48A03B 0xFFFFFFFFFFFFFFFE 0xFFFFFFFFFFFFFFFF

/-- `(N − 1)/2`, least significant word first: the largest s a Bitcoin ECDSA signature may carry. -/
def half0 : UInt64 := 0xDFE92F46681B20A0
def half1 : UInt64 := 0x5D576E7357A4501D
def half2 : UInt64 := 0xFFFFFFFFFFFFFFFF
def half3 : UInt64 := 0x7FFFFFFFFFFFFFFF

/-- Whether the scalar is above `(N − 1)/2` (1 or 0): taking it from that number borrows. -/
def isHigh (a : Sc) : UInt64 :=
  let (_, b) := sbb half0 a.a0 0
  let (_, b) := sbb half1 a.a1 b
  let (_, b) := sbb half2 a.a2 b
  let (_, b) := sbb half3 a.a3 b
  b

/-- Whether two scalars are the same four words. For values that are not secret. -/
def same (a b : Sc) : Bool := a.a0 == b.a0 && a.a1 == b.a1 && a.a2 == b.a2 && a.a3 == b.a3

/-- Bit `i` of the scalar (1 or 0), for a position that is not a secret. -/
@[inline] def bit (a : Sc) (i : Nat) : UInt64 :=
  let word := if i < 64 then a.a0 else if i < 128 then a.a1 else if i < 192 then a.a2 else a.a3
  (word >>> (i % 64).toUInt64) &&& 1

end Sc

end SecpCt
