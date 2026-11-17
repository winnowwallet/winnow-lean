import SecpCt.Word

/-! # The field: numbers modulo P = 2²⁵⁶ − 2³² − 977

An element is four words, least significant first, and always the one representative below P. Every operation
does the same sequence of word operations whatever the element is.

The reductions follow winnow's `Secp/Fast.lean`, with each `if` on a carry replaced by a mask. -/

namespace SecpCt

structure Fe where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  deriving Inhabited

namespace Fe

/-- `2²⁵⁶ − P`. -/
def c : UInt64 := 0x1000003D1

def zero : Fe := ⟨0, 0, 0, 0⟩
def one : Fe := ⟨1, 0, 0, 0⟩
def ofWord (w : UInt64) : Fe := ⟨w, 0, 0, 0⟩

/-- `x mod P` for `x < 2²⁵⁶`: `x ≥ P` exactly when `x + c` carries out, and then that sum is `x − P`. -/
@[inline] def canon (u0 u1 u2 u3 : UInt64) : Fe :=
  let (v0, k) := adc u0 c 0
  let (v1, k) := adc u1 0 k
  let (v2, k) := adc u2 0 k
  let (v3, k) := adc u3 0 k
  let m := mask k
  ⟨select m v0 u0, select m v1 u1, select m v2 u2, select m v3 u3⟩

/-- `low + 2²⁵⁶·high mod P`, as `low + c·high`, twice. -/
@[inline] def reduce (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) : Fe :=
  let (k, u0) := mulAdd t4 c t0 0
  let (k, u1) := mulAdd t5 c t1 k
  let (k, u2) := mulAdd t6 c t2 k
  let (u4, u3) := mulAdd t7 c t3 k
  let (h, l) := mulWide u4 c
  let (u0, k) := adc u0 l 0
  let (u1, k) := adc u1 h k
  let (u2, k) := adc u2 0 k
  let (u3, k) := adc u3 0 k
  -- one more 2²⁵⁶ ≡ c; the sum is then small, so this cannot carry again
  let (u0, k) := adc u0 (c &&& mask k) 0
  let (u1, k) := adc u1 0 k
  let (u2, k) := adc u2 0 k
  let (u3, _) := adc u3 0 k
  canon u0 u1 u2 u3

def mul (a b : Fe) : Fe :=
  let (k, t0) := mulAdd a.a0 b.a0 0 0
  let (k, r1) := mulAdd a.a0 b.a1 k 0
  let (k, r2) := mulAdd a.a0 b.a2 k 0
  let (r4, r3) := mulAdd a.a0 b.a3 k 0
  let (k, t1) := mulAdd a.a1 b.a0 r1 0
  let (k, r2) := mulAdd a.a1 b.a1 r2 k
  let (k, r3) := mulAdd a.a1 b.a2 r3 k
  let (r5, r4) := mulAdd a.a1 b.a3 r4 k
  let (k, t2) := mulAdd a.a2 b.a0 r2 0
  let (k, r3) := mulAdd a.a2 b.a1 r3 k
  let (k, r4) := mulAdd a.a2 b.a2 r4 k
  let (r6, r5) := mulAdd a.a2 b.a3 r5 k
  let (k, t3) := mulAdd a.a3 b.a0 r3 0
  let (k, t4) := mulAdd a.a3 b.a1 r4 k
  let (k, t5) := mulAdd a.a3 b.a2 r5 k
  let (t7, t6) := mulAdd a.a3 b.a3 r6 k
  reduce t0 t1 t2 t3 t4 t5 t6 t7

def sqr (a : Fe) : Fe := mul a a

/-- `a + b`. On a carry out, the true sum is `2²⁵⁶` more, which is `c` more modulo P, and adding `c` cannot
carry again; without one, the sum may still be P or more. -/
def add (a b : Fe) : Fe :=
  let (s0, k) := adc a.a0 b.a0 0
  let (s1, k) := adc a.a1 b.a1 k
  let (s2, k) := adc a.a2 b.a2 k
  let (s3, k) := adc a.a3 b.a3 k
  let (s0, k) := adc s0 (c &&& mask k) 0
  let (s1, k) := adc s1 0 k
  let (s2, k) := adc s2 0 k
  let (s3, _) := adc s3 0 k
  canon s0 s1 s2 s3

/-- `a − b`. On a borrow, the true difference is P more than what is left, which is `c` less; taking `c`
away cannot borrow again. -/
def sub (a b : Fe) : Fe :=
  let (d0, k) := sbb a.a0 b.a0 0
  let (d1, k) := sbb a.a1 b.a1 k
  let (d2, k) := sbb a.a2 b.a2 k
  let (d3, k) := sbb a.a3 b.a3 k
  let (d0, k) := sbb d0 (c &&& mask k) 0
  let (d1, k) := sbb d1 0 k
  let (d2, k) := sbb d2 0 k
  let (d3, _) := sbb d3 0 k
  ⟨d0, d1, d2, d3⟩

def neg (a : Fe) : Fe := sub zero a

/-- 1 if the element is zero, else 0. -/
def isZero (a : Fe) : UInt64 := nonzero (a.a0 ||| a.a1 ||| a.a2 ||| a.a3) ^^^ 1

/-- 1 if the element is odd, else 0. -/
def isOdd (a : Fe) : UInt64 := a.a0 &&& 1

/-- `a` where the mask is all ones, `b` where it is all zeros. -/
def choose (m : UInt64) (a b : Fe) : Fe :=
  ⟨select m a.a0 b.a0, select m a.a1 b.a1, select m a.a2 b.a2, select m a.a3 b.a3⟩

/-- `a` to a power that is not a secret, given as four words, least significant first: the exponent's bits
decide what is done. -/
def power (a : Fe) (e0 e1 e2 e3 : UInt64) : Fe := Id.run do
  let mut r := one
  for word in [e3, e2, e1, e0] do
    for i in [0:64] do
      r := sqr r
      if (word >>> (63 - i).toUInt64) &&& 1 == 1 then r := mul r a
  return r

/-- `1/a`, as `a` to the power P − 2; zero for zero. -/
def inv (a : Fe) : Fe :=
  power a 0xFFFFFFFEFFFFFC2D 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF

/-- The element 32 bytes stand for, most significant first, reduced modulo P. -/
def ofBytes (b : ByteArray) : Fe := canon (wordAt b 24) (wordAt b 16) (wordAt b 8) (wordAt b 0)

/-- The element as 32 bytes, most significant first. -/
def bytes (a : Fe) : ByteArray :=
  pushWord (pushWord (pushWord (pushWord (ByteArray.emptyWithCapacity 32) a.a3) a.a2) a.a1) a.a0

end Fe

end SecpCt
