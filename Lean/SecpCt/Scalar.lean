import SecpCt.Word

/-! # Scalars: numbers modulo N, the number of points on the curve

A secret key is a scalar, and so is the secret number each signature is made with. Like a field element, a
scalar is four words, least significant first, always the representative below N, and every operation does
the same thing whatever the scalar is.

Multiplication goes through arrays of words. Their sizes and the positions read are fixed by the code, never
by a value. -/

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

/-- `2²⁵⁶ − N`, least significant word first: 129 bits. -/
def complement : Array UInt64 := #[0x402DA1732FC9BEBF, 0x4551231950B75FC4, 1]

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

/-- The product of two numbers given as words, least significant first: as many words as both together. -/
def mulWords (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut out := Array.replicate (a.size + b.size) (0 : UInt64)
  for i in [0:a.size] do
    let mut carry : UInt64 := 0
    for j in [0:b.size] do
      let (h, l) := mulAdd a[i]! b[j]! out[i + j]! carry
      out := out.set! (i + j) l
      carry := h
    out := out.set! (i + b.size) carry
  return out

/-- The sum of two numbers given as words, to `size` words; anything above that is dropped, and the callers
choose `size` so that nothing is. -/
def addWords (a b : Array UInt64) (size : Nat) : Array UInt64 := Id.run do
  let mut out := Array.replicate size (0 : UInt64)
  let mut carry : UInt64 := 0
  for i in [0:size] do
    let (s, k) := adc (a.getD i 0) (b.getD i 0) carry
    out := out.set! i s
    carry := k
  return out

/-- `low + 2²⁵⁶·high` is the same modulo N as `low + complement·high`, which is shorter. `t` is `low` in its
first four words and `high` in the rest; the result has `size` words. -/
def fold (t : Array UInt64) (size : Nat) : Array UInt64 :=
  addWords (t.extract 0 4) (mulWords (t.extract 4 t.size) complement) size

/-- A number of eight words, modulo N. Three folds bring 512 bits to 386, to 260, to 257 at most, which is
below 2N. -/
def reduceWide (t : Array UInt64) : Sc :=
  let q := fold (fold (fold t 7) 5) 5
  reduceOnce q[0]! q[1]! q[2]! q[3]! q[4]!

def mul (a b : Sc) : Sc :=
  reduceWide (mulWords #[a.a0, a.a1, a.a2, a.a3] #[b.a0, b.a1, b.a2, b.a3])

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

/-- Bit `i` of the scalar (1 or 0), for a position that is not a secret. -/
@[inline] def bit (a : Sc) (i : Nat) : UInt64 :=
  let word := if i < 64 then a.a0 else if i < 128 then a.a1 else if i < 192 then a.a2 else a.a3
  (word >>> (i % 64).toUInt64) &&& 1

end Sc

end SecpCt
