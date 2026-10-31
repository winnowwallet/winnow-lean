import Secp.Field.Ops
import Secp.Curve.Spec

/-! # The fast field and scalar multiplication compiled code runs

`Fq` is a `List UInt64`, so every product allocates a chain of boxed limbs, and `smulJ` is double-and-add
over all 256 bits: right for proofs, about 9 ms for one `k·G`. Here a field element is one structure of four
unboxed limbs, and `k·G` adds one precomputed multiple per 4-bit window of `k` (64 mixed additions, no
doublings); `k·P` doubles four times per window and adds one of `1·P … 15·P`. The formulas are
`Formulas.lean`'s, written out for this type.

Nothing here is proved. `Secp.mulG`, `mulPt`, `mulGAdd` and `liftX?` (`Secp.Keys`) and Winnow's `mulGen`,
`mulOpt` and `addOpt` (`Winnow.Keys.Secp256k1`) stay the proved definitions every theorem is about; compiled
code runs this file instead (`@[implemented_by]`). That the two agree is trusted, and checked:
`crypto-test`'s "fast curve" checks compare them on random scalars and points through the proved code
(`Secp.smul?`, `Fq.sqrt?`), and BIP340's vectors and every other test run through this path. -/

namespace Secp.Fast

structure F where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  deriving BEq, Inhabited

/-- `2^256 - P`. -/
def cC : UInt64 := 0x1000003D1

def m32 : UInt64 := 0xFFFFFFFF

@[inline] def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& m32; let a1 := a >>> 32
  let b0 := b &&& m32; let b1 := b >>> 32
  let p00 := a0 * b0; let p01 := a0 * b1; let p10 := a1 * b0; let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& m32) + (p10 &&& m32)
  ((p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)), ((p00 &&& m32) + (mid <<< 32)))

/-- `a·b + c + d` as (high, low); it fits in 128 bits. -/
@[inline] def mulAdd (a b c d : UInt64) : UInt64 × UInt64 :=
  let (h, l) := mulWide a b
  let l1 := l + c
  let h := if l1 < l then h + 1 else h
  let l2 := l1 + d
  ((if l2 < l1 then h + 1 else h), l2)

@[inline] def adc (a b k : UInt64) : UInt64 × UInt64 :=
  let s := a + b
  let k1 : UInt64 := if s < a then 1 else 0
  let s2 := s + k
  (s2, k1 + (if s2 < s then 1 else 0))

/-- `x mod P` for `x < 2^256`: `x ≥ P` exactly when `x + cC` carries out, and then that sum is `x - P`. -/
@[inline] def canon (u0 u1 u2 u3 : UInt64) : F :=
  let (v0, k) := adc u0 cC 0
  let (v1, k) := adc u1 0 k
  let (v2, k) := adc u2 0 k
  let (v3, k) := adc u3 0 k
  if k == 1 then ⟨v0, v1, v2, v3⟩ else ⟨u0, u1, u2, u3⟩

/-- `lo + 2^256·hi mod P`, as `lo + cC·hi`, twice. -/
@[inline] def reduce (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) : F :=
  let (c, u0) := mulAdd t4 cC t0 0
  let (c, u1) := mulAdd t5 cC t1 c
  let (c, u2) := mulAdd t6 cC t2 c
  let (u4, u3) := mulAdd t7 cC t3 c
  let (h, l) := mulWide u4 cC
  let (u0, k) := adc u0 l 0
  let (u1, k) := adc u1 h k
  let (u2, k) := adc u2 0 k
  let (u3, k) := adc u3 0 k
  -- one more 2^256 ≡ cC; the sum is then small, so this cannot carry again
  let (u0, k) := adc u0 (if k == 1 then cC else 0) 0
  let (u1, k) := adc u1 0 k
  let (u2, k) := adc u2 0 k
  let (u3, _) := adc u3 0 k
  canon u0 u1 u2 u3

def mul (a b : F) : F :=
  let (c, t0) := mulAdd a.a0 b.a0 0 0
  let (c, r1) := mulAdd a.a0 b.a1 c 0
  let (c, r2) := mulAdd a.a0 b.a2 c 0
  let (r4, r3) := mulAdd a.a0 b.a3 c 0
  let (c, t1) := mulAdd a.a1 b.a0 r1 0
  let (c, r2) := mulAdd a.a1 b.a1 r2 c
  let (c, r3) := mulAdd a.a1 b.a2 r3 c
  let (r5, r4) := mulAdd a.a1 b.a3 r4 c
  let (c, t2) := mulAdd a.a2 b.a0 r2 0
  let (c, r3) := mulAdd a.a2 b.a1 r3 c
  let (c, r4) := mulAdd a.a2 b.a2 r4 c
  let (r6, r5) := mulAdd a.a2 b.a3 r5 c
  let (c, t3) := mulAdd a.a3 b.a0 r3 0
  let (c, t4) := mulAdd a.a3 b.a1 r4 c
  let (c, t5) := mulAdd a.a3 b.a2 r5 c
  let (t7, t6) := mulAdd a.a3 b.a3 r6 c
  reduce t0 t1 t2 t3 t4 t5 t6 t7

/-- `a + b`: on a carry out, `+ cC` (no further carry: the sum is then below `P`); else `canon`. -/
def add (a b : F) : F :=
  let (s0, k) := adc a.a0 b.a0 0
  let (s1, k) := adc a.a1 b.a1 k
  let (s2, k) := adc a.a2 b.a2 k
  let (s3, k) := adc a.a3 b.a3 k
  if k == 1 then
    let (s0, k) := adc s0 cC 0
    let (s1, k) := adc s1 0 k
    let (s2, k) := adc s2 0 k
    ⟨s0, s1, s2, s3 + k⟩
  else canon s0 s1 s2 s3

@[inline] def sbb (a b k : UInt64) : UInt64 × UInt64 :=
  let d := a - b
  let k1 : UInt64 := if a < b then 1 else 0
  let d2 := d - k
  (d2, k1 + (if d < k then 1 else 0))

/-- `a - b`: on a borrow, `- cC` (that is `+ P` mod 2^256; no further borrow). -/
def sub (a b : F) : F :=
  let (d0, k) := sbb a.a0 b.a0 0
  let (d1, k) := sbb a.a1 b.a1 k
  let (d2, k) := sbb a.a2 b.a2 k
  let (d3, k) := sbb a.a3 b.a3 k
  if k == 1 then
    let (d0, k) := sbb d0 cC 0
    let (d1, k) := sbb d1 0 k
    let (d2, k) := sbb d2 0 k
    ⟨d0, d1, d2, d3 - k⟩
  else ⟨d0, d1, d2, d3⟩

instance : Add F := ⟨add⟩
instance : Sub F := ⟨sub⟩
instance : Mul F := ⟨mul⟩

def zero : F := ⟨0, 0, 0, 0⟩
def one : F := ⟨1, 0, 0, 0⟩
def F.isZero (a : F) : Bool := a.a0 == 0 && a.a1 == 0 && a.a2 == 0 && a.a3 == 0

def F.ofNat (n : Nat) : F :=
  let n := n % P
  ⟨UInt64.ofNat n, UInt64.ofNat (n / 2^64), UInt64.ofNat (n / 2^128), UInt64.ofNat (n / 2^192)⟩

def F.toNat (a : F) : Nat :=
  a.a0.toNat + 2^64 * a.a1.toNat + 2^128 * a.a2.toNat + 2^192 * a.a3.toNat

/-- Through `Nat`, as `Fq.inv?` does; checked by multiplying back. -/
def F.inv? (a : F) : Option F :=
  let w := F.ofNat (natInv a.toNat P)
  if mul a w == one then some w else none

/-- `a^(P-2)` by square-and-multiply on the fast field; checked by multiplying back. -/
def F.invF? (a : F) : Option F := Id.run do
  let e := P - 2
  let mut r := one
  for i' in [0:256] do
    let i := 255 - i'
    r := r * r
    if e.testBit i then r := r * a
  return if mul a r == one then some r else none

/-- `a^e` by square-and-multiply over `e`'s bits, top down. -/
def F.pow (a : F) (e : Nat) : F := Id.run do
  let mut r := one
  for i' in [0:e.log2 + 1] do
    let i := e.log2 - i'
    r := r * r
    if e.testBit i then r := r * a
  return r

/-- A square root, `c^((P+1)/4)` (`P ≡ 3 mod 4`), checked by squaring it back; `none` when `c` is not a
square. -/
def F.sqrt? (c : F) : Option F :=
  let y := c.pow ((P + 1) / 4)
  if y * y == c then some y else none

def F.isOdd (a : F) : Bool := a.a0 % 2 == 1

/-- An affine point that is not infinity. -/
structure A where
  x : F
  y : F
  deriving Inhabited

structure J where
  X : F
  Y : F
  Z : F
  deriving Inhabited

def J.inf : J := ⟨one, one, zero⟩

/-- dbl-2009-l with a = 0 (`dblF`). -/
def J.double (j : J) : J :=
  if j.Z.isZero then j else
  let X := j.X; let Y := j.Y; let Z := j.Z
  let A := X * X
  let B := Y * Y
  let C := B * B
  let t := (X + B) * (X + B) - A - C
  let D := t + t
  let E := A + A + A
  let F := E * E
  let X3 := F - (D + D)
  let C2 := C + C; let C4 := C2 + C2; let C8 := C4 + C4
  ⟨X3, E * (D - X3) - C8, (Y + Y) * Z⟩

/-- madd-2007-bl (`hrF`, `maddF`), with `Jac.addAffine`'s cases for `H = 0`. -/
def J.addA (j : J) (p : A) : J :=
  if j.Z.isZero then ⟨p.x, p.y, one⟩ else
  let X := j.X; let Y := j.Y; let Z := j.Z
  let Z1Z1 := Z * Z
  let H := p.x * Z1Z1 - X
  let R := p.y * Z * Z1Z1 - Y
  if H.isZero then (if R.isZero then j.double else J.inf) else
  let HH := H * H
  let I2 := HH + HH; let I := I2 + I2
  let Jm := H * I
  let r := R + R
  let V := X * I
  let X3 := r * r - Jm - (V + V)
  ⟨X3, r * (V - X3) - (Y + Y) * Jm, (Z + H) * (Z + H) - Z1Z1 - HH⟩

def J.toA? (j : J) : Option A :=
  if j.Z.isZero then none else
  match j.Z.inv? with
  | some w => let w2 := w * w; some ⟨j.X * w2, j.Y * w2 * w⟩
  | none => none

def G : A := ⟨F.ofNat Spec.Gx.val, F.ofNat Spec.Gy.val⟩

/-- `j·2^(4i)·G` at `16·i + j` for windows `i < 64` and `1 ≤ j < 16` (index `16·i` unused). Built once. -/
def gTable : Array A := Id.run do
  let mut t : Array A := Array.mkEmpty 1024
  let mut base : A := G
  for _ in [0:64] do
    t := t.push base
    let mut acc : J := ⟨base.x, base.y, one⟩
    for _ in [1:16] do
      t := t.push (acc.toA?.getD default)
      acc := acc.addA base
    -- acc is 16·base now
    base := acc.toA?.getD default
  return t

/-- `k·G` for `k < 2^256`, in Jacobian form: one table point per nonzero window. -/
def mulGJ (k : Nat) : J := Id.run do
  let mut r := J.inf
  for i in [0:64] do
    let w := (k >>> (4 * i)) % 16
    if w != 0 then r := r.addA gTable[16 * i + w]!
  return r

/-- `k·G`; `none` is infinity. -/
def mulG (k : Nat) : Option A := (mulGJ k).toA?

/-- Affine forms of Jacobian points through one inverse (Montgomery's trick); none of them infinity. -/
def toAs? (js : Array J) : Option (Array A) := Id.run do
  let mut pre : Array F := Array.mkEmpty js.size
  let mut acc := one
  for j in js do
    acc := acc * j.Z
    pre := pre.push acc
  let some inv := acc.invF? | return none
  let mut out : Array A := Array.replicate js.size default
  let mut w := inv
  for i' in [0:js.size] do
    let i := js.size - 1 - i'
    let zi := if i == 0 then w else w * pre[i - 1]!
    w := w * js[i]!.Z
    let z2 := zi * zi
    out := out.set! i ⟨js[i]!.X * z2, js[i]!.Y * z2 * zi⟩
  return some out

/-- `k·p`: four doublings and at most one table addition per window, top down. -/
def mulPtJ (k : Nat) (p : A) : Option J := Id.run do
  let mut js : Array J := #[⟨p.x, p.y, one⟩]
  let mut acc : J := ⟨p.x, p.y, one⟩
  for _ in [2:16] do
    acc := acc.addA p
    js := js.push acc
  let some t := toAs? js | return none
  let tab := #[default] ++ t
  let mut r := J.inf
  for i' in [0:64] do
    let i := 63 - i'
    r := r.double.double.double.double
    let w := (k >>> (4 * i)) % 16
    if w != 0 then r := r.addA tab[w]!
  return some r

def mulPt (k : Nat) (p : A) : Option A := (mulPtJ k p).bind J.toA?

end Secp.Fast
