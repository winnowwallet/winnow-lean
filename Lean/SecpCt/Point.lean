import SecpCt.Field
import SecpCt.Scalar

/-! # Points on the curve y² = x³ + 7, and multiplying one by a number

A point is three field elements (X : Y : Z), standing for x = X/Z, y = Y/Z; the point at infinity is
(0 : 1 : 0). Addition uses the complete formulas of Renes, Costello and Batina ("Complete addition formulas
for prime order elliptic curves", 2016) for curves of this shape:

    X₃ = (X₁Y₂ + X₂Y₁)(Y₁Y₂ − 3bZ₁Z₂) − 3b(Y₁Z₂ + Y₂Z₁)(X₁Z₂ + X₂Z₁)
    Y₃ = (Y₁Y₂ + 3bZ₁Z₂)(Y₁Y₂ − 3bZ₁Z₂) + 9bX₁X₂(X₁Z₂ + X₂Z₁)
    Z₃ = (Y₁Z₂ + Y₂Z₁)(Y₁Y₂ + 3bZ₁Z₂) + 3X₁X₂(X₁Y₂ + X₂Y₁)

They are complete: the same arithmetic is right for two different points, for a point and itself, and when
either is the point at infinity. So there are no cases to tell apart, and nothing to branch on.

Multiplying a point by a scalar looks at each of the scalar's 256 bits in turn: double, add the point, and
keep the sum or not by a mask. Every multiplication does exactly the same work. That is the specification's
own way of multiplying (`Secp.Spec.smul`), step for step, which is why it can be proved to be it: a faster
way (a table of multiples, say) would need the curve's group law, which nobody here has proved. For a scalar
that is not secret there is `mulPublic`, which leaves out the additions the mask would have thrown away. -/

namespace SecpCt

structure Point where
  x : Fe
  y : Fe
  z : Fe
  deriving Inhabited

namespace Point

def infinity : Point := ⟨Fe.zero, Fe.one, Fe.zero⟩

/-- The generator. -/
def generator : Point :=
  ⟨⟨0x59F2815B16F81798, 0x029BFCDB2DCE28D9, 0x55A06295CE870B07, 0x79BE667EF9DCBBAC⟩,
   ⟨0x9C47D08FFB10D4B8, 0xFD17B448A6855419, 0x5DA4FBFC0E1108A8, 0x483ADA7726A3C465⟩,
   Fe.one⟩

/-- 3b, for b = 7. -/
def b3 : Fe := Fe.ofWord 21

/-- The sum of two points, by the complete formulas. -/
def add (p q : Point) : Point :=
  let xx := Fe.mul p.x q.x
  let yy := Fe.mul p.y q.y
  let zz := Fe.mul p.z q.z
  -- X₁Y₂ + X₂Y₁, Y₁Z₂ + Y₂Z₁ and X₁Z₂ + X₂Z₁, each from one product and the three above
  let xy := Fe.sub (Fe.mul (Fe.add p.x p.y) (Fe.add q.x q.y)) (Fe.add xx yy)
  let yz := Fe.sub (Fe.mul (Fe.add p.y p.z) (Fe.add q.y q.z)) (Fe.add yy zz)
  let xz := Fe.sub (Fe.mul (Fe.add p.x p.z) (Fe.add q.x q.z)) (Fe.add xx zz)
  let xx3 := Fe.add (Fe.add xx xx) xx
  let bzz := Fe.mul b3 zz
  let plus := Fe.add yy bzz
  let minus := Fe.sub yy bzz
  let bxz := Fe.mul b3 xz
  ⟨Fe.sub (Fe.mul xy minus) (Fe.mul yz bxz),
   Fe.add (Fe.mul plus minus) (Fe.mul bxz xx3),
   Fe.add (Fe.mul yz plus) (Fe.mul xx3 xy)⟩

/-- Twice a point, by the same paper's complete doubling for curves of this shape, which is the addition
formulas for a point and itself with the curve's equation used to shorten them:

    X₃ = 2XY(Y² − 9bZ²)
    Y₃ = (Y² − 9bZ²)(Y² + 3bZ²) + 24bY²Z²
    Z₃ = 8Y³Z

Nine multiplications where the addition takes fourteen, and still no cases: it is right for the point at
infinity too. -/
def double (p : Point) : Point :=
  let yy := Fe.mul p.y p.y
  let yy2 := Fe.add yy yy
  let yy4 := Fe.add yy2 yy2
  let yy8 := Fe.add yy4 yy4
  let yz := Fe.mul p.y p.z
  let bzz := Fe.mul b3 (Fe.mul p.z p.z)
  let bzz3 := Fe.add (Fe.add bzz bzz) bzz
  let minus := Fe.sub yy bzz3
  let xy := Fe.mul p.x p.y
  let half := Fe.mul minus xy
  ⟨Fe.add half half,
   Fe.add (Fe.mul bzz yy8) (Fe.mul minus (Fe.add yy bzz)),
   Fe.mul yz yy8⟩

/-- `p` where the mask is all ones, `q` where it is all zeros. -/
def choose (m : UInt64) (p q : Point) : Point := ⟨Fe.choose m p.x q.x, Fe.choose m p.y q.y, Fe.choose m p.z q.z⟩

/-- `k` times a point of the curve, for a `k` that may be secret: double, add the point, and keep the sum or
not by a mask, for each of the 256 bits. Every multiplication does exactly the same work. -/
def mul (k : Sc) (p : Point) : Point := Id.run do
  let mut acc := infinity
  for i in [0:256] do
    acc := double acc
    acc := choose (mask (k.bit (255 - i))) (add acc p) acc
  return acc

/-- `k` times the generator. -/
def mulGenerator (k : Sc) : Point := mul k generator

/-- `k` times a point of the curve, for a `k` that is **not** secret (a tweak written in a descriptor, a
number out of a signature): the same doublings, and the addition only where the bit is set. What it does
shows which bits are set. -/
def mulPublic (k : Sc) (p : Point) : Point := Id.run do
  let mut acc := infinity
  for i in [0:256] do
    acc := double acc
    if k.bit (255 - i) == 1 then acc := add acc p
  return acc

/-- The same point with the other y. -/
def neg (p : Point) : Point := ⟨p.x, Fe.neg p.y, p.z⟩

/-- The point with these two coordinates. They must be a point of the curve: the formulas above are only
right on it. -/
def ofAffine (x y : Fe) : Point := ⟨x, y, Fe.one⟩

/-- The point's x and y, and whether it is the point at infinity (1 or 0), for which they mean nothing. -/
def affine (p : Point) : Fe × Fe × UInt64 :=
  let zInverse := Fe.inv p.z
  (Fe.mul p.x zInverse, Fe.mul p.y zInverse, Fe.isZero p.z)

end Point

end SecpCt
