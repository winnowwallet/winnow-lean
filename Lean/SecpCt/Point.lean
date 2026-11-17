import SecpCt.Field
import SecpCt.Scalar

/-! # Points on the curve y² = x³ + 7, and multiplying the generator by a secret

A point is three field elements (X : Y : Z), standing for x = X/Z, y = Y/Z; the point at infinity is
(0 : 1 : 0). Addition uses the complete formulas of Renes, Costello and Batina ("Complete addition formulas
for prime order elliptic curves", 2016) for curves of this shape:

    X₃ = (X₁Y₂ + X₂Y₁)(Y₁Y₂ − 3bZ₁Z₂) − 3b(Y₁Z₂ + Y₂Z₁)(X₁Z₂ + X₂Z₁)
    Y₃ = (Y₁Y₂ + 3bZ₁Z₂)(Y₁Y₂ − 3bZ₁Z₂) + 9bX₁X₂(X₁Z₂ + X₂Z₁)
    Z₃ = (Y₁Z₂ + Y₂Z₁)(Y₁Y₂ + 3bZ₁Z₂) + 3X₁X₂(X₁Y₂ + X₂Y₁)

They are complete: the same arithmetic is right for two different points, for a point and itself, and when
either is the point at infinity. So there are no cases to tell apart, and nothing to branch on.

Multiplying the generator by a scalar looks at each of the scalar's 256 bits in turn: double, add the
generator, and keep the sum or not by a mask. Every multiplication does exactly the same work. -/

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

/-- `p` where the mask is all ones, `q` where it is all zeros. -/
def choose (m : UInt64) (p q : Point) : Point := ⟨Fe.choose m p.x q.x, Fe.choose m p.y q.y, Fe.choose m p.z q.z⟩

/-- `k` times the generator. -/
def mulGenerator (k : Sc) : Point := Id.run do
  let mut acc := infinity
  for i in [0:256] do
    acc := add acc acc
    acc := choose (mask (k.bit (255 - i))) (add acc generator) acc
  return acc

/-- The point's x and y, and whether it is the point at infinity (1 or 0), for which they mean nothing. -/
def affine (p : Point) : Fe × Fe × UInt64 :=
  let zInverse := Fe.inv p.z
  (Fe.mul p.x zInverse, Fe.mul p.y zInverse, Fe.isZero p.z)

end Point

end SecpCt
