import SecpCt.Schnorr

/-! # Public keys: reading them, tweaking them, and checking a BIP 340 signature

Everything the wallet does with a point of the curve that is not a secret, on the same field and point
arithmetic the signing code uses (`SecpCt/Field.lean`, `SecpCt/Point.lean`): there is no other.

A public point is an `Affine`: two coordinates, never the point at infinity. One is made only here, by a
function that has checked it is on the curve (`liftX?`, the parsers) or computed it from points that were.
That matters: the addition formulas are right only for points of this curve, and `pointMul` multiplies a
point someone else supplied by a number that may be secret. Given a point of another curve it would answer
about that curve.

What is public is handled plainly (`mulPublic`, `if`); what may be secret (the scalar of `pointMul`, a key)
goes through the code that does the same work whatever it is given.

`SecpCt/KeySpecs.lean` says what each of these is on the curve as specified. -/

namespace SecpCt

/-- 7, the curve's constant. -/
def seven : Fe := Fe.ofWord 7

/-- A point of the curve other than the point at infinity. -/
structure Affine where
  private mk ::
  x : Fe
  y : Fe
  deriving Inhabited

namespace Affine

/-- Whether y is odd. -/
def isOdd (p : Affine) : Bool := p.y.isOdd == 1

/-- The same point with the other y. -/
def neg (p : Affine) : Affine := ⟨p.x, Fe.neg p.y⟩

/-- The point in the three coordinates the arithmetic uses. -/
def point (p : Affine) : Point := Point.ofAffine p.x p.y

/-- 33 bytes: 02 or 03 for an even or odd y, then x. -/
def compressed (p : Affine) : ByteArray := ByteArray.mk #[if p.isOdd then 3 else 2] ++ p.x.bytes

/-- 65 bytes: 04, x, y. -/
def uncompressed (p : Affine) : ByteArray := ByteArray.mk #[4] ++ p.x.bytes ++ p.y.bytes

/-- x alone, 32 bytes. -/
def xBytes (p : Affine) : ByteArray := p.x.bytes

end Affine

/-- A point as two coordinates, unless it is the point at infinity. For a result that is not secret. -/
def Point.toAffine? (p : Point) : Option Affine :=
  let coordinates := p.affine
  if coordinates.2.2 == 1 then none else some ⟨coordinates.1, coordinates.2.1⟩

/-- Whether `y² = x³ + 7`. -/
def onCurve (x y : Fe) : Bool := Fe.same (Fe.sqr y) (Fe.add (Fe.mul (Fe.sqr x) x) seven)

/-- The point with this x and an even y (`lift_x`), if there is one. -/
def liftX? (x : Fe) : Option Affine :=
  (Fe.sqrt? (Fe.add (Fe.mul (Fe.sqr x) x) seven)).map fun y => ⟨x, if y.isOdd == 1 then Fe.neg y else y⟩

/-- A BIP 340 public key: 32 bytes, an x below P with a point above it; the one with the even y. -/
def parseXOnly (b : ByteArray) : Option Affine := (Fe.ofBytes? b).bind liftX?

/-- A compressed public key: 02 or 03, then an x below P with a point above it. -/
def parseCompressed (b : ByteArray) : Option Affine :=
  if b.size == 33 && (b[0]! == 2 || b[0]! == 3) then
    (parseXOnly (b.extract 1 33)).map fun p => if b[0]! == 3 then p.neg else p
  else none

/-- An uncompressed public key: 04, x, y, both below P and on the curve; or the hybrid form, 06 or 07, whose
first byte must also say whether y is odd. -/
def parseUncompressed (b : ByteArray) : Option Affine :=
  if b.size == 65 && (b[0]! == 4 || b[0]! == 6 || b[0]! == 7) then
    (Fe.ofBytes? (b.extract 1 33)).bind fun x => (Fe.ofBytes? (b.extract 33 65)).bind fun y =>
      if onCurve x y && (b[0]! == 4 || ((y.isOdd == 1) == (b[0]! == 7))) then some ⟨x, y⟩ else none
  else none

/-- A number that is not secret, as 32 bytes below N: a tweak, or a number out of a signature. -/
def scalar? (b : ByteArray) : Option Sc :=
  if b.size == 32 && Sc.isBelowN b == 1 then some (Sc.ofBytes b) else none

/-- `t·G`, for a `t` that is not secret; nothing for zero. -/
def generatorMul (t : Sc) : Option Affine := (Point.mulPublic t Point.generator).toAffine?

/-- `t·G + P`, for a `t` that is not secret; nothing when the sum is the point at infinity. -/
def pointAdd (p : Affine) (t : Sc) : Option Affine :=
  (Point.add (Point.mulPublic t Point.generator) p.point).toAffine?

/-- `k·P`, for a `k` that may be secret: the multiplication does the same work whatever `k` is. Whether the
product is a point is looked at afterwards (it is, for every `k` from 1 to N − 1). -/
def pointMul (k : Sc) (p : Affine) : Option Affine := (Point.mul k p.point).toAffine?

/-- The sum of points; nothing when it is the point at infinity, or for no points at all. -/
def combine (points : List Affine) : Option Affine :=
  (points.foldl (fun sum p => Point.add sum p.point) Point.infinity).toAffine?

/-- The public point of a secret number, by the multiplication that does the same work whatever it is;
nothing for zero. -/
def publicPoint (d : Sc) : Option Affine := (Point.mulGenerator d).toAffine?

/-- `d`, or `N − d` if `d·G` has an odd y: the key BIP 340 and BIP 341 mean by a secret, the one whose public
point has an even y. Chosen by a mask. -/
def evenKey (d : Sc) : Sc := Sc.negIf (Point.mulGenerator d).affine.2.1.isOdd d

/-! ## BIP 340 verification -/

/-- Whether the 64 bytes `signature` are a BIP 340 signature of `message` under the 32-byte public key
`key`: for `r` and `s` out of the signature and `e` the challenge, `s·G − e·P` is a point with an even y
whose x is `r`. -/
def verify (signature message key : ByteArray) : Bool :=
  signature.size == 64 &&
  ((parseXOnly key).bind fun p => (Fe.ofBytes? (signature.extract 0 32)).bind fun r =>
    (scalar? (signature.extract 32 64)).bind fun s =>
      let e := Sc.ofBytes (Secp.Sha256.tagged "BIP0340/challenge" (r.bytes ++ p.x.bytes ++ message))
      (Point.add (Point.mulPublic s Point.generator) (Point.mulPublic e p.point).neg).toAffine?.filter fun sum =>
        !sum.isOdd && Fe.same sum.x r).isSome

/-- The BIP 340 signature of `message` under `secret`, checked under the signer's own public key before it is
returned. `none` if `secret` is not a key or `aux` is not 32 bytes. -/
def signVerified (secret message aux : ByteArray) : Option ByteArray :=
  (sign secret message aux).filter fun signature =>
    (publicKey secret).any fun key => verify signature message key.1

end SecpCt
