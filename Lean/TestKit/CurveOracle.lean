import Secp.Signing

/-! # `k·G` on plain numbers, for tests only

The signing references (`Secp/Signing.lean`) take "k·G" as a function, and the theorems give them the
specification's, which does not run. A test needs one that does, and it must not be the code under test.
This is that: the textbook double-and-add on `Nat`s, in the three coordinates that put off the division to
the end. It is slow, it branches on every bit, and nothing the wallet runs imports it.

`secpct-test` and `fuzz` give it to the references and hold the signing code to what comes out, on inputs
the proofs (`SecpCt.sign_eq`, `SecpCt.Ecdsa.sign_eq`) already cover: the proofs say the source is right, and
this says the compiled code is, on the inputs tried. -/

namespace TestKit.CurveOracle
open Secp (P)

private def sub (a b : Nat) : Nat := (a + P - b % P) % P

private def power (a e : Nat) : Nat := Id.run do
  let mut r := 1
  for i in [0:256] do
    r := r * r % P
    if e.testBit (255 - i) then r := r * a % P
  return r

/-- `(X, Y, Z)` stands for the point `(X/Z², Y/Z³)`; `Z = 0` for the point at infinity. -/
private abbrev Point := Nat × Nat × Nat

private def infinity : Point := (1, 1, 0)

private def double (p : Point) : Point :=
  let (x, y, z) := p
  if z == 0 || y == 0 then infinity else
  let s := 4 * x * y * y % P
  let m := 3 * x * x % P
  let x' := sub (m * m) (2 * s)
  (x', sub (m * sub s x') (8 * y * y * y * y), 2 * y * z % P)

/-- `p` plus the point `(gx, gy)`. -/
private def add (p : Point) (gx gy : Nat) : Point :=
  let (x, y, z) := p
  if z == 0 then (gx, gy, 1) else
  let zz := z * z % P
  let h := sub (gx * zz) x
  let r := sub (gy * zz * z) y
  if h == 0 then (if r == 0 then double p else infinity) else
  let hh := h * h % P
  let x' := sub (sub (r * r) (hh * h)) (2 * x * hh)
  (x', sub (r * sub (x * hh) x') (y * hh * h), z * h % P)

/-- `k` times the generator, for `k` below 2²⁵⁶: its two coordinates, or nothing for the point at infinity. -/
def mulG : Secp.MulG := fun k => Id.run do
  let (gx, gy) := (Secp.Spec.Gx.val, Secp.Spec.Gy.val)
  let mut sum := infinity
  for i in [0:256] do
    sum := double sum
    if k.testBit (255 - i) then sum := add sum gx gy
  let (x, y, z) := sum
  if z == 0 then return none
  let inverse := power z (P - 2)
  return some (x * inverse % P * inverse % P, y * inverse % P * inverse % P * inverse % P)

end TestKit.CurveOracle
