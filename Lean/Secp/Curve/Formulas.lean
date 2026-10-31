import Secp.Curve.Spec

/-! # The Jacobian formulas, once, over any `+ - *`

Written generically so the same text runs on the limb field and is reasoned about in `Fin P`
(`*_map` carries one to the other), and so proofs never see the formulas unfolded into a tree.
The `*_correct` theorems are the algebra: with `x = X/Z²`, `y = Y/Z³`, the formulas compute the
spec's tangent and chord. Inverses appear only as witnesses `a * w = 1`. -/

namespace Secp

/-- dbl-2009-l with a = 0: `2·(X, Y, Z)`. -/
def dblF {α : Type} [Add α] [Sub α] [Mul α] (X Y Z : α) : α × α × α :=
  let A := X * X
  let B := Y * Y
  let C := B * B
  let t := (X + B) * (X + B) - A - C
  let D := t + t
  let E := A + A + A
  let F := E * E
  let X3 := F - (D + D)
  let C2 := C + C; let C4 := C2 + C2; let C8 := C4 + C4
  let Y3 := E * (D - X3) - C8
  let Z3 := (Y + Y) * Z
  (X3, Y3, Z3)

/-- The two differences madd-2007-bl branches on: `H = x2·Z² - X`, `R = y2·Z³ - Y`. -/
def hrF {α : Type} [Sub α] [Mul α] (X Y Z x2 y2 : α) : α × α :=
  let Z1Z1 := Z * Z
  (x2 * Z1Z1 - X, y2 * Z * Z1Z1 - Y)

/-- madd-2007-bl: `(X, Y, Z) + (x2, y2)` when `H ≠ 0`. -/
def maddF {α : Type} [Add α] [Sub α] [Mul α] (X Y Z x2 y2 : α) : α × α × α :=
  let Z1Z1 := Z * Z
  let H := x2 * Z1Z1 - X
  let R := y2 * Z * Z1Z1 - Y
  let HH := H * H
  let I2 := HH + HH; let I := I2 + I2
  let J := H * I
  let r := R + R
  let V := X * I
  let X3 := r * r - J - (V + V)
  let Y3 := r * (V - X3) - (Y + Y) * J
  let Z3 := (Z + H) * (Z + H) - Z1Z1 - HH
  (X3, Y3, Z3)

theorem dblF_map (X Y Z : Fq) :
    ((dblF X Y Z).1.toF, (dblF X Y Z).2.1.toF, (dblF X Y Z).2.2.toF) = dblF X.toF Y.toF Z.toF := by
  simp only [dblF, Fq.toF_mul, Fq.toF_add, Fq.toF_sub]

theorem hrF_map (X Y Z x2 y2 : Fq) :
    ((hrF X Y Z x2 y2).1.toF, (hrF X Y Z x2 y2).2.toF) = hrF X.toF Y.toF Z.toF x2.toF y2.toF := by
  simp only [hrF, Fq.toF_mul, Fq.toF_sub]

theorem maddF_map (X Y Z x2 y2 : Fq) :
    ((maddF X Y Z x2 y2).1.toF, (maddF X Y Z x2 y2).2.1.toF, (maddF X Y Z x2 y2).2.2.toF)
      = maddF X.toF Y.toF Z.toF x2.toF y2.toF := by
  simp only [maddF, Fq.toF_mul, Fq.toF_add, Fq.toF_sub]

open Spec

theorem dblF_Z (X Y Z : F) : (dblF X Y Z).2.2 = 2 * Y * Z := by simp only [dblF]; grind

theorem dblF_correct (X Y Z w v w3 : F) (hw : Z * w = 1)
    (hv : 2 * (Y * (w * w * w)) * v = 1) (hw3 : (dblF X Y Z).2.2 * w3 = 1) :
    let x1 := X * (w * w); let y1 := Y * (w * w * w)
    let l := 3 * x1 * x1 * v
    let x3 := l * l - 2 * x1
    (dblF X Y Z).1 * (w3 * w3) = x3 ∧ (dblF X Y Z).2.1 * (w3 * w3 * w3) = l * (x1 - x3) - y1 := by
  simp only [dblF] at hw3 ⊢
  constructor <;> grind

theorem hrF_eq (X Y Z x2 y2 w : F) (hw : Z * w = 1) :
    (hrF X Y Z x2 y2).1 = (x2 - X * (w * w)) * (Z * Z)
      ∧ (hrF X Y Z x2 y2).2 = (y2 - Y * (w * w * w)) * (Z * Z * Z) := by
  simp only [hrF]; constructor <;> grind

theorem maddF_Z (X Y Z x2 y2 : F) : (maddF X Y Z x2 y2).2.2 = 2 * Z * (hrF X Y Z x2 y2).1 := by
  simp only [maddF, hrF]; grind

theorem maddF_correct (X Y Z x2 y2 w v w3 : F) (hw : Z * w = 1)
    (hv : (x2 - X * (w * w)) * v = 1) (hw3 : (maddF X Y Z x2 y2).2.2 * w3 = 1) :
    let x1 := X * (w * w); let y1 := Y * (w * w * w)
    let l := (y2 - y1) * v
    let x3 := l * l - x1 - x2
    (maddF X Y Z x2 y2).1 * (w3 * w3) = x3 ∧ (maddF X Y Z x2 y2).2.1 * (w3 * w3 * w3) = l * (x1 - x3) - y1 := by
  simp only [maddF] at hw3 ⊢
  constructor <;> grind

end Secp
