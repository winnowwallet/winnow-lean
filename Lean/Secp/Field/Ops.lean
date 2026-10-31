import Secp.Field.Fp

/-! # More field operations

Constants and conversions from `Nat`, negation, parity and exponentiation, plus the two
operations whose success is not proven: the inverse (extended Euclid on `Nat`) and the square
root (`c^((P+1)/4)`). Both multiply their answer back and return `none` unless it checks, so
`inv?_spec` and `sqrt?_spec` hold with no assumption about `P`. -/

namespace Secp

/-- The four limbs of `n mod 2^256`. -/
def toLimbs (n : Nat) : List UInt64 :=
  [UInt64.ofNat n, UInt64.ofNat (n / 2^64), UInt64.ofNat (n / 2^128), UInt64.ofNat (n / 2^192)]

theorem val_toLimbs (n : Nat) (h : n < 2^256) : val (toLimbs n) = n := by
  simp only [toLimbs, val_cons, val_nil, UInt64.toNat_ofNat']
  omega

def Fq.ofNat (n : Nat) : Fq :=
  ⟨toLimbs (n % P), by
    have : n % P < P := Nat.mod_lt _ (by decide)
    have := P_lt
    exact ⟨rfl, by rw [val_toLimbs _ (by omega)]; omega⟩⟩

@[simp] theorem Fq.toF_ofNat (n : Nat) : (Fq.ofNat n).toF = ⟨n % P, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp only [Fq.toF, Fq.ofNat]
  have : n % P < P := Nat.mod_lt _ (by decide)
  have := P_lt
  exact val_toLimbs _ (by omega)

def Fq.toNat (a : Fq) : Nat := val a.1

theorem Fq.toNat_eq (a : Fq) : a.toNat = a.toF.val := rfl

instance : OfNat Fq n := ⟨Fq.ofNat n⟩

def Fq.neg (a : Fq) : Fq := 0 - a
instance : Neg Fq := ⟨Fq.neg⟩

@[simp] theorem Fq.toF_zero : (0 : Fq).toF = 0 := by
  show (Fq.ofNat 0).toF = 0; rw [Fq.toF_ofNat]; rfl

@[simp] theorem Fq.toF_one : (1 : Fq).toF = 1 := by
  show (Fq.ofNat 1).toF = 1; rw [Fq.toF_ofNat]; rfl

@[simp] theorem Fq.toF_neg (a : Fq) : (-a).toF = -a.toF := by
  show (0 - a).toF = -a.toF
  rw [Fq.toF_sub, Fq.toF_zero, Fin.sub_def, Fin.neg_def]
  simp

/-- Odd as an integer below `P`: the parity BIP340 and SEC1 encodings use. -/
def Fq.isOdd (a : Fq) : Bool := a.toNat % 2 == 1

/-- `a^e`, square-and-multiply from the top bit. -/
def Fq.pow (a : Fq) (e : Nat) : Fq :=
  (List.range (Nat.log2 e + 1)).reverse.foldl (fun r i => if e.testBit i then r * r * a else r * r) 1

/-- Extended Euclid: `x` with `a * x ≡ gcd a m (mod m)`, run for a fixed number of steps. -/
def natInv (a m : Nat) : Nat := go 1024 m a 0 1
where
  go : Nat → Nat → Nat → Int → Int → Nat
    | 0, _, _, _, t => (t % (m : Int)).toNat
    | fuel + 1, r0, r1, t0, t1 =>
      if r1 = 0 then (t0 % (m : Int)).toNat
      else go fuel r1 (r0 % r1) t1 (t0 - (r0 / r1 : Nat) * t1)

/-- The inverse, or `none` when the candidate does not check. -/
def Fq.inv? (a : Fq) : Option Fq :=
  let w := Fq.ofNat (natInv a.toNat P)
  if a * w = 1 then some w else none

theorem Fq.inv?_spec {a w : Fq} (h : a.inv? = some w) : a.toF * w.toF = 1 := by
  simp only [Fq.inv?] at h
  split at h
  · rename_i hc; cases h; rw [← Fq.toF_mul, hc, Fq.toF_one]
  · cases h

/-- A square root, or `none` when the candidate does not check (`c` is not a square). -/
def Fq.sqrt? (c : Fq) : Option Fq :=
  let y := c.pow ((P + 1) / 4)
  if y * y = c then some y else none

theorem Fq.sqrt?_spec {c y : Fq} (h : c.sqrt? = some y) : y.toF * y.toF = c.toF := by
  simp only [Fq.sqrt?] at h
  split at h
  · rename_i hc; cases h; rw [← Fq.toF_mul, hc]
  · cases h

end Secp
