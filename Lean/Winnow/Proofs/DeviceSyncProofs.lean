import Winnow.Wallet.DeviceSync

/-! # Proofs for `Winnow.DeviceSync`

Moved out of runtime `Winnow/Wallet/DeviceSync.lean` so runtime modules contain zero theorems.
Phase 1 establishes the `Stamp` join-semilattice and clock-monotonicity laws; Phase 4 extends this file
with replica metadata convergence and `Existence.reassert` funded-account protection. -/

namespace Winnow.Proofs.DeviceSync
open Winnow.DeviceSync

theorem Stamp.lt_def (a b : Stamp) : a < b ↔ a.time < b.time ∨ (a.time = b.time ∧ a.device < b.device) := Iff.rfl

theorem Stamp.max_idem (a : Stamp) : Stamp.max a a = a := by
  simp [Stamp.max]

theorem Stamp.max_comm (a b : Stamp) : Stamp.max a b = Stamp.max b a := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  simp only [Stamp.max, Stamp.lt_def]
  split <;> split <;> first | rfl | (simp only [Stamp.mk.injEq]; omega)

theorem Stamp.max_assoc (a b c : Stamp) : Stamp.max (Stamp.max a b) c = Stamp.max a (Stamp.max b c) := by
  obtain ⟨at_, ad⟩ := a
  obtain ⟨bt, bd⟩ := b
  obtain ⟨ct, cd⟩ := c
  by_cases h1 : at_ < bt ∨ (at_ = bt ∧ ad < bd) <;> by_cases h2 : bt < ct ∨ (bt = ct ∧ bd < cd) <;>
    by_cases h3 : at_ < ct ∨ (at_ = ct ∧ ad < cd) <;> simp [Stamp.max, Stamp.lt_def, h1, h2, h3] <;> omega

theorem Stamp.after_later (clock now device : Nat) (s : Stamp) (h : s.time ≤ clock) :
    s < Stamp.after clock now device := by
  simp only [Stamp.lt_def, Stamp.after]
  left
  have : clock + 1 ≤ Nat.max now (clock + 1) := Nat.le_max_right _ _
  omega

end Winnow.Proofs.DeviceSync
