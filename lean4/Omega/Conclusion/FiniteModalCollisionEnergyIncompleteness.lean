import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Omega.Conclusion

/-- Concrete finite-modal collision-energy data.  The set `A m` is the retained finite family of
Fourier modes, `a m k` is the normalized amplitude, and `collisionEnergy m` is the collision
normalization. -/
structure conclusion_finite_modal_collision_energy_incompleteness_data where
  A : ℕ → Finset ℕ
  a : ℕ → ℕ → ℝ
  collisionEnergy : ℕ → ℝ
  collisionEnergy_pos : ∀ m, 0 < collisionEnergy m
  amplitude_sq_nonneg : ∀ m k, 0 ≤ (a m k) ^ 2
  amplitude_sq_le_one : ∀ m k, (a m k) ^ 2 ≤ 1
  support_small :
    Tendsto
      (fun m : ℕ =>
        ((A m).card : ℝ) / ((Nat.fib (m + 2) : ℝ) * collisionEnergy m))
      atTop (nhds 0)

namespace conclusion_finite_modal_collision_energy_incompleteness_data

/-- The normalized partial collision energy carried by the selected finite mode set. -/
noncomputable def normalizedPartialEnergy
    (D : conclusion_finite_modal_collision_energy_incompleteness_data) (m : ℕ) : ℝ :=
  (D.A m).sum (fun k => (D.a m k) ^ 2) /
    ((Nat.fib (m + 2) : ℝ) * D.collisionEnergy m)

/-- The finite-mode energy share vanishes asymptotically. -/
def energyShareVanishes
    (D : conclusion_finite_modal_collision_energy_incompleteness_data) : Prop :=
  Tendsto D.normalizedPartialEnergy atTop (nhds 0)

end conclusion_finite_modal_collision_energy_incompleteness_data

/-- Paper label: `thm:conclusion-finite-modal-collision-energy-incompleteness`. -/
theorem paper_conclusion_finite_modal_collision_energy_incompleteness
    (D : conclusion_finite_modal_collision_energy_incompleteness_data) :
    D.energyShareVanishes := by
  classical
  refine squeeze_zero ?nonneg ?upper D.support_small
  · intro m
    have hfib_pos_nat : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
    have hfib_pos : 0 < (Nat.fib (m + 2) : ℝ) := by exact_mod_cast hfib_pos_nat
    have hden_nonneg :
        0 ≤ (Nat.fib (m + 2) : ℝ) * D.collisionEnergy m :=
      (mul_pos hfib_pos (D.collisionEnergy_pos m)).le
    have hsum_nonneg : 0 ≤ (D.A m).sum (fun k => (D.a m k) ^ 2) :=
      Finset.sum_nonneg fun k _ => D.amplitude_sq_nonneg m k
    exact div_nonneg hsum_nonneg hden_nonneg
  · intro m
    have hfib_pos_nat : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
    have hfib_pos : 0 < (Nat.fib (m + 2) : ℝ) := by exact_mod_cast hfib_pos_nat
    have hden_nonneg :
        0 ≤ (Nat.fib (m + 2) : ℝ) * D.collisionEnergy m :=
      (mul_pos hfib_pos (D.collisionEnergy_pos m)).le
    have hsum_le :
        (D.A m).sum (fun k => (D.a m k) ^ 2) ≤ ((D.A m).card : ℝ) := by
      calc
        (D.A m).sum (fun k => (D.a m k) ^ 2) ≤ (D.A m).sum (fun _k => (1 : ℝ)) := by
          exact Finset.sum_le_sum fun k _ => D.amplitude_sq_le_one m k
        _ = ((D.A m).card : ℝ) := by simp
    exact div_le_div_of_nonneg_right hsum_le hden_nonneg

end Omega.Conclusion
