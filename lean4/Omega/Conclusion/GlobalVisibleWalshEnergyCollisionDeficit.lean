import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-global-visible-walsh-energy-collision-deficit`. Summing the
fiberwise Walsh-energy identity and substituting the collision probability gives the global
visible-energy deficit. -/
theorem paper_conclusion_global_visible_walsh_energy_collision_deficit {X : Type*} [Fintype X]
    (m : ℕ) (d energy : X → ℝ) (Col : ℝ)
    (hEnergy : ∀ x, energy x = (2 : ℝ) ^ m * d x - d x ^ 2)
    (hPartition : (∑ x, d x) = (2 : ℝ) ^ m)
    (hCol : Col = (∑ x, d x ^ 2) / (2 : ℝ) ^ (2 * m)) :
    (∑ x, energy x) = (2 : ℝ) ^ (2 * m) * (1 - Col) := by
  have hsum :
      (∑ x, energy x) = (2 : ℝ) ^ m * (∑ x, d x) - ∑ x, d x ^ 2 := by
    simp [hEnergy, Finset.sum_sub_distrib, Finset.mul_sum]
  have hpow : (2 : ℝ) ^ (2 * m) = (2 : ℝ) ^ m * (2 : ℝ) ^ m := by
    rw [show 2 * m = m + m by omega, pow_add]
  have hpow_ne : (2 : ℝ) ^ (2 * m) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
  calc
    (∑ x, energy x) = (2 : ℝ) ^ m * (∑ x, d x) - ∑ x, d x ^ 2 := hsum
    _ = (2 : ℝ) ^ (2 * m) - ∑ x, d x ^ 2 := by rw [hPartition, hpow]
    _ = (2 : ℝ) ^ (2 * m) * (1 - Col) := by
      rw [hCol]
      field_simp [hpow_ne]

end Omega.Conclusion
