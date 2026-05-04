import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-fixed-freezing-maxfiber-skeleton-projection`. -/
theorem paper_xi_fixed_freezing_maxfiber_skeleton_projection {ι : Type*} [Fintype ι]
    (π ν f : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hL1 : (∑ i, |π i - ν i|) ≤ 2 * ε) (hf : ∀ i, |f i| ≤ 1) :
    |(∑ i, π i * f i) - (∑ i, ν i * f i)| ≤ 2 * ε := by
  have _hε_nonneg : 0 ≤ ε := hε
  have hdiff :
      (∑ i, π i * f i) - (∑ i, ν i * f i) =
        ∑ i, (π i - ν i) * f i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    ring
  calc
    |(∑ i, π i * f i) - (∑ i, ν i * f i)|
        = |∑ i, (π i - ν i) * f i| := by rw [hdiff]
    _ ≤ ∑ i, |(π i - ν i) * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |π i - ν i| * |f i| := by simp [abs_mul]
    _ ≤ ∑ i, |π i - ν i| * 1 := by
      exact Finset.sum_le_sum fun i _hi =>
        mul_le_mul_of_nonneg_left (hf i) (abs_nonneg (π i - ν i))
    _ = ∑ i, |π i - ν i| := by simp
    _ ≤ 2 * ε := hL1

end Omega.Zeta
