import Omega.Zeta.XiEndpointJensenSingleDefectAreaLaw
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-endpoint-jensen-finite-ensemble-area-law`. -/
theorem paper_xi_endpoint_jensen_finite_ensemble_area_law {J : ℕ} (m : Fin J → ℕ)
    (δ area : Fin J → ℝ)
    (harea : ∀ j, area j = 2 * Real.pi * min (δ j) 1)
    (hstrip : ∀ j, 0 < δ j ∧ δ j < 1) :
    (∑ j, (m j : ℝ) * area j = 2 * Real.pi * ∑ j, (m j : ℝ) * min (δ j) 1) ∧
      (∑ j, (m j : ℝ) * δ j =
        (1 / (2 * Real.pi)) * ∑ j, (m j : ℝ) * area j) := by
  constructor
  · calc
      ∑ j, (m j : ℝ) * area j =
          ∑ j, (m j : ℝ) * (2 * Real.pi * min (δ j) 1) := by
        simp [harea]
      _ = 2 * Real.pi * ∑ j, (m j : ℝ) * min (δ j) 1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
  · have hmin : ∀ j, min (δ j) 1 = δ j := by
      intro j
      exact min_eq_left (le_of_lt (hstrip j).2)
    calc
      ∑ j, (m j : ℝ) * δ j =
          (1 / (2 * Real.pi)) *
            (2 * Real.pi * ∑ j, (m j : ℝ) * δ j) := by
        field_simp [Real.pi_ne_zero]
      _ = (1 / (2 * Real.pi)) *
            (∑ j, (m j : ℝ) * (2 * Real.pi * min (δ j) 1)) := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hmin j]
        ring
      _ = (1 / (2 * Real.pi)) * ∑ j, (m j : ℝ) * area j := by
        congr 1
        simp [harea]

end Omega.Zeta
