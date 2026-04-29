import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-bulk-curvature-mass-quantization`. If each logistic-kernel component
has unit mass, the bulk curvature mass is the number of components times the common scale. -/
theorem paper_xi_bulk_curvature_mass_quantization (κ : ℕ) (hκ : 1 ≤ κ)
    (massPhi : Fin κ → ℝ) (Kmass : ℝ) (hPhi : ∀ j, massPhi j = 1)
    (hK : Kmass = (2 * κ - 1 : ℝ) * ∑ j : Fin κ, massPhi j) :
    Kmass = (κ : ℝ) * (2 * κ - 1 : ℝ) ∧ ∀ j : Fin κ, massPhi j = 1 := by
  have _hκ_pos : (0 : ℝ) < (κ : ℝ) := by exact_mod_cast hκ
  have hsum : (∑ j : Fin κ, massPhi j) = (κ : ℝ) := by
    calc
      (∑ j : Fin κ, massPhi j) = ∑ _j : Fin κ, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact hPhi j
      _ = (κ : ℝ) := by simp
  constructor
  · calc
      Kmass = (2 * κ - 1 : ℝ) * (κ : ℝ) := by
        rw [hK, hsum]
      _ = (κ : ℝ) * (2 * κ - 1 : ℝ) := by ring
  · exact hPhi

end Omega.Zeta
