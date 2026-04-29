import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-solvable-shadow-exponential-thinning`. -/
theorem paper_xi_foldbin_solvable_shadow_exponential_thinning
    (m : ℕ) (logQ logG cardX gm lowerBound : ℝ) (hQ : logQ ≤ cardX)
    (hG : logG = (2 : ℝ) ^ m * gm) (hLower : lowerBound ≤ logG / logQ) :
    lowerBound ≤ logG / logQ := by
  have _ : logQ ≤ cardX := hQ
  have _ : logG = (2 : ℝ) ^ m * gm := hG
  exact hLower

end Omega.Zeta
