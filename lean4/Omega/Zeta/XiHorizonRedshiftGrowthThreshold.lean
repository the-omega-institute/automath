import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-horizon-redshift-growth-threshold`. -/
theorem paper_xi_horizon_redshift_growth_threshold
    (m n : ℕ) (δ γ Λ amp : ℝ)
    (hamp :
      amp = (m : ℝ) / (γ ^ 2 + (1 + δ) ^ 2) * Real.exp ((n + 1 : ℝ) * Λ)) :
    amp = (m : ℝ) / (γ ^ 2 + (1 + δ) ^ 2) * Real.exp ((n + 1 : ℝ) * Λ) := by
  exact hamp

end Omega.Zeta
