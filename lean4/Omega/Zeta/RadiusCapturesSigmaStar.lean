import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:radius-captures-sigma-star`. -/
theorem paper_radius_captures_sigma_star {Pole : Type} (radiusOf : Pole → ℝ) (R : ℝ)
    (h_lower : ∀ ρ, R ≤ radiusOf ρ)
    (h_greatest : ∀ r, (∀ ρ, r ≤ radiusOf ρ) → r ≤ R) :
    ∀ r, (∀ ρ, r ≤ radiusOf ρ) ↔ r ≤ R := by
  intro r
  constructor
  · intro hr
    exact h_greatest r hr
  · intro hr ρ
    exact le_trans hr (h_lower ρ)

end Omega.Zeta
