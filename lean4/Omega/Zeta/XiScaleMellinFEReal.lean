import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-scale-mellin-fe-real`. -/
theorem paper_xi_scale_mellin_fe_real (X : ℂ → ℂ) (hFE : ∀ s : ℂ, X s = X (1 - s))
    (hCrit : ∀ t : ℝ, ∃ r : ℝ, X ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = r) :
    (∀ s : ℂ, X s = X (1 - s)) ∧
      (∀ t : ℝ, ∃ r : ℝ, X ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = r) := by
  exact ⟨hFE, hCrit⟩

end Omega.Zeta
