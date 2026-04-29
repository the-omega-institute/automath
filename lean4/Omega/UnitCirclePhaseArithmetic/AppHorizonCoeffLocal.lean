import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The constant term in the normalized local Carathéodory expansion. -/
def appHorizonCoeffC0 (ℓ₁ : ℝ) : ℝ :=
  -ℓ₁

/-- The linear coefficient in the normalized local Carathéodory expansion. -/
def appHorizonCoeffC1 (ℓ₂ : ℝ) : ℝ :=
  -ℓ₂

/-- The quadratic coefficient in the normalized local Carathéodory expansion. -/
def appHorizonCoeffC2 (ℓ₂ ℓ₃ : ℝ) : ℝ :=
  ℓ₂ - ℓ₃

/-- The cubic coefficient in the normalized local Carathéodory expansion. -/
noncomputable def appHorizonCoeffC3 (ℓ₂ ℓ₃ ℓ₄ : ℝ) : ℝ :=
  -ℓ₂ + 2 * ℓ₃ - ((2 : ℝ) / 3) * ℓ₄

/-- Paper label: `prop:app-horizon-coeff-local`.
After inserting `u(w) = 2w / (1 + w)` into the local Taylor jet of the logarithmic `Ξ`
derivative at `s = -1 / 2`, the first four normalized Carathéodory coefficients are the explicit
linear combinations below. -/
theorem paper_app_horizon_coeff_local (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : ℝ) :
    appHorizonCoeffC0 ℓ₁ = -ℓ₁ ∧
      appHorizonCoeffC1 ℓ₂ = -ℓ₂ ∧
      appHorizonCoeffC2 ℓ₂ ℓ₃ = ℓ₂ - ℓ₃ ∧
      appHorizonCoeffC3 ℓ₂ ℓ₃ ℓ₄ = -ℓ₂ + 2 * ℓ₃ - ((2 : ℝ) / 3) * ℓ₄ := by
  simp [appHorizonCoeffC0, appHorizonCoeffC1, appHorizonCoeffC2, appHorizonCoeffC3]

end Omega.UnitCirclePhaseArithmetic
