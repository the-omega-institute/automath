import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The equilibrium slope selected by the Legendre package. -/
def einstein_legendre_alpha_star (alpha : ℝ → ℝ) : ℝ :=
  alpha 0

/-- Concrete reciprocal-curvature package: if the Legendre side already records
`I''(α(θ)) = 1 / α'(θ)` and the slope field satisfies `α'(0) = P''(0)`, then the Einstein-style
Legendre identity follows at the base point `θ = 0`. -/
def einstein_legendre_statement : Prop :=
  ∀ (P alpha I : ℝ → ℝ),
    HasDerivAt alpha (deriv (deriv P) 0) 0 →
      (∀ θ : ℝ, deriv (deriv I) (alpha θ) = 1 / deriv alpha θ) →
        deriv (deriv I) (einstein_legendre_alpha_star alpha) = 1 / deriv (deriv P) 0

/-- Paper label: `prop:einstein-legendre`. -/
theorem paper_einstein_legendre : einstein_legendre_statement := by
  intro P alpha I hAlpha hLegendre
  simp [einstein_legendre_alpha_star, hLegendre 0,
    show deriv alpha 0 = deriv (deriv P) 0 by simpa using hAlpha.deriv]

end

end Omega.SyncKernelWeighted
