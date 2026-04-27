import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-bulk-curvature-moment-generating-factorization`. -/
theorem paper_xi_bulk_curvature_moment_generating_factorization (κ : ℕ) (hκ : 0 < κ)
    (σ : Fin κ → ℝ) (exp : ℝ → ℝ) (Mp kernel : ℝ → ℝ)
    (hFactor :
      ∀ t, Mp t = kernel t * ((1 / (κ : ℝ)) * ∑ j : Fin κ, exp (t * σ j)))
    (hKernel : ∀ t, kernel t ≠ 0) :
    ∀ t, (kernel t)⁻¹ * Mp t = (1 / (κ : ℝ)) * ∑ j : Fin κ, exp (t * σ j) := by
  intro t
  rw [hFactor t]
  field_simp [hKernel t]

end Omega.Zeta
