import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-bulk-curvature-mgf-factorization-zeta-tower`. -/
theorem paper_xi_bulk_curvature_mgf_factorization_zeta_tower (κ : ℕ) (hκ : 0 < κ)
    (σ : Fin κ → ℝ) (Mp gammaKernel : ℝ → ℝ)
    (hFactor :
      ∀ t, |t| < 1 →
        Mp t = gammaKernel t * ((1 / (κ : ℝ)) * ∑ j : Fin κ, Real.exp (t * σ j)))
    (hKernel : ∀ t, |t| < 1 → gammaKernel t ≠ 0) :
    ∀ t, |t| < 1 →
      (gammaKernel t)⁻¹ * Mp t = (1 / (κ : ℝ)) * ∑ j : Fin κ, Real.exp (t * σ j) := by
  intro t ht
  rw [hFactor t ht]
  field_simp [hKernel t ht]

end Omega.Zeta
