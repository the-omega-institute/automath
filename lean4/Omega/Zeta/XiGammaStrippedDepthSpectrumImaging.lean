import Mathlib.Tactic
import Omega.Zeta.XiBulkCurvatureMomentGeneratingFactorization

namespace Omega.Zeta

/-- Paper label: `prop:xi-gamma-stripped-depth-spectrum-imaging`. -/
theorem paper_xi_gamma_stripped_depth_spectrum_imaging (κ : ℕ) (hκ : 0 < κ)
    (σ : Fin κ → ℝ) (Mp gammaKernel : ℝ → ℝ)
    (hFactor : ∀ t, |t| < 1 →
      Mp t = gammaKernel t * ((1 / (κ : ℝ)) * ∑ j : Fin κ, Real.exp (t * σ j)))
    (hKernel : ∀ t, |t| < 1 → gammaKernel t ≠ 0) :
    ∀ t, |t| < 1 →
      (gammaKernel t)⁻¹ * Mp t = (1 / (κ : ℝ)) * ∑ j : Fin κ, Real.exp (t * σ j) := by
  intro t ht
  rw [hFactor t ht]
  field_simp [hKernel t ht]

end Omega.Zeta
