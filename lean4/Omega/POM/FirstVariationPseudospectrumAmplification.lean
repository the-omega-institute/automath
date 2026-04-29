import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace Omega.POM

open Complex

/-- Paper label: `thm:pom-first-variation-pseudospectrum-amplification`.

An exact projected first-variation eigenvector, an approximate intertwining identity, a
small residual, and a nonvanishing projection produce an approximate eigenvector for `B`
at the lifted spectral point `rho^(b-1) * mu`. -/
theorem paper_pom_first_variation_pseudospectrum_amplification
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (T : E →L[ℂ] E) (B : F →L[ℂ] F) (Pi R : E →L[ℂ] F)
    (b : ℕ) (rho : ℝ) (mu : ℂ) (eps sigma : ℝ) (x : E) (hsigma : 0 < sigma)
    (heps : 0 ≤ eps) (hIntertwine : ∀ v : E, Pi (T v) = B (Pi v) + R v)
    (hEigen : T x = (((rho : ℂ) ^ (b - 1)) * mu) • x) (hResidual : ‖R x‖ ≤ eps)
    (hProjection : sigma ≤ ‖Pi x‖) :
    ∃ y : F,
      y ≠ 0 ∧
        ‖B y - (((rho : ℂ) ^ (b - 1)) * mu) • y‖ ≤ (eps / sigma) * ‖y‖ := by
  let z : ℂ := ((rho : ℂ) ^ (b - 1)) * mu
  refine ⟨Pi x, ?_, ?_⟩
  · exact norm_pos_iff.mp (lt_of_lt_of_le hsigma hProjection)
  · have hprojected : z • Pi x = B (Pi x) + R x := by
      have h := hIntertwine x
      rw [hEigen] at h
      simpa [z] using h
    have hdiff : B (Pi x) - z • Pi x = -R x := by
      rw [hprojected]
      abel
    have hscale : eps ≤ (eps / sigma) * ‖Pi x‖ := by
      calc
        eps = (eps / sigma) * sigma := by
          field_simp [hsigma.ne']
        _ ≤ (eps / sigma) * ‖Pi x‖ := by
          exact mul_le_mul_of_nonneg_left hProjection (div_nonneg heps hsigma.le)
    calc
      ‖B (Pi x) - z • Pi x‖ = ‖R x‖ := by rw [hdiff, norm_neg]
      _ ≤ eps := hResidual
      _ ≤ (eps / sigma) * ‖Pi x‖ := hscale

end Omega.POM
