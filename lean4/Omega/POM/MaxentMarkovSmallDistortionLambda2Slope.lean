import Mathlib.Tactic
import Omega.POM.MaxentMarkovLaguerreSecularSpectrum

namespace Omega.POM

/-- The linearized second eigenvalue branch in the one-pole small-distortion model. -/
def pom_maxent_markov_small_distortion_lambda2_slope_lambda2
    (D : MaxentMarkovLaguerreSecularSpectrumData) (δ : ℝ) : ℝ :=
  1 - D.kappa * δ

/-- The first-order slope coefficient is the unique secular root from the audited one-pole model.
-/
def pom_maxent_markov_small_distortion_lambda2_slope_mu2
    (D : MaxentMarkovLaguerreSecularSpectrumData) : ℝ :=
  D.kappa

/-- Uniqueness of the second-eigenvalue slope coefficient, expressed through the secular equation.
-/
def pom_maxent_markov_small_distortion_lambda2_slope_unique_mu2
    (D : MaxentMarkovLaguerreSecularSpectrumData) : Prop :=
  ∀ μ : ℝ, (∀ z : ℝ, D.secularPolynomial z = 0 ↔ z = μ) → μ = D.kappa

/-- Paper label: `thm:pom-maxent-markov-small-distortion-lambda2-slope`. In the audited one-pole
model, the second eigenvalue branch is exactly linear with slope `μ₂ = κ`, and the secular-root
certificate identifies `κ` uniquely. -/
theorem paper_pom_maxent_markov_small_distortion_lambda2_slope
    (D : MaxentMarkovLaguerreSecularSpectrumData) :
    (∀ δ : ℝ,
      1 - pom_maxent_markov_small_distortion_lambda2_slope_lambda2 D δ =
        pom_maxent_markov_small_distortion_lambda2_slope_mu2 D * δ) ∧
      pom_maxent_markov_small_distortion_lambda2_slope_unique_mu2 D := by
  refine ⟨?_, ?_⟩
  · intro δ
    simp [pom_maxent_markov_small_distortion_lambda2_slope_lambda2,
      pom_maxent_markov_small_distortion_lambda2_slope_mu2]
  · intro μ hμ
    have hrootκ := pom_maxent_markov_laguerre_secular_spectrum_root_iff D D.kappa
    have hμκ : D.kappa = μ := (hμ D.kappa).1 (hrootκ.2 rfl)
    exact hμκ.symm

end Omega.POM
