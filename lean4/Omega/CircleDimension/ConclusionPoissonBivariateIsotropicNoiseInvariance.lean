import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `prop:conclusion-poisson-bivariate-isotropic-noise-invariance`. -/
theorem paper_conclusion_poisson_bivariate_isotropic_noise_invariance
    (A B A' B' KL KL' : ℝ) (hA : A' = A) (hB : B' = B)
    (hKL : KL = A ^ 2 / 8 + B ^ 2 / 2)
    (hKL' : KL' = A' ^ 2 / 8 + B' ^ 2 / 2) :
    A' = A ∧ B' = B ∧ KL' = KL := by
  subst A'
  subst B'
  subst KL
  simp [hKL']

end Omega.CircleDimension
