import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateFdivFourthOrderComplexM2
import Omega.CircleDimension.PoissonBivariateFdivSixthOrderComplexM3

namespace Omega.CircleDimension

private lemma sumsq_eq_zero_iff {a b : ℝ} :
    a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha2 : a ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h]
    have hb2 : b ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h]
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    ring

noncomputable def poissonBivariateEntropyDissipationFourthLeading
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : ℝ :=
  (fpp1 / 2) * ((sigmaGamma2 - sigmaDelta2) ^ 2 + (2 * sigmaGammaDelta) ^ 2)

noncomputable def poissonBivariateEntropyDissipationSixthLeading
    (fpp1 k300 k210 k120 k030 : ℝ) : ℝ :=
  (9 * fpp1 / 16) * (((3 * k120 - k300) ^ 2) + ((3 * k210 - k030) ^ 2))

def poissonBivariateVarianceCancellation
    (sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : Prop :=
  sigmaGamma2 = sigmaDelta2 ∧ sigmaGammaDelta = 0

def poissonBivariateCubicCancellation (k300 k210 k120 k030 : ℝ) : Prop :=
  k300 = 3 * k120 ∧ k030 = 3 * k210

/-- Paper-facing entropy-dissipation package for the bivariate Poisson asymptotics: the
fourth-order dissipation is the derivative of the quadratic KL term and the sixth-order
dissipation is the derivative of the cubic term, so positivity of the common prefactor forces the
rigidity cases exactly when the corresponding moment-cancellation square sums vanish.
    prop:cdim-poisson-bivariate-entropy-dissipation-asymptotics-rigidity -/
theorem paper_cdim_poisson_bivariate_entropy_dissipation_asymptotics_rigidity
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta k300 k210 k120 k030 D4 D6 : ℝ)
    (hfpp1 : 0 < fpp1)
    (hD4 :
      D4 =
        4 * (fpp1 * poissonBivariateFourthOrderQuadraticInvariant
          sigmaGamma2 sigmaDelta2 sigmaGammaDelta))
    (hD6 :
      D6 =
        6 * (fpp1 * ((3 / 32 : ℝ) *
          (((3 * k120 - k300) ^ 2) + ((3 * k210 - k030) ^ 2))))) :
    D4 = poissonBivariateEntropyDissipationFourthLeading
        fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta ∧
      D6 = poissonBivariateEntropyDissipationSixthLeading fpp1 k300 k210 k120 k030 ∧
      (D4 = 0 ↔
        poissonBivariateVarianceCancellation sigmaGamma2 sigmaDelta2 sigmaGammaDelta) ∧
      (D6 = 0 ↔ poissonBivariateCubicCancellation k300 k210 k120 k030) := by
  have h4 :=
    paper_cdim_poisson_bivariate_fdiv_fourth_order_complex_m2
      fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta
  have h6 :=
    paper_cdim_poisson_bivariate_fdiv_sixth_order_complex_m3
      fpp1 k300 k210 k120 k030
  have hD4_formula :
      D4 =
        poissonBivariateEntropyDissipationFourthLeading
          fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta := by
    rw [hD4]
    dsimp [poissonBivariateEntropyDissipationFourthLeading]
    linarith [h4]
  have hD6_formula :
      D6 = poissonBivariateEntropyDissipationSixthLeading fpp1 k300 k210 k120 k030 := by
    rw [hD6]
    dsimp [poissonBivariateEntropyDissipationSixthLeading]
    linarith [h6]
  have hD4_rigidity :
      D4 = 0 ↔ poissonBivariateVarianceCancellation sigmaGamma2 sigmaDelta2 sigmaGammaDelta := by
    rw [hD4_formula]
    dsimp [poissonBivariateEntropyDissipationFourthLeading, poissonBivariateVarianceCancellation]
    have hcoeff : 0 < fpp1 / 2 := by positivity
    constructor
    · intro hzero
      have hsum :
          (sigmaGamma2 - sigmaDelta2) ^ 2 + (2 * sigmaGammaDelta) ^ 2 = 0 := by
        nlinarith
      have hpair := (sumsq_eq_zero_iff
        (a := sigmaGamma2 - sigmaDelta2) (b := 2 * sigmaGammaDelta)).1 hsum
      rcases hpair with ⟨hvar, hcov⟩
      constructor
      · nlinarith
      · nlinarith
    · rintro ⟨hvar, hcov⟩
      simp [hvar, hcov]
  have hD6_rigidity : D6 = 0 ↔ poissonBivariateCubicCancellation k300 k210 k120 k030 := by
    rw [hD6_formula]
    dsimp [poissonBivariateEntropyDissipationSixthLeading, poissonBivariateCubicCancellation]
    have hcoeff : 0 < 9 * fpp1 / 16 := by positivity
    constructor
    · intro hzero
      have hsum :
          ((3 * k120 - k300) ^ 2) + ((3 * k210 - k030) ^ 2) = 0 := by
        nlinarith
      have hpair := (sumsq_eq_zero_iff
        (a := 3 * k120 - k300) (b := 3 * k210 - k030)).1 hsum
      rcases hpair with ⟨hodd, heven⟩
      constructor <;> nlinarith
    · rintro ⟨hodd, heven⟩
      simp [hodd, heven]
  exact ⟨hD4_formula, hD6_formula, hD4_rigidity, hD6_rigidity⟩

end Omega.CircleDimension
