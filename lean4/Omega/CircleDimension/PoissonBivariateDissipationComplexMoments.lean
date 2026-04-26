import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateEntropyDissipationAsymptoticsRigidity

namespace Omega.CircleDimension

/-- Paper label: `cor:cdim-poisson-bivariate-dissipation-complex-moments`.
The entropy-dissipation constants can be rewritten in terms of the complex moments `m₂` and `m₃`,
and the same package carries the fourth-order and sixth-order rigidity criteria. -/
theorem paper_cdim_poisson_bivariate_dissipation_complex_moments
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta k300 k210 k120 k030 D4 D6 : ℝ)
    (hfpp1 : 0 < fpp1)
    (hD4 :
      D4 =
        4 * (fpp1 * poissonBivariateFourthOrderQuadraticInvariant
          sigmaGamma2 sigmaDelta2 sigmaGammaDelta))
    (hD6 :
      D6 =
        6 * (fpp1 * ((3 / 32 : ℝ) *
          (((3 * k120 - k300) ^ 2) + ((3 * k210 - k030) ^ 2)))) ) :
    let m2Re := sigmaGamma2 - sigmaDelta2
    let m2Im := 2 * sigmaGammaDelta
    let m3Re := k300 - 3 * k120
    let m3Im := 3 * k210 - k030
    D4 = (fpp1 / 2) * (m2Re ^ 2 + m2Im ^ 2) ∧
      D6 = (9 * fpp1 / 16) * (m3Re ^ 2 + m3Im ^ 2) ∧
      (D4 = 0 ↔
        poissonBivariateVarianceCancellation sigmaGamma2 sigmaDelta2 sigmaGammaDelta) ∧
      (D6 = 0 ↔ poissonBivariateCubicCancellation k300 k210 k120 k030) := by
  have hM2 :=
    paper_cdim_poisson_bivariate_fdiv_fourth_order_complex_m2
      fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta
  have hM3 :=
    paper_cdim_poisson_bivariate_fdiv_sixth_order_complex_m3
      fpp1 k300 k210 k120 k030
  rcases
      paper_cdim_poisson_bivariate_entropy_dissipation_asymptotics_rigidity
        fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta k300 k210 k120 k030 D4 D6 hfpp1 hD4 hD6 with
    ⟨hFourth, hSixth, hFourthZero, hSixthZero⟩
  dsimp at hM2 hM3 ⊢
  refine ⟨?_, ?_, hFourthZero, hSixthZero⟩
  · linarith
  · linarith

end Omega.CircleDimension
