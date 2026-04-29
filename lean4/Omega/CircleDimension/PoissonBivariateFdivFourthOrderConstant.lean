import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateSecondOrderNormalForm
import Omega.CircleDimension.PoissonKernelDerivativeL1Energy

namespace Omega.CircleDimension

/-- The variance mode appearing in the fourth-order `f`-divergence constant is the pure-variance
piece of the second-order normal form, rescaled so that its coefficient is exactly
`σ_γ² - σ_δ²`. -/
noncomputable def poissonBivariateFourthOrderVarianceMode
    (sigmaGamma2 sigmaDelta2 : ℝ) : ℝ :=
  2 * poissonBivariateShiftedQuadraticTerm 1 sigmaGamma2 sigmaDelta2 0

/-- The covariance mode appearing in the same constant is the pure-covariance piece of the
second-order normal form. -/
noncomputable def poissonBivariateFourthOrderCovarianceMode (sigmaGammaDelta : ℝ) : ℝ :=
  poissonBivariateShiftedQuadraticTerm 1 0 0 (-sigmaGammaDelta)

/-- The even kernel-energy integral attached to the Cauchy profile `u₁`. -/
noncomputable def poissonBivariateFourthOrderEvenEnergy : ℝ :=
  poissonKernelSecondEnergy 1 / 4

/-- The odd kernel-energy integral attached to the Cauchy profile `u₂`. -/
noncomputable def poissonBivariateFourthOrderOddEnergy : ℝ :=
  poissonKernelSecondEnergy 1

/-- The quadratic invariant controlling the fourth-order `f`-divergence asymptotic constant. -/
noncomputable def poissonBivariateFourthOrderQuadraticInvariant
    (sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : ℝ :=
  (sigmaGamma2 - sigmaDelta2) ^ 2 / 8 + sigmaGammaDelta ^ 2 / 2

/-- The leading-order energy before simplifying the two profile integrals. -/
noncomputable def poissonBivariateFourthOrderEnergyExpansion
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : ℝ :=
  (fpp1 / 2) *
    (poissonBivariateFourthOrderEvenEnergy *
        (poissonBivariateFourthOrderVarianceMode sigmaGamma2 sigmaDelta2) ^ 2 +
      poissonBivariateFourthOrderOddEnergy *
        (poissonBivariateFourthOrderCovarianceMode sigmaGammaDelta) ^ 2)

/-- Publication-facing wrapper for the fourth-order sharp `f`-divergence constant in the
bivariate Poisson/Cauchy setting.
    prop:cdim-poisson-bivariate-fdiv-fourth-order-constant -/
def PoissonBivariateFdivFourthOrderConstant
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) : Prop :=
  poissonBivariateFourthOrderEnergyExpansion fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta =
    fpp1 * poissonBivariateFourthOrderQuadraticInvariant
      sigmaGamma2 sigmaDelta2 sigmaGammaDelta

theorem paper_cdim_poisson_bivariate_fdiv_fourth_order_constant
    (fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta : ℝ) :
    PoissonBivariateFdivFourthOrderConstant fpp1 sigmaGamma2 sigmaDelta2 sigmaGammaDelta := by
  have hCancel := paper_cdim_poisson_bivariate_second_order_cancellation_realizable
  have _hrealizable : poissonBivariateRealizableWitness := hCancel.2.2
  have hEnergy : poissonKernelSecondEnergy 1 = 1 := by
    simpa using (paper_cdim_poisson_kernel_derivative_l1_energy 1 zero_lt_one).2.2.2
  unfold PoissonBivariateFdivFourthOrderConstant poissonBivariateFourthOrderEnergyExpansion
    poissonBivariateFourthOrderQuadraticInvariant poissonBivariateFourthOrderVarianceMode
    poissonBivariateFourthOrderCovarianceMode poissonBivariateFourthOrderEvenEnergy
    poissonBivariateFourthOrderOddEnergy
  rw [hEnergy]
  simp [poissonBivariateShiftedQuadraticTerm]
  ring

end Omega.CircleDimension
