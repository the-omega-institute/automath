import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateSecondOrderCancellationRealizable

namespace Omega.CircleDimension

/-- The first-order term in the shifted bivariate Poisson expansion. Centering forces it to
vanish. -/
noncomputable def poissonBivariateShiftedLinearTerm (t meanGamma meanDelta : ℝ) : ℝ :=
  meanGamma / t - meanDelta / t

/-- The quadratic normal form obtained after using harmonicity to trade the `t`-second derivative
for the negative `x`-second derivative and then rewriting that derivative through the variance and
covariance package. -/
noncomputable def poissonBivariateShiftedQuadraticTerm
    (t varGamma varDelta covGammaDelta : ℝ) : ℝ :=
  (((varGamma - varDelta) / 2) - covGammaDelta) / t ^ 2

/-- The explicit cubic-decay remainder retained after the second-order truncation. -/
noncomputable def poissonBivariateShiftedRemainder (t remainderCoeff : ℝ) : ℝ :=
  remainderCoeff / t ^ 3

/-- After centering kills the first-order terms, harmonicity replaces the `t`-second derivative by
minus the `x`-second derivative, and the latter is identified with the variance difference, the
shifted bivariate Poisson expansion takes the stated second-order normal form.
    prop:cdim-poisson-bivariate-second-order-normal-form -/
theorem paper_cdim_poisson_bivariate_second_order_normal_form
    (t meanGamma meanDelta dtt dxx varGamma varDelta covGammaDelta remainderCoeff : ℝ)
    (ht : t ≠ 0) (hmeanGamma : meanGamma = 0) (hmeanDelta : meanDelta = 0)
    (hharm : dtt = -dxx) (hxx : dxx = varDelta - varGamma) :
    poissonBivariateShiftedLinearTerm t meanGamma meanDelta +
        dtt / (2 * t ^ 2) - covGammaDelta / t ^ 2 +
        poissonBivariateShiftedRemainder t remainderCoeff =
      poissonBivariateShiftedQuadraticTerm t varGamma varDelta covGammaDelta +
        poissonBivariateShiftedRemainder t remainderCoeff := by
  have hcancel := paper_cdim_poisson_bivariate_second_order_cancellation_realizable
  have _hrealizable : poissonBivariateRealizableWitness := hcancel.2.2
  subst meanGamma meanDelta dtt dxx
  unfold poissonBivariateShiftedLinearTerm poissonBivariateShiftedQuadraticTerm
    poissonBivariateShiftedRemainder
  field_simp [ht]
  ring

end Omega.CircleDimension
