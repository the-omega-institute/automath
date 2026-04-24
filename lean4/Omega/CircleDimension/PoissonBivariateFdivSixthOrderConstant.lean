import Mathlib.Tactic
import Omega.CircleDimension.PoissonBivariateSecondOrderCancellationRealizable

namespace Omega.CircleDimension

/-- The odd third-order profile coefficient extracted from the cubic Poisson/Cauchy normal form. -/
noncomputable def poissonBivariateSixthOrderOddMode (kappa300 kappa120 : ℝ) : ℝ :=
  (3 * kappa120 - kappa300) / 6

/-- The even third-order profile coefficient extracted from the cubic Poisson/Cauchy normal form. -/
noncomputable def poissonBivariateSixthOrderEvenMode (kappa210 kappa030 : ℝ) : ℝ :=
  (3 * kappa210 - kappa030) / 6

/-- The common `L²(G(y)dy)` energy of the odd cubic profile. -/
noncomputable def poissonBivariateSixthOrderOddEnergy : ℝ := 27 / 4

/-- The common `L²(G(y)dy)` energy of the even cubic profile. -/
noncomputable def poissonBivariateSixthOrderEvenEnergy : ℝ := 27 / 4

/-- The cubic fingerprint invariant controlling the sixth-order `f`-divergence asymptotic. -/
noncomputable def poissonBivariateSixthOrderCubicFingerprintInvariant
    (kappa300 kappa210 kappa120 kappa030 : ℝ) : ℝ :=
  (3 * kappa120 - kappa300) ^ 2 + (3 * kappa210 - kappa030) ^ 2

/-- The sixth-order energy before plugging in the common odd/even profile value `27/4`. -/
noncomputable def poissonBivariateSixthOrderEnergyExpansion
    (fpp1 kappa300 kappa210 kappa120 kappa030 : ℝ) : ℝ :=
  (fpp1 / 2) *
    (poissonBivariateSixthOrderOddEnergy *
        (poissonBivariateSixthOrderOddMode kappa300 kappa120) ^ 2 +
      poissonBivariateSixthOrderEvenEnergy *
        (poissonBivariateSixthOrderEvenMode kappa210 kappa030) ^ 2)

/-- Publication-facing wrapper for the sixth-order sharp `f`-divergence constant in the
bivariate Poisson/Cauchy setting.
    prop:cdim-poisson-bivariate-fdiv-sixth-order-constant -/
def PoissonBivariateFdivSixthOrderConstant
    (fpp1 kappa300 kappa210 kappa120 kappa030 : Real) : Prop :=
  poissonBivariateSixthOrderEnergyExpansion fpp1 kappa300 kappa210 kappa120 kappa030 =
    fpp1 * (3 / 32) *
      poissonBivariateSixthOrderCubicFingerprintInvariant
        kappa300 kappa210 kappa120 kappa030

theorem paper_cdim_poisson_bivariate_fdiv_sixth_order_constant
    (fpp1 kappa300 kappa210 kappa120 kappa030 : Real) :
    PoissonBivariateFdivSixthOrderConstant fpp1 kappa300 kappa210 kappa120 kappa030 := by
  have hCancel := paper_cdim_poisson_bivariate_second_order_cancellation_realizable
  have _hrealizable : poissonBivariateRealizableWitness := hCancel.2.2
  unfold PoissonBivariateFdivSixthOrderConstant poissonBivariateSixthOrderEnergyExpansion
    poissonBivariateSixthOrderCubicFingerprintInvariant poissonBivariateSixthOrderOddEnergy
    poissonBivariateSixthOrderEvenEnergy poissonBivariateSixthOrderOddMode
    poissonBivariateSixthOrderEvenMode
  ring

end Omega.CircleDimension
