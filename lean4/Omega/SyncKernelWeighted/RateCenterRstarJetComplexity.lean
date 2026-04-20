import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Local analytic data for the `R⋆`-centered jet estimate. The fields record the radius of
analyticity, the unit-root evaluation point, the boundary sup norm entering Cauchy's estimate, the
target jet order, and the logarithmic order lower bound extracted for the chosen error tolerance.
-/
structure RateCenterRstarJetComplexityData where
  Rstar : ℝ
  unitRootDistance : ℝ
  boundarySup : ℝ
  errorTolerance : ℝ
  jetOrder : ℕ
  prime : ℕ
  hRstar : 0 < Rstar
  hunitRoot_nonneg : 0 ≤ unitRootDistance
  hunitRoot_lt : unitRootDistance < Rstar
  hboundary_nonneg : 0 ≤ boundarySup
  jetLogLower :
    Real.log (errorTolerance⁻¹) / Real.log (Rstar / unitRootDistance) ≤ jetOrder + 1
  orderFiveOutside_h : Rstar < 2 * Real.sin (Real.pi / 5)

namespace RateCenterRstarJetComplexityData

/-- The normalized distance from the center to the sampled point. -/
def radiusRatio (D : RateCenterRstarJetComplexityData) : ℝ :=
  D.unitRootDistance / D.Rstar

/-- The Cauchy remainder bound decays by one additional factor of the normalized radius. -/
def cauchyJetErrorBound (D : RateCenterRstarJetComplexityData) : Prop :=
  D.boundarySup * D.radiusRatio ^ (D.jetOrder + 1) ≤
    D.boundarySup * D.radiusRatio ^ D.jetOrder

/-- The jet order required at the prime root is bounded below by the logarithmic complexity ratio.
-/
def primeJetOrderLowerBound (D : RateCenterRstarJetComplexityData) : Prop :=
  Real.log (D.errorTolerance⁻¹) / Real.log (D.Rstar / D.unitRootDistance) ≤ D.jetOrder + 1

/-- The fifth root of unity lies outside the `R⋆` disk. -/
def orderFiveOutsideRadius (D : RateCenterRstarJetComplexityData) : Prop :=
  D.Rstar < 2 * Real.sin (Real.pi / 5)

end RateCenterRstarJetComplexityData

open RateCenterRstarJetComplexityData

/-- Package the Cauchy remainder bound at radius `R⋆`, the logarithmic lower bound on the required
jet order at prime roots, and the fact that the fifth root lies outside the `R⋆` disk.
    prop:rate-center-Rstar-jet-complexity -/
theorem paper_rate_center_rstar_jet_complexity (D : RateCenterRstarJetComplexityData) :
    D.cauchyJetErrorBound ∧ D.primeJetOrderLowerBound ∧ D.orderFiveOutsideRadius := by
  refine ⟨?_, D.jetLogLower, D.orderFiveOutside_h⟩
  have hratio_nonneg : 0 ≤ D.radiusRatio := by
    exact div_nonneg D.hunitRoot_nonneg D.hRstar.le
  have hratio_le_one : D.radiusRatio ≤ 1 := by
    simpa [RateCenterRstarJetComplexityData.radiusRatio] using (div_le_one D.hRstar).2 D.hunitRoot_lt.le
  have hpow_nonneg : 0 ≤ D.radiusRatio ^ D.jetOrder := by
    exact pow_nonneg hratio_nonneg _
  have hstep :
      D.radiusRatio ^ (D.jetOrder + 1) ≤ D.radiusRatio ^ D.jetOrder := by
    have hmul :
        D.radiusRatio ^ D.jetOrder * D.radiusRatio ≤ D.radiusRatio ^ D.jetOrder * 1 := by
      exact mul_le_mul_of_nonneg_left hratio_le_one hpow_nonneg
    simpa [pow_succ] using hmul
  exact mul_le_mul_of_nonneg_left hstep D.hboundary_nonneg

end

end Omega.SyncKernelWeighted
