import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Finite spectral-decomposition data for the endpoint theorem: separation curves share one
denominator and one modal list, while fixed-target hitting tails share a target-dependent
denominator and target-dependent modal list. -/
structure ConclusionEndpointStartpointOnlyAmplitudeNotModesData where
  Start : Type*
  Target : Type*
  separationDenominatorDegree : ℕ
  separationCommonDenominator : Fin separationDenominatorDegree → ℚ
  separationStartDenominator : Start → Fin separationDenominatorDegree → ℚ
  separationModeCount : ℕ
  separationMode : Fin separationModeCount → ℚ
  separationAmplitude : Start → Fin separationModeCount → ℚ
  separationCurve : Start → ℕ → ℚ
  hittingDenominatorDegree : Target → ℕ
  hittingCommonDenominator : (y : Target) → Fin (hittingDenominatorDegree y) → ℚ
  hittingStartDenominator : (y : Target) → Start → Fin (hittingDenominatorDegree y) → ℚ
  hittingModeCount : Target → ℕ
  hittingMode : (y : Target) → Fin (hittingModeCount y) → ℚ
  hittingAmplitude : (y : Target) → Start → Fin (hittingModeCount y) → ℚ
  hittingTail : Target → Start → ℕ → ℚ
  separation_denominator_shared :
    ∀ x, separationStartDenominator x = separationCommonDenominator
  separation_modal_expansion :
    ∀ x m, separationCurve x m =
      ∑ i : Fin separationModeCount, separationAmplitude x i * separationMode i ^ m
  hitting_denominator_shared :
    ∀ y x, hittingStartDenominator y x = hittingCommonDenominator y
  hitting_tail_modal_expansion :
    ∀ y x k, hittingTail y x k =
      ∑ i : Fin (hittingModeCount y), hittingAmplitude y x i * hittingMode y i ^ k

/-- Paper-facing statement: starts only change amplitudes.  The denominator and modal positions
are shared across starts for separation curves, and for each fixed target in the hitting tails. -/
def ConclusionEndpointStartpointOnlyAmplitudeNotModesStatement
    (D : ConclusionEndpointStartpointOnlyAmplitudeNotModesData) : Prop :=
  (∀ x, D.separationStartDenominator x = D.separationCommonDenominator) ∧
    (∀ x m, D.separationCurve x m =
      ∑ i : Fin D.separationModeCount, D.separationAmplitude x i * D.separationMode i ^ m) ∧
    (∀ y x, D.hittingStartDenominator y x = D.hittingCommonDenominator y) ∧
    (∀ y x k, D.hittingTail y x k =
      ∑ i : Fin (D.hittingModeCount y), D.hittingAmplitude y x i * D.hittingMode y i ^ k)

/-- Paper label: `thm:conclusion-endpoint-startpoint-only-amplitude-not-modes`. -/
theorem paper_conclusion_endpoint_startpoint_only_amplitude_not_modes
    (D : ConclusionEndpointStartpointOnlyAmplitudeNotModesData) :
    ConclusionEndpointStartpointOnlyAmplitudeNotModesStatement D := by
  exact ⟨D.separation_denominator_shared, D.separation_modal_expansion,
    D.hitting_denominator_shared, D.hitting_tail_modal_expansion⟩

end Omega.Conclusion
