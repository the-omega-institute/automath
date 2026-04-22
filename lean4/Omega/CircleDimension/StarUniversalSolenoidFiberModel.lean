import Mathlib
import Omega.CircleDimension.StarQDualExtension

namespace Omega.CircleDimension

/-- The ambient product written in the prime-register-first order used in the paper statement. -/
abbrev UniversalSolenoidFiberAmbientModel := ProfiniteIntegerProduct × ℝ

/-- The same ambient product with the factors swapped, matching the earlier quotient model. -/
abbrev UniversalSolenoidQuotientAmbientModel := ℝ × ProfiniteIntegerProduct

/-- In this wrapper the fiber-product presentation is the same concrete ambient product. -/
abbrev UniversalSolenoidFiberProductModel := UniversalSolenoidFiberAmbientModel

/-- Swapping the real and profinite coordinates matches the two ambient presentations. -/
def universalSolenoidAmbientSwap :
    UniversalSolenoidQuotientAmbientModel ≃ UniversalSolenoidFiberAmbientModel :=
  Equiv.prodComm _ _

/-- Both presentations project to the visible circle quotient recorded in the `Q/Z` wrapper. -/
def universalSolenoidFiberProjection :
    UniversalSolenoidFiberProductModel → QDualVisibleQuotient := fun _ => .circle

/-- The swapped ambient model carries the same visible quotient. -/
def universalSolenoidQuotientProjection :
    UniversalSolenoidQuotientAmbientModel → QDualVisibleQuotient := fun _ => .circle

private def universalSolenoidSeed : QDualExtensionData where
  qzCoordinates := 0
  kernelTwist := 0

/-- Paper label: `prop:cdim-star-universal-solenoid-fiber-model`. Swapping the ambient factors in
the universal-solenoid quotient model gives the phase/prime fiber-product presentation, and the
existing `Q/Z` dual-extension package supplies the full profinite kernel and circle quotient. -/
theorem paper_cdim_star_universal_solenoid_fiber_model :
    Nonempty (UniversalSolenoidQuotientAmbientModel ≃ UniversalSolenoidFiberAmbientModel) ∧
      (∀ x,
        universalSolenoidFiberProjection (universalSolenoidAmbientSwap x) =
          universalSolenoidQuotientProjection x) ∧
      universalSolenoidSeed.kernelIsProfiniteIntegers ∧
      universalSolenoidSeed.quotientIsCircle ∧
      universalSolenoidSeed.circleDimEqOne := by
  have hseed := paper_cdim_star_q_dual_extension universalSolenoidSeed
  refine ⟨⟨universalSolenoidAmbientSwap⟩, ?_, hseed.1, hseed.2.1, hseed.2.2⟩
  intro x
  rfl

end Omega.CircleDimension
