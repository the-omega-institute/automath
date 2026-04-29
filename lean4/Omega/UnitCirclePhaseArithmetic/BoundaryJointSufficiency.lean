import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion

/-- Re-export of the chapter-local boundary-budget axes used by the unit-circle phase arithmetic
interface. -/
abbrev UnitCircleBoundaryBudgetAxes := BoundaryBudgetAxes

/-- Re-export of the chapter-local verifier output type. -/
abbrev UnitCircleBoundaryVerifierResult := BoundaryVerifierResult

/-- The unit-circle phase arithmetic chapter uses the same three-axis boundary verifier interface
as the typed-address biaxial completion chapter. -/
abbrev UnitCircleBoundaryJointVerifierData := BoundaryJointVerifierData

/-- Joint closure of the radius blindspot, address collision, and endpoint heat axes is sufficient
for the boundary verifier to emit a certificate, and each axis remains logically non-substitutable
when the other two pass.
    thm:unit-circle-boundary-joint-sufficiency -/
theorem paper_unit_circle_boundary_joint_sufficiency (D : UnitCircleBoundaryJointVerifierData) :
    (D.axes.radiusBlindspotClosed ∧ D.axes.addressCollisionClosed ∧
        D.axes.endpointHeatClosed ∧ D.toeplitzPsdPassed →
      D.verifierResult = .certificate) ∧
    ((D.axes.addressCollisionClosed ∧ D.axes.endpointHeatClosed ∧
        ¬ D.axes.radiusBlindspotClosed) →
      D.verifierResult ≠ .certificate) ∧
    ((D.axes.radiusBlindspotClosed ∧ D.axes.endpointHeatClosed ∧
        ¬ D.axes.addressCollisionClosed) →
      D.verifierResult ≠ .certificate) ∧
    ((D.axes.radiusBlindspotClosed ∧ D.axes.addressCollisionClosed ∧
        ¬ D.axes.endpointHeatClosed) →
      D.verifierResult ≠ .certificate) := by
  rcases paper_typed_address_biaxial_completion_boundary_joint_sufficiency D with
    ⟨hsufficient, _, hradius, haddress, hendpoint⟩
  exact ⟨hsufficient, hradius, haddress, hendpoint⟩

end Omega.UnitCirclePhaseArithmetic
