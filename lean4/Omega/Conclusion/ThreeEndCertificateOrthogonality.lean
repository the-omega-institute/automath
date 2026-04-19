import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency
import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality
import Omega.TypedAddressBiaxialCompletion.ThreeEndBudget

namespace Omega.Conclusion

open Omega.TypedAddressBiaxialCompletion

/-- Concrete bundle of the three certificate packages used in the conclusion-level orthogonality
statement. -/
structure ThreeEndCertificateOrthogonalityData where
  boundary : BoundaryJointVerifierData
  budget : BudgetOrthogonalityData
  closure : ThreeEndBudgetData

/-- The verifier factors through the product of the boundary certificate, the typed-address
budget certificate, and the three-end closure certificate. -/
def ThreeEndCertificateOrthogonalityData.factorsThroughProduct
    (D : ThreeEndCertificateOrthogonalityData) : Prop :=
  (D.boundary.axes.radiusBlindspotClosed ∧
      D.boundary.axes.addressCollisionClosed ∧
      D.boundary.axes.endpointHeatClosed ∧
      D.boundary.toeplitzPsdPassed ∧
      D.budget.legalReadout ∧
      D.closure.radiusBudgetClosed ∧
      D.closure.addressBudgetClosed ∧
      D.closure.endpointBudgetClosed ∧
      D.closure.toeplitzPsdClosed →
    D.boundary.verifierResult = .certificate ∧
      D.budget.visibleBudgetPassed ∧
      D.budget.registerBudgetPassed ∧
      D.budget.modeBudgetPassed ∧
      D.closure.verifierAccepts)

/-- Each certificate axis stays non-substitutable when the other two pass: the boundary package
forces failure on any missing boundary axis, the typed-address budget forces failure on any missing
budget axis, and the three-end closure package returns its standardized failure witness whenever an
end budget is missing. -/
def ThreeEndCertificateOrthogonalityData.failuresAreOrthogonal
    (D : ThreeEndCertificateOrthogonalityData) : Prop :=
  ((D.boundary.axes.addressCollisionClosed ∧ D.boundary.axes.endpointHeatClosed ∧
      ¬ D.boundary.axes.radiusBlindspotClosed) →
    D.boundary.verifierResult ≠ .certificate) ∧
  ((D.boundary.axes.radiusBlindspotClosed ∧ D.boundary.axes.endpointHeatClosed ∧
      ¬ D.boundary.axes.addressCollisionClosed) →
    D.boundary.verifierResult ≠ .certificate) ∧
  ((D.boundary.axes.radiusBlindspotClosed ∧ D.boundary.axes.addressCollisionClosed ∧
      ¬ D.boundary.axes.endpointHeatClosed) →
    D.boundary.verifierResult ≠ .certificate) ∧
  ((D.budget.registerBudgetPassed ∧ D.budget.modeBudgetPassed ∧
      ¬ D.budget.visibleBudgetPassed) →
    ¬ D.budget.legalReadout) ∧
  ((D.budget.visibleBudgetPassed ∧ D.budget.modeBudgetPassed ∧
      ¬ D.budget.registerBudgetPassed) →
    ¬ D.budget.legalReadout) ∧
  ((D.budget.visibleBudgetPassed ∧ D.budget.registerBudgetPassed ∧
      ¬ D.budget.modeBudgetPassed) →
    ¬ D.budget.legalReadout) ∧
  ((¬ D.closure.radiusBudgetClosed ∨ ¬ D.closure.addressBudgetClosed ∨
      ¬ D.closure.endpointBudgetClosed ∨ ¬ D.closure.toeplitzPsdClosed) →
    D.closure.failureWitness)

/-- Conclusion-level package: the offline verifier factors through the product of the three
certificate packages, and failures on each axis remain logically orthogonal. -/
theorem paper_conclusion_three_end_certificate_orthogonality
    (D : ThreeEndCertificateOrthogonalityData) :
    D.factorsThroughProduct ∧ D.failuresAreOrthogonal := by
  have hBoundary :=
    paper_typed_address_biaxial_completion_boundary_joint_sufficiency D.boundary
  have hBudget :=
    paper_typed_address_biaxial_completion_budget_orthogonality D.budget
  have hClosure :=
    paper_typed_address_biaxial_completion_three_end_budget D.closure
  rcases hBoundary with ⟨hBoundaryAccepts, _, hBoundaryRadius, hBoundaryAddress, hBoundaryEndpoint⟩
  rcases hBudget with ⟨hBudgetPasses, hBudgetVisible, hBudgetRegister, hBudgetMode⟩
  rcases hClosure with ⟨hClosureAccepts, hClosureFailure⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, ha, he, hpsd, hlegal, hcr, hca, hce, hct⟩
    have hBoundaryCert : D.boundary.verifierResult = .certificate :=
      hBoundaryAccepts ⟨hr, ha, he, hpsd⟩
    have hBudgetAll :
        D.budget.visibleBudgetPassed ∧ D.budget.registerBudgetPassed ∧ D.budget.modeBudgetPassed :=
      hBudgetPasses hlegal
    have hClosureCert : D.closure.verifierAccepts :=
      hClosureAccepts ⟨hcr, hca, hce, hct⟩
    exact ⟨hBoundaryCert, hBudgetAll.1, hBudgetAll.2.1, hBudgetAll.2.2, hClosureCert⟩
  · exact ⟨hBoundaryRadius, hBoundaryAddress, hBoundaryEndpoint, hBudgetVisible,
      hBudgetRegister, hBudgetMode, hClosureFailure⟩

end Omega.Conclusion
