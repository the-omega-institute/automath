import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- The ordered five-gate window-6 audit either passes all gates or fails at the first missing
certificate. -/
theorem paper_typed_address_biaxial_completion_window6_audit_pass_fail_rules
    (fixedBaseline boundaryCertificates budgetSplit residualVisible crossscaleGate : Prop) :
    (fixedBaseline ∧ boundaryCertificates ∧ budgetSplit ∧ residualVisible ∧ crossscaleGate) ∨
      (¬ fixedBaseline) ∨
      (fixedBaseline ∧ ¬ boundaryCertificates) ∨
      (fixedBaseline ∧ boundaryCertificates ∧ ¬ budgetSplit) ∨
      (fixedBaseline ∧ boundaryCertificates ∧ budgetSplit ∧ ¬ residualVisible) ∨
      (fixedBaseline ∧ boundaryCertificates ∧ budgetSplit ∧ residualVisible ∧
        ¬ crossscaleGate) := by
  by_cases hFixed : fixedBaseline
  · by_cases hBoundary : boundaryCertificates
    · by_cases hBudget : budgetSplit
      · by_cases hResidual : residualVisible
        · by_cases hCrossscale : crossscaleGate
          · exact Or.inl ⟨hFixed, hBoundary, hBudget, hResidual, hCrossscale⟩
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
              ⟨hFixed, hBoundary, hBudget, hResidual, hCrossscale⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
            ⟨hFixed, hBoundary, hBudget, hResidual⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hFixed, hBoundary, hBudget⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨hFixed, hBoundary⟩
  · exact Or.inr <| Or.inl hFixed

end Omega.TypedAddressBiaxialCompletion
