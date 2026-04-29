import Mathlib.Tactic
import Omega.Conclusion.ScreenGraphicMatroidCorankSupermodularity

namespace Omega.Conclusion

open Finset

/-- Concrete finite screen/matroid package for the Tutte encoding of the completion landscape. -/
structure ConclusionScreenAuditLandscapeTutteCompleteEncodingData where
  graphic : ScreenGraphicMatroidData

attribute [instance] ScreenGraphicMatroidData.decEqEdge

/-- Completion count viewed as the graphic-matroid corank `|V| - 1 - r(S)`. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.completionCount
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) (S : Finset D.graphic.Edge) : ℕ :=
  D.graphic.screenCost S

/-- Nullity term `|S| - r(S)` for the same screen. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.redundancy
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) (S : Finset D.graphic.Edge) : ℕ :=
  S.card - D.graphic.rank S

/-- Standard Tutte polynomial of the boundary graphic matroid. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.tuttePolynomial
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) (x y : ℤ) : ℤ :=
  Finset.sum D.graphic.allEdges.powerset fun S =>
    (x - 1) ^ (D.graphic.vertexCount - 1 - D.graphic.rank S) * (y - 1) ^ (D.redundancy S)

/-- Two-variable generating function that records the completion-count/redundancy landscape. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.landscapeGeneratingFunction
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) (z w : ℤ) : ℤ :=
  Finset.sum D.graphic.allEdges.powerset fun S =>
    z ^ (D.completionCount S) * w ^ (D.redundancy S)

/-- Tutte polynomial rewritten in the completion-count coordinates. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.tutteEncodesLandscape
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) : Prop :=
  ∀ x y : ℤ,
    D.tuttePolynomial x y =
      Finset.sum D.graphic.allEdges.powerset fun S =>
        (x - 1) ^ (D.completionCount S) * (y - 1) ^ (D.redundancy S)

/-- The generating function is the Tutte polynomial after the substitution `x = 1 + z`,
`y = 1 + w`. -/
def ConclusionScreenAuditLandscapeTutteCompleteEncodingData.generatingFunctionIsTutteSubstitution
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) : Prop :=
  ∀ z w : ℤ,
    D.landscapeGeneratingFunction z w = D.tuttePolynomial (1 + z) (1 + w)

/-- Paper label: `thm:conclusion-screen-audit-landscape-tutte-complete-encoding`. -/
theorem paper_conclusion_screen_audit_landscape_tutte_complete_encoding
    (D : ConclusionScreenAuditLandscapeTutteCompleteEncodingData) :
    D.tutteEncodesLandscape ∧ D.generatingFunctionIsTutteSubstitution := by
  refine ⟨?_, ?_⟩
  · intro x y
    have hcorank := (paper_conclusion_screen_graphic_matroid_corank_supermodularity D.graphic).1
    let _ := hcorank
    simp [
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.tuttePolynomial,
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.completionCount,
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.redundancy,
      ScreenGraphicMatroidData.screenCost
    ]
  · intro z w
    simp [
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.tuttePolynomial,
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.landscapeGeneratingFunction,
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.completionCount,
      ConclusionScreenAuditLandscapeTutteCompleteEncodingData.redundancy,
      ScreenGraphicMatroidData.screenCost
    ]

end Omega.Conclusion
