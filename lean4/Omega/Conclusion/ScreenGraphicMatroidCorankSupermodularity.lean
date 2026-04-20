import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.Conclusion.ScreenAuditGapSupermodularity

namespace Omega.Conclusion

open Finset

/-- Concrete graphic-matroid rank data for a finite screen edge set. The corank-style screen cost
is `|V| - 1 - r(S)`. -/
structure ScreenGraphicMatroidData where
  Edge : Type
  decEqEdge : DecidableEq Edge
  allEdges : Finset Edge
  vertexCount : ℕ
  rank : Finset Edge → ℕ
  rank_empty : rank ∅ = 0
  rank_full : rank allEdges = vertexCount - 1
  rank_bounded : ∀ s, rank s ≤ vertexCount - 1
  rank_mono : ∀ {s t : Finset Edge}, s ⊆ t → rank s ≤ rank t
  rank_submod : ∀ s t, rank (s ∩ t) + rank (s ∪ t) ≤ rank s + rank t

attribute [instance] ScreenGraphicMatroidData.decEqEdge

/-- The corank-style screen completion cost `λ(S) = |V| - 1 - r(S)`. -/
def ScreenGraphicMatroidData.screenCost (D : ScreenGraphicMatroidData)
    (S : Finset D.Edge) : ℕ :=
  D.vertexCount - 1 - D.rank S

/-- The screen cost has the expected normalization and is antitone under enlarging the visible
screen. -/
def ScreenGraphicMatroidData.corank_formula (D : ScreenGraphicMatroidData) : Prop :=
  D.screenCost ∅ = D.vertexCount - 1 ∧
    D.screenCost D.allEdges = 0 ∧
    ∀ {S T : Finset D.Edge}, S ⊆ T → D.screenCost T ≤ D.screenCost S

/-- Supermodularity of the corank-style screen cost. -/
def ScreenGraphicMatroidData.supermodular (D : ScreenGraphicMatroidData) : Prop :=
  ∀ S T : Finset D.Edge,
    D.screenCost S + D.screenCost T ≤ D.screenCost (S ∩ T) + D.screenCost (S ∪ T)

/-- Graphic-matroid corank representation and supermodularity for the screen completion cost. -/
theorem paper_conclusion_screen_graphic_matroid_corank_supermodularity
    (D : ScreenGraphicMatroidData) : D.corank_formula ∧ D.supermodular := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · simp [ScreenGraphicMatroidData.screenCost, D.rank_empty]
    · simp [ScreenGraphicMatroidData.screenCost, D.rank_full]
    · intro S T hST
      dsimp [ScreenGraphicMatroidData.screenCost]
      have hS := D.rank_bounded S
      have hT := D.rank_bounded T
      have hmono := D.rank_mono hST
      omega
  · intro S T
    simpa [ScreenGraphicMatroidData.screenCost,
      Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap] using
      Omega.Conclusion.ScreenAuditGapSupermodularity.auditGap_supermodular
        (D.vertexCount - 1) D.rank D.rank_bounded D.rank_submod S T

end Omega.Conclusion
