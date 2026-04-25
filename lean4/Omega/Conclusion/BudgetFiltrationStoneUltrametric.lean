import Mathlib.Tactic
import Omega.SPG.PrefixMetric

namespace Omega.Conclusion

open Omega

noncomputable section

/-- Concrete depth-`B` Boolean truth assignment on the Stone-prefix model. -/
structure conclusion_budget_filtration_stone_ultrametric_data where
  depth : ℕ
  truthValues : Word depth → Bool

namespace conclusion_budget_filtration_stone_ultrametric_data

/-- The Boolean truth set cut out by the depth-`B` prefix assignment. -/
def conclusion_budget_filtration_stone_ultrametric_truthSet
    (h : conclusion_budget_filtration_stone_ultrametric_data) : Set SPG.OmegaInfinity :=
  {x | h.truthValues (SPG.prefixWord x h.depth) = true}

/-- A finite union of depth-`B` closed balls, indexed by the corresponding finite words. -/
def conclusion_budget_filtration_stone_ultrametric_ballUnion
    (h : conclusion_budget_filtration_stone_ultrametric_data) (U : Finset (Word h.depth)) :
    Set SPG.OmegaInfinity :=
  {x | ∃ w ∈ U, SPG.prefixDist x (SPG.extendWord w) ≤ (1 / 2 : ℝ) ^ h.depth}

/-- The first-disagreement metric is ultrametric. -/
def is_ultrametric (_h : conclusion_budget_filtration_stone_ultrametric_data) : Prop :=
  ∀ x y z : SPG.OmegaInfinity,
    SPG.prefixDist x z ≤ max (SPG.prefixDist x y) (SPG.prefixDist y z)

/-- Depth-`B` cylinders are exactly the closed balls of radius `2^{-B}`. -/
def cylinder_sets_are_balls (h : conclusion_budget_filtration_stone_ultrametric_data) : Prop :=
  ∀ w : Word h.depth,
    SPG.cylinderWord w =
      {x : SPG.OmegaInfinity | SPG.prefixDist x (SPG.extendWord w) ≤ (1 / 2 : ℝ) ^ h.depth}

/-- Boolean truth sets determined at depth `B` are finite unions of depth-`B` balls. -/
def boolean_truth_sets_are_finite_ball_unions
    (h : conclusion_budget_filtration_stone_ultrametric_data) : Prop :=
  ∃ U : Finset (Word h.depth),
    conclusion_budget_filtration_stone_ultrametric_truthSet h =
      conclusion_budget_filtration_stone_ultrametric_ballUnion h U

end conclusion_budget_filtration_stone_ultrametric_data

open conclusion_budget_filtration_stone_ultrametric_data

/-- Paper label: `prop:conclusion-budget-filtration-stone-ultrametric`. In the concrete binary
prefix model, the SPG prefix distance is ultrametric, its depth-`B` cylinders are the radius
`2^{-B}` balls, and every depth-`B` Boolean truth set is a finite union of such balls. -/
theorem paper_conclusion_budget_filtration_stone_ultrametric
    (h : conclusion_budget_filtration_stone_ultrametric_data) :
    h.is_ultrametric ∧ h.cylinder_sets_are_balls ∧ h.boolean_truth_sets_are_finite_ball_unions := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    exact SPG.prefixDist_ultrametric x y z
  · intro w
    exact SPG.cylinderWord_eq_closedBall w
  · refine ⟨Finset.univ.filter (fun w : Word h.depth => h.truthValues w = true), ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨SPG.prefixWord x h.depth, ?_, ?_⟩
      · simpa [conclusion_budget_filtration_stone_ultrametric_truthSet] using hx
      · have hxCylinder : x ∈ SPG.cylinderWord (SPG.prefixWord x h.depth) := by
          simp [SPG.cylinderWord]
        rw [SPG.cylinderWord_eq_closedBall] at hxCylinder
        exact hxCylinder
    · rintro ⟨w, hw, hxBall⟩
      have hwTrue : h.truthValues w = true := by
        simp at hw
        exact hw
      have hxCylinder : x ∈ SPG.cylinderWord w := by
        have hxBallSet :
            x ∈ {y : SPG.OmegaInfinity | SPG.prefixDist y (SPG.extendWord w) ≤ (1 / 2 : ℝ) ^ h.depth} :=
          hxBall
        rw [← SPG.cylinderWord_eq_closedBall (w := w)] at hxBallSet
        exact hxBallSet
      have hprefix : SPG.prefixWord x h.depth = w := by
        simpa [SPG.cylinderWord] using hxCylinder
      simpa [conclusion_budget_filtration_stone_ultrametric_truthSet, hprefix] using hwTrue

end

end Omega.Conclusion
