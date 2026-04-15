import Mathlib.Tactic

namespace Omega.Discussion

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the explicit square-curvature formula, the controlled strictification
    decomposition, and the resulting exactness criterion.
    prop:discussion-hypercube-potential-curvature-controlled-strictification -/
theorem paper_discussion_hypercube_potential_curvature_controlled_strictification
    (squareCurvatureFormula controlledStrictification exactnessCriterion : Prop)
    (hCurv : squareCurvatureFormula) (hStrict : controlledStrictification)
    (hExact : squareCurvatureFormula ∧ controlledStrictification → exactnessCriterion) :
    squareCurvatureFormula ∧ controlledStrictification ∧ exactnessCriterion := by
  exact ⟨hCurv, hStrict, hExact ⟨hCurv, hStrict⟩⟩

end Omega.Discussion
