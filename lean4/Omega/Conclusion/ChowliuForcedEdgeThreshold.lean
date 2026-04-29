import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the forced-edge threshold criterion. An optimal score is recorded together
with an omitted-edge certificate whose value is always squeezed between the threshold and the score
of any tree omitting the distinguished edge. -/
structure conclusion_chowliu_forced_edge_threshold_data where
  Tree : Type
  Vertex : Type
  edge : Vertex × Vertex
  treeScore : Tree → ℝ
  optimalTreeScore : ℝ
  omittedEdgeThreshold : ℝ
  omittedEdgeCertificate : Tree → ℝ
  edgeInTree : Tree → Prop
  threshold_strict : optimalTreeScore < omittedEdgeThreshold
  certificate_lower :
    ∀ T, ¬ edgeInTree T → omittedEdgeThreshold ≤ omittedEdgeCertificate T
  certificate_upper :
    ∀ T, ¬ edgeInTree T → omittedEdgeCertificate T ≤ treeScore T

namespace conclusion_chowliu_forced_edge_threshold_data

/-- The distinguished edge belongs to every score-optimal tree. -/
def edge_forced_in_every_optimal_tree
    (D : conclusion_chowliu_forced_edge_threshold_data) : Prop :=
  ∀ T, D.treeScore T = D.optimalTreeScore → D.edgeInTree T

end conclusion_chowliu_forced_edge_threshold_data

open conclusion_chowliu_forced_edge_threshold_data

/-- Paper label: `thm:conclusion-chowliu-forced-edge-threshold`. If every tree omitting the chosen
edge carries a certificate at least as large as the threshold, while the threshold lies strictly
above the optimal score, then no optimal tree can omit that edge. -/
theorem paper_conclusion_chowliu_forced_edge_threshold
    (D : conclusion_chowliu_forced_edge_threshold_data) : D.edge_forced_in_every_optimal_tree := by
  intro T hOptimal
  by_contra hOmit
  have hLower := D.certificate_lower T hOmit
  have hUpper := D.certificate_upper T hOmit
  have hThreshold : D.omittedEdgeThreshold ≤ D.optimalTreeScore := by
    rw [hOptimal] at hUpper
    linarith
  linarith [D.threshold_strict, hThreshold]

end Omega.Conclusion
