import Mathlib.Tactic
import Omega.Conclusion.ChowliuForcedEdgeThreshold

namespace Omega.Conclusion

/-- Concrete data for the unique-tree threshold criterion. Each edge of the reference tree carries
its own forced-edge threshold witness, and containing every reference edge characterizes the
reference tree among the candidate trees. -/
structure conclusion_chowliu_unique_tree_threshold_data where
  Tree : Type
  Edge : Type
  referenceTree : Tree
  referenceEdges : Finset Edge
  treeScore : Tree → ℝ
  optimalTreeScore : ℝ
  edgeInTree : Edge → Tree → Prop
  omittedEdgeThreshold : Edge → ℝ
  omittedEdgeCertificate : Edge → Tree → ℝ
  referenceTree_optimal : treeScore referenceTree = optimalTreeScore
  threshold_strict :
    ∀ e ∈ referenceEdges, optimalTreeScore < omittedEdgeThreshold e
  certificate_lower :
    ∀ e ∈ referenceEdges, ∀ T, ¬ edgeInTree e T →
      omittedEdgeThreshold e ≤ omittedEdgeCertificate e T
  certificate_upper :
    ∀ e ∈ referenceEdges, ∀ T, ¬ edgeInTree e T →
      omittedEdgeCertificate e T ≤ treeScore T
  reference_edges_characterize :
    ∀ T, (∀ e ∈ referenceEdges, edgeInTree e T) → T = referenceTree

namespace conclusion_chowliu_unique_tree_threshold_data

/-- The reference tree is the unique score-optimal tree. -/
def reference_tree_is_unique_optimal
    (D : conclusion_chowliu_unique_tree_threshold_data) : Prop :=
  D.treeScore D.referenceTree = D.optimalTreeScore ∧
    ∀ T, D.treeScore T = D.optimalTreeScore → T = D.referenceTree

end conclusion_chowliu_unique_tree_threshold_data

open conclusion_chowliu_forced_edge_threshold_data
open conclusion_chowliu_unique_tree_threshold_data

/-- Paper label: `thm:conclusion-chowliu-unique-tree-threshold`. -/
theorem paper_conclusion_chowliu_unique_tree_threshold
    (D : conclusion_chowliu_unique_tree_threshold_data) : D.reference_tree_is_unique_optimal := by
  refine ⟨D.referenceTree_optimal, ?_⟩
  intro T hOptimal
  apply D.reference_edges_characterize T
  intro e he
  let F : conclusion_chowliu_forced_edge_threshold_data := {
    Tree := D.Tree
    Vertex := D.Edge
    edge := (e, e)
    treeScore := D.treeScore
    optimalTreeScore := D.optimalTreeScore
    omittedEdgeThreshold := D.omittedEdgeThreshold e
    omittedEdgeCertificate := D.omittedEdgeCertificate e
    edgeInTree := D.edgeInTree e
    threshold_strict := D.threshold_strict e he
    certificate_lower := D.certificate_lower e he
    certificate_upper := D.certificate_upper e he
  }
  exact paper_conclusion_chowliu_forced_edge_threshold F T hOptimal

end Omega.Conclusion
