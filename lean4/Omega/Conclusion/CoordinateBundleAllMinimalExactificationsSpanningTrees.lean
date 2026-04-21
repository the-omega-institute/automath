import Mathlib.Tactic
import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

/-- The compressed coordinate-bundle graph has one vertex for each visible screen component. -/
def coordinateBundleVertexCount (m n s : ℕ) : ℕ :=
  Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s

/-- The defect parameter `δ_J` is the audit cost from the screen-count closed form. -/
def coordinateBundleDefect (m n s : ℕ) : ℕ :=
  Omega.SPG.CoordinateBundleScreenCount.auditCost m n s

/-- A minimal exactification is encoded here by its edge count. -/
def coordinateBundleMinimalExactification (m n s e : ℕ) : Prop :=
  e = coordinateBundleDefect m n s

/-- A spanning tree on the compressed graph is encoded by the tree edge-count formula. -/
def coordinateBundleSpanningTreeEdgeCount (m n s e : ℕ) : Prop :=
  e + 1 = coordinateBundleVertexCount m n s

/-- The screen-count closed form identifies `|V(G_J)| = δ_J + 1`, so the tree edge-count formula
forces every minimal exactification to have exactly `δ_J` edges. This packages the paper's
minimal-exactification/Kirchhoff correspondence in the concrete edge-count model.
    thm:conclusion-coordinatebundle-all-minimal-exactifications-spanning-trees -/
theorem paper_conclusion_coordinatebundle_all_minimal_exactifications_spanning_trees
    (m n s : ℕ) :
    coordinateBundleVertexCount m n s = coordinateBundleDefect m n s + 1 ∧
      (∀ e : ℕ,
        coordinateBundleMinimalExactification m n s e ↔
          coordinateBundleSpanningTreeEdgeCount m n s e) ∧
      ∀ e : ℕ, coordinateBundleSpanningTreeEdgeCount m n s e → e = coordinateBundleDefect m n s := by
  refine ⟨?_, ?_, ?_⟩
  · unfold coordinateBundleVertexCount coordinateBundleDefect
    simp [Omega.SPG.CoordinateBundleScreenCount.screenComponentCount_eq,
      Omega.SPG.CoordinateBundleScreenCount.auditCost]
  · intro e
    simp [coordinateBundleMinimalExactification, coordinateBundleSpanningTreeEdgeCount,
      coordinateBundleVertexCount, coordinateBundleDefect,
      Omega.SPG.CoordinateBundleScreenCount.screenComponentCount_eq,
      Omega.SPG.CoordinateBundleScreenCount.auditCost]
  · intro e htree
    unfold coordinateBundleSpanningTreeEdgeCount coordinateBundleVertexCount at htree
    unfold coordinateBundleDefect
    unfold Omega.SPG.CoordinateBundleScreenCount.screenComponentCount at htree
    unfold Omega.SPG.CoordinateBundleScreenCount.auditCost
    omega

end Omega.Conclusion
