import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete finite cut package for the coordinate-bundle strict boundary gap argument.

The predicates are attached to an actual edge type.  `isPureBoundaryStar` is not an abstract
conclusion: `pureBoundaryStar_iff` identifies it with every selected edge being boundary-incident,
and the cut certificate fields encode the strict-gap/cut-property step for MST edges. -/
structure conclusion_coordinatebundle_strict_boundary_gap_forces_stars_data where
  Edge : Type
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  boundaryIncident : Edge → Prop
  cutCertificate : Finset Edge → Edge → Vertex → Prop
  isMinimumSpanningTree : Finset Edge → Prop
  isPureBoundaryStar : Finset Edge → Prop
  tree_edge_card : ∀ T, isMinimumSpanningTree T → T.card + 1 = Fintype.card Vertex
  mst_edge_cutCertificate :
    ∀ T e, isMinimumSpanningTree T → e ∈ T → ∃ v, cutCertificate T e v
  strict_boundary_gap_forces_boundary :
    ∀ T e v, isMinimumSpanningTree T → e ∈ T → cutCertificate T e v → boundaryIncident e
  pureBoundaryStar_iff : ∀ T, isPureBoundaryStar T ↔ ∀ e ∈ T, boundaryIncident e

attribute [instance] conclusion_coordinatebundle_strict_boundary_gap_forces_stars_data.vertexFintype

/-- Paper label: `thm:conclusion-coordinatebundle-strict-boundary-gap-forces-stars`. -/
theorem paper_conclusion_coordinatebundle_strict_boundary_gap_forces_stars
    (D : conclusion_coordinatebundle_strict_boundary_gap_forces_stars_data) :
    ∀ T, D.isMinimumSpanningTree T → D.isPureBoundaryStar T := by
  intro T hT
  rw [D.pureBoundaryStar_iff]
  intro e heT
  rcases D.mst_edge_cutCertificate T e hT heT with ⟨v, hv⟩
  exact D.strict_boundary_gap_forces_boundary T e v hT heT hv

end Omega.Conclusion
