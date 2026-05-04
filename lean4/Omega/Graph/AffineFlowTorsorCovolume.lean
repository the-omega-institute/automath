import Omega.Graph.FlowLatticeGramDeterminantTreeWeight

namespace Omega.Graph

/-- Paper label: `cor:xi-affine-flow-torsor-covolume`. -/
theorem paper_xi_affine_flow_torsor_covolume (G : FlowWeightedMultigraph) (hconn : G.Connected)
    (hasIntegralSolution affineTorsor : Prop) (covolumeSq : Real)
    (haffine : hasIntegralSolution -> affineTorsor)
    (hcovol : covolumeSq = flowLatticeGramDet G) :
    hasIntegralSolution -> affineTorsor ∧ covolumeSq = G.weightedTreeSum / G.edgeWeightDet := by
  intro hsolution
  refine ⟨haffine hsolution, ?_⟩
  calc
    covolumeSq = flowLatticeGramDet G := hcovol
    _ = G.weightedTreeSum / G.edgeWeightDet :=
      paper_xi_flow_lattice_gram_determinant_tree_weight G hconn

end Omega.Graph
