import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Graph.FlowLatticeGramDeterminantTreeWeight
import Omega.SPG.KirchhoffFundamentalCutCapacityHadamard

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete conclusion-level package combining the SPG Hadamard bound for a chosen spanning tree
with the flow-lattice/tree-weight identity for the same weighted connected graph. -/
structure FundamentalCutHadamardData (treeRank : Nat) where
  capacityData : Omega.SPG.KirchhoffFundamentalCutCapacityData treeRank
  graph : Omega.Graph.FlowWeightedMultigraph
  graphConnected : graph.Connected
  treeWeight : ℝ
  cutProduct : ℝ
  edgeWeightDet : ℝ
  flowLatticeCovol : ℝ
  weightedCutVectorsPairwiseOrthogonal : Prop
  treeWeight_eq : treeWeight = capacityData.kirchhoffDeterminant
  cutProduct_eq : cutProduct = ∏ t, capacityData.cutCapacity t
  edgeWeightDet_eq : edgeWeightDet = graph.edgeWeightDet
  treeSum_eq : graph.weightedTreeSum = treeWeight
  edgeWeightDet_pos : 0 < edgeWeightDet
  flowLatticeCovol_eq : flowLatticeCovol = Real.sqrt (Omega.Graph.flowLatticeGramDet graph)
  hadamardEquality_iff_orthogonal :
    capacityData.kirchhoffDeterminant = ∏ t, capacityData.cutCapacity t ↔
      weightedCutVectorsPairwiseOrthogonal

/-- Tree-weight bound coming from the fundamental-cut Hadamard inequality. -/
def FundamentalCutHadamardData.treeWeightLeCutProduct {treeRank : Nat}
    (D : FundamentalCutHadamardData treeRank) : Prop :=
  D.treeWeight ≤ D.cutProduct

/-- Flow-lattice covolume bound obtained by combining the tree-weight bound with the
flow-lattice/tree-weight identity. -/
def FundamentalCutHadamardData.flowLatticeCovolLeCutProduct {treeRank : Nat}
    (D : FundamentalCutHadamardData treeRank) : Prop :=
  D.flowLatticeCovol ≤ Real.sqrt (D.cutProduct / D.edgeWeightDet)

/-- Equality in both conclusion inequalities is equivalent to pairwise orthogonality of the
weighted fundamental-cut vectors. -/
def FundamentalCutHadamardData.equalityCriterion {treeRank : Nat}
    (D : FundamentalCutHadamardData treeRank) : Prop :=
  (D.treeWeight = D.cutProduct ∧
      D.flowLatticeCovol = Real.sqrt (D.cutProduct / D.edgeWeightDet)) ↔
    D.weightedCutVectorsPairwiseOrthogonal

/-- Paper package: combine the existing SPG Hadamard bound for a tree basis of cuts with the
flow-lattice/tree-weight covolume identity to obtain both inequalities, and identify the equality
case with pairwise orthogonality of the weighted cut vectors.
    thm:conclusion-fundamental-cut-hadamard-rigidity -/
theorem paper_conclusion_fundamental_cut_hadamard_rigidity {treeRank : Nat}
    (D : Omega.Conclusion.FundamentalCutHadamardData treeRank) :
    D.treeWeightLeCutProduct ∧ D.flowLatticeCovolLeCutProduct ∧ D.equalityCriterion := by
  rcases Omega.SPG.paper_spg_kirchhoff_fundamental_cut_capacity_hadamard D.capacityData with
    ⟨_, _, hHadamard, _, _⟩
  have hGraph :
      Omega.Graph.flowLatticeGramDet D.graph =
        D.graph.weightedTreeSum / D.graph.edgeWeightDet :=
    Omega.Graph.paper_xi_flow_lattice_gram_determinant_tree_weight D.graph D.graphConnected
  have hFlowRatio :
      Omega.Graph.flowLatticeGramDet D.graph = D.treeWeight / D.edgeWeightDet := by
    calc
      Omega.Graph.flowLatticeGramDet D.graph
          = D.graph.weightedTreeSum / D.graph.edgeWeightDet := hGraph
      _ = D.treeWeight / D.edgeWeightDet := by rw [D.treeSum_eq, D.edgeWeightDet_eq]
  have hTreeLe : D.treeWeight ≤ D.cutProduct := by
    calc
      D.treeWeight = D.capacityData.kirchhoffDeterminant := D.treeWeight_eq
      _ ≤ ∏ t, D.capacityData.cutCapacity t := hHadamard
      _ = D.cutProduct := D.cutProduct_eq.symm
  have hInvNonneg : 0 ≤ D.edgeWeightDet⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt D.edgeWeightDet_pos)
  have hDivLe : D.treeWeight / D.edgeWeightDet ≤ D.cutProduct / D.edgeWeightDet := by
    have hMul :
        D.treeWeight * D.edgeWeightDet⁻¹ ≤ D.cutProduct * D.edgeWeightDet⁻¹ :=
      mul_le_mul_of_nonneg_right hTreeLe hInvNonneg
    simpa [div_eq_mul_inv] using hMul
  have hFlowEq : D.flowLatticeCovol = Real.sqrt (D.treeWeight / D.edgeWeightDet) := by
    rw [D.flowLatticeCovol_eq, hFlowRatio]
  have hFlowLe : D.flowLatticeCovol ≤ Real.sqrt (D.cutProduct / D.edgeWeightDet) := by
    calc
      D.flowLatticeCovol = Real.sqrt (D.treeWeight / D.edgeWeightDet) := hFlowEq
      _ ≤ Real.sqrt (D.cutProduct / D.edgeWeightDet) := Real.sqrt_le_sqrt hDivLe
  refine ⟨hTreeLe, hFlowLe, ?_⟩
  constructor
  · rintro ⟨hTreeEq, _⟩
    have hCapacityEq : D.capacityData.kirchhoffDeterminant = ∏ t, D.capacityData.cutCapacity t := by
      calc
        D.capacityData.kirchhoffDeterminant = D.treeWeight := D.treeWeight_eq.symm
        _ = D.cutProduct := hTreeEq
        _ = ∏ t, D.capacityData.cutCapacity t := D.cutProduct_eq
    exact D.hadamardEquality_iff_orthogonal.mp hCapacityEq
  · intro hOrth
    have hCapacityEq :
        D.capacityData.kirchhoffDeterminant = ∏ t, D.capacityData.cutCapacity t :=
      D.hadamardEquality_iff_orthogonal.mpr hOrth
    have hTreeEq : D.treeWeight = D.cutProduct := by
      calc
        D.treeWeight = D.capacityData.kirchhoffDeterminant := D.treeWeight_eq
        _ = ∏ t, D.capacityData.cutCapacity t := hCapacityEq
        _ = D.cutProduct := D.cutProduct_eq.symm
    refine ⟨hTreeEq, ?_⟩
    calc
      D.flowLatticeCovol = Real.sqrt (D.treeWeight / D.edgeWeightDet) := hFlowEq
      _ = Real.sqrt (D.cutProduct / D.edgeWeightDet) := by rw [hTreeEq]

end Omega.Conclusion
