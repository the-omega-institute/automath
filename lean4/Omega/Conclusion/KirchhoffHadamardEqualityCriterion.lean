import Omega.Conclusion.FundamentalCutHadamardRigidity

namespace Omega.Conclusion

/-- Paper-facing Kirchhoff/Hadamard equality criterion extracted from the stronger conclusion-level
fundamental-cut rigidity package.
    thm:conclusion-kirchhoff-hadamard-equality-criterion -/
theorem paper_conclusion_kirchhoff_hadamard_equality_criterion {treeRank : Nat}
    (D : FundamentalCutHadamardData treeRank) :
    D.treeWeightLeCutProduct ∧
      (D.treeWeight = D.cutProduct ↔ D.weightedCutVectorsPairwiseOrthogonal) := by
  have hRigidity := paper_conclusion_fundamental_cut_hadamard_rigidity D
  refine ⟨hRigidity.1, ?_⟩
  constructor
  · intro hEq
    have hCapacityEq : D.capacityData.kirchhoffDeterminant = ∏ t, D.capacityData.cutCapacity t := by
      calc
        D.capacityData.kirchhoffDeterminant = D.treeWeight := D.treeWeight_eq.symm
        _ = D.cutProduct := hEq
        _ = ∏ t, D.capacityData.cutCapacity t := D.cutProduct_eq
    exact D.hadamardEquality_iff_orthogonal.mp hCapacityEq
  · intro hOrth
    have hCapacityEq : D.capacityData.kirchhoffDeterminant = ∏ t, D.capacityData.cutCapacity t :=
      D.hadamardEquality_iff_orthogonal.mpr hOrth
    calc
      D.treeWeight = D.capacityData.kirchhoffDeterminant := D.treeWeight_eq
      _ = ∏ t, D.capacityData.cutCapacity t := hCapacityEq
      _ = D.cutProduct := D.cutProduct_eq.symm

end Omega.Conclusion
