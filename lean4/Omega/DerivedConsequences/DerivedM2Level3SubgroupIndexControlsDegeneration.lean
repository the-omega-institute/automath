import Omega.Conclusion.S4BoundaryTotalTorusRankConservation

namespace Omega.DerivedConsequences

/-- Paper label: `cor:derived-m2-level3-subgroup-index-controls-degeneration`. -/
theorem paper_derived_m2_level3_subgroup_index_controls_degeneration :
    (Omega.Conclusion.mainGenus Omega.Conclusion.S4BoundaryType.one = 4 ∧
        Omega.Conclusion.totalTorusRank Omega.Conclusion.S4BoundaryType.one = 12) ∧
      (Omega.Conclusion.mainGenus Omega.Conclusion.S4BoundaryType.two = 10 ∧
        Omega.Conclusion.totalTorusRank Omega.Conclusion.S4BoundaryType.two = 6) ∧
      (Omega.Conclusion.mainGenus Omega.Conclusion.S4BoundaryType.three = 12 ∧
        Omega.Conclusion.totalTorusRank Omega.Conclusion.S4BoundaryType.three = 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Omega.Conclusion.mainGenus, Omega.Conclusion.totalTorusRank]

end Omega.DerivedConsequences
