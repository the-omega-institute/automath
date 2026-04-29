import Omega.Conclusion.Window6BoundaryCliffordIdealExactSplit
import Omega.GU.Window6Center2RankExcludesSimpleGroups

namespace Omega.Conclusion

structure Window6BoundaryDoubleIrreducibilityData where
  simpleEnvelope : Omega.GU.CompactConnectedSimpleLieType

def conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data :
    Window6BoundaryTripleSpinorRigidityData :=
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_data

def conclusion_window6_boundary_double_irreducibility_obstruction_split_data :
    conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data :=
  {}

def conclusion_window6_boundary_double_irreducibility_obstruction_center_data
    (D : Window6BoundaryDoubleIrreducibilityData) :
    Omega.GU.Window6Center2RankExcludesSimpleGroupsData :=
  { envelope := D.simpleEnvelope
    boundaryCentralRank := 3
    boundaryCentralRank_eq_three := rfl }

def Window6BoundaryDoubleIrreducibilityData.noCompactIrreducibleModel
    (_D : Window6BoundaryDoubleIrreducibilityData) : Prop :=
  let splitData := conclusion_window6_boundary_double_irreducibility_obstruction_split_data
  Window6BoundaryTripleSpinorRigidityStatement
      conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data ∧
    splitData.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_k0_ranks ∧
    (3 : ℕ) ≠ 1

def Window6BoundaryDoubleIrreducibilityData.noConnectedSimpleEnvelope
    (D : Window6BoundaryDoubleIrreducibilityData) : Prop :=
  Omega.GU.Window6Center2RankExcludesSimpleGroupsData.no_compact_connected_simple_envelope
    (conclusion_window6_boundary_double_irreducibility_obstruction_center_data D)

/-- `thm:conclusion-window6-boundary-double-irreducibility-obstruction` -/
theorem paper_conclusion_window6_boundary_double_irreducibility_obstruction
    (D : Window6BoundaryDoubleIrreducibilityData) :
    D.noCompactIrreducibleModel ∧ D.noConnectedSimpleEnvelope := by
  have hBoundary :
      Window6BoundaryTripleSpinorRigidityStatement
        conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data :=
    paper_conclusion_window6_boundary_triple_spinor_rigidity
      conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data
  have hSplit :=
    paper_conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting
      conclusion_window6_boundary_double_irreducibility_obstruction_split_data
  have hSimple : D.noConnectedSimpleEnvelope := by
    simpa [Window6BoundaryDoubleIrreducibilityData.noConnectedSimpleEnvelope,
      conclusion_window6_boundary_double_irreducibility_obstruction_center_data] using
      Omega.GU.paper_window6_center_2rank_excludes_simple_groups
        (conclusion_window6_boundary_double_irreducibility_obstruction_center_data D)
  refine ⟨?_, hSimple⟩
  exact ⟨hBoundary, hSplit.2.2.2, by decide⟩

end Omega.Conclusion
