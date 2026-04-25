import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryTripleSpinorRigidity
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Concrete wrapper for the window-`6` boundary-Clifford ideal split. -/
structure conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data where
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_witness : Unit := ()

/-- The three canonical boundary `M₂` summands singled out by the triple-spinor package. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_data :
    Window6BoundaryTripleSpinorRigidityData :=
  { leftDim := 2
    middleDim := 2
    rightDim := 2
    leftFaithful := by
      unfold containsFaithfulM2Block
      omega
    middleFaithful := by
      unfold containsFaithfulM2Block
      omega
    rightFaithful := by
      unfold containsFaithfulM2Block
      omega }

/-- The full window-`6` ambient multiplicity count of `M₂` blocks. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_ambient_m2_blocks :
    ℕ := 8

/-- The three boundary `M₂` blocks removed as the ideal. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks :
    ℕ := 3

/-- The remaining `M₂` blocks in the split quotient. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks :
    ℕ := 5

namespace conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data

/-- The three boundary `M₂` blocks form the canonical ideal inside the ambient `8/4/9`
decomposition. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_is_ideal
    (_D : conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data) : Prop :=
  Window6BoundaryTripleSpinorRigidityStatement
      conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_data ∧
    conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks ≤
      conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_ambient_m2_blocks

/-- Removing the three boundary `M₂` blocks leaves an exact split
`M₂(C)^8 = M₂(C)^3 ⊕ M₂(C)^5`. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_exact_split
    (_D : conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data) : Prop :=
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_ambient_m2_blocks =
      conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks +
        conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks ∧
    8 + 4 + 9 = 3 + (5 + 4 + 9)

/-- Dimension bookkeeping after removing the boundary ideal. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_dimension_counts
    (_D : conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data) : Prop :=
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks *
      2 ^ 2 = 12 ∧
    conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks *
        2 ^ 2 +
      4 * 3 ^ 2 +
      9 * 4 ^ 2 = 200 ∧
    12 + 200 = 212

/-- Semisimple `K₀` ranks are counted by the numbers of simple matrix blocks. -/
def conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_k0_ranks
    (_D : conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data) : Prop :=
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks = 3 ∧
    conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks +
        4 + 9 = 18 ∧
    3 + 18 = 21

end conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data

/-- Paper label:
`thm:conclusion-window6-boundary-clifford-ideal-exact-12-plus-200-splitting`. -/
theorem paper_conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting
    (D : conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data) :
    D.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_is_ideal ∧
      D.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_exact_split ∧
      D.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_dimension_counts ∧
      D.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_k0_ranks := by
  have hboundary :=
    paper_conclusion_window6_boundary_triple_spinor_rigidity
      conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_data
  have hambient : 8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 := window6_S2_wedderburn
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨hboundary, by decide⟩
  · constructor
    · norm_num [conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_ambient_m2_blocks,
        conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks,
        conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks]
    · norm_num
  · refine ⟨?_, ?_, by norm_num⟩
    · norm_num [conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks]
    · norm_num [conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks]
  · refine ⟨by norm_num
      [conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_m2_blocks],
      by norm_num
        [conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_quotient_m2_blocks],
      by norm_num⟩

end Omega.Conclusion
