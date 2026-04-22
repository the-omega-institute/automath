import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.GroupUnification.BoundaryShift4UpliftIsomorphism
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.GU

open Finset

/-- The six short roots in the window-6 `B₃` dictionary. -/
def boundary_m10_b3c3_rigid_four_block_split_short_roots : Finset Weight :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}

/-- The six long roots whose two nonzero coordinates have the same sign. -/
def boundary_m10_b3c3_rigid_four_block_split_a2_plus : Finset Weight :=
  {(1, 1, 0), (-1, -1, 0), (1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, -1, -1)}

/-- The six long roots whose two nonzero coordinates have opposite signs. -/
def boundary_m10_b3c3_rigid_four_block_split_a2_minus : Finset Weight :=
  {(1, -1, 0), (-1, 1, 0), (1, 0, -1), (-1, 0, 1), (0, 1, -1), (0, -1, 1)}

theorem boundary_m10_b3c3_rigid_four_block_split_partition_certificate :
    boundary_m10_b3c3_rigid_four_block_split_short_roots.card = 6 ∧
      boundary_m10_b3c3_rigid_four_block_split_a2_plus.card = 6 ∧
      boundary_m10_b3c3_rigid_four_block_split_a2_minus.card = 6 ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_short_roots
        boundary_m10_b3c3_rigid_four_block_split_a2_plus ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_short_roots
        boundary_m10_b3c3_rigid_four_block_split_a2_minus ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_a2_plus
        boundary_m10_b3c3_rigid_four_block_split_a2_minus ∧
      boundary_m10_b3c3_rigid_four_block_split_short_roots ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_minus =
        b3VisibleSupport.erase zeroWeight := by
  native_decide

/-- Paper-facing wrapper for the rigid `6 + 6 + 6 + 3` split carried by the `m = 10` boundary
layer through the shift-4 uplift from the window-6 `B₃/C₃` root--Cartan dictionary. -/
theorem paper_boundary_m10_b3c3_rigid_four_block_split :
    Fintype.card Window6ShortRootParityBlock = 6 ∧
      Fintype.card Window6LongRootParityBlock = 12 ∧
      Fintype.card Window6BoundaryParityBlock = 3 ∧
      boundary_m10_b3c3_rigid_four_block_split_short_roots.card = 6 ∧
      boundary_m10_b3c3_rigid_four_block_split_a2_plus.card = 6 ∧
      boundary_m10_b3c3_rigid_four_block_split_a2_minus.card = 6 ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_short_roots
        boundary_m10_b3c3_rigid_four_block_split_a2_plus ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_short_roots
        boundary_m10_b3c3_rigid_four_block_split_a2_minus ∧
      Disjoint boundary_m10_b3c3_rigid_four_block_split_a2_plus
        boundary_m10_b3c3_rigid_four_block_split_a2_minus ∧
      boundary_m10_b3c3_rigid_four_block_split_short_roots ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_minus =
        b3VisibleSupport.erase zeroWeight ∧
      b3AdjointWeightMultiset.card = 21 ∧
      c3AdjointWeightMultiset.card = 21 ∧
      boundaryZeroWeights.card = 3 ∧
      Function.Bijective (Omega.GroupUnification.boundaryShift4Uplift 6) ∧
      Omega.cBoundaryCount 10 = 21 := by
  rcases paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, hBoundaryZeroWeights, hb3Adjoint, hc3Adjoint, hShort, hLong, hBoundary, _, _, _⟩
  rcases boundary_m10_b3c3_rigid_four_block_split_partition_certificate with
    ⟨hShortCard, hPlusCard, hMinusCard, hDisjPlus, hDisjMinus, hDisjPm, hPartition⟩
  have hBij : Function.Bijective (Omega.GroupUnification.boundaryShift4Uplift 6) :=
    (Omega.GroupUnification.paper_boundary_shift4_uplift_isomorphism).2
  refine ⟨hShort, hLong, hBoundary, hShortCard, hPlusCard, hMinusCard, hDisjPlus, hDisjMinus,
    hDisjPm, hPartition, hb3Adjoint, hc3Adjoint, hBoundaryZeroWeights, hBij,
    Omega.cBoundaryCount_ten⟩

end Omega.GU
