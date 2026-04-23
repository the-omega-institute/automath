import Mathlib.Tactic
import Omega.GU.BoundaryM10B3C3RigidFourBlockSplit

namespace Omega.GU

open Finset

/-- Paper label: `cor:fold6-weyl-two-orbit-compression`. The window-6 `B₃` root dictionary splits
into a 6-point short-root sector and a 12-point long-root sector, so any Weyl-invariant sectorwise
constant statistic compresses to the two corresponding orbit sums. -/
theorem paper_fold6_weyl_two_orbit_compression (f : Weight → ℚ)
    (hshort :
      ∀ r ∈ boundary_m10_b3c3_rigid_four_block_split_short_roots, f r = f (1, 0, 0))
    (hlong :
      ∀ r ∈ boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_minus, f r = f (1, 1, 0)) :
    (boundary_m10_b3c3_rigid_four_block_split_short_roots ∪
        (boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
          boundary_m10_b3c3_rigid_four_block_split_a2_minus)).card = 18 ∧
      (boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
        boundary_m10_b3c3_rigid_four_block_split_a2_minus).card = 12 ∧
      Finset.sum boundary_m10_b3c3_rigid_four_block_split_short_roots f = 6 * f (1, 0, 0) ∧
      Finset.sum
          (boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
            boundary_m10_b3c3_rigid_four_block_split_a2_minus) f = 12 * f (1, 1, 0) ∧
      Finset.sum
          (boundary_m10_b3c3_rigid_four_block_split_short_roots ∪
            (boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
              boundary_m10_b3c3_rigid_four_block_split_a2_minus)) f =
        6 * f (1, 0, 0) + 12 * f (1, 1, 0) := by
  classical
  let longRoots :=
    boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
      boundary_m10_b3c3_rigid_four_block_split_a2_minus
  let allRoots := boundary_m10_b3c3_rigid_four_block_split_short_roots ∪ longRoots
  rcases boundary_m10_b3c3_rigid_four_block_split_partition_certificate with
    ⟨hShortCard, hPlusCard, hMinusCard, hDisjShortPlus, hDisjShortMinus, hDisjPlusMinus, _⟩
  have hDisjShortLong :
      Disjoint boundary_m10_b3c3_rigid_four_block_split_short_roots longRoots := by
    rw [show longRoots =
      boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
        boundary_m10_b3c3_rigid_four_block_split_a2_minus by rfl]
    rw [Finset.disjoint_union_right]
    exact ⟨hDisjShortPlus, hDisjShortMinus⟩
  have hLongCard : longRoots.card = 12 := by
    rw [show longRoots =
      boundary_m10_b3c3_rigid_four_block_split_a2_plus ∪
        boundary_m10_b3c3_rigid_four_block_split_a2_minus by rfl]
    rw [Finset.card_union_of_disjoint hDisjPlusMinus, hPlusCard, hMinusCard]
  have hAllCard : allRoots.card = 18 := by
    rw [show allRoots = boundary_m10_b3c3_rigid_four_block_split_short_roots ∪ longRoots by rfl]
    rw [Finset.card_union_of_disjoint hDisjShortLong, hShortCard, hLongCard]
  have hShortSum :
      Finset.sum boundary_m10_b3c3_rigid_four_block_split_short_roots f = 6 * f (1, 0, 0) := by
    calc
      Finset.sum boundary_m10_b3c3_rigid_four_block_split_short_roots f
          = Finset.sum boundary_m10_b3c3_rigid_four_block_split_short_roots (fun _ => f (1, 0, 0)) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              exact hshort r hr
      _ = boundary_m10_b3c3_rigid_four_block_split_short_roots.card • f (1, 0, 0) := by
            simp
      _ = 6 * f (1, 0, 0) := by
            rw [hShortCard, nsmul_eq_mul]
            norm_num
  have hLongSum : Finset.sum longRoots f = 12 * f (1, 1, 0) := by
    calc
      Finset.sum longRoots f = Finset.sum longRoots (fun _ => f (1, 1, 0)) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        exact hlong r (by simpa [longRoots] using hr)
      _ = longRoots.card • f (1, 1, 0) := by simp
      _ = 12 * f (1, 1, 0) := by
            rw [hLongCard, nsmul_eq_mul]
            norm_num
  have hAllSum :
      Finset.sum allRoots f = 6 * f (1, 0, 0) + 12 * f (1, 1, 0) := by
    calc
      Finset.sum allRoots f
          = Finset.sum boundary_m10_b3c3_rigid_four_block_split_short_roots f +
              Finset.sum longRoots f := by
                rw [show allRoots =
                  boundary_m10_b3c3_rigid_four_block_split_short_roots ∪ longRoots by rfl]
                exact Finset.sum_union hDisjShortLong
      _ = 6 * f (1, 0, 0) + 12 * f (1, 1, 0) := by rw [hShortSum, hLongSum]
  exact ⟨by simpa [allRoots, longRoots] using hAllCard,
    by simpa [longRoots] using hLongCard,
    hShortSum,
    by simpa [longRoots] using hLongSum,
    by simpa [allRoots, longRoots] using hAllSum⟩

end Omega.GU
