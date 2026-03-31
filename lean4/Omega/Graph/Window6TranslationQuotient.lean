import Omega.Folding.BinFold
import Omega.Conclusion.Window6Collision
import Mathlib.Tactic

namespace Omega.GU

/-- Concrete witness: window-6 fiber sizes take three distinct values 2,3,4.
    prop:window6-no-translation-quotient-fiber -/
theorem window6_fiber_sizes_not_constant :
    ∃ x y z : X 6, cBinFiberMult 6 x = 2 ∧ cBinFiberMult 6 y = 3 ∧ cBinFiberMult 6 z = 4 := by
  refine ⟨cBinFold 6 13, cBinFold 6 33, cBinFold 6 37, ?_⟩
  refine ⟨by native_decide, ?_, ?_⟩
  · exact (paper_boundary_fiber_sizes_six).1
  · exact (paper_boundary_fiber_sizes_six).2.1

/-- No constant class size can explain the window-6 fiber relation.
    prop:window6-no-translation-quotient-fiber -/
theorem window6_no_translation_quotient_fiber :
    ¬ ∃ hSize : Nat,
      ((Finset.univ : Finset (X 6)).filter (fun x => cBinFiberMult 6 x = hSize)).card = Fintype.card (X 6) := by
  intro h
  rcases h with ⟨hSize, hcard⟩
  rcases window6_fiber_sizes_not_constant with ⟨x, y, z, hx, hy, hz⟩
  have hsub := Finset.filter_subset (fun x => cBinFiberMult 6 x = hSize) (Finset.univ : Finset (X 6))
  have hEq : ((Finset.univ : Finset (X 6)).filter (fun x => cBinFiberMult 6 x = hSize)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    simp
  have hxmem : cBinFiberMult 6 x = hSize := by
    have : x ∈ ((Finset.univ : Finset (X 6)).filter (fun x => cBinFiberMult 6 x = hSize)) := by
      rw [hEq]
      simp
    simpa using this
  have hymem : cBinFiberMult 6 y = hSize := by
    have : y ∈ ((Finset.univ : Finset (X 6)).filter (fun x => cBinFiberMult 6 x = hSize)) := by
      rw [hEq]
      simp
    simpa using this
  linarith

end Omega.GU
