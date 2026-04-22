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

/-- No additive subgroup of `ZMod 64` can cut out the window-6 bin-fold fibers by translation.
    prop:window6-no-translation-quotient-fiber -/
theorem window6_no_translation_quotient_subgroup :
    ¬ ∃ H : AddSubgroup (ZMod 64),
        ∀ x y : ZMod 64, cBinFold 6 x.val = cBinFold 6 y.val ↔ y - x ∈ H := by
  rintro ⟨H, hH⟩
  have h21eq : cBinFold 6 37 = cBinFold 6 58 := by native_decide
  have h34eq : cBinFold 6 37 = cBinFold 6 3 := by native_decide
  have h21 : (21 : ZMod 64) ∈ H := by
    have : ((58 : ZMod 64) - (37 : ZMod 64)) ∈ H := (hH 37 58).mp h21eq
    simpa using this
  have h34 : (34 : ZMod 64) ∈ H := by
    have : ((37 : ZMod 64) - (3 : ZMod 64)) ∈ H := (hH 3 37).mp h34eq.symm
    simpa using this
  have h13 : (13 : ZMod 64) ∈ H := by simpa using H.sub_mem h34 h21
  have h8 : (8 : ZMod 64) ∈ H := by simpa using H.sub_mem h21 h13
  have h5 : (5 : ZMod 64) ∈ H := by simpa using H.sub_mem h13 h8
  have h3 : (3 : ZMod 64) ∈ H := by simpa using H.sub_mem h8 h5
  have h2 : (2 : ZMod 64) ∈ H := by simpa using H.sub_mem h5 h3
  have h1 : (1 : ZMod 64) ∈ H := by simpa using H.sub_mem h3 h2
  have h01 : cBinFold 6 0 = cBinFold 6 1 := by
    exact (hH 0 1).2 (by simpa using h1)
  have hneq : cBinFold 6 0 ≠ cBinFold 6 1 := by
    simpa using (binFold6_edge_separation ⟨0, by decide⟩ ⟨0, by decide⟩)
  exact hneq h01

/-- Exact paper-facing wrapper for the window-6 translation-quotient obstruction.
    prop:window6-no-translation-quotient-fiber -/
theorem paper_window6_no_translation_quotient_fiber :
    ¬ ∃ H : AddSubgroup (ZMod 64),
        ∀ x y : ZMod 64, cBinFold 6 x.val = cBinFold 6 y.val ↔ y - x ∈ H := by
  exact window6_no_translation_quotient_subgroup

end Omega.GU
