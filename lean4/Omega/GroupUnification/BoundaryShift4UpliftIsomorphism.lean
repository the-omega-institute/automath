import Omega.Folding.BoundaryLayer

namespace Omega.GroupUnification

/-- Chapter-local wrapper for the shift-4 uplift into the boundary layer. -/
abbrev boundaryShift4Uplift (n : Nat) : Omega.X n → Omega.BoundaryWordSubtype n :=
  fun v =>
    ⟨⟨Omega.boundaryUpliftMap v, Omega.boundaryUpliftMap_no11 v⟩,
      Omega.boundaryUpliftMap_isBoundary v⟩

/-- Strip the two boundary bits on each side of a boundary word. -/
abbrev boundaryShift4Strip (n : Nat) : Omega.BoundaryWordSubtype n → Omega.X n :=
  fun w => ⟨Omega.boundaryStripMap w.1.1, Omega.boundaryStripMap_no11_of_boundary w.1 w.2⟩

theorem boundaryShift4Strip_leftInverse (n : Nat) :
    Function.LeftInverse (boundaryShift4Strip n) (boundaryShift4Uplift n) := by
  intro v
  apply Subtype.ext
  exact Omega.boundaryStrip_uplift v

theorem boundaryShift4Strip_rightInverse (n : Nat) :
    Function.RightInverse (boundaryShift4Strip n) (boundaryShift4Uplift n) := by
  intro w
  apply Subtype.ext
  apply Subtype.ext
  exact Omega.boundaryUplift_strip_boundary w.1 w.2

/-- Paper-facing package for the shift-4 boundary uplift isomorphism. The general clause records
the explicit uplift/strip inverses for `n ≥ 2`, and the second clause specializes the bijection to
the window `n = 6` used in the boundary-layer audit.
    thm:boundary-shift4-uplift-isomorphism -/
theorem paper_boundary_shift4_uplift_isomorphism :
    (∀ n : Nat, 2 ≤ n →
      Function.LeftInverse (boundaryShift4Strip n) (boundaryShift4Uplift n) ∧
        Function.RightInverse (boundaryShift4Strip n) (boundaryShift4Uplift n)) ∧
      Function.Bijective (boundaryShift4Uplift 6) := by
  refine ⟨?_, Omega.boundaryUplift_bijective 6⟩
  intro n _hn
  exact ⟨boundaryShift4Strip_leftInverse n, boundaryShift4Strip_rightInverse n⟩

end Omega.GroupUnification
