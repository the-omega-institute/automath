import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:xi-sym-invariant-z2-grading-trivial`.
An invariant subset for the full permutation action is either empty or all of the finite type. -/
theorem paper_xi_sym_invariant_z2_grading_trivial {Delta : Type*} [Fintype Delta]
    [DecidableEq Delta] (A : Finset Delta) (hcard : 3 <= Fintype.card Delta)
    (hinv : forall sigma : Equiv.Perm Delta, A.image sigma = A) : A = ∅ ∨ A = Finset.univ := by
  have _hcard := hcard
  by_cases hA : A.Nonempty
  · rcases hA with ⟨x, hx⟩
    right
    ext y
    constructor
    · intro _
      simp
    · intro _
      have hyImage : y ∈ A.image (Equiv.swap x y) := by
        exact Finset.mem_image.mpr ⟨x, hx, by simp⟩
      simpa [hinv (Equiv.swap x y)] using hyImage
  · left
    ext y
    constructor
    · intro hy
      exact False.elim (hA ⟨y, hy⟩)
    · intro hy
      cases hy

end Omega.Conclusion
