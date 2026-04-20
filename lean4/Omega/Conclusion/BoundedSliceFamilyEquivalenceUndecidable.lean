import Mathlib.Tactic

namespace Omega.Conclusion

/-- A reduction from an undecidable non-halting predicate to pointwise semantic equivalence of
slice families transfers undecidability to the family-equivalence problem. The proof is the
family-indexed analogue of the scalar semantic-equivalence wrapper.
    thm:conclusion-bounded-slice-family-equivalence-undecidable -/
theorem paper_conclusion_bounded_slice_family_equivalence_undecidable {Code Slice : Type*}
    (semEq : Slice → Slice → Prop) (embed : Code → Nat → Slice) (ref : Nat → Slice)
    (nonHalting : Code → Prop)
    (hReduction : ∀ c, nonHalting c ↔ ∀ m, semEq (embed c m) (ref m))
    (hUndecidable : ¬ Nonempty (∀ c, Decidable (nonHalting c))) :
    ¬ Nonempty (∀ G H : Nat → Slice, Decidable (∀ m, semEq (G m) (H m))) := by
  classical
  intro hFamilyEq
  apply hUndecidable
  refine ⟨?_⟩
  intro c
  let hFamilyDec : ∀ G H : Nat → Slice, Decidable (∀ m, semEq (G m) (H m)) :=
    Classical.choice hFamilyEq
  letI := hFamilyDec (embed c) ref
  exact decidable_of_iff (∀ m, semEq (embed c m) (ref m)) (hReduction c).symm

end Omega.Conclusion
