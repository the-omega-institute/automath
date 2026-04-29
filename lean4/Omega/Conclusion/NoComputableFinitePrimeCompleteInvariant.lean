import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-no-computable-finite-prime-complete-invariant`. -/
theorem paper_conclusion_no_computable_finite_prime_complete_invariant {A D : Type}
    [DecidableEq D] (equiv : A → A → Prop) (Inv : A → D)
    (complete : ∀ a b : A, equiv a b ↔ Inv a = Inv b)
    (undecidable :
      Not (∃ decide : A → A → Bool, ∀ a b : A, decide a b = true ↔ equiv a b)) :
    False := by
  refine undecidable ⟨fun a b => if Inv a = Inv b then true else false, ?_⟩
  intro a b
  by_cases h : Inv a = Inv b
  · simp [h, (complete a b).mpr h]
  · have hnot : ¬ equiv a b := fun he => h ((complete a b).mp he)
    simp [h, hnot]

end Omega.Conclusion
