import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_no_computable_complete_normal_form {A : Type} [DecidableEq A]
    (equiv : A → A → Prop)
    (undecidable_equiv :
      ¬ ∃ decideEquiv : A → A → Bool, ∀ a b, decideEquiv a b = true ↔ equiv a b)
    (NF : A → A) (h_sound : ∀ a, equiv (NF a) a)
    (h_complete : ∀ a b, equiv a b ↔ NF a = NF b) :
    False := by
  have _hsound : ∀ a, equiv (NF a) a := h_sound
  apply undecidable_equiv
  refine ⟨fun a b => if NF a = NF b then true else false, ?_⟩
  intro a b
  by_cases hnf : NF a = NF b
  · simp [hnf, h_complete a b]
  · simp [hnf, h_complete a b]

end Omega.Conclusion
