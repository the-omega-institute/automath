import Mathlib.Data.Finset.Card

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oracle-success-double-ldp-variational`. -/
theorem paper_conclusion_oracle_success_double_ldp_variational
    {X Ω : Type*} [Fintype X] [Fintype Ω] [DecidableEq X]
    (fold : Ω → X) (B : ℕ) :
    ∃ cover : X → Finset Ω,
      (∀ x, ∀ a ∈ cover x, fold a = x) ∧
        (∀ x,
          (cover x).card =
            min ((Finset.univ.filter fun a => fold a = x).card) (2 ^ B)) := by
  classical
  let fiber : X → Finset Ω := fun x => Finset.univ.filter fun a => fold a = x
  have hchoose :
      ∀ x, ∃ s : Finset Ω, s ⊆ fiber x ∧ s.card = min (fiber x).card (2 ^ B) := by
    intro x
    exact Finset.exists_subset_card_eq
      (s := fiber x) (n := min (fiber x).card (2 ^ B)) (Nat.min_le_left _ _)
  refine ⟨fun x => Classical.choose (hchoose x), ?_, ?_⟩
  · intro x a ha
    have hsub : Classical.choose (hchoose x) ⊆ fiber x := (Classical.choose_spec (hchoose x)).1
    have ha_fiber : a ∈ fiber x := hsub ha
    exact (Finset.mem_filter.mp ha_fiber).2
  · intro x
    simpa [fiber] using (Classical.choose_spec (hchoose x)).2

end Omega.Conclusion
