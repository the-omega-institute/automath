import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-structure-two-plus-three-splitting`. -/
theorem paper_conclusion_window6_hidden_structure_two_plus_three_splitting :
    Fintype.card (Fin 2 × Fin 2) = 4 ∧
      Fintype.card (Fin 2 × Fin 2 × Fin 2) = 8 ∧
        ¬ (∃ f : (Fin 2 × Fin 2 × Fin 2) -> (Fin 2 × Fin 2), Function.Injective f) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · rintro ⟨f, hf⟩
    have hcard := Fintype.card_le_of_injective f hf
    norm_num at hcard

end Omega.Conclusion
