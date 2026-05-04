import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fold-zero-temperature-orthant-selection`. -/
theorem paper_conclusion_fold_zero_temperature_orthant_selection {m : ℕ} (h : Fin m → ℝ)
    (h_ne : ∀ i, h i ≠ 0) :
    (∀ α : Fin m → Bool,
      ((∑ i, (if α i then h i else 0)) ≤ (∑ i, (if 0 < h i then h i else 0)))) ∧
      (∀ β : Fin m → Bool,
        (∀ α : Fin m → Bool,
          ((∑ i, (if α i then h i else 0)) ≤ (∑ i, (if β i then h i else 0)))) →
          β = fun i => decide (0 < h i)) := by
  constructor
  · intro α
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hi : 0 < h i
    · cases α i <;> simp [hi, le_of_lt hi]
    · have hle : h i ≤ 0 := le_of_not_gt hi
      cases α i <;> simp [hi, hle]
  · intro β hβ
    funext i
    by_cases hi : 0 < h i
    · cases hβi : β i
      · let α : Fin m → Bool := Function.update β i true
        have hlt :
            (∑ j, (if β j then h j else 0)) <
              (∑ j, (if α j then h j else 0)) := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro j _
            by_cases hji : j = i
            · subst hji
              simp [α, hβi, le_of_lt hi]
            · simp [α, hji]
          · refine ⟨i, Finset.mem_univ i, ?_⟩
            simp [α, hβi, hi]
        exact False.elim ((not_lt_of_ge (hβ α)) hlt)
      · simp [hi]
    · have hle : h i ≤ 0 := le_of_not_gt hi
      have hlt_i : h i < 0 := lt_of_le_of_ne hle (h_ne i)
      cases hβi : β i
      · simp [hi]
      · let α : Fin m → Bool := Function.update β i false
        have hlt :
            (∑ j, (if β j then h j else 0)) <
              (∑ j, (if α j then h j else 0)) := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro j _
            by_cases hji : j = i
            · subst hji
              simp [α, hβi, hle]
            · simp [α, hji]
          · refine ⟨i, Finset.mem_univ i, ?_⟩
            simp [α, hβi, hlt_i]
        exact False.elim ((not_lt_of_ge (hβ α)) hlt)

end Omega.Conclusion
