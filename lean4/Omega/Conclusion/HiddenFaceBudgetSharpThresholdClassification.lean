import Mathlib.Data.Finset.Card

namespace Omega.Conclusion

/-- Paper-facing threshold classification wrapper for hidden-face budgets.
    thm:conclusion-hidden-face-budget-sharp-threshold-classification -/
theorem paper_conclusion_hidden_face_budget_sharp_threshold_classification
    {U Face : Type} [DecidableEq Face] (Dist_m : U → U → ℕ) (n : ℕ)
    (hSmall : ∀ A B, Dist_m A B < 2 * n → A = B)
    (hSharp : ∀ A B, Dist_m A B = 2 * n → A ≠ B → ∃ Q : Finset Face, Q.card = 2 * n) :
    (∀ A B Tcard, Dist_m A B ≤ Tcard → Tcard < 2 * n → A = B) ∧
      (∀ A B Tcard, Dist_m A B ≤ Tcard → Tcard = 2 * n → A ≠ B →
        ∃ Q : Finset Face, Q.card = 2 * n) := by
  constructor
  · intro A B Tcard hDist hTcard
    exact hSmall A B (lt_of_le_of_lt hDist hTcard)
  · intro A B Tcard hDist hTcard hNe
    have hle : Dist_m A B ≤ 2 * n := by
      simpa [hTcard] using hDist
    have hge : 2 * n ≤ Dist_m A B := by
      apply Nat.le_of_not_lt
      intro hlt
      exact hNe (hSmall A B hlt)
    exact hSharp A B (Nat.le_antisymm hle hge) hNe

end Omega.Conclusion
