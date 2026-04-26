import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete two-case minimal-budget gap data.  The budget is `1` on the nonhalting side and
`2` on the halting side, and the last field records the undecidability of any Boolean separator
for the halting predicate. -/
structure conclusion_budget_factor2_inapproximability_data where
  Instance : Type u
  halts : Instance → Prop
  budget : Instance → ℕ
  budget_eq_one_of_not_halts : ∀ π, ¬ halts π → budget π = 1
  budget_eq_two_of_halts : ∀ π, halts π → budget π = 2
  halting_not_decidable :
    ¬ ∃ decider : Instance → Bool, ∀ π, decider π = true ↔ halts π

namespace conclusion_budget_factor2_inapproximability_data

/-- No total integer-valued approximation can have a uniform factor strictly below `2`. -/
def no_subtwo_computable_approx
    (D : conclusion_budget_factor2_inapproximability_data) : Prop :=
  ∀ (A : D.Instance → ℕ) (c : ℚ), c < 2 →
    ¬ ∀ π, D.budget π ≤ A π ∧ (A π : ℚ) ≤ c * D.budget π

/-- No total integer-valued approximation can satisfy the strict factor-`2` inequality. -/
def no_strict_two_computable_approx
    (D : conclusion_budget_factor2_inapproximability_data) : Prop :=
  ∀ A : D.Instance → ℕ,
    ¬ ∀ π, D.budget π ≤ A π ∧ (A π : ℚ) < 2 * D.budget π

end conclusion_budget_factor2_inapproximability_data

/-- Paper label: `thm:conclusion-budget-factor2-inapproximability`. -/
theorem paper_conclusion_budget_factor2_inapproximability
    (D : conclusion_budget_factor2_inapproximability_data) :
    D.no_subtwo_computable_approx ∧ D.no_strict_two_computable_approx := by
  classical
  constructor
  · intro A c hc hA
    apply D.halting_not_decidable
    refine ⟨fun π => decide (2 ≤ A π), ?_⟩
    intro π
    change decide (2 ≤ A π) = true ↔ D.halts π
    rw [decide_eq_true_eq]
    constructor
    · intro htwo
      by_contra hnot
      have hbudget : D.budget π = 1 := D.budget_eq_one_of_not_halts π hnot
      have hupper : (A π : ℚ) < 2 := by
        calc
          (A π : ℚ) ≤ c * D.budget π := (hA π).2
          _ = c := by rw [hbudget]; norm_num
          _ < 2 := hc
      have hAπ_lt_two : A π < 2 := by exact_mod_cast hupper
      omega
    · intro hhalts
      have hbudget : D.budget π = 2 := D.budget_eq_two_of_halts π hhalts
      simpa [hbudget] using (hA π).1
  · intro A hA
    apply D.halting_not_decidable
    refine ⟨fun π => decide (2 ≤ A π), ?_⟩
    intro π
    change decide (2 ≤ A π) = true ↔ D.halts π
    rw [decide_eq_true_eq]
    constructor
    · intro htwo
      by_contra hnot
      have hbudget : D.budget π = 1 := D.budget_eq_one_of_not_halts π hnot
      have hupper : (A π : ℚ) < 2 := by
        calc
          (A π : ℚ) < 2 * D.budget π := (hA π).2
          _ = 2 := by rw [hbudget]; norm_num
      have hAπ_lt_two : A π < 2 := by exact_mod_cast hupper
      omega
    · intro hhalts
      have hbudget : D.budget π = 2 := D.budget_eq_two_of_halts π hhalts
      simpa [hbudget] using (hA π).1

end Omega.Conclusion
