import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-linear-budget-absolute-counting-wall`. -/
theorem paper_conclusion_linear_budget_absolute_counting_wall {X : Type*} [Fintype X]
    (d : X → ℕ) (m B : ℕ) :
    ((∑ x, min (d x) (2 ^ B) : ℕ) : ℝ) / (2 : ℝ) ^ m ≤
      (Fintype.card X : ℝ) * (2 : ℝ) ^ B / (2 : ℝ) ^ m := by
  have hsum_nat : (∑ x, min (d x) (2 ^ B) : ℕ) ≤ ∑ _x : X, 2 ^ B := by
    exact Finset.sum_le_sum fun _x _hx => Nat.min_le_right _ _
  have hsum_real :
      ((∑ x, min (d x) (2 ^ B) : ℕ) : ℝ) ≤
        (Fintype.card X : ℝ) * (2 : ℝ) ^ B := by
    calc
      ((∑ x, min (d x) (2 ^ B) : ℕ) : ℝ) ≤
          ((∑ _x : X, 2 ^ B : ℕ) : ℝ) := by
            exact_mod_cast hsum_nat
      _ = (Fintype.card X : ℝ) * (2 : ℝ) ^ B := by
            simp
  exact div_le_div_of_nonneg_right hsum_real (by positivity)

end Omega.Conclusion
