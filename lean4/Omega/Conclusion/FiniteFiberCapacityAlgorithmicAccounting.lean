import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-finite-fiber-capacity-algorithmic-accounting`. -/
theorem paper_conclusion_finite_fiber_capacity_algorithmic_accounting {X : Type} [Fintype X]
    (d : X → ℕ) (K : X → ℕ → ℕ) (c : ℕ)
    (h_lower : ∀ x B, K x B ≤ Nat.min (d x) (2 ^ B))
    (h_middle : ∀ x B, Nat.min (d x) (2 ^ B) ≤ K x (B + c))
    (h_upper : ∀ x B, K x (B + c) ≤ 2 ^ c * Nat.min (d x) (2 ^ B)) :
    ∀ B,
      (∑ x, K x B) ≤ ∑ x, Nat.min (d x) (2 ^ B) ∧
        (∑ x, Nat.min (d x) (2 ^ B)) ≤ ∑ x, K x (B + c) ∧
        (∑ x, K x (B + c)) ≤ 2 ^ c * ∑ x, Nat.min (d x) (2 ^ B) := by
  intro B
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_le_sum fun x _ => h_lower x B
  · exact Finset.sum_le_sum fun x _ => h_middle x B
  · calc
      ∑ x, K x (B + c) ≤ ∑ x, (2 ^ c * Nat.min (d x) (2 ^ B)) := by
        exact Finset.sum_le_sum fun x _ => h_upper x B
      _ = 2 ^ c * ∑ x, Nat.min (d x) (2 ^ B) := by
        simp [Finset.mul_sum]

end Omega.Conclusion
