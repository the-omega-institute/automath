import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fold-fiber-hardcore-universal-cumulant-transport`. -/
theorem paper_conclusion_fold_fiber_hardcore_universal_cumulant_transport
    (m : ℕ) (p : ℝ) (total bernoulli : ℕ → ℝ)
    (htransport : ∀ n, 1 ≤ n → total n = (m : ℝ) * bernoulli n)
    (h1 : bernoulli 1 = p) (h2 : bernoulli 2 = p * (1 - p))
    (h3 : bernoulli 3 = p * (1 - p) * (1 - 2 * p))
    (h4 : bernoulli 4 = p * (1 - p) * (1 - 6 * p + 6 * p ^ 2)) :
    (∀ n, 1 ≤ n → total n = (m : ℝ) * bernoulli n) ∧
      total 1 = (m : ℝ) * p ∧
      total 2 = (m : ℝ) * (p * (1 - p)) ∧
      total 3 = (m : ℝ) * (p * (1 - p) * (1 - 2 * p)) ∧
      total 4 = (m : ℝ) * (p * (1 - p) * (1 - 6 * p + 6 * p ^ 2)) := by
  refine ⟨htransport, ?_, ?_, ?_, ?_⟩
  · rw [htransport 1 (by norm_num), h1]
  · rw [htransport 2 (by norm_num), h2]
  · rw [htransport 3 (by norm_num), h3]
  · rw [htransport 4 (by norm_num), h4]

end Omega.Conclusion
