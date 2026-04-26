import Mathlib.Tactic
import Omega.SPG.HypercubeGradientConsistency

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-onequarter-cross-category-rigidity`. -/
theorem paper_conclusion_onequarter_cross_category_rigidity :
    ((1 : ℝ) / (2 * (2 : ℝ)) = 1 / 4) ∧
      (2 * (1 + 1) = 4 ∧
        (∀ k₁ k₂ : ℕ, k₁ < k₂ → 2 * (k₁ + 1) < 2 * (k₂ + 1)) ∧
        (2 ^ 2 = 4 ∧ 2 ^ 3 = 8)) ∧
      ((∀ (fu fv log_quv log_qvu : ℤ),
          (fu + log_quv) - (fv + log_qvu) = (log_quv - log_qvu) - (fv - fu)) ∧
        (∀ eps : ℕ, 4 * (eps / 4) ≤ eps) ∧
        (∀ eps : ℕ, 4 ∣ eps → 4 * (eps / 4) = eps) ∧
        (2 * (1 + 1) = 4)) := by
  exact ⟨by norm_num, Omega.SPG.paper_spg_hypercube_gradient_consistency_by_square_defect,
    Omega.SPG.paper_spg_hypercube_near_detailed_balance_optimal⟩

end Omega.Conclusion
