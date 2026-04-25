import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

theorem paper_conclusion_born_weight_derived_from_hardy_and_fold_expectation (n : ℕ)
    (ψ : Fin n → ℂ) (hψ : ψ ≠ 0) :
    ∃ μ : Fin n → ℝ,
      (∀ x, 0 ≤ μ x) ∧ (∀ x, μ x = ‖ψ x‖ ^ 2 / (∑ i, ‖ψ i‖ ^ 2)) := by
  refine ⟨fun x => ‖ψ x‖ ^ 2 / (∑ i, ‖ψ i‖ ^ 2), ?_, ?_⟩
  · intro x
    have hden_pos : 0 < ∑ i, ‖ψ i‖ ^ 2 := by
      obtain ⟨x0, hx0⟩ : ∃ x0, ψ x0 ≠ 0 := by
        by_contra hzero
        push_neg at hzero
        apply hψ
        ext i
        exact hzero i
      have hterm_pos : 0 < ‖ψ x0‖ ^ 2 := by
        exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hx0)
      have hsingle : ‖ψ x0‖ ^ 2 ≤ ∑ i, ‖ψ i‖ ^ 2 := by
        exact Finset.single_le_sum (fun i _ => sq_nonneg ‖ψ i‖) (by simp)
      exact lt_of_lt_of_le hterm_pos hsingle
    exact div_nonneg (sq_nonneg ‖ψ x‖) hden_pos.le
  · intro x
    rfl

end Omega.Conclusion
