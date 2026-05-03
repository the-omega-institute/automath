import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `prop:conclusion-resonance-budget-no-l2-envelope`. -/
theorem paper_conclusion_resonance_budget_no_l2_envelope
    (C w : ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hCnonneg : ∀ u : ℕ, 1 ≤ u → 0 ≤ C u)
    (hCdiv : ∀ B : ℝ, ∃ N : ℕ, B < ∑ u ∈ Finset.Icc 1 N, (C u) ^ 2) :
    ¬ ((∃ B : ℝ, ∀ N : ℕ, ∑ u ∈ Finset.Icc 1 N, (w u) ^ 2 ≤ B) ∧
        ∀ u : ℕ, 1 ≤ u → C u ≤ K * w u) := by
  rintro ⟨⟨B, hB⟩, hCw⟩
  have hKsq_nonneg : 0 ≤ K ^ 2 := le_of_lt (sq_pos_of_ne_zero hK.ne')
  rcases hCdiv (K ^ 2 * B) with ⟨N, hN⟩
  have hsum_le : (∑ u ∈ Finset.Icc 1 N, (C u) ^ 2) ≤ K ^ 2 * B := by
    calc
      (∑ u ∈ Finset.Icc 1 N, (C u) ^ 2)
          ≤ ∑ u ∈ Finset.Icc 1 N, (K * w u) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro u hu
            have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
            have hCu_nonneg : 0 ≤ C u := hCnonneg u hu1
            have hKw_nonneg : 0 ≤ K * w u := le_trans hCu_nonneg (hCw u hu1)
            exact (sq_le_sq₀ hCu_nonneg hKw_nonneg).mpr (hCw u hu1)
      _ = ∑ u ∈ Finset.Icc 1 N, K ^ 2 * (w u) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            ring
      _ = K ^ 2 * ∑ u ∈ Finset.Icc 1 N, (w u) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ K ^ 2 * B := by
            exact mul_le_mul_of_nonneg_left (hB N) hKsq_nonneg
  exact not_lt_of_ge hsum_le hN

end Omega.Conclusion
