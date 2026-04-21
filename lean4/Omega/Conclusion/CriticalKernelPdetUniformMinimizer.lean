import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Auxiliary quadratic mass controlling the critical-kernel pseudodeterminant. -/
noncomputable def criticalKernelQuadraticMass {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, (w i) ^ 2

/-- Closed-form critical-kernel pseudodeterminant used in the uniform-minimizer estimate. -/
noncomputable def criticalKernelPdet {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ((n : ℝ) / (n - 1)) ^ (n - 1) * criticalKernelQuadraticMass w

private lemma one_le_criticalKernelQuadraticMass {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw_sum : (∑ i, w i) = 1) : 1 ≤ criticalKernelQuadraticMass w := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hsq_nonneg : 0 ≤ ∑ i, (w i - 1 / (n : ℝ)) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i _
    exact sq_nonneg (w i - 1 / (n : ℝ))
  have hexpand :
      ∑ i, (w i - 1 / (n : ℝ)) ^ 2 =
        ∑ i, (w i) ^ 2 - 2 * (1 / (n : ℝ)) * (∑ i, w i) + (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by
    let c : ℝ := 1 / (n : ℝ)
    calc
      ∑ i, (w i - 1 / (n : ℝ)) ^ 2
          = ∑ i, ((w i) ^ 2 - 2 * c * w i + c ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              dsimp [c]
              ring
      _ = ∑ i, ((w i) ^ 2 - 2 * c * w i) + ∑ i, c ^ 2 := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i, (w i) ^ 2) - ∑ i, (2 * c * w i) + ∑ i, c ^ 2 := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, (w i) ^ 2) - 2 * c * (∑ i, w i) + (n : ℝ) * c ^ 2 := by
            rw [← Finset.mul_sum]
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = (∑ i, (w i) ^ 2) - 2 * (1 / (n : ℝ)) * (∑ i, w i) + (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by
            simp [c]
  have hsq_bound : 0 ≤ ∑ i, (w i) ^ 2 - 1 / (n : ℝ) := by
    rw [hexpand, hw_sum] at hsq_nonneg
    have hcollapse :
        (∑ i, (w i) ^ 2) - 2 * (1 / (n : ℝ)) * (1 : ℝ) + (n : ℝ) * (1 / (n : ℝ)) ^ 2 =
          (∑ i, (w i) ^ 2) - 1 / (n : ℝ) := by
      field_simp [hn_ne]
      ring
    rwa [hcollapse] at hsq_nonneg
  have hmul_nonneg : 0 ≤ (n : ℝ) * (∑ i, (w i) ^ 2 - 1 / (n : ℝ)) := by
    exact mul_nonneg hn_pos.le hsq_bound
  have : 1 ≤ (n : ℝ) * ∑ i, (w i) ^ 2 := by
    have hmul_expand :
        (n : ℝ) * (∑ i, (w i) ^ 2 - 1 / (n : ℝ)) = (n : ℝ) * ∑ i, (w i) ^ 2 - 1 := by
      field_simp [hn_ne]
    rw [hmul_expand] at hmul_nonneg
    nlinarith
  simpa [criticalKernelQuadraticMass] using this

/-- The closed-form critical-kernel pseudodeterminant is minimized by the uniform distribution,
and its value is bounded below by the uniform benchmark.
    thm:conclusion-critical-kernel-pdet-uniform-minimizer -/
theorem paper_conclusion_critical_kernel_pdet_uniform_minimizer (n : ℕ) (hn : 2 ≤ n)
    (w : Fin n → ℝ) (_hw_pos : ∀ i, 0 < w i) (hw_sum : (∑ i, w i) = 1) :
    ((n : ℝ) / (n - 1)) ^ (n - 1) ≤ criticalKernelPdet w := by
  have hmass : 1 ≤ criticalKernelQuadraticMass w :=
    one_le_criticalKernelQuadraticMass hn w hw_sum
  have hden_pos_nat : 0 < n - 1 := by omega
  have hden_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have hone_le : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hbase_nonneg : 0 ≤ ((n : ℝ) / (n - 1)) ^ (n - 1) := by
    apply pow_nonneg
    exact div_nonneg (show 0 ≤ (n : ℝ) by positivity)
      hden_nonneg
  calc
    ((n : ℝ) / (n - 1)) ^ (n - 1)
        ≤ ((n : ℝ) / (n - 1)) ^ (n - 1) * criticalKernelQuadraticMass w := by
            simpa [one_mul] using mul_le_mul_of_nonneg_left hmass hbase_nonneg
    _ = criticalKernelPdet w := by rfl

end Omega.Conclusion
