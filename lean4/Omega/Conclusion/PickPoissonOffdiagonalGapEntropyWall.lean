import Mathlib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-pick-poisson-offdiagonal-gap-entropy-wall`. -/
theorem paper_conclusion_pick_poisson_offdiagonal_gap_entropy_wall {k : ℕ} (hk : 0 < k)
    {S Delta I : ℝ} (hS : S = 1 - Delta) (hSpos : 0 < S) (hSle : S ≤ 1)
    (hI : I ≥ (k : ℝ) * Real.log ((k : ℝ) / S)) :
    I ≥ (k : ℝ) * Real.log ((k : ℝ) / (1 - Delta)) ∧
      I ≥ (k : ℝ) * Real.log (k : ℝ) := by
  have hfirst : I ≥ (k : ℝ) * Real.log ((k : ℝ) / (1 - Delta)) := by
    simpa [hS] using hI
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_nonneg : 0 ≤ (k : ℝ) := le_of_lt hk_pos
  have hS_inv : 1 ≤ S⁻¹ := (one_le_inv₀ hSpos).mpr hSle
  have hdiv_ge : (k : ℝ) ≤ (k : ℝ) / S := by
    rw [div_eq_mul_inv]
    nth_rewrite 1 [← mul_one (k : ℝ)]
    exact mul_le_mul_of_nonneg_left hS_inv hk_nonneg
  have hlog_ge : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) / S) :=
    Real.log_le_log hk_pos hdiv_ge
  have hmul_ge :
      (k : ℝ) * Real.log (k : ℝ) ≤ (k : ℝ) * Real.log ((k : ℝ) / S) :=
    mul_le_mul_of_nonneg_left hlog_ge hk_nonneg
  exact ⟨hfirst, le_trans hmul_ge hI⟩

end Omega.Conclusion
