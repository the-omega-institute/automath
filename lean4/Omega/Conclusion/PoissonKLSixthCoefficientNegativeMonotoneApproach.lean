import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-kl-sixth-coefficient-negative-monotone-approach`. -/
theorem paper_conclusion_poisson_kl_sixth_coefficient_negative_monotone_approach
    (σ μ3 μ4 B6 : ℝ) (hσ : 0 < σ) (hμ4 : σ ^ 4 ≤ μ4)
    (hμ3 : μ3 ^ 2 ≤ σ ^ 2 * μ4)
    (hB6 : B6 = σ ^ 6 / 64 - σ ^ 2 * μ4 / 8 + 3 * μ3 ^ 2 / 32) :
    B6 < 0 := by
  have hσ2_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hσ6_pos : 0 < σ ^ 6 := by positivity
  have hμ4_scaled : σ ^ 6 ≤ σ ^ 2 * μ4 := by
    have hmul := mul_le_mul_of_nonneg_left hμ4 hσ2_nonneg
    nlinarith
  have hB6_bound : B6 ≤ -σ ^ 6 / 64 := by
    nlinarith
  nlinarith

end Omega.Conclusion
