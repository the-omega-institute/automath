import Mathlib.Tactic

namespace Omega.Conclusion

/-- The sixth-order KL coefficient is forced negative by the Pearson lower bound on `μ₂ μ₄`, so the
scaled KL profile approaches its fourth-order limit from below. -/
theorem paper_conclusion_poisson_cauchy_kl_sixth_negative_one_sided_approach
    {mu2 mu3 mu4 K4 K6 : ℝ} (hmu2 : 0 < mu2) (hK4 : K4 = mu2 ^ 2 / 8)
    (hK6 : K6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32)
    (hPearson : mu2 * mu4 ≥ mu3 ^ 2 + mu2 ^ 3) :
    K6 ≤ -(7 * mu2 ^ 3 + 2 * mu3 ^ 2) / 64 ∧ K6 < 0 ∧
      ∀ t > 0, K4 + K6 / t ^ 2 ≤ K4 := by
  let _ := hK4
  have hK6_bound : K6 ≤ -(7 * mu2 ^ 3 + 2 * mu3 ^ 2) / 64 := by
    nlinarith [hK6, hPearson]
  have hmu2_cube : 0 < mu2 ^ 3 := by positivity
  have hmu3_sq : 0 ≤ mu3 ^ 2 := sq_nonneg mu3
  have hK6_neg : K6 < 0 := by
    have hneg_rhs : -(7 * mu2 ^ 3 + 2 * mu3 ^ 2) / 64 < 0 := by
      nlinarith
    exact lt_of_le_of_lt hK6_bound hneg_rhs
  have hK6_nonpos : K6 ≤ 0 := le_of_lt hK6_neg
  refine ⟨hK6_bound, hK6_neg, ?_⟩
  intro t ht
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hdiv_nonpos : K6 / t ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hK6_nonpos ht_sq_nonneg
  linarith

end Omega.Conclusion
