import Mathlib.Tactic

namespace Omega.Conclusion

/-- The sixth-order Renyi coefficient is uniformly negative under the Pearson-type moment bound,
and it decreases strictly with the Renyi parameter on `(0, ∞)`.
    thm:conclusion-poisson-cauchy-renyi-sixth-negative-monotone -/
theorem paper_conclusion_poisson_cauchy_renyi_sixth_negative_monotone {mu2 mu3 mu4 : Real}
    (hmu2 : 0 < mu2) (hPearson : mu2 * mu4 ≥ mu3 ^ 2 + mu2 ^ 3) :
    (∀ {alpha : Real}, 0 < alpha →
      alpha * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha - 2) * mu2 ^ 3 / 64) < 0) ∧
      (∀ {alpha beta : Real}, 0 < alpha → alpha < beta →
        beta * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (beta - 2) * mu2 ^ 3 / 64) <
          alpha * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha - 2) * mu2 ^ 3 / 64)) := by
  have hmu2_cube : 0 < mu2 ^ 3 := by positivity
  have hmu3_sq : 0 ≤ mu3 ^ 2 := sq_nonneg mu3
  constructor
  · intro alpha halpha
    have halpha6 : 0 < alpha + 6 := by linarith
    have hinner :
        3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha - 2) * mu2 ^ 3 / 64 < 0 := by
      nlinarith
    exact mul_neg_of_pos_of_neg halpha hinner
  · intro alpha beta halpha hab
    have hbeta : 0 < beta := lt_trans halpha hab
    have hbeta_alpha : 0 < beta - alpha := sub_pos.mpr hab
    have halphabeta6 : 0 < alpha + beta + 6 := by linarith
    have hinner :
        3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha + beta - 2) * mu2 ^ 3 / 64 < 0 := by
      nlinarith
    have hfactor :
        beta * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (beta - 2) * mu2 ^ 3 / 64) -
            alpha * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha - 2) * mu2 ^ 3 / 64) =
          (beta - alpha) *
            (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha + beta - 2) * mu2 ^ 3 / 64) := by
      ring
    have hdiff :
        beta * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (beta - 2) * mu2 ^ 3 / 64) -
            alpha * (3 * mu3 ^ 2 / 32 - mu2 * mu4 / 8 - (alpha - 2) * mu2 ^ 3 / 64) <
          0 := by
      rw [hfactor]
      exact mul_neg_of_pos_of_neg hbeta_alpha hinner
    linarith

end Omega.Conclusion
