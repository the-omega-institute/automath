import Mathlib.Tactic
import Omega.Folding.AutocovarianceSeedValues
import Omega.Folding.BernoulliPCovarianceExplicitEvenOdd
import Omega.Folding.GaugeAnomalyCovClosed

namespace Omega.Folding

/-- The linear-mode coefficient in the off-critical Bernoulli-`p` autocovariance formulas. -/
noncomputable def bernoulliPJordanAlpha (p : ℚ) : ℚ :=
  -(p ^ 3 * (p ^ 2 - 3 * p + 1) ^ 2) / ((p + 1) ^ 2 * (2 * p - 1) * (p ^ 2 - p + 1))

/-- The odd-lag quadratic-mode coefficient away from `p = 1 / 2`. -/
noncomputable def bernoulliPJordanBeta (p : ℚ) : ℚ :=
  p ^ 2 * (1 - p) * (p ^ 5 + 4 * p ^ 4 - 4 * p ^ 3 - 5 * p ^ 2 + 7 * p - 2) /
    ((p + 1) * (2 * p - 1) * (p ^ 2 - p + 1) ^ 2)

/-- The even-lag quadratic-mode coefficient away from `p = 1 / 2`. -/
noncomputable def bernoulliPJordanDelta (p : ℚ) : ℚ :=
  p ^ 2 * (1 - p) ^ 2 * (p ^ 5 - p ^ 4 - 6 * p ^ 3 + 3 * p ^ 2 + 2 * p - 1) /
    ((p + 1) * (2 * p - 1) * (p ^ 2 - p + 1) ^ 2)

/-- The repeated-root factor `r(p) = p (1 - p)`. -/
def bernoulliPJordanRadius (p : ℚ) : ℚ :=
  p * (1 - p)

/-- The odd-lag closed form `Cov(g₀, g_{2m+1})` away from `p = 1 / 2`. -/
noncomputable def bernoulliPJordanOddClosed (p : ℚ) (m : ℕ) : ℚ :=
  bernoulliPJordanAlpha p * p ^ (2 * m) + bernoulliPJordanBeta p * bernoulliPJordanRadius p ^ m

/-- The even-lag closed form `Cov(g₀, g_{2m+2})` away from `p = 1 / 2`. -/
noncomputable def bernoulliPJordanEvenClosed (p : ℚ) (m : ℕ) : ℚ :=
  -bernoulliPJordanAlpha p * p ^ (2 * m + 1) +
    bernoulliPJordanDelta p * bernoulliPJordanRadius p ^ m

/-- The critical `p = 1 / 2` Jordan closed form, indexed by the lag `k ≥ 1`. -/
noncomputable def bernoulliPJordanCriticalClosed (k : ℕ) : ℚ :=
  (1 / 16 : ℚ) * (1 / 2 : ℚ) ^ (k - 1) +
    ((-13 : ℚ) / 1296 - (k - 1 : ℚ) / 216) * ((-1 : ℚ) / 2) ^ (k - 1)

/-- A packaged full autocovariance model that switches between the critical Jordan form and the
off-critical odd/even formulas. -/
noncomputable def bernoulliPFullAutocovarianceJordan (p : ℚ) (k : ℕ) : ℚ :=
  if p = 1 / 2 then
    bernoulliPJordanCriticalClosed k
  else if Odd k then
    bernoulliPJordanOddClosed p ((k - 1) / 2)
  else
    bernoulliPJordanEvenClosed p ((k / 2).pred)

/-- The full Bernoulli-`p` autocovariance package splits away from `p = 1 / 2` into the odd and
even closed forms, while at `p = 1 / 2` it collapses to the explicit Jordan critical law.
    thm:fold-bernoulli-p-full-autocovariance-jordan -/
theorem paper_fold_bernoulli_p_full_autocovariance_jordan (p : ℚ) :
    (∀ m : ℕ, p ≠ 1 / 2 →
      bernoulliPFullAutocovarianceJordan p (2 * m + 1) = bernoulliPJordanOddClosed p m) ∧
    (∀ m : ℕ, p ≠ 1 / 2 →
      bernoulliPFullAutocovarianceJordan p (2 * m + 2) = bernoulliPJordanEvenClosed p m) ∧
    (∀ k : ℕ, 1 ≤ k → p = 1 / 2 →
      bernoulliPFullAutocovarianceJordan p k =
        (1 / 16 : ℚ) * (1 / 2 : ℚ) ^ (k - 1) +
          ((-13 : ℚ) / 1296 - (k - 1 : ℚ) / 216) * ((-1 : ℚ) / 2) ^ (k - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hp
    have hodd : Odd (2 * m + 1) := by
      exact odd_two_mul_add_one m
    rw [bernoulliPFullAutocovarianceJordan, if_neg hp, if_pos hodd]
    simp [bernoulliPJordanOddClosed]
  · intro m hp
    have hnotodd : ¬ Odd (2 * m + 2) := by
      apply Nat.not_odd_iff_even.mpr
      refine ⟨m + 1, by omega⟩
    rw [bernoulliPFullAutocovarianceJordan, if_neg hp, if_neg hnotodd]
    simp [bernoulliPJordanEvenClosed]
  · intro k hk hp
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hclosed := Omega.paper_fold_gauge_anomaly_cov_closed (k - 1)
    rw [bernoulliPFullAutocovarianceJordan, if_pos hp]
    simpa [bernoulliPJordanCriticalClosed, AutocovarianceSeedValues.autoCov, hk'] using hclosed

end Omega.Folding
