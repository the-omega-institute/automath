import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCovClosed

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- The order-`1` distribution moment supported on `{1 / 2, -1 / 2}`. The coefficient `d`
records the `δ'_{-1/2}` weight, whose contribution on `x^k` is
`-d * k * (-1 / 2)^(k - 1) = 2 * d * k * (-1 / 2)^k`. -/
noncomputable def gaugeAnomalyCovarianceDistributionMoment (a b d : ℚ) (k : ℕ) : ℚ :=
  a * (1 / 2 : ℚ) ^ k + b * (-1 / 2 : ℚ) ^ k + (2 * d) * (k : ℚ) * (-1 / 2 : ℚ) ^ k

private theorem gaugeAnomalyCovarianceDistributionMoment_closed (k : ℕ) :
    autoCov k = gaugeAnomalyCovarianceDistributionMoment (1 / 8) (7 / 648) (1 / 216) k := by
  simp [autoCov, gaugeAnomalyCovarianceDistributionMoment]
  ring

private theorem gaugeAnomalyCovarianceDistributionMoment_unique
    {a b d : ℚ}
    (h : ∀ k : ℕ, 1 ≤ k → autoCov k = gaugeAnomalyCovarianceDistributionMoment a b d k) :
    a = 1 / 8 ∧ b = 7 / 648 ∧ d = 1 / 216 := by
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  rw [autoCov_one] at h1
  rw [autoCov_two] at h2
  rw [autoCov_three] at h3
  dsimp [gaugeAnomalyCovarianceDistributionMoment] at h1 h2 h3
  norm_num at h1 h2 h3
  have ha : a = 1 / 8 := by
    linarith
  have hb : b = 7 / 648 := by
    linarith
  have hd : d = 1 / 216 := by
    linarith
  exact ⟨ha, hb, hd⟩

/-- The closed gauge-anomaly autocovariance sequence is the unique order-`1` moment functional
supported on `{1 / 2, -1 / 2}` with the explicit coefficients from the paper.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem paper_fold_gauge_anomaly_covariance_distribution_moment :
    (∀ k : ℕ, 1 ≤ k →
      autoCov k = gaugeAnomalyCovarianceDistributionMoment (1 / 8) (7 / 648) (1 / 216) k) ∧
    ∀ a b d : ℚ,
      (∀ k : ℕ, 1 ≤ k → autoCov k = gaugeAnomalyCovarianceDistributionMoment a b d k) →
      a = 1 / 8 ∧ b = 7 / 648 ∧ d = 1 / 216 := by
  refine ⟨?_, ?_⟩
  · intro k _
    exact gaugeAnomalyCovarianceDistributionMoment_closed k
  · intro a b d h
    exact gaugeAnomalyCovarianceDistributionMoment_unique h

end Omega.Folding
