import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTauIntClosed

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues

/-- The finite covariance prefix `Σ_{k=1}^m C_k` attached to the closed gauge-anomaly
autocovariance law. -/
noncomputable def gaugeAnomalyCovPrefix (m : ℕ) : ℚ :=
  Finset.sum (Finset.range m) (fun k => autoCov (k + 1))

/-- The exact stationary variance of the length-`m` partial sum
`G_m = ∑_{t=1}^m g_t` computed from the covariance law
`Var(G_m) = m C₀ + 2 * Σ_{k=1}^{m-1} (m-k) C_k`. -/
noncomputable def gaugeAnomalyFiniteVariance (m : ℕ) : ℚ :=
  m * gaugeAnomalyCovZero +
    2 * Finset.sum (Finset.range m) (fun k => ((m : ℚ) - (k + 1 : ℚ)) * autoCov (k + 1))

private theorem gaugeAnomalyCovPrefix_closed (m : ℕ) :
    gaugeAnomalyCovPrefix m =
      ((232 : ℚ) - 243 * (1 / 2 : ℚ) ^ m + ((6 : ℚ) * m + 11) * (-1 / 2 : ℚ) ^ m) / 1944 := by
  induction m with
  | zero =>
      norm_num [gaugeAnomalyCovPrefix]
  | succ m ih =>
      have hsum :
          Finset.sum (Finset.range m) (fun k => autoCov (k + 1)) =
            ((232 : ℚ) - 243 * (1 / 2 : ℚ) ^ m + ((6 : ℚ) * m + 11) * (-1 / 2 : ℚ) ^ m) / 1944 := by
        simpa [gaugeAnomalyCovPrefix] using ih
      rw [gaugeAnomalyCovPrefix, Finset.sum_range_succ, hsum, autoCov]
      norm_num
      ring

private theorem gaugeAnomalyFiniteVariance_step (m : ℕ) :
    gaugeAnomalyFiniteVariance (m + 1) =
      gaugeAnomalyFiniteVariance m + gaugeAnomalyCovZero + 2 * gaugeAnomalyCovPrefix m := by
  rw [gaugeAnomalyFiniteVariance, gaugeAnomalyFiniteVariance, gaugeAnomalyCovPrefix,
    Finset.sum_range_succ]
  simp
  have hsplit :
      Finset.sum (Finset.range m) (fun k => ((m : ℚ) - (k : ℚ)) * autoCov (k + 1)) =
        Finset.sum (Finset.range m) (fun k => ((m : ℚ) - (k + 1 : ℚ)) * autoCov (k + 1)) +
          Finset.sum (Finset.range m) (fun k => autoCov (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hsplit]
  ring

private theorem gaugeAnomalyFiniteVariance_closed_aux (m : ℕ) :
    gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 + (1 / 2 : ℚ) ^ (m + 1) -
        (((2 : ℚ) * m + 3) / 486) * (-1 / 2 : ℚ) ^ m := by
  induction m with
  | zero =>
      norm_num [gaugeAnomalyFiniteVariance]
  | succ m ih =>
      rw [gaugeAnomalyFiniteVariance_step, ih, gaugeAnomalyCovZero, gaugeAnomalyCovPrefix_closed]
      norm_num
      ring_nf

/-- Closed form for the variance of the stationary gauge-anomaly partial sums.
    thm:fold-gauge-anomaly-var-finite-closed -/
theorem paper_fold_gauge_anomaly_var_finite_closed (m : ℕ) :
    gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 +
        ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m) := by
  rw [gaugeAnomalyFiniteVariance_closed_aux]
  have hhalf : (1 / 2 : ℚ) ^ m = (2 ^ m : ℚ)⁻¹ := by
    exact by
      simpa [one_div] using (inv_pow (2 : ℚ) m).symm
  have hpow : (-1 / 2 : ℚ) ^ m = (-1 : ℚ) ^ m * (2 ^ m : ℚ)⁻¹ := by
    calc
      (-1 / 2 : ℚ) ^ m = (-1 : ℚ) ^ m * (1 / 2 : ℚ) ^ m := by
        simpa [div_eq_mul_inv] using (mul_pow (-1 : ℚ) ((2 : ℚ)⁻¹) m)
      _ = (-1 : ℚ) ^ m * (2 ^ m : ℚ)⁻¹ := by rw [hhalf]
  rw [pow_succ, hhalf, hpow]
  ring_nf

/-- Paper-facing alias for the finite variance closed form.
    thm:fold-gauge-anomaly-finite-var-closed -/
theorem paper_fold_gauge_anomaly_finite_var_closed (m : ℕ) :
    gaugeAnomalyFiniteVariance m =
      (118 / 243 : ℚ) * m - 40 / 81 +
        ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m) := by
  simpa using paper_fold_gauge_anomaly_var_finite_closed m

end Omega.Folding
