import Mathlib

open MeasureTheory intervalIntegral

namespace Omega.POM

/-- Quadratic pressure profile used in the concrete oracle-gap model. -/
noncomputable def pomOracleTau (q : ℝ) : ℝ :=
  (1 : ℝ) / 2 + q ^ 2 / 2

/-- Pressure slope on the hot phase. -/
noncomputable def pomOracleSlope (q : ℝ) : ℝ :=
  q

/-- Restricted variational profile after substituting the hot-phase optimizer `a = τ'(q)`. -/
noncomputable def pomOracleGamma (a : ℝ) : ℝ :=
  pomOracleTau a + (1 - a) * pomOracleSlope a

/-- Oracle gap area on the unit budget interval. -/
noncomputable def pomOracleGapArea : ℝ :=
  ∫ a in (0 : ℝ)..1, (1 - pomOracleGamma a)

/-- `L²` energy of the pressure slope on the hot phase. -/
noncomputable def pomOracleSlopeEnergy : ℝ :=
  (1 / 2 : ℝ) * ∫ q in (0 : ℝ)..1, (pomOracleSlope q) ^ 2

/-- Paper label: `thm:pom-oracle-gap-area-law-energy`. In the quadratic model, the restricted
variational profile integrates to the same value as the `L²` energy of the pressure slope. -/
theorem paper_pom_oracle_gap_area_law_energy :
    pomOracleGapArea = pomOracleSlopeEnergy := by
  unfold pomOracleGapArea pomOracleSlopeEnergy pomOracleGamma pomOracleTau pomOracleSlope
  have hrewrite :
      (∫ a in (0 : ℝ)..1, 1 - (1 / 2 + a ^ 2 / 2 + (1 - a) * a)) =
        ∫ a in (0 : ℝ)..1, ((1 / 2 : ℝ) - a + a ^ 2 / 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with a ha
    ring_nf
  rw [hrewrite]
  have hlin : IntervalIntegrable (fun a : ℝ => (-1 : ℝ) * a) volume 0 1 :=
    intervalIntegrable_id.const_mul (-1 : ℝ)
  have hsq : IntervalIntegrable (fun a : ℝ => ((1 : ℝ) / 2) * a ^ 2) volume 0 1 := by
    exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hsum : IntervalIntegrable (fun a : ℝ => (-1 : ℝ) * a + ((1 : ℝ) / 2) * a ^ 2) volume 0 1 :=
    hlin.add hsq
  have hsplit :
      (∫ a in (0 : ℝ)..1, ((1 / 2 : ℝ) - a + a ^ 2 / 2)) =
        ∫ a in (0 : ℝ)..1, (1 / 2 : ℝ) + ((-1 : ℝ) * a + ((1 : ℝ) / 2) * a ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with a ha
    ring_nf
  rw [hsplit]
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const hsum]
  rw [intervalIntegral.integral_add hlin hsq]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num

end Omega.POM
