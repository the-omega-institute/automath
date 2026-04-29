import Mathlib.Tactic

namespace Omega.Zeta

/-- The endpoint quotient whose two real-root sides have different logarithmic scales. -/
noncomputable def xi_phil_endpoint_asymmetry_log_correction_quotient (a : ℝ) : ℝ :=
  (1 - a ^ 2)⁻¹ * Real.log (1 + (1 + a)⁻¹ ^ 2)

/-- The positive endpoint model after writing `a = 1 - h`. -/
noncomputable def xi_phil_endpoint_asymmetry_log_correction_positive_model (h : ℝ) : ℝ :=
  (h * 2 - h ^ 2)⁻¹ * Real.log (1 + (2 - h)⁻¹ ^ 2)

/-- The negative endpoint model after writing `a = -1 + h`. -/
noncomputable def xi_phil_endpoint_asymmetry_log_correction_negative_model (h : ℝ) : ℝ :=
  (h * 2 - h ^ 2)⁻¹ * Real.log (1 + h⁻¹ ^ 2)

/-- Paper label: `cor:xi-phiL-endpoint-asymmetry-log-correction`.

The endpoint quotient factors into the same algebraic pole `h * (2 - h)` on both sides. The
positive endpoint keeps a bounded logarithmic argument `(2 - h)⁻¹`, while the negative endpoint
contains the singular logarithmic correction `h⁻¹`. The final two clauses record the elementary
nonnegativity of both model terms in the real-root window `0 < h < 2`. -/
theorem paper_xi_phil_endpoint_asymmetry_log_correction
    (h : ℝ) (hpos : 0 < h) (hlt : h < 2) :
    xi_phil_endpoint_asymmetry_log_correction_quotient (1 - h) =
        xi_phil_endpoint_asymmetry_log_correction_positive_model h ∧
      xi_phil_endpoint_asymmetry_log_correction_quotient (-1 + h) =
        xi_phil_endpoint_asymmetry_log_correction_negative_model h ∧
      0 ≤ xi_phil_endpoint_asymmetry_log_correction_positive_model h ∧
      0 ≤ xi_phil_endpoint_asymmetry_log_correction_negative_model h := by
  have htwopos : 0 < 2 - h := sub_pos.mpr hlt
  have hpolepos : 0 < h * (2 - h) := mul_pos hpos htwopos
  have hpoleexpandedpos : 0 < h * 2 - h ^ 2 := by
    convert hpolepos using 1
    ring
  constructor
  · rw [xi_phil_endpoint_asymmetry_log_correction_quotient,
      xi_phil_endpoint_asymmetry_log_correction_positive_model]
    have hden : 1 - (1 - h) ^ 2 = h * 2 - h ^ 2 := by ring
    have hbase : 1 + (1 - h) = 2 - h := by ring
    rw [hden, hbase]
  constructor
  · rw [xi_phil_endpoint_asymmetry_log_correction_quotient,
      xi_phil_endpoint_asymmetry_log_correction_negative_model]
    have hden : 1 - (-1 + h) ^ 2 = h * 2 - h ^ 2 := by ring
    have hbase : 1 + (-1 + h) = h := by ring
    rw [hden, hbase]
  constructor
  · have harg : 1 ≤ 1 + (2 - h)⁻¹ ^ 2 := by nlinarith [sq_nonneg ((2 - h)⁻¹)]
    exact mul_nonneg (inv_nonneg.mpr hpoleexpandedpos.le) (Real.log_nonneg harg)
  · have harg : 1 ≤ 1 + h⁻¹ ^ 2 := by nlinarith [sq_nonneg h⁻¹]
    exact mul_nonneg (inv_nonneg.mpr hpoleexpandedpos.le) (Real.log_nonneg harg)

end Omega.Zeta
