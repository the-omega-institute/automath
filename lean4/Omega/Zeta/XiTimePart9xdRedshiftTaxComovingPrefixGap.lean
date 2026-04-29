import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xd-redshift-tax-comoving-prefix-gap`. -/
theorem paper_xi_time_part9xd_redshift_tax_comoving_prefix_gap
    (T δ0 pfix pmov : ℝ) (hδ0 : 0 < δ0) (hδ0_lt : δ0 < 1 / 2) (hT : 0 ≤ T)
    (hfix : Real.log ((T ^ 2 + (1 + δ0) ^ 2) / (4 * δ0)) / Real.log 2 ≤ pfix)
    (hmov : pmov = Real.log (((1 + δ0) ^ 2) / (4 * δ0)) / Real.log 2) :
    Real.log (1 + T ^ 2 / (1 + δ0) ^ 2) / Real.log 2 ≤ pfix - pmov := by
  have hden_pos : 0 < (4 : ℝ) * δ0 := by positivity
  have hone_pos : 0 < 1 + δ0 := by linarith
  have hone_sq_pos : 0 < (1 + δ0) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hT_sq_nonneg : 0 ≤ T ^ 2 := by simpa [pow_two] using mul_nonneg hT hT
  have hnum_pos : 0 < T ^ 2 + (1 + δ0) ^ 2 :=
    add_pos_of_nonneg_of_pos hT_sq_nonneg hone_sq_pos
  have hquot :
      1 + T ^ 2 / (1 + δ0) ^ 2 =
        ((T ^ 2 + (1 + δ0) ^ 2) / (4 * δ0)) /
          (((1 + δ0) ^ 2) / (4 * δ0)) := by
    field_simp [ne_of_gt hden_pos, ne_of_gt hone_sq_pos]
    ring
  have hlog :
      Real.log (1 + T ^ 2 / (1 + δ0) ^ 2) / Real.log 2 =
        Real.log ((T ^ 2 + (1 + δ0) ^ 2) / (4 * δ0)) / Real.log 2 -
          Real.log (((1 + δ0) ^ 2) / (4 * δ0)) / Real.log 2 := by
    rw [hquot]
    rw [Real.log_div (ne_of_gt (div_pos hnum_pos hden_pos))
      (ne_of_gt (div_pos hone_sq_pos hden_pos))]
    ring
  rw [hlog, hmov]
  linarith

end Omega.Zeta
