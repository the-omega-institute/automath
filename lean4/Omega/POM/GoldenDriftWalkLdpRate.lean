import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-golden-drift-walk-ldp-rate`.
The Bernoulli KL rate for the golden drift walk expands to the closed logarithmic form. -/
theorem paper_pom_golden_drift_walk_ldp_rate {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    ((1 + x) / 2) *
          Real.log (((1 + x) / 2) / (Real.goldenRatio ^ (-(1 : ℝ)))) / Real.log 2 +
        ((1 - x) / 2) *
            Real.log (((1 - x) / 2) / (Real.goldenRatio ^ (-(2 : ℝ)))) / Real.log 2 =
      -1 + ((3 - x) / 2) * (Real.log Real.goldenRatio / Real.log 2) +
        (x / 2) * (Real.log ((1 + x) / (1 - x)) / Real.log 2) +
          (1 / 2) * (Real.log (1 - x ^ 2) / Real.log 2) := by
  have pom_golden_drift_walk_ldp_rate_one_add_pos : 0 < 1 + x := by linarith
  have pom_golden_drift_walk_ldp_rate_one_sub_pos : 0 < 1 - x := by linarith
  have pom_golden_drift_walk_ldp_rate_log_two_ne : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have pom_golden_drift_walk_ldp_rate_phi_pow_one_ne :
      Real.goldenRatio ^ (-(1 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.goldenRatio_pos _)
  have pom_golden_drift_walk_ldp_rate_phi_pow_two_ne :
      Real.goldenRatio ^ (-(2 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.goldenRatio_pos _)
  have pom_golden_drift_walk_ldp_rate_log_first :
      Real.log (((1 + x) / 2) / (Real.goldenRatio ^ (-(1 : ℝ)))) =
        Real.log (1 + x) - Real.log 2 + Real.log Real.goldenRatio := by
    have hhalf : (1 + x) / 2 ≠ 0 := by positivity
    calc
      Real.log (((1 + x) / 2) / (Real.goldenRatio ^ (-(1 : ℝ)))) =
          Real.log ((1 + x) / 2) -
            Real.log (Real.goldenRatio ^ (-(1 : ℝ))) := by
            rw [Real.log_div hhalf pom_golden_drift_walk_ldp_rate_phi_pow_one_ne]
      _ = (Real.log (1 + x) - Real.log 2) -
            (-(1 : ℝ) * Real.log Real.goldenRatio) := by
            rw [Real.log_div (ne_of_gt pom_golden_drift_walk_ldp_rate_one_add_pos)
              (by norm_num : (2 : ℝ) ≠ 0)]
            rw [Real.log_rpow Real.goldenRatio_pos]
      _ = Real.log (1 + x) - Real.log 2 + Real.log Real.goldenRatio := by ring
  have pom_golden_drift_walk_ldp_rate_log_second :
      Real.log (((1 - x) / 2) / (Real.goldenRatio ^ (-(2 : ℝ)))) =
        Real.log (1 - x) - Real.log 2 + 2 * Real.log Real.goldenRatio := by
    have hhalf : (1 - x) / 2 ≠ 0 := by positivity
    calc
      Real.log (((1 - x) / 2) / (Real.goldenRatio ^ (-(2 : ℝ)))) =
          Real.log ((1 - x) / 2) -
            Real.log (Real.goldenRatio ^ (-(2 : ℝ))) := by
            rw [Real.log_div hhalf pom_golden_drift_walk_ldp_rate_phi_pow_two_ne]
      _ = (Real.log (1 - x) - Real.log 2) -
            (-(2 : ℝ) * Real.log Real.goldenRatio) := by
            rw [Real.log_div (ne_of_gt pom_golden_drift_walk_ldp_rate_one_sub_pos)
              (by norm_num : (2 : ℝ) ≠ 0)]
            rw [Real.log_rpow Real.goldenRatio_pos]
      _ = Real.log (1 - x) - Real.log 2 + 2 * Real.log Real.goldenRatio := by ring
  have pom_golden_drift_walk_ldp_rate_log_ratio :
      Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) := by
    rw [Real.log_div (ne_of_gt pom_golden_drift_walk_ldp_rate_one_add_pos)
      (ne_of_gt pom_golden_drift_walk_ldp_rate_one_sub_pos)]
  have pom_golden_drift_walk_ldp_rate_log_square :
      Real.log (1 - x ^ 2) = Real.log (1 + x) + Real.log (1 - x) := by
    rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring]
    rw [Real.log_mul (ne_of_gt pom_golden_drift_walk_ldp_rate_one_add_pos)
      (ne_of_gt pom_golden_drift_walk_ldp_rate_one_sub_pos)]
  rw [pom_golden_drift_walk_ldp_rate_log_first, pom_golden_drift_walk_ldp_rate_log_second,
    pom_golden_drift_walk_ldp_rate_log_ratio, pom_golden_drift_walk_ldp_rate_log_square]
  field_simp [pom_golden_drift_walk_ldp_rate_log_two_ne]
  ring

end Omega.POM
