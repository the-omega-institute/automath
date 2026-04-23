import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- Paper label: `prop:gut-A-cancels-lambda1`. At the scalar level, centering the logarithmic
deviations cancels the common `log λ₁` term exactly, and the remaining maximal deviation is the
larger of the two endpoint log-ratios. -/
theorem paper_gut_a_cancels_lambda1 (lambda1 eta_geo eta_min eta_max : ℝ) (hlambda1 : 0 < lambda1)
    (heta_geo : 0 < eta_geo) (heta_min : 0 < eta_min) (heta_max : 0 < eta_max)
    (heta_min_le : eta_min ≤ eta_geo) (heta_geo_le : eta_geo ≤ eta_max) :
    max
        (|((Real.log lambda1 - Real.log eta_min) - (Real.log lambda1 - Real.log eta_geo))|)
        (|((Real.log lambda1 - Real.log eta_max) - (Real.log lambda1 - Real.log eta_geo))|) =
      Real.log (max (eta_geo / eta_min) (eta_max / eta_geo)) := by
  let _ := hlambda1
  have hlog_min_le_geo : Real.log eta_min ≤ Real.log eta_geo :=
    Real.strictMonoOn_log.monotoneOn heta_min heta_geo heta_min_le
  have hlog_geo_le_max : Real.log eta_geo ≤ Real.log eta_max :=
    Real.strictMonoOn_log.monotoneOn heta_geo heta_max heta_geo_le
  have hleft :
      |((Real.log lambda1 - Real.log eta_min) - (Real.log lambda1 - Real.log eta_geo))| =
        Real.log (eta_geo / eta_min) := by
    calc
      |((Real.log lambda1 - Real.log eta_min) - (Real.log lambda1 - Real.log eta_geo))|
          = |Real.log eta_geo - Real.log eta_min| := by ring_nf
      _ = Real.log eta_geo - Real.log eta_min := by
        exact abs_of_nonneg (sub_nonneg.mpr hlog_min_le_geo)
      _ = Real.log (eta_geo / eta_min) := by
        rw [Real.log_div heta_geo.ne' heta_min.ne']
  have hright :
      |((Real.log lambda1 - Real.log eta_max) - (Real.log lambda1 - Real.log eta_geo))| =
        Real.log (eta_max / eta_geo) := by
    calc
      |((Real.log lambda1 - Real.log eta_max) - (Real.log lambda1 - Real.log eta_geo))|
          = |Real.log eta_geo - Real.log eta_max| := by ring_nf
      _ = -(Real.log eta_geo - Real.log eta_max) := by
        exact abs_of_nonpos (sub_nonpos.mpr hlog_geo_le_max)
      _ = Real.log eta_max - Real.log eta_geo := by ring
      _ = Real.log (eta_max / eta_geo) := by
        rw [Real.log_div heta_max.ne' heta_geo.ne']
  have hratio_left_pos : 0 < eta_geo / eta_min := div_pos heta_geo heta_min
  have hratio_right_pos : 0 < eta_max / eta_geo := div_pos heta_max heta_geo
  calc
    max
        (|((Real.log lambda1 - Real.log eta_min) - (Real.log lambda1 - Real.log eta_geo))|)
        (|((Real.log lambda1 - Real.log eta_max) - (Real.log lambda1 - Real.log eta_geo))|)
        = max (Real.log (eta_geo / eta_min)) (Real.log (eta_max / eta_geo)) := by
            rw [hleft, hright]
    _ = Real.log (max (eta_geo / eta_min) (eta_max / eta_geo)) := by
      by_cases hcmp : eta_geo / eta_min ≤ eta_max / eta_geo
      · rw [max_eq_right hcmp, max_eq_right]
        exact Real.strictMonoOn_log.monotoneOn hratio_left_pos hratio_right_pos hcmp
      · rw [max_eq_left (le_of_not_ge hcmp), max_eq_left]
        exact Real.strictMonoOn_log.monotoneOn hratio_right_pos hratio_left_pos (le_of_not_ge hcmp)

end Omega.GU
