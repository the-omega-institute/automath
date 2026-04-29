import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9y-window6-base24-volume-density-identity`. -/
theorem paper_xi_time_part9y_window6_base24_volume_density_identity
    (gaugeLog nonminimal minimal total : ℕ) (hgauge : gaugeLog = 13)
    (hnonminimal : nonminimal = 13) (hminimal : minimal = 8) (htotal : total = 21) :
    (gaugeLog : ℚ) / total = (nonminimal : ℚ) / total ∧
      (nonminimal : ℚ) / total = (13 : ℚ) / 21 ∧
      1 - (gaugeLog : ℚ) / total = (minimal : ℚ) / total ∧
      (minimal : ℚ) / total = (8 : ℚ) / 21 := by
  subst gaugeLog
  subst nonminimal
  subst minimal
  subst total
  norm_num

end Omega.Zeta
