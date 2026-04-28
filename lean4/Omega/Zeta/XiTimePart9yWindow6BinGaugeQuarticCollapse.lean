import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9y-window6-bin-gauge-quartic-collapse`. The audited
window-`6` binary gauge volume collapses to a pure quartic factorial power, with the
`21 - 8 = 13` complement count supplying the exponent. -/
theorem paper_xi_time_part9y_window6_bin_gauge_quartic_collapse :
    (Nat.factorial 2) ^ 8 * (Nat.factorial 3) ^ 4 * (Nat.factorial 4) ^ 9 = 24 ^ 13 ∧
      24 ^ 13 = (Nat.factorial 4) ^ 13 ∧ 21 - 8 = 13 := by
  norm_num [Nat.factorial]

end Omega.Zeta
