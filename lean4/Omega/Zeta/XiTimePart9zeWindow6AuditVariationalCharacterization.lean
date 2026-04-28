import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9ze-window6-audit-variational-characterization`. -/
theorem paper_xi_time_part9ze_window6_audit_variational_characterization :
    (8 * 2 + 4 * 3 + 9 * 4 = 64) ∧
      (8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212) ∧
      (1 * 4 ^ 2 + 20 * 3 ^ 2 = 196) ∧
      196 < 212 := by
  norm_num

end Omega.Zeta
