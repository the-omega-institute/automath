import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.UnitaryDeterminantZeroUnitCircle

namespace Omega.Zeta

/-- The critical line `Re(s) = 1/2` is equivalent to the horizon-circle condition
    `|(L : ℂ)^(-s)| = L^(-1/2)` for every real base `L > 1`.
    cor:xi-critical-line-horizon-circle -/
theorem paper_xi_critical_line_horizon_circle {L : ℝ} (hL : 1 < L) {s : ℂ} (z : ℂ)
    (hz : z = (L : ℂ) ^ (-s)) : s.re = 1 / 2 ↔ ‖z‖ = L ^ (-(1 / 2 : ℝ)) := by
  rw [hz]
  constructor
  · intro hs
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hL)]
    simpa [Complex.neg_re, hs]
  · intro hzNorm
    have hexp : -s.re = -(1 / 2 : ℝ) := by
      apply (Real.strictMono_rpow_of_base_gt_one hL).injective
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hL)] at hzNorm
      simpa [Complex.neg_re] using hzNorm
    linarith

end Omega.Zeta
