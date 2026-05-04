import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9m-kl-controls-maxfiber-excess`. -/
theorem paper_xi_time_part9m_kl_controls_maxfiber_excess
    (m : Nat) (maxFiber avgFiber tvGap klGap : ℝ)
    (hExcess : maxFiber - avgFiber ≤ (2 : ℝ) ^ m * tvGap)
    (hPinsker : tvGap ≤ Real.sqrt (klGap / 2)) :
    maxFiber - avgFiber ≤ (2 : ℝ) ^ m * Real.sqrt (klGap / 2) := by
  have hMul :
      (2 : ℝ) ^ m * tvGap ≤ (2 : ℝ) ^ m * Real.sqrt (klGap / 2) := by
    exact mul_le_mul_of_nonneg_left hPinsker (by positivity)
  exact le_trans hExcess hMul

end Omega.Zeta
