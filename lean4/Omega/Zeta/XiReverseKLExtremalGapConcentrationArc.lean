import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-reversekl-extremal-gap-concentration-arc`. -/
theorem paper_xi_reversekl_extremal_gap_concentration_arc
    (Delta a r delta mass oneMinusNormSq : ℝ)
    (ha : 0 < a)
    (hr : 0 < r)
    (hdelta : 0 < delta)
    (hfirst : oneMinusNormSq ≤ Delta / (a ^ 2 * r ^ 2))
    (hmass : mass ≤ (4 / delta ^ 2) * oneMinusNormSq) :
    oneMinusNormSq ≤ Delta / (a ^ 2 * r ^ 2) ∧
      mass ≤ (4 / delta ^ 2) * (Delta / (a ^ 2 * r ^ 2)) := by
  have _ : 0 < a ^ 2 * r ^ 2 := by positivity
  constructor
  · exact hfirst
  · have hcoeff_nonneg : 0 ≤ (4 / delta ^ 2 : ℝ) := by positivity
    exact hmass.trans (mul_le_mul_of_nonneg_left hfirst hcoeff_nonneg)

end Omega.Zeta
