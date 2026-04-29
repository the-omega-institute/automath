import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-golden-w1-two-phase-arithmetic-mean-eight-fifteenths`. -/
theorem paper_xi_golden_w1_two_phase_arithmetic_mean_eight_fifteenths (s : ℚ) :
    (((1 / 2 : ℚ) + 1 / (2 * s)) + ((1 / 2 : ℚ) - 1 / (2 * s) + 1 / 15)) / 2 =
      8 / 15 := by
  ring_nf

end Omega.Zeta
