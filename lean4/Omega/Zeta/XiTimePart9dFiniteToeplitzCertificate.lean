import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9d-finite-toeplitz-certificate`.  Replacing the Toeplitz tail
by an error budget under a nonnegative prefactor preserves the upper bound. -/
theorem paper_xi_time_part9d_finite_toeplitz_certificate (D C E tail epsTerm : ℝ)
    (hC : 0 ≤ C) (hMain : D ≤ C * (E + tail)) (hTail : tail ≤ epsTerm) :
    D ≤ C * E + C * epsTerm := by
  have hScaled : C * tail ≤ C * epsTerm := mul_le_mul_of_nonneg_left hTail hC
  calc
    D ≤ C * (E + tail) := hMain
    _ = C * E + C * tail := by ring
    _ ≤ C * E + C * epsTerm := by linarith

end Omega.Zeta
