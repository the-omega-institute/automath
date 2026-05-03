import Mathlib

namespace Omega.Folding

/-- Paper label: `prop:window6-crt-rectangular-band`. -/
theorem paper_window6_crt_rectangular_band (x y : Nat) :
    ((7 * x + 15 * y) % 3 = x % 3) ∧ ((7 * x + 15 * y) % 7 = y % 7) := by
  constructor
  · omega
  · omega

end Omega.Folding
