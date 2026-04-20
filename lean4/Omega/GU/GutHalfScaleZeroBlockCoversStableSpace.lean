import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- The half-scale zero-block lower bound matches the standard Fibonacci count for the stable
space, so the zero blocks cover a full half-scale stable space.
    thm:gut-half-scale-zero-block-covers-stable-space -/
theorem paper_gut_half_scale_zero_block_covers_stable_space
    (zeroBlockCard stableCount : Nat → Nat) (m : Nat) (hm : (m + 2) % 6 = 0)
    (h_zero : zeroBlockCard m ≥ Nat.fib ((m + 2) / 2))
    (h_count : stableCount ((m - 2) / 2) = Nat.fib ((m + 2) / 2)) :
    zeroBlockCard m ≥ stableCount ((m - 2) / 2) := by
  let _ := hm
  simpa [h_count] using h_zero

end Omega.GU
