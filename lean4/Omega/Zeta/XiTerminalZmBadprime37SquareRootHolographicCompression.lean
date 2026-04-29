import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-badprime37-square-root-holographic-compression`. -/
theorem paper_xi_terminal_zm_badprime37_square_root_holographic_compression
    (k n imageSize fiberMultiplicity : Nat) (hn : n = 2 ^ k) (hImage : imageSize ≤ n)
    (hFiber : fiberMultiplicity = n ^ 2 - n) :
    imageSize ≤ 2 ^ k ∧ fiberMultiplicity = 2 ^ (2 * k) - 2 ^ k := by
  constructor
  · simpa [hn] using hImage
  · rw [hFiber, hn]
    calc
      (2 ^ k) ^ 2 - 2 ^ k = 2 ^ (k + k) - 2 ^ k := by
        rw [pow_two, ← pow_add]
      _ = 2 ^ (2 * k) - 2 ^ k := by
        rw [show k + k = 2 * k by omega]

end Omega.Zeta
