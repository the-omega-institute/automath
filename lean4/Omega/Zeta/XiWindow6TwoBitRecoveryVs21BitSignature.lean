import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-two-bit-recovery-vs-21bit-signature`. -/
theorem paper_xi_window6_two_bit_recovery_vs_21bit_signature :
    (8 * min 2 (2 ^ 0) + 4 * min 3 (2 ^ 0) + 9 * min 4 (2 ^ 0) = 21) ∧
      (8 * min 2 (2 ^ 1) + 4 * min 3 (2 ^ 1) + 9 * min 4 (2 ^ 1) = 42) ∧
        (8 * min 2 (2 ^ 2) + 4 * min 3 (2 ^ 2) + 9 * min 4 (2 ^ 2) = 64) ∧
          2 ^ 6 = 64 ∧ 2 < 21 := by
  native_decide

end Omega.Zeta
