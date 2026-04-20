import Mathlib.Tactic
import Omega.GroupUnification.FibLieResonanceGlobalClassification

namespace Omega.GroupUnification

/-- The minimal Fibonacci-Lie resonance cases `3` and `8` occur exactly at the
shifted indices `m + 2 = 4, 6`, hence exactly for `m = 2, 4`. -/
theorem paper_fib_lie_resonance_scarcity_su2_su3 (m : Nat) :
    (Nat.fib (m + 2) = 3 ∨ Nat.fib (m + 2) = 8) ↔ (m = 2 ∨ m = 4) := by
  constructor
  · intro h
    rcases h with h3 | h8
    · left
      apply Nat.fib_add_two_strictMono.injective
      calc
        Nat.fib (m + 2) = 3 := h3
        _ = Nat.fib (2 + 2) := by native_decide
    · right
      apply Nat.fib_add_two_strictMono.injective
      calc
        Nat.fib (m + 2) = 8 := h8
        _ = Nat.fib (4 + 2) := by native_decide
  · intro h
    rcases h with rfl | rfl
    · left
      native_decide
    · right
      native_decide

end Omega.GroupUnification
