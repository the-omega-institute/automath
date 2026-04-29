import Mathlib.Tactic
import Omega.GroupUnification.FibLieResonanceGlobalClassification

namespace Omega.GroupUnification

/-- Paper label: `cor:fib-lie-resonance-ladder-global-closure`.
The only Fibonacci-Lie resonance dimensions in the audited ladder are `3, 8, 21, 55`, which
occur exactly at `m = 2, 4, 6, 8`; hence every resonant case lies in the global window `m ≤ 8`. -/
theorem paper_fib_lie_resonance_ladder_global_closure (m : ℕ) :
    (Nat.fib (m + 2) = 3 ∨ Nat.fib (m + 2) = 8 ∨ Nat.fib (m + 2) = 21 ∨ Nat.fib (m + 2) = 55) →
      m ≤ 8 := by
  intro h
  rcases (paper_fib_lie_resonance_global_classification m).1 h with rfl | rfl | rfl | rfl <;>
    omega

end Omega.GroupUnification
