import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GroupUnification

/-- The four resonance dimensions `3, 8, 21, 55` occur exactly at the Fibonacci indices
`m + 2 = 4, 6, 8, 10`, hence exactly for `m = 2, 4, 6, 8`. -/
theorem paper_fib_lie_resonance_global_classification (m : ℕ) :
    (Nat.fib (m + 2) = 3 ∨ Nat.fib (m + 2) = 8 ∨ Nat.fib (m + 2) = 21 ∨ Nat.fib (m + 2) = 55) ↔
      (m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 8) := by
  constructor
  · intro h
    rcases h with h3 | h8 | h21 | h55
    · left
      have hm' : m = 2 := by
        apply Nat.fib_add_two_strictMono.injective
        calc
          Nat.fib (m + 2) = 3 := h3
          _ = Nat.fib (2 + 2) := by native_decide
      exact hm'
    · right
      left
      have hm' : m = 4 := by
        apply Nat.fib_add_two_strictMono.injective
        calc
          Nat.fib (m + 2) = 8 := h8
          _ = Nat.fib (4 + 2) := by native_decide
      exact hm'
    · right
      right
      left
      have hm' : m = 6 := by
        apply Nat.fib_add_two_strictMono.injective
        calc
          Nat.fib (m + 2) = 21 := h21
          _ = Nat.fib (6 + 2) := by native_decide
      exact hm'
    · right
      right
      right
      have hm' : m = 8 := by
        apply Nat.fib_add_two_strictMono.injective
        calc
          Nat.fib (m + 2) = 55 := h55
          _ = Nat.fib (8 + 2) := by native_decide
      exact hm'
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · left
      native_decide
    · right
      left
      native_decide
    · right
      right
      left
      native_decide
    · right
      right
      right
      native_decide

end Omega.GroupUnification
