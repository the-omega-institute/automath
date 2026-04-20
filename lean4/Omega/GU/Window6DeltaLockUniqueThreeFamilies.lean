import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- Paper label: `cor:window6-delta-lock-unique-three-families`. -/
theorem paper_window6_delta_lock_unique_three_families (Nf : Nat)
    (hTop : Nat.fib 9 ≤ 15 * Nf ∧ 15 * Nf < Nat.fib 10) : Nf = 3 := by
  have hFib9 : Nat.fib 9 = 34 := by native_decide
  have hFib10 : Nat.fib 10 = 55 := by native_decide
  rw [hFib9, hFib10] at hTop
  omega

end Omega.GU
