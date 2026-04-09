import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- `F_2 = 1`.
    cor:window6-double-lock-12 -/
theorem fib_two_eq_one : Nat.fib 2 = 1 := by decide

/-- `F_4 = 3`.
    cor:window6-double-lock-12 -/
theorem fib_four_eq_three : Nat.fib 4 = 3 := by decide

/-- `F_6 = 8`.
    cor:window6-double-lock-12 -/
theorem fib_six_eq_eight : Nat.fib 6 = 8 := by decide

/-- Boundary-tower sum `F_2 + F_4 + F_6 = 12`.
    cor:window6-double-lock-12 -/
theorem boundary_tower_sum : Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 := by
  rw [fib_two_eq_one, fib_four_eq_three, fib_six_eq_eight]

/-- Rigidity-sector recombination `8 + 4 = 12`.
    cor:window6-double-lock-12 -/
theorem rigidity_sector_sum : (8 + 4 : ℕ) = 12 := by decide

/-- Paper package: window-6 numerical 12 double-lock.
    cor:window6-double-lock-12 -/
theorem paper_window6_double_lock_12 :
    Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 ∧
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    (8 + 4 : ℕ) = 12 ∧
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = (8 + 4 : ℕ) := by
  refine ⟨fib_two_eq_one, fib_four_eq_three, fib_six_eq_eight,
          boundary_tower_sum, rigidity_sector_sum, ?_⟩
  rw [boundary_tower_sum, rigidity_sector_sum]

end Omega.GU
