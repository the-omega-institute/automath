import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Zeta.LucasBarrier

/-- Lucas number: L(n) = F(n-1) + F(n+1). -/
def lucas (n : ℕ) : ℕ := Nat.fib (n - 1) + Nat.fib (n + 1)

/-- Fibonacci-Lucas multiplication identity seeds: F(2n) = F(n) · L(n).
    con:xi-fold-window6-lucas-barrier-collision-gap -/
theorem paper_zeta_lucas_barrier_seeds :
    (lucas 2 = 3) ∧ (lucas 3 = 4) ∧ (lucas 4 = 7) ∧
    (lucas 5 = 11) ∧ (lucas 6 = 18) ∧
    (Nat.fib 4 = Nat.fib 2 * lucas 2) ∧
    (Nat.fib 6 = Nat.fib 3 * lucas 3) ∧
    (Nat.fib 8 = Nat.fib 4 * lucas 4) ∧
    (Nat.fib 10 = Nat.fib 5 * lucas 5) ∧
    (Nat.fib 12 = Nat.fib 6 * lucas 6) ∧
    (Nat.fib 4 / Nat.fib 2 = lucas 2) ∧
    (Nat.fib 6 / Nat.fib 3 = lucas 3) ∧
    (Nat.fib 8 / Nat.fib 4 = lucas 4) := by
  unfold lucas
  norm_num [Nat.fib_add_two]

end Omega.Zeta.LucasBarrier
