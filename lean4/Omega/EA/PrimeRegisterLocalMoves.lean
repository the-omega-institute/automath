import Mathlib.Tactic
import Omega.EA.PrimeRegisterFibValuation

namespace Omega.EA.PrimeRegisterLocalMoves

open Omega.EA

/-- Base move: `single 0 2` and `single 1 1` have the same valuation
    (both equal `2 = 2·F_2 = 1·F_3`).
    prop:prime-register-local-moves-preserve-valuation -/
theorem base_move_preserves_valPr :
    valPr (Finsupp.single 0 2) = valPr (Finsupp.single 1 1) := by
  rw [valPr_single, valPr_single]
  decide

/-- Fibonacci recurrence move: `single (k+2) 1 ↔ single (k+1) 1 + single k 1`.
    prop:prime-register-local-moves-preserve-valuation -/
theorem fib_move_preserves_valPr (k : ℕ) :
    valPr (Finsupp.single (k + 2) 1) =
      valPr (Finsupp.single (k + 1) 1 + Finsupp.single k 1) := by
  rw [valPr_add, valPr_single, valPr_single, valPr_single]
  simp only [one_mul]
  -- Goal: fib (k + 2 + 2) = fib (k + 1 + 2) + fib (k + 2)
  -- i.e., fib (k + 4) = fib (k + 3) + fib (k + 2)
  have h : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
    Nat.fib_add_two (n := k + 2)
  have heq1 : k + 2 + 2 = k + 4 := by omega
  have heq2 : k + 1 + 2 = k + 3 := by omega
  rw [heq1, heq2, h]
  ring

/-- Paper package: local moves preserve prime register valuation.
    prop:prime-register-local-moves-preserve-valuation -/
theorem paper_prime_register_local_moves_preserve_valuation :
    valPr (Finsupp.single 0 2) = valPr (Finsupp.single 1 1) ∧
    (∀ k : ℕ, valPr (Finsupp.single (k + 2) 1) =
      valPr (Finsupp.single (k + 1) 1 + Finsupp.single k 1)) :=
  ⟨base_move_preserves_valPr, fib_move_preserves_valPr⟩

end Omega.EA.PrimeRegisterLocalMoves
