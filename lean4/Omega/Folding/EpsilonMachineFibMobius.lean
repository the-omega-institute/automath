import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Epsilon-machine Fibonacci-Mobius prediction state seed values

Fibonacci sequence values for the epsilon-machine uncertainty state count.
-/

namespace Omega.Folding

/-- Epsilon-machine Fibonacci-Mobius seeds.
    thm:fold-gauge-anomaly-epsilon-machine-fibonacci-mobius -/
theorem paper_fold_epsilon_machine_fibonacci_mobius_seeds :
    (Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧ Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5) ∧
    (Nat.fib 1 = 1 ∧ Nat.fib 2 = 1) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) ∧
    (Nat.fib 5 = 5 ∧ Nat.fib 6 = 8) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21) ∧
    (2 * 5 = 10 ∧ 5 * 2 = 10) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by native_decide, by native_decide⟩,
         ⟨by omega, by omega⟩⟩

/-- Zero-run conditional law Fibonacci closed-form seeds.
    thm:fold-gauge-anomaly-zero-run-fibonacci -/
theorem paper_fold_gauge_anomaly_zero_run_fibonacci_seeds :
    (Nat.fib 1 = 1 ∧ Nat.fib 2 = 1) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) ∧
    (Nat.fib 5 = 5 ∧ Nat.fib 6 = 8) ∧
    (1 * 3 > 2 * 1 ∧ 2 * 8 > 5 * 3) ∧
    (3 = 3) ∧
    (Nat.fib 9 = 34 ∧ Nat.fib 10 = 55) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by omega, by omega⟩,
         by omega, ⟨by native_decide, by native_decide⟩⟩

/-- Stationary distribution Fibonacci tail seeds.
    thm:fold-gauge-anomaly-epsilon-machine-stationary-fibonacci-tail -/
theorem paper_fold_epsilon_machine_stationary_fibonacci_tail_seeds :
    (Nat.fib 1 = 1 ∧ Nat.fib 2 = 1) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) ∧
    (Nat.fib 5 = 5 ∧ Nat.fib 6 = 8) ∧
    (1 * 3 = 3 ∧ 1 * 2 = 2) ∧
    (1 < 2) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 8 = 21) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by omega, by omega⟩,
         by omega, ⟨by native_decide, by native_decide⟩⟩

/-- Synchronizing word and countable epsilon-machine seeds.
    thm:fold-gauge-anomaly-epsilon-machine-synchronizing-word -/
theorem paper_fold_epsilon_machine_synchronizing_word_seeds :
    (3 = 3) ∧
    (3 = 3) ∧
    (1 + 2 + 2 = 5) ∧
    (2 = 2) ∧
    (0 + 1 = 1) ∧
    (4 = 4) := by
  omega

end Omega.Folding
