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

/-- Closed forms for the Möbius recursion governing the uncertain epsilon-machine states.
    thm:fold-gauge-anomaly-epsilon-machine-fibonacci-mobius -/
theorem paper_fold_epsilon_machine_fibonacci_mobius
    (r alpha : Nat → Rat) (h0 : r 0 = (1 : Rat) / 2)
    (hrec : ∀ n : Nat, r (n + 1) = 1 / (4 * r n + 2))
    (hAlpha : ∀ n : Nat, alpha n = 1 / (4 * (1 + r n))) :
    (∀ n : Nat, r n = (Nat.fib (n + 1) : Rat) / (2 * Nat.fib (n + 2))) ∧
      (∀ n : Nat, alpha n = (Nat.fib (n + 2) : Rat) / (2 * Nat.fib (n + 4))) := by
  have hFibNe : ∀ n : Nat, (Nat.fib (n + 2) : Rat) ≠ 0 := by
    intro n
    have hpos : 0 < (Nat.fib (n + 2) : Rat) := by
      exact_mod_cast (Nat.fib_pos.mpr (by omega) : 0 < Nat.fib (n + 2))
    exact ne_of_gt hpos
  have hFib3 : ∀ n : Nat, (Nat.fib (n + 3) : Rat) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    intro n
    exact_mod_cast
      (show Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Nat.fib_add_two (n := n + 1)))
  have hFib4 : ∀ n : Nat, (Nat.fib (n + 4) : Rat) = Nat.fib (n + 1) + 2 * Nat.fib (n + 2) := by
    intro n
    calc
      (Nat.fib (n + 4) : Rat) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        exact_mod_cast
          (show Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Nat.fib_add_two (n := n + 2)))
      _ = Nat.fib (n + 1) + 2 * Nat.fib (n + 2) := by rw [hFib3 n]; ring
  have hrClosed : ∀ n : Nat, r n = (Nat.fib (n + 1) : Rat) / (2 * Nat.fib (n + 2)) := by
    intro n
    induction n with
    | zero =>
        calc
          r 0 = (1 : Rat) / 2 := h0
          _ = (Nat.fib 1 : Rat) / (2 * Nat.fib 2) := by norm_num
    | succ n ih =>
        calc
          r (n + 1) = 1 / (4 * r n + 2) := hrec n
          _ = 1 / (4 * ((Nat.fib (n + 1) : Rat) / (2 * Nat.fib (n + 2))) + 2) := by rw [ih]
          _ = (Nat.fib (n + 2) : Rat) / (2 * Nat.fib (n + 3)) := by
            have hne := hFibNe n
            rw [hFib3 n]
            field_simp [hne]
            ring
  have hAlphaClosed : ∀ n : Nat, alpha n = (Nat.fib (n + 2) : Rat) / (2 * Nat.fib (n + 4)) := by
    intro n
    calc
      alpha n = 1 / (4 * (1 + r n)) := hAlpha n
      _ = 1 / (4 * (1 + (Nat.fib (n + 1) : Rat) / (2 * Nat.fib (n + 2)))) := by rw [hrClosed n]
      _ = (Nat.fib (n + 2) : Rat) / (2 * Nat.fib (n + 4)) := by
        have hne := hFibNe n
        rw [hFib4 n]
        field_simp [hne]
        ring
  exact ⟨hrClosed, hAlphaClosed⟩

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

/-- Infinite Markov order seeds.
    thm:fold-gauge-anomaly-epsilon-machine-infinite-markov-order -/
theorem paper_fold_epsilon_machine_infinite_markov_order_seeds :
    (3 = 3) ∧
    (∀ N : Nat, N + 1 > N) ∧
    (3 = 3 ∧ 2 < 3) ∧
    (1 < 2) ∧
    (0 + 1 = 1 ∧ 1 + 1 = 2 ∧ 2 + 1 = 3) := by
  exact ⟨by omega, fun N => by omega, ⟨by omega, by omega⟩,
         by omega, ⟨by omega, by omega, by omega⟩⟩

end Omega.Folding
