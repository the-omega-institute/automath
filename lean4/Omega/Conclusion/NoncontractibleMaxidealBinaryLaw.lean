import Mathlib.Tactic
import Omega.Core.Fib
import Omega.POM.MaxNoncontractibleFiberMod6Phase

namespace Omega.Conclusion

/-- Concrete token for the noncontractible maximal-ideal binary law. -/
abbrev conclusion_noncontractible_maxideal_binary_law_data :=
  Unit

namespace conclusion_noncontractible_maxideal_binary_law_data

/-- The binary Fibonacci parity bit attached to the maximal block. -/
def conclusion_noncontractible_maxideal_binary_law_fibonacciBit
    (_D : conclusion_noncontractible_maxideal_binary_law_data) (m : ℕ) : ℕ :=
  Nat.fib (m + 2) % 2

/-- The two residue classes on which the Fibonacci parity bit vanishes. -/
def conclusion_noncontractible_maxideal_binary_law_zeroBitPhase
    (_D : conclusion_noncontractible_maxideal_binary_law_data) (m : ℕ) : Prop :=
  m % 6 = 1 ∨ m % 6 = 4

/-- Paper-facing concrete statement: the maximal-block phase split is the audited `m mod 6`
noncontractible fiber formula, and its binary parity bit is the period-three Fibonacci pattern
read on the same six residues. -/
def conclusion_noncontractible_maxideal_binary_law_statement
    (D : conclusion_noncontractible_maxideal_binary_law_data) : Prop :=
  (∀ m : ℕ,
      17 ≤ m →
        (m % 6 = 0 ∨ m % 6 = 4) →
          noncontractibleFiberCount m = noncontractibleMainFiberCount m) ∧
    (∀ m : ℕ,
      17 ≤ m →
        (m % 6 = 1 ∨ m % 6 = 5) →
          noncontractibleFiberCount m = noncontractibleSecondFiberCount m) ∧
      (∀ m : ℕ,
        17 ≤ m →
          (m % 6 = 2 ∨ m % 6 = 3) →
            noncontractibleFiberCount m = noncontractibleThirdFiberCount m) ∧
        (∀ m : ℕ,
          D.conclusion_noncontractible_maxideal_binary_law_fibonacciBit m = 0 ↔
            D.conclusion_noncontractible_maxideal_binary_law_zeroBitPhase m)

end conclusion_noncontractible_maxideal_binary_law_data

/-- Paper label: `thm:conclusion-noncontractible-maxideal-binary-law`. -/
theorem paper_conclusion_noncontractible_maxideal_binary_law
    (D : ℕ → ℕ) (retained : ℕ → Prop)
    (hEven : ∀ k : ℕ, D (2 * k) = Nat.fib (k + 2))
    (hOdd : ∀ k : ℕ, D (2 * k + 1) = 2 * Nat.fib (k + 1))
    (hRetained : ∀ m : ℕ, retained m ↔ Odd (D m)) :
    (∀ k : ℕ, retained (6 * k) ∧ retained (6 * k + 4)) ∧
      (∀ k : ℕ, ¬ retained (6 * k + 1) ∧ ¬ retained (6 * k + 2) ∧
        ¬ retained (6 * k + 3) ∧ ¬ retained (6 * k + 5)) := by
  have fib_odd_of_mod_ne_zero :
      ∀ n : ℕ, n % 3 ≠ 0 → Odd (Nat.fib n) := by
    intro n hn
    rw [Nat.odd_iff, Omega.fib_mod_two_period n]
    have hlt : n % 3 < 3 := Nat.mod_lt n (by omega)
    interval_cases h : n % 3
    · exact False.elim (hn rfl)
    · simp [Nat.fib]
    · simp [Nat.fib]
  have fib_not_odd_of_mod_zero :
      ∀ n : ℕ, n % 3 = 0 → ¬ Odd (Nat.fib n) := by
    intro n hn
    rw [Nat.not_odd_iff, Omega.fib_mod_two_period n]
    simp [hn, Nat.fib]
  have two_mul_fib_not_odd : ∀ n : ℕ, ¬ Odd (2 * Nat.fib n) := by
    intro n
    rw [Nat.not_odd_iff]
    omega
  refine ⟨?_, ?_⟩
  · intro k
    constructor
    · rw [hRetained, show 6 * k = 2 * (3 * k) by ring, hEven]
      exact fib_odd_of_mod_ne_zero (3 * k + 2) (by omega)
    · rw [hRetained, show 6 * k + 4 = 2 * (3 * k + 2) by ring, hEven]
      exact fib_odd_of_mod_ne_zero (3 * k + 4) (by omega)
  · intro k
    constructor
    · rw [hRetained, show 6 * k + 1 = 2 * (3 * k) + 1 by ring, hOdd]
      exact two_mul_fib_not_odd (3 * k + 1)
    constructor
    · rw [hRetained, show 6 * k + 2 = 2 * (3 * k + 1) by ring, hEven]
      exact fib_not_odd_of_mod_zero (3 * k + 3) (by omega)
    constructor
    · rw [hRetained, show 6 * k + 3 = 2 * (3 * k + 1) + 1 by ring, hOdd]
      exact two_mul_fib_not_odd (3 * k + 2)
    · rw [hRetained, show 6 * k + 5 = 2 * (3 * k + 2) + 1 by ring, hOdd]
      exact two_mul_fib_not_odd (3 * k + 3)

end Omega.Conclusion
