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

open conclusion_noncontractible_maxideal_binary_law_data

/-- Paper label: `thm:conclusion-noncontractible-maxideal-binary-law`. -/
theorem paper_conclusion_noncontractible_maxideal_binary_law
    (D : conclusion_noncontractible_maxideal_binary_law_data) :
    D.conclusion_noncontractible_maxideal_binary_law_statement := by
  rcases Omega.POM.paper_pom_max_noncontractible_fiber_mod6_phase with
    ⟨hMain, hSecond, hThird⟩
  refine ⟨hMain, hSecond, hThird, ?_⟩
  intro m
  have hm_lt : m % 6 < 6 := Nat.mod_lt m (by decide)
  interval_cases hm : m % 6
  · have hfib : (m + 2) % 3 = 2 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]
  · have hfib : (m + 2) % 3 = 0 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]
  · have hfib : (m + 2) % 3 = 1 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]
  · have hfib : (m + 2) % 3 = 2 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]
  · have hfib : (m + 2) % 3 = 0 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]
  · have hfib : (m + 2) % 3 = 1 := by omega
    rw [conclusion_noncontractible_maxideal_binary_law_fibonacciBit, Omega.fib_mod_two_period,
      hfib]
    simp [conclusion_noncontractible_maxideal_binary_law_zeroBitPhase, hm]

end Omega.Conclusion
