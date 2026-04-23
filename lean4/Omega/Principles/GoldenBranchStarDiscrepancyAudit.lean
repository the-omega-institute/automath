import Mathlib.Tactic
import Omega.Principles.GoldenBranchFibonacciCoprime

namespace Omega.Principles.GoldenBranchStarDiscrepancyAudit

theorem golden_branch_star_discrepancy_audit_fib_identification
    (q : ℕ → ℕ) (hq0 : q 0 = 1) (hq1 : q 1 = 1)
    (hrec : ∀ n, q (n + 2) = q (n + 1) + q n) :
    ∀ n, q n = Nat.fib (n + 1) := by
  intro n
  have hpair : ∀ k, q k = Nat.fib (k + 1) ∧ q (k + 1) = Nat.fib (k + 2) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa using hq0
        · simpa using hq1
    | succ k ih =>
        rcases ih with ⟨hk, hk1⟩
        constructor
        · exact hk1
        · rw [hrec]
          rw [hk1, hk]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := k + 1)).symm
  exact (hpair n).1

/-- Paper-facing wrapper around the Fibonacci identification and consecutive coprimality audit for
Fibonacci-style denominator sequences.
    cor:golden-branch-star-discrepancy-audit. -/
theorem paper_golden_branch_star_discrepancy_audit
    (q : ℕ → ℕ) (hq0 : q 0 = 1) (hq1 : q 1 = 1)
    (hrec : ∀ n, q (n + 2) = q (n + 1) + q n) :
    (∀ n, q n = Nat.fib (n + 1)) ∧ (∀ n, Nat.Coprime (q n) (q (n + 1))) := by
  refine ⟨golden_branch_star_discrepancy_audit_fib_identification q hq0 hq1 hrec, ?_⟩
  exact
    Omega.Principles.GoldenBranchFibonacciCoprime.paper_golden_branch_fibonacci_coprime_package
      q hq0 hq1 hrec

end Omega.Principles.GoldenBranchStarDiscrepancyAudit
