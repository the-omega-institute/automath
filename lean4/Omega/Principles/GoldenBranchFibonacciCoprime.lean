import Mathlib.Tactic

namespace Omega.Principles.GoldenBranchFibonacciCoprime

/-- Paper seed: consecutive terms of any Fibonacci-like sequence
    starting from `(1, 1)` are coprime.
    `cor:golden-branch-star-discrepancy-audit`. -/
theorem paper_golden_branch_fibonacci_coprime_seeds
    (q : ℕ → ℕ) (hq0 : q 0 = 1) (hq1 : q 1 = 1)
    (hrec : ∀ n, q (n + 2) = q (n + 1) + q n) :
    ∀ n, Nat.Coprime (q n) (q (n + 1)) := by
  intro n
  induction n with
  | zero =>
      simp [hq0, hq1]
  | succ k ih =>
      rw [hrec]
      have ih' : Nat.Coprime (q (k + 1)) (q k) := ih.symm
      simpa [add_comm] using (Nat.coprime_add_self_right.2 ih')

theorem paper_golden_branch_fibonacci_coprime_package
    (q : ℕ → ℕ) (hq0 : q 0 = 1) (hq1 : q 1 = 1)
    (hrec : ∀ n, q (n + 2) = q (n + 1) + q n) :
    ∀ n, Nat.Coprime (q n) (q (n + 1)) :=
  paper_golden_branch_fibonacci_coprime_seeds q hq0 hq1 hrec

end Omega.Principles.GoldenBranchFibonacciCoprime
