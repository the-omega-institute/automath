import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-foldbin-audited-even-fibonacci-linear-low-budget-phase`. -/
theorem paper_xi_foldbin_audited_even_fibonacci_linear_low_budget_phase
    (B m : ℕ) (degeneracy : ℕ → ℕ)
    (hthreshold : ∀ x ∈ Finset.range (Nat.fib (m + 2)), 2 ^ B ≤ degeneracy x) :
    (∑ x ∈ Finset.range (Nat.fib (m + 2)), min (degeneracy x) (2 ^ B)) =
      Nat.fib (m + 2) * 2 ^ B := by
  calc
    (∑ x ∈ Finset.range (Nat.fib (m + 2)), min (degeneracy x) (2 ^ B))
        = ∑ x ∈ Finset.range (Nat.fib (m + 2)), 2 ^ B := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact Nat.min_eq_right (hthreshold x hx)
    _ = Nat.fib (m + 2) * 2 ^ B := by
          simp [Finset.card_range]

end Omega.Zeta
