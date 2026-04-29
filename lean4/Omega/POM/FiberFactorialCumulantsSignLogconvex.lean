import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-fiber-factorial-cumulants-sign-logconvex`. Positive finite
power-sums over a nonempty positive fiber are positive, and the power-sum sequence is
log-convex by finite Cauchy-Schwarz. -/
theorem paper_pom_fiber_factorial_cumulants_sign_logconvex {d : ℕ} (hd : 0 < d)
    (q : Fin d → ℝ) (hq : ∀ j, 0 < q j) :
    (∀ n : ℕ, 1 ≤ n → 0 < ∑ j : Fin d, q j ^ n) ∧
      (∀ n : ℕ, 2 ≤ n →
        (∑ j : Fin d, q j ^ n) ^ 2 ≤
          (∑ j : Fin d, q j ^ (n - 1)) * (∑ j : Fin d, q j ^ (n + 1))) := by
  classical
  constructor
  · intro n _hn
    refine Finset.sum_pos' ?_ ?_
    · intro j _hj
      exact le_of_lt (pow_pos (hq j) n)
    · refine ⟨⟨0, hd⟩, Finset.mem_univ _, ?_⟩
      exact pow_pos (hq ⟨0, hd⟩) n
  · intro n hn
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ)
      (r := fun j : Fin d => q j ^ n)
      (f := fun j : Fin d => q j ^ (n - 1))
      (g := fun j : Fin d => q j ^ (n + 1)) ?_ ?_ ?_
    · intro j _hj
      exact pow_nonneg (le_of_lt (hq j)) (n - 1)
    · intro j _hj
      exact pow_nonneg (le_of_lt (hq j)) (n + 1)
    · intro j _hj
      have hpow : n - 1 + (n + 1) = n + n := by omega
      calc
        (q j ^ n) ^ 2 = q j ^ (n + n) := by
          rw [pow_two, ← pow_add]
        _ = q j ^ (n - 1 + (n + 1)) := by
          rw [hpow]
        _ = q j ^ (n - 1) * q j ^ (n + 1) := by
          rw [pow_add]

end Omega.POM
