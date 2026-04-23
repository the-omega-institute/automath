import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Zeta.GmFibonacciSubtowerEntrypointCriterion

namespace Omega.Zeta

theorem paper_gm_fibonacci_moduli_cofinal (m : ℕ) (hm : 1 ≤ m) : ∃ n ≥ 1, m ∣ Nat.fib n := by
  have hm' : 0 < m := hm
  refine ⟨gmFibonacciEntrypoint m, Nat.succ_le_of_lt (gmFibonacciEntrypoint_pos hm'), ?_⟩
  exact gmFibonacciEntrypoint_dvd_fib hm'

end Omega.Zeta
