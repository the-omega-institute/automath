import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic
import Omega.Zeta.GmFibonacciModuliCofinal

namespace Omega.Conclusion

open scoped BigOperators

/-- The prefixed Fibonacci denominator product. -/
def conclusion_fibonacci_solenoid_dual_q_denominator (N : ℕ) : ℕ :=
  (Finset.range N).prod fun i => Nat.fib (i + 1)

/-- Paper label: `cor:conclusion-fibonacci-solenoid-dual-q`. -/
theorem paper_conclusion_fibonacci_solenoid_dual_q (p k : ℕ) (hp : Nat.Prime p) :
    ∃ N, p ^ k ∣ conclusion_fibonacci_solenoid_dual_q_denominator N := by
  have hpow_pos : 0 < p ^ k := pow_pos hp.pos k
  rcases Omega.Zeta.paper_gm_fibonacci_moduli_cofinal (p ^ k) hpow_pos with
    ⟨n, hn, hdiv⟩
  refine ⟨n, hdiv.trans ?_⟩
  have hmem : n - 1 ∈ Finset.range n := by
    rw [Finset.mem_range]
    omega
  have hfib_dvd :
      Nat.fib ((n - 1) + 1) ∣ conclusion_fibonacci_solenoid_dual_q_denominator n := by
    simpa [conclusion_fibonacci_solenoid_dual_q_denominator] using
      Finset.dvd_prod_of_mem (f := fun i => Nat.fib (i + 1)) hmem
  simpa [Nat.sub_add_cancel hn] using hfib_dvd

end Omega.Conclusion
