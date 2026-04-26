import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Zeta

/-- The effective Lambert-`W` inversion proxy `A / (log A - log log A)`. -/
noncomputable def xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_proxy (A : ℝ) : ℝ :=
  A / (Real.log A - Real.log (Real.log A))

private theorem xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_primorial_log_lower
    (k : ℕ) :
    ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
        Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
      Real.log (Omega.POM.firstPrimeProduct k) := by
  have hq : ∀ i : Fin k, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair : Pairwise fun i j : Fin k => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
    intro i j hij
    refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
    intro hEq
    apply hij
    ext
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  exact (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
    k 1 (fun i : Fin k => Omega.POM.nthPrime i) hq hpair).2.2

/-- Paper label: `thm:xi-terminal-zm-cdim-prime-ledger-lambertw-lower-bound`.

The primorial lower bound reduces the auditable capacity requirement to the standard
`k log k`-scale inequality. Once the first-order Lambert-`W` denominator dominates `log (k + 1)`,
the explicit proxy `A / (log A - log log A)` is bounded above by `k + 1`. -/
theorem paper_xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound
    (r0 N : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hr0 : 0 < r0) (hN : 1 < N)
    (hCapacity :
      r0 * Real.log N ≤
        ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
          Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2))
    (hGrowth : r0 * Real.log N ≤ (k + 1 : ℝ) * Real.log (k + 1))
    (hLambert :
      Real.log (k + 1) ≤
        Real.log (r0 * Real.log N) - Real.log (Real.log (r0 * Real.log N))) :
    r0 * Real.log N ≤ Real.log (Omega.POM.firstPrimeProduct k) ∧
      xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_proxy (r0 * Real.log N) ≤ k + 1 := by
  have hPrimorial :=
    xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_primorial_log_lower k
  have hLedger : r0 * Real.log N ≤ Real.log (Omega.POM.firstPrimeProduct k) := by
    exact le_trans hCapacity hPrimorial
  have hLogN_pos : 0 < Real.log N := Real.log_pos hN
  have hA_nonneg : 0 ≤ r0 * Real.log N := by
    exact mul_nonneg hr0.le hLogN_pos.le
  have hk_cast : (2 : ℝ) ≤ k + 1 := by
    exact_mod_cast Nat.succ_le_succ hk
  have hLogk_pos : 0 < Real.log (k + 1) := by
    apply Real.log_pos
    linarith
  have hDen_pos :
      0 < Real.log (r0 * Real.log N) - Real.log (Real.log (r0 * Real.log N)) := by
    exact lt_of_lt_of_le hLogk_pos hLambert
  have hProxy_le_log :
      xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_proxy (r0 * Real.log N) ≤
        (r0 * Real.log N) / Real.log (k + 1) := by
    unfold xi_terminal_zm_cdim_prime_ledger_lambertw_lower_bound_proxy
    exact div_le_div_of_nonneg_left hA_nonneg hLogk_pos hLambert
  have hLogBound :
      (r0 * Real.log N) / Real.log (k + 1) ≤ k + 1 := by
    rw [div_le_iff₀ hLogk_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hGrowth
  exact ⟨hLedger, le_trans hProxy_le_log hLogBound⟩

end Omega.Zeta
