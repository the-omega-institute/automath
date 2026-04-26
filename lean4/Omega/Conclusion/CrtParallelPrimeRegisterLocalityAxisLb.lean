import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-crt-parallel-prime-register-locality-axis-lb`.
If a local prime-register architecture with `T` active axes and uniform depth cap `M` covers a
budget `B`, then the logarithmic budget is bounded by the `M`-fold primorial log, and the standard
primorial lower bound supplies the corresponding axis-growth obstruction. -/
theorem paper_conclusion_crt_parallel_prime_register_locality_axis_lb
    (B T M : ℕ) (hB : 1 ≤ B) (_hM : 1 ≤ M)
    (hBudget : B ≤ Omega.POM.firstPrimeProduct T ^ M) :
    Real.log B ≤ (M : ℝ) * Real.log (Omega.POM.firstPrimeProduct T) ∧
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (Omega.POM.firstPrimeProduct T)) := by
  have hB_pos : 0 < (B : ℝ) := by
    exact_mod_cast hB
  have hbudget_real : (B : ℝ) ≤ ((Omega.POM.firstPrimeProduct T ^ M : ℕ) : ℝ) := by
    exact_mod_cast hBudget
  have hprod_pos_nat : 0 < Omega.POM.firstPrimeProduct T := Omega.POM.firstPrimeProduct_pos T
  have hprod_pos : 0 < (Omega.POM.firstPrimeProduct T : ℝ) := by
    exact_mod_cast hprod_pos_nat
  have hlog_budget :
      Real.log B ≤ (M : ℝ) * Real.log (Omega.POM.firstPrimeProduct T) := by
    calc
      Real.log B ≤ Real.log (((Omega.POM.firstPrimeProduct T) ^ M : ℕ) : ℝ) :=
        Real.log_le_log hB_pos hbudget_real
      _ = (M : ℝ) * Real.log (Omega.POM.firstPrimeProduct T) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, Real.log_rpow hprod_pos]
  have hq : ∀ i : Fin T, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair :
      Pairwise fun i j : Fin T => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
    intro i j hij
    refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
    intro hEq
    apply hij
    ext
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  have hprimorial :
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (Omega.POM.firstPrimeProduct T)) :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
      T 1 (fun i : Fin T => Omega.POM.nthPrime i) hq hpair).2.2
  exact ⟨hlog_budget, hprimorial⟩

end Omega.Conclusion
