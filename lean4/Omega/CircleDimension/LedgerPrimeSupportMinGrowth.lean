import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.CircleDimension.AddressLedgerJointBudgetLowerBound
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.CircleDimension

private lemma log_two_pow_mul_firstPrimeProduct
    (b k : ℕ) :
    Real.log ((((2 ^ b) * Omega.POM.firstPrimeProduct k : ℕ) : ℝ)) =
      (b : ℝ) * Real.log 2 + Real.log (Omega.POM.firstPrimeProduct k) := by
  have hpow_ne : ((2 : ℝ) ^ b) ≠ 0 := by positivity
  have hprod_ne : (Omega.POM.firstPrimeProduct k : ℝ) ≠ 0 := by
    exact_mod_cast (Omega.POM.firstPrimeProduct_pos k).ne'
  calc
    Real.log ((((2 ^ b) * Omega.POM.firstPrimeProduct k : ℕ) : ℝ))
      = Real.log (((2 : ℝ) ^ b) * (Omega.POM.firstPrimeProduct k : ℝ)) := by norm_num
    _ = Real.log ((2 : ℝ) ^ b) + Real.log (Omega.POM.firstPrimeProduct k) := by
          rw [Real.log_mul hpow_ne hprod_ne]
  have hpow_log : Real.log ((2 : ℝ) ^ b) = (b : ℝ) * Real.log 2 := by
    rw [← Real.rpow_natCast, Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
  simp [hpow_log]

/-- Paper-facing minimum-growth package for a squarefree prime ledger: the joint address/ledger
budget gives the logarithmic lower bound for the ledger size, and the primorial theorem supplies
the squarefree support-growth lower bound.
    cor:cdim-ledger-prime-support-min-growth -/
theorem paper_cdim_ledger_prime_support_min_growth
    (b heavy k : ℕ) (hheavy : 1 ≤ heavy)
    {Γ R : Type*} [Fintype Γ] [Fintype R]
    (A : Γ → Fin (2 ^ b)) (r : Γ → R)
    (hBucket : ∃ a : Fin (2 ^ b), heavy ≤ Fintype.card {γ // A γ = a})
    (hInj : Function.Injective fun γ => (A γ, r γ))
    (hR : Fintype.card R = Omega.POM.firstPrimeProduct k) :
    Real.log (heavy : ℝ) ≤
        (b : ℝ) * Real.log 2 + Real.log (Omega.POM.firstPrimeProduct k) ∧
      ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
          Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (Omega.POM.firstPrimeProduct k)) := by
  have hbudget : heavy ≤ 2 ^ b * Omega.POM.firstPrimeProduct k := by
    rw [← hR]
    exact paper_cdim_address_ledger_joint_budget_lower_bound b heavy A r hBucket hInj
  have hheavy_pos : 0 < (heavy : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hheavy)
  have hbudget_real :
      (heavy : ℝ) ≤ (((2 ^ b) * Omega.POM.firstPrimeProduct k : ℕ) : ℝ) := by
    exact_mod_cast hbudget
  have hlog_budget :
      Real.log (heavy : ℝ) ≤
        Real.log ((((2 ^ b) * Omega.POM.firstPrimeProduct k : ℕ) : ℝ)) := by
    exact Real.log_le_log hheavy_pos hbudget_real
  have hq : ∀ i : Fin k, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair :
      Pairwise fun i j : Fin k => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
    intro i j hij
    refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
    intro hEq
    apply hij
    ext
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  have hprimorial :
      ((k + 1 : ℝ) * Real.log (k + 1) - (k + 1) +
          Real.log (k + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (Omega.POM.firstPrimeProduct k) :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
      k 1 (fun i : Fin k => Omega.POM.nthPrime i) hq hpair).2.2
  refine ⟨?_, hprimorial⟩
  calc
    Real.log (heavy : ℝ)
      ≤ Real.log ((((2 ^ b) * Omega.POM.firstPrimeProduct k : ℕ) : ℝ)) := hlog_budget
    _ = (b : ℝ) * Real.log 2 + Real.log (Omega.POM.firstPrimeProduct k) :=
      log_two_pow_mul_firstPrimeProduct b k

end Omega.CircleDimension
