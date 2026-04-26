import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PrefixPrimeLedgerConservation
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_godel_logarithmic_dimension_tax_prod_fin_eq_firstPrimeProduct (T : ℕ) :
    (∏ t : Fin T, Omega.POM.nthPrime t) = Omega.POM.firstPrimeProduct T := by
  calc
    ∏ t : Fin T, Omega.POM.nthPrime t
      = ∏ x ∈ Finset.range T, if h : x < T then Omega.POM.nthPrime x else 1 := by
          simpa using (Finset.prod_fin_eq_prod_range (c := fun t : Fin T => Omega.POM.nthPrime t))
    _ = Omega.POM.firstPrimeProduct T := by
          rw [Omega.POM.firstPrimeProduct]
          refine Finset.prod_congr rfl ?_
          intro x hx
          simp [Finset.mem_range.mp hx]

/-- Paper label: `thm:conclusion-godel-logarithmic-dimension-tax`.
Bounding the exponent vector between the squarefree primorial and its `A`-fold thickening yields a
base-`2` logarithmic sandwich for the single Gödel integer; the existing primorial lower bound then
upgrades the lower side to the expected `T log T` scale. -/
theorem paper_conclusion_godel_logarithmic_dimension_tax
    (T A : ℕ) (hA : 1 ≤ A) (r : Fin T → ℕ)
    (hr_lower : ∀ t, 1 ≤ r t) (hr_upper : ∀ t, r t ≤ A) :
    let N : ℕ := ∏ t : Fin T, Omega.POM.nthPrime t ^ r t
    Omega.CircleDimension.realLog2 (Omega.POM.firstPrimeProduct T) ≤
        Omega.CircleDimension.realLog2 N ∧
      Omega.CircleDimension.realLog2 N ≤
        (A : ℝ) * Omega.CircleDimension.realLog2 (Omega.POM.firstPrimeProduct T) ∧
      (((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
            Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) / Real.log 2 ≤
        Omega.CircleDimension.realLog2 N) := by
  dsimp
  let N : ℕ := ∏ t : Fin T, Omega.POM.nthPrime t ^ r t
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfirst_pos_nat : 0 < Omega.POM.firstPrimeProduct T := Omega.POM.firstPrimeProduct_pos T
  have hfirst_pos : 0 < (Omega.POM.firstPrimeProduct T : ℝ) := by
    exact_mod_cast hfirst_pos_nat
  have hN_pos_nat : 0 < N := by
    refine Finset.prod_pos ?_
    intro t ht
    exact Nat.pow_pos (Omega.POM.nthPrime_prime t).pos
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN_pos_nat
  have hfirst_le_N_nat :
      Omega.POM.firstPrimeProduct T ≤ N := by
    have hprod_le :
        Finset.prod (Finset.univ : Finset (Fin T)) (fun t => Omega.POM.nthPrime t) ≤
          Finset.prod (Finset.univ : Finset (Fin T)) (fun t => Omega.POM.nthPrime t ^ r t) := by
      exact Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin T)))
        (f := fun t : Fin T => Omega.POM.nthPrime t)
        (g := fun t : Fin T => Omega.POM.nthPrime t ^ r t) (by
          intro t ht
          have hbase : 0 < Omega.POM.nthPrime t := (Omega.POM.nthPrime_prime t).pos
          have hpow : Omega.POM.nthPrime t ^ 1 ≤ Omega.POM.nthPrime t ^ r t :=
            Nat.pow_le_pow_right hbase (hr_lower t)
          simpa using hpow)
    simpa [Omega.POM.firstPrimeProduct,
      conclusion_godel_logarithmic_dimension_tax_prod_fin_eq_firstPrimeProduct] using hprod_le
  have hN_le_nat :
      N ≤ (Omega.POM.firstPrimeProduct T) ^ A := by
    have hprod_le :
        Finset.prod (Finset.univ : Finset (Fin T)) (fun t => Omega.POM.nthPrime t ^ r t) ≤
          Finset.prod (Finset.univ : Finset (Fin T)) (fun t => Omega.POM.nthPrime t ^ A) := by
      exact Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin T)))
        (f := fun t : Fin T => Omega.POM.nthPrime t ^ r t)
        (g := fun t : Fin T => Omega.POM.nthPrime t ^ A) (by
          intro t ht
          exact Nat.pow_le_pow_right (Omega.POM.nthPrime_prime t).pos (hr_upper t))
    calc
      N = ∏ t : Fin T, Omega.POM.nthPrime t ^ r t := rfl
      _ ≤ ∏ t : Fin T, Omega.POM.nthPrime t ^ A := hprod_le
      _ = (∏ t : Fin T, Omega.POM.nthPrime t) ^ A := by
            simpa using (Finset.prod_pow (s := (Finset.univ : Finset (Fin T))) (n := A)
              (f := fun t => Omega.POM.nthPrime t))
      _ = (Omega.POM.firstPrimeProduct T) ^ A := by
            rw [conclusion_godel_logarithmic_dimension_tax_prod_fin_eq_firstPrimeProduct]
  have hlog_lower :
      Real.log (Omega.POM.firstPrimeProduct T) ≤ Real.log N := by
    exact Real.log_le_log hfirst_pos (by exact_mod_cast hfirst_le_N_nat)
  have hlog_upper :
      Real.log N ≤ Real.log ((Omega.POM.firstPrimeProduct T : ℝ) ^ A) := by
    have hbound : (N : ℝ) ≤ (Omega.POM.firstPrimeProduct T : ℝ) ^ A := by
      exact_mod_cast hN_le_nat
    exact Real.log_le_log hN_pos hbound
  have hlog_upper' :
      Real.log ((Omega.POM.firstPrimeProduct T : ℝ) ^ A) =
        (A : ℝ) * Real.log (Omega.POM.firstPrimeProduct T) := by
    rw [← Real.rpow_natCast, Real.log_rpow hfirst_pos]
  have hrealLog2_lower :
      Omega.CircleDimension.realLog2 (Omega.POM.firstPrimeProduct T) ≤
        Omega.CircleDimension.realLog2 N := by
    unfold Omega.CircleDimension.realLog2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hlog_lower (by positivity)
  have hrealLog2_upper :
      Omega.CircleDimension.realLog2 N ≤
        (A : ℝ) * Omega.CircleDimension.realLog2 (Omega.POM.firstPrimeProduct T) := by
    unfold Omega.CircleDimension.realLog2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      Real.log N * (Real.log 2)⁻¹ ≤
          Real.log ((Omega.POM.firstPrimeProduct T : ℝ) ^ A) * (Real.log 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hlog_upper (by positivity)
      _ = (A : ℝ) * (Real.log (Omega.POM.firstPrimeProduct T) * (Real.log 2)⁻¹) := by
        rw [hlog_upper']
        ring
  have hq : ∀ i : Fin T, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair : Pairwise fun i j : Fin T => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
    intro i j hij
    refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
    intro hEq
    apply hij
    ext
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  have hstirling :
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (Omega.POM.firstPrimeProduct T) :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
      T 1 (fun i : Fin T => Omega.POM.nthPrime i) hq hpair).2.2
  have hstirling_log2 :
      (((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
            Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) / Real.log 2 ≤
        Omega.CircleDimension.realLog2 N) := by
    unfold Omega.CircleDimension.realLog2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_trans hstirling hlog_lower) (by positivity)
  exact ⟨hrealLog2_lower, hrealLog2_upper, hstirling_log2⟩

end Omega.Conclusion
