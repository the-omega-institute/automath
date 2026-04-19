import Mathlib
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Conclusion

open scoped BigOperators Nat.Prime

/-- The quadratic relaxation-time lower bound coming from the lazy walk on `ℤ/pℤ`. -/
noncomputable def primeRegisterLazyCycleRelaxationTime (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 / 4

/-- In a strictly increasing prime-modulus register, the slowest coordinate is the last one. -/
noncomputable def primeRegisterWorstPrimeModulus {T : ℕ} (q : Fin T → ℕ) (hT : 1 ≤ T) : ℕ :=
  q ⟨T - 1, Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 1) hT) (by decide : 0 < 1)⟩

private lemma nthPrime_le_of_strictMonoPrime {T : ℕ} (q : Fin T → ℕ)
    (hprime : ∀ i, Nat.Prime (q i))
    (hmono : StrictMono q)
    (n : ℕ) (hn : n < T) :
    Omega.POM.nthPrime n ≤ q ⟨n, hn⟩ := by
  have hrec :
      ∀ m, ∀ hm : m < T, Omega.POM.nthPrime m ≤ q ⟨m, hm⟩ := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hm
    have hleast :=
      Nat.isLeast_nth_of_infinite (p := Nat.Prime) Nat.infinite_setOf_prime m
    apply hleast.2
    constructor
    · exact hprime ⟨m, hm⟩
    · intro k hk
      have hkT : k < T := lt_trans hk hm
      have hprev : Omega.POM.nthPrime k ≤ q ⟨k, hkT⟩ := ih k hk hkT
      have hlt : q ⟨k, hkT⟩ < q ⟨m, hm⟩ := hmono hk
      exact lt_of_le_of_lt hprev hlt
  exact hrec n hn

private lemma firstPrimeProduct_le_prod_of_strictMonoPrime {T : ℕ} (q : Fin T → ℕ)
    (hprime : ∀ i, Nat.Prime (q i))
    (hmono : StrictMono q) :
    Omega.POM.firstPrimeProduct T ≤ ∏ i, q i := by
  have hsortedRange :
      Omega.POM.firstPrimeProduct T ≤
        ∏ i ∈ Finset.range T, if h : i < T then q ⟨i, h⟩ else 1 := by
    exact Finset.prod_le_prod' (s := Finset.range T)
      (f := fun i => Omega.POM.nthPrime i)
      (g := fun i => if h : i < T then q ⟨i, h⟩ else 1)
      (by
        intro i hi
        simp [Finset.mem_range.mp hi, nthPrime_le_of_strictMonoPrime q hprime hmono i
          (Finset.mem_range.mp hi)])
  have hsortedEq :
      (∏ i ∈ Finset.range T, if h : i < T then q ⟨i, h⟩ else 1) = ∏ i : Fin T, q i :=
    (Finset.prod_fin_eq_prod_range (c := q)).symm
  exact hsortedEq ▸ hsortedRange

set_option maxHeartbeats 400000 in
/-- Among strictly increasing prime moduli, the initial segment of primes minimizes the worst
modulus. Therefore any register whose total modulus product clears a primorial threshold `B`
inherits the quadratic mixing lower bound coming from the slowest cyclic coordinate.
`thm:conclusion-prime-register-worst-modulus-mixing-lower-bound` -/
theorem paper_conclusion_prime_register_worst_modulus_mixing_lower_bound
    (B T : ℕ) (hT : 1 ≤ T) (q : Fin T → ℕ)
    (hprime : ∀ i, Nat.Prime (q i))
    (hmono : StrictMono q)
    (hBudget : B ≤ Omega.POM.firstPrimeProduct T) :
    B ≤ ∏ i, q i ∧
      primeRegisterLazyCycleRelaxationTime (Omega.POM.nthPrime (T - 1)) ≤
        primeRegisterLazyCycleRelaxationTime (primeRegisterWorstPrimeModulus q hT) := by
  have hprod : Omega.POM.firstPrimeProduct T ≤ ∏ i, q i :=
    firstPrimeProduct_le_prod_of_strictMonoPrime q hprime hmono
  have hlast : T - 1 < T := Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 1) hT) (by decide : 0 < 1)
  have hworst :
      Omega.POM.nthPrime (T - 1) ≤ primeRegisterWorstPrimeModulus q hT := by
    simpa [primeRegisterWorstPrimeModulus] using
      nthPrime_le_of_strictMonoPrime q hprime hmono (T - 1) hlast
  have hworst_sq :
      ((Omega.POM.nthPrime (T - 1) : ℝ) ^ 2) ≤
        ((primeRegisterWorstPrimeModulus q hT : ℝ) ^ 2) := by
    have hworst_real :
        (Omega.POM.nthPrime (T - 1) : ℝ) ≤ (primeRegisterWorstPrimeModulus q hT : ℝ) := by
      exact_mod_cast hworst
    nlinarith
  refine ⟨le_trans hBudget hprod, ?_⟩
  unfold primeRegisterLazyCycleRelaxationTime
  have hfour : (0 : ℝ) ≤ 4 := by norm_num
  exact div_le_div_of_nonneg_right hworst_sq hfour

end Omega.Conclusion
