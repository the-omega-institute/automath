import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality
import Omega.POM.PrimeDeterminantAbelianizationFactorization

namespace Omega.POM

/-- Paper label: `thm:pom-faithful-2x2-geometric-primorial-area-law`.
Taking the word that uses each generator once, the determinant area is `π` times the ledger
product, and the existing primorial theorem supplies the logarithmic lower bound. -/
theorem paper_pom_faithful_2x2_geometric_primorial_area_law {T N : ℕ} (p : Fin T → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hpinj : Function.Injective p) (hN : 1 ≤ N)
    (hbound : ∀ i, p i < N) :
    ∃ w : List (Fin T),
      w.length = T ∧
        Real.log (primeDetArea p w) ≥ Real.log Real.pi + Real.log (firstPrimeProduct T) := by
  have _hencoding := paper_pom_prime_determinant_2x2_free_encoding p hprime hN hbound
  have _hfactorization := paper_pom_prime_determinant_abelianization_factorization p hprime hN hbound
  let w : List (Fin T) := List.finRange T
  refine ⟨w, by simp [w], ?_⟩
  have hq : ∀ i, 2 ≤ p i := fun i => (hprime i).two_le
  have hpair : Pairwise fun i j => Nat.Coprime (p i) (p j) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).2 fun hij' => hij (hpinj hij')
  have hprimorial :
      Real.log (firstPrimeProduct T) ≤ Real.log (ledgerProduct p) := by
    simpa using (paper_pom_coprime_ledger_primorial_optimality T 1 p hq hpair).1
  have hledger_pos : 0 < (ledgerProduct p : ℝ) := by
    exact_mod_cast ledgerProduct_pos p hq
  have harea :
      primeDetArea p w = Real.pi * ledgerProduct p := by
    unfold primeDetArea w
    rw [parikhPrimeProduct_eq_list_prod]
    simpa [Function.comp, ledgerProduct] using (Fin.prod_univ_def fun i => (p i : ℝ)).symm
  calc
    Real.log (primeDetArea p w) = Real.log Real.pi + Real.log (ledgerProduct p) := by
      rw [harea, Real.log_mul Real.pi_ne_zero hledger_pos.ne']
    _ ≥ Real.log Real.pi + Real.log (firstPrimeProduct T) := by
      linarith

end Omega.POM
