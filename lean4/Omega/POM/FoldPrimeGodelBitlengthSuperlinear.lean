import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.GodelCoprimeInflation
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.POM

open Omega.Folding

/-- The replay Gödel code in the full prime-register specialization, where every coordinate in the
prefix is active. -/
noncomputable def foldPrimeReplayGodelCode (m : ℕ) : ℕ :=
  prefixGodelProduct Omega.POM.nthPrime (fun _ => true) m

private lemma nthPrime_pairwise :
    Pairwise fun i j : ℕ => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
  intro i j hij
  refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
  intro hij'
  exact hij ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij')

private lemma foldPrimeReplayGodelCode_eq_firstPrimeProduct (m : ℕ) :
    foldPrimeReplayGodelCode m = Omega.POM.firstPrimeProduct m := by
  unfold foldPrimeReplayGodelCode Omega.Folding.prefixGodelProduct Omega.Folding.activeSupport
  simp only [Finset.filter_true]
  calc
    ∏ i : Fin m, Omega.POM.nthPrime i
      = ∏ x ∈ Finset.range m, if h : x < m then Omega.POM.nthPrime x else 1 := by
          simpa using
            (Finset.prod_fin_eq_prod_range (c := fun i : Fin m => Omega.POM.nthPrime i))
    _ = Omega.POM.firstPrimeProduct m := by
          rw [Omega.POM.firstPrimeProduct]
          refine Finset.prod_congr rfl ?_
          intro x hx
          simp [Finset.mem_range.mp hx]

/-- Paper label: `thm:pom-fold-prime-godel-bitlength-superlinear`.
In the full prime-register replay model the Gödel code dominates the primorial pointwise, and the
existing primorial estimate upgrades this to the expected `m log m`-scale lower bound. -/
theorem paper_pom_fold_prime_godel_bitlength_superlinear (m : ℕ) :
    Omega.POM.firstPrimeProduct m ≤ foldPrimeReplayGodelCode m ∧
      Real.log (Omega.POM.firstPrimeProduct m) ≤ Real.log (foldPrimeReplayGodelCode m) ∧
      ((m + 1 : ℝ) * Real.log (m + 1) - (m + 1) +
          Real.log (m + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (foldPrimeReplayGodelCode m)) := by
  have hEq : foldPrimeReplayGodelCode m = Omega.POM.firstPrimeProduct m :=
    foldPrimeReplayGodelCode_eq_firstPrimeProduct m
  have hStirling :
      ((m + 1 : ℝ) * Real.log (m + 1) - (m + 1) +
          Real.log (m + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (Omega.POM.firstPrimeProduct m) :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
      m 1 (fun i : Fin m => Omega.POM.nthPrime i)
      (fun i => (Omega.POM.nthPrime_prime i).two_le)
      (by
        intro i j hij
        exact nthPrime_pairwise (fun h => hij (Fin.ext h)))).2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq]
  · simpa [hEq]
  · simpa [hEq] using hStirling

end Omega.POM
