import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Folding

/-- Active coordinates of the Boolean support in the first `m` slots. -/
def activeSupport (b : ℕ → Bool) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => b i.1

/-- Number of active coordinates in the first `m` slots. -/
def activeCount (b : ℕ → Bool) (m : ℕ) : ℕ :=
  (activeSupport b m).card

/-- Prefix Gödel product using only the active coordinates. -/
def prefixGodelProduct (q : ℕ → ℕ) (b : ℕ → Bool) (m : ℕ) : ℕ :=
  (activeSupport b m).prod fun i => q i.1

/-- The global register family is pairwise coprime. -/
def PairwiseCoprimeRegister (q : ℕ → ℕ) : Prop :=
  Pairwise fun i j => Nat.Coprime (q i) (q j)

/-- Every register base is at least `2`. -/
def RegisterLowerBound (q : ℕ → ℕ) : Prop :=
  ∀ i, 2 ≤ q i

/-- Prime-register specialization. -/
def PrimeRegisterSpecialization (q : ℕ → ℕ) : Prop :=
  ∀ i, q i = Omega.POM.nthPrime i

/-- Concrete seed behind the coprime-inflation claim: for any active prefix, pairwise-coprime
registers dominate the primorial of the active support count; in the prime-register specialization,
the same active product is bounded above by the full primorial of the prefix length.
    thm:fold-gauge-anomaly-godel-coprime-inflation -/
def GodelCoprimeInflationSpec (q : ℕ → ℕ) (b : ℕ → Bool) (_α : ℝ) : Prop :=
  (PairwiseCoprimeRegister q ∧ RegisterLowerBound q →
      ∀ m, Omega.POM.firstPrimeProduct (activeCount b m) ≤ prefixGodelProduct q b m) ∧
    (PrimeRegisterSpecialization q →
      ∀ m, prefixGodelProduct q b m ≤ Omega.POM.firstPrimeProduct m)

private noncomputable def activeLedger (q : ℕ → ℕ) (b : ℕ → Bool) (m : ℕ) :
    Fin (activeCount b m) → ℕ :=
  fun i => q (((activeSupport b m).orderEmbOfFin rfl i).1)

private lemma ledgerProduct_activeLedger (q : ℕ → ℕ) (b : ℕ → Bool) (m : ℕ) :
    Omega.POM.ledgerProduct (activeLedger q b m) = prefixGodelProduct q b m := by
  classical
  simpa using
    (show Omega.POM.ledgerProduct (activeLedger q b m) = prefixGodelProduct q b m from by
      unfold Omega.POM.ledgerProduct activeLedger prefixGodelProduct activeCount
      simpa using
        (Finset.prod_image (s := (Finset.univ : Finset (Fin (activeSupport b m).card)))
          (g := (activeSupport b m).orderEmbOfFin rfl) (f := fun i : Fin m => q i.1)
          ((activeSupport b m).orderEmbOfFin rfl).injective.injOn).symm)

private lemma pairwise_activeLedger (q : ℕ → ℕ) (b : ℕ → Bool) (m : ℕ)
    (hpair : PairwiseCoprimeRegister q) :
    Pairwise fun i j => Nat.Coprime (activeLedger q b m i) (activeLedger q b m j) := by
  intro i j hij
  exact hpair (by
    intro hEq
    have himage :
        ((activeSupport b m).orderEmbOfFin rfl i) = ((activeSupport b m).orderEmbOfFin rfl j) :=
      Fin.ext hEq
    exact hij (((activeSupport b m).orderEmbOfFin rfl).injective himage))

private lemma lowerBound_activeLedger (q : ℕ → ℕ) (b : ℕ → Bool) (m : ℕ)
    (hq : RegisterLowerBound q) :
    ∀ i, 2 ≤ activeLedger q b m i := by
  intro i
  exact hq (((activeSupport b m).orderEmbOfFin rfl i).1)

private lemma firstPrimeProduct_le_prefixGodelProduct (q : ℕ → ℕ) (b : ℕ → Bool)
    (hpair : PairwiseCoprimeRegister q) (hq : RegisterLowerBound q) (m : ℕ) :
    Omega.POM.firstPrimeProduct (activeCount b m) ≤ prefixGodelProduct q b m := by
  have hbase :=
    (Omega.POM.paper_pom_coprime_ledger_primorial_optimality (activeCount b m) 0
      (activeLedger q b m) (lowerBound_activeLedger q b m hq)
      (pairwise_activeLedger q b m hpair)).2.1
  rw [ledgerProduct_activeLedger] at hbase
  exact hbase

private lemma prefixGodelProduct_le_firstPrimeProduct (q : ℕ → ℕ) (b : ℕ → Bool)
    (hqprime : PrimeRegisterSpecialization q) (m : ℕ) :
    prefixGodelProduct q b m ≤ Omega.POM.firstPrimeProduct m := by
  classical
  unfold prefixGodelProduct activeSupport
  have hsubset : Finset.filter (fun i : Fin m => b i.1) Finset.univ ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.filter_subset _ _
  have hle :
      (Finset.filter (fun i : Fin m => b i.1) Finset.univ).prod (fun i => q i.1) ≤
        Finset.univ.prod (fun i : Fin m => q i.1) := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hsubset ?_
    intro i _ _
    rw [hqprime i.1]
    exact Nat.succ_le_of_lt (Omega.POM.nthPrime_prime i.1).pos
  have hfull : Finset.univ.prod (fun i : Fin m => q i.1) = Omega.POM.firstPrimeProduct m := by
    calc
      Finset.univ.prod (fun i : Fin m => q i.1) =
          Finset.univ.prod (fun i : Fin m => Omega.POM.nthPrime i.1) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            exact hqprime i.1
      _ = Omega.POM.firstPrimeProduct m := by
        calc
          Finset.univ.prod (fun i : Fin m => Omega.POM.nthPrime i.1) =
              ∏ x ∈ Finset.range m, if h : x < m then Omega.POM.nthPrime x else 1 := by
                simpa using
                  (Finset.prod_fin_eq_prod_range (c := fun i : Fin m => Omega.POM.nthPrime i.1))
          _ = Omega.POM.firstPrimeProduct m := by
                rw [Omega.POM.firstPrimeProduct]
                refine Finset.prod_congr rfl ?_
                intro x hx
                simp [Finset.mem_range.mp hx]
  exact hle.trans (le_of_eq hfull)

theorem paper_fold_gauge_anomaly_godel_coprime_inflation
    (q : ℕ → ℕ) (b : ℕ → Bool) (α : ℝ) : GodelCoprimeInflationSpec q b α := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hpair, hq⟩ m
    exact firstPrimeProduct_le_prefixGodelProduct q b hpair hq m
  · intro hqprime m
    exact prefixGodelProduct_le_firstPrimeProduct q b hqprime m

end Omega.Folding
