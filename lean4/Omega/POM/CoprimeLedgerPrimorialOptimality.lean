import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators Nat.Prime

/-- The `n`-th prime, indexed from `0`. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Product of the first `T` primes. -/
noncomputable def firstPrimeProduct (T : ℕ) : ℕ :=
  ∏ i ∈ Finset.range T, nthPrime i

/-- Total ledger base product. -/
noncomputable def ledgerProduct {T : ℕ} (q : Fin T → ℕ) : ℕ :=
  ∏ i, q i

/-- The chosen prime divisor of a ledger base, implemented by `Nat.minFac`. -/
noncomputable def chosenPrimeDivisor {T : ℕ} (q : Fin T → ℕ) (i : Fin T) : ℕ :=
  Nat.minFac (q i)

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) := by
  simpa [nthPrime] using Nat.prime_nth_prime n

lemma firstPrimeProduct_pos (T : ℕ) : 0 < firstPrimeProduct T := by
  refine Finset.prod_pos ?_
  intro i hi
  exact (nthPrime_prime i).pos

lemma ledgerProduct_pos {T : ℕ} (q : Fin T → ℕ) (hq : ∀ i, 2 ≤ q i) : 0 < ledgerProduct q := by
  refine Finset.prod_pos ?_
  intro i hi
  exact lt_of_lt_of_le (by decide : 0 < 2) (hq i)

lemma chosenPrimeDivisor_prime {T : ℕ} (q : Fin T → ℕ) (hq : ∀ i, 2 ≤ q i) (i : Fin T) :
    Nat.Prime (chosenPrimeDivisor q i) := by
  simpa [chosenPrimeDivisor] using Nat.minFac_prime (ne_of_gt (lt_of_lt_of_le (by decide) (hq i)))

lemma chosenPrimeDivisor_dvd {T : ℕ} (q : Fin T → ℕ) (i : Fin T) :
    chosenPrimeDivisor q i ∣ q i := by
  simpa [chosenPrimeDivisor] using Nat.minFac_dvd (q i)

lemma chosenPrimeDivisor_le {T : ℕ} (q : Fin T → ℕ) (hq : ∀ i, 2 ≤ q i) (i : Fin T) :
    chosenPrimeDivisor q i ≤ q i := by
  exact Nat.le_of_dvd (lt_of_lt_of_le (by decide : 0 < 2) (hq i)) (chosenPrimeDivisor_dvd q i)

lemma chosenPrimeDivisor_injective {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    Function.Injective (chosenPrimeDivisor q) := by
  intro i j hij
  by_contra hne
  have hcop :
      Nat.Coprime (chosenPrimeDivisor q i) (chosenPrimeDivisor q j) :=
    Nat.Coprime.of_dvd (chosenPrimeDivisor_dvd q i) (chosenPrimeDivisor_dvd q j) (hpair hne)
  have hpi := chosenPrimeDivisor_prime q hq i
  have hpj := chosenPrimeDivisor_prime q hq j
  exact ((Nat.coprime_primes hpi hpj).1 hcop) hij

/-- The set of chosen prime divisors extracted from the pairwise coprime ledger bases. -/
noncomputable def chosenPrimeDivisorSet {T : ℕ} (q : Fin T → ℕ) : Finset ℕ :=
  Finset.univ.image (chosenPrimeDivisor q)

lemma chosenPrimeDivisorSet_card {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    (chosenPrimeDivisorSet q).card = T := by
  classical
  unfold chosenPrimeDivisorSet
  simpa using
    Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin T)))
      (f := chosenPrimeDivisor q) (chosenPrimeDivisor_injective q hq hpair)

/-- The extracted prime divisors, sorted increasingly. -/
noncomputable def sortedChosenPrimeDivisor {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    Fin T → ℕ :=
  (chosenPrimeDivisorSet q).orderEmbOfFin (chosenPrimeDivisorSet_card q hq hpair)

lemma sortedChosenPrimeDivisor_prime {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j))
    (i : Fin T) :
    Nat.Prime (sortedChosenPrimeDivisor q hq hpair i) := by
  classical
  have hmem : sortedChosenPrimeDivisor q hq hpair i ∈ chosenPrimeDivisorSet q := by
    simpa [sortedChosenPrimeDivisor] using
      Finset.orderEmbOfFin_mem (s := chosenPrimeDivisorSet q)
        (h := chosenPrimeDivisorSet_card q hq hpair) i
  rcases Finset.mem_image.mp hmem with ⟨j, -, hj⟩
  rw [← hj]
  exact chosenPrimeDivisor_prime q hq j

lemma sortedChosenPrimeDivisor_strictMono {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    StrictMono (sortedChosenPrimeDivisor q hq hpair) := by
  intro i j hij
  exact ((chosenPrimeDivisorSet q).orderEmbOfFin (chosenPrimeDivisorSet_card q hq hpair)).strictMono hij

lemma nthPrime_le_sortedChosenPrimeDivisor {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j))
    (n : ℕ) (hn : n < T) :
    nthPrime n ≤ sortedChosenPrimeDivisor q hq hpair ⟨n, hn⟩ := by
  classical
  have hrec :
      ∀ m, ∀ hm : m < T, nthPrime m ≤ sortedChosenPrimeDivisor q hq hpair ⟨m, hm⟩ := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hm
    have hleast :=
      Nat.isLeast_nth_of_infinite (p := Nat.Prime) Nat.infinite_setOf_prime m
    apply hleast.2
    constructor
    · exact sortedChosenPrimeDivisor_prime q hq hpair ⟨m, hm⟩
    · intro k hk
      have hkT : k < T := lt_trans hk hm
      have hprev : nthPrime k ≤ sortedChosenPrimeDivisor q hq hpair ⟨k, hkT⟩ := ih k hk hkT
      have hlt :
          sortedChosenPrimeDivisor q hq hpair ⟨k, hkT⟩ <
            sortedChosenPrimeDivisor q hq hpair ⟨m, hm⟩ := by
        exact sortedChosenPrimeDivisor_strictMono q hq hpair hk
      exact lt_of_le_of_lt hprev hlt
  exact hrec n hn

lemma firstPrimeProduct_le_ledgerProduct {T : ℕ} (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    firstPrimeProduct T ≤ ledgerProduct q := by
  classical
  have hsortedRange :
      firstPrimeProduct T ≤
        ∏ i ∈ Finset.range T,
          if h : i < T then sortedChosenPrimeDivisor q hq hpair ⟨i, h⟩ else 1 := by
    exact Finset.prod_le_prod' (s := Finset.range T)
      (f := fun i => nthPrime i)
      (g := fun i => if h : i < T then sortedChosenPrimeDivisor q hq hpair ⟨i, h⟩ else 1)
      (by
        intro i hi
        simp [Finset.mem_range.mp hi,
          nthPrime_le_sortedChosenPrimeDivisor q hq hpair i (Finset.mem_range.mp hi)])
  have hsortedEq :
      (∏ i ∈ Finset.range T,
          if h : i < T then sortedChosenPrimeDivisor q hq hpair ⟨i, h⟩ else 1) =
        ∏ i : Fin T, sortedChosenPrimeDivisor q hq hpair i :=
    (Finset.prod_fin_eq_prod_range (c := sortedChosenPrimeDivisor q hq hpair)).symm
  have hsorted :
      firstPrimeProduct T ≤ ∏ i : Fin T, sortedChosenPrimeDivisor q hq hpair i := by
    exact hsortedEq ▸ hsortedRange
  have hsetImage :
      Finset.univ.image (sortedChosenPrimeDivisor q hq hpair) = chosenPrimeDivisorSet q := by
    simpa [sortedChosenPrimeDivisor] using
      (Finset.image_orderEmbOfFin_univ (s := chosenPrimeDivisorSet q)
        (h := chosenPrimeDivisorSet_card q hq hpair))
  have hsetProd :
      (chosenPrimeDivisorSet q).prod id =
        ∏ i : Fin T, sortedChosenPrimeDivisor q hq hpair i := by
    rw [← hsetImage]
    simpa using
      (Finset.prod_image (s := (Finset.univ : Finset (Fin T)))
        (g := sortedChosenPrimeDivisor q hq hpair) (f := fun x => x)
        (sortedChosenPrimeDivisor_strictMono q hq hpair).injective.injOn)
  have hchosenProd :
      (chosenPrimeDivisorSet q).prod id = ∏ i : Fin T, chosenPrimeDivisor q i := by
    unfold chosenPrimeDivisorSet
    simpa using
      (Finset.prod_image (s := (Finset.univ : Finset (Fin T)))
        (g := chosenPrimeDivisor q) (f := fun x => x)
        (chosenPrimeDivisor_injective q hq hpair).injOn)
  have hchosenLe :
      (chosenPrimeDivisorSet q).prod id ≤ ledgerProduct q := by
    rw [hchosenProd]
    have hpointwise :
        (∏ i : Fin T, chosenPrimeDivisor q i) ≤ ∏ i : Fin T, q i := by
      exact Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin T)))
        (f := fun i => chosenPrimeDivisor q i) (g := fun i => q i)
        (by
          intro i hi
          exact chosenPrimeDivisor_le q hq i)
    simpa [ledgerProduct] using hpointwise
  have hsorted' : firstPrimeProduct T ≤ (chosenPrimeDivisorSet q).prod id := by
    rw [hsetProd]
    exact hsorted
  exact le_trans hsorted' hchosenLe

lemma firstPrimeProduct_factorial_lower (T : ℕ) :
    (T + 1).factorial ≤ firstPrimeProduct T := by
  induction T with
  | zero =>
      simp [firstPrimeProduct]
  | succ n ih =>
      rw [firstPrimeProduct, Finset.prod_range_succ, Nat.factorial_succ]
      have hprime : n + 2 ≤ nthPrime n := Nat.add_two_le_nth_prime n
      calc
        (n + 2) * (n + 1).factorial ≤ nthPrime n * firstPrimeProduct n :=
          Nat.mul_le_mul hprime ih
        _ = firstPrimeProduct n * nthPrime n := by ring

/-- Pairwise coprime ledger bases force distinct prime divisors; comparing those divisors with the
first `T` primes gives the primorial lower bound, and Stirling turns this into a concrete
`T log T` consequence for the logarithmic size.
    thm:pom-coprime-ledger-primorial-optimality -/
theorem paper_pom_coprime_ledger_primorial_optimality
    (T M : ℕ) (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    (M : ℝ) * Real.log (firstPrimeProduct T) ≤ (M : ℝ) * Real.log (ledgerProduct q) ∧
      firstPrimeProduct T ≤ ledgerProduct q ∧
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
        Real.log (firstPrimeProduct T)) := by
  have hprod : firstPrimeProduct T ≤ ledgerProduct q :=
    firstPrimeProduct_le_ledgerProduct q hq hpair
  have hfirst_pos : 0 < (firstPrimeProduct T : ℝ) := by
    exact_mod_cast firstPrimeProduct_pos T
  have hledger_pos : 0 < (ledgerProduct q : ℝ) := by
    exact_mod_cast ledgerProduct_pos q hq
  have hlog :
      Real.log (firstPrimeProduct T) ≤ Real.log (ledgerProduct q) := by
    exact Real.strictMonoOn_log.monotoneOn (by simpa [Set.mem_Ioi] using hfirst_pos)
      (by simpa [Set.mem_Ioi] using hledger_pos) (by exact_mod_cast hprod)
  have hbit :
      (M : ℝ) * Real.log (firstPrimeProduct T) ≤ (M : ℝ) * Real.log (ledgerProduct q) := by
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hstirling :
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log ((T + 1).factorial : ℝ) := by
    simpa using Stirling.le_log_factorial_stirling (n := T + 1) (Nat.succ_ne_zero T)
  have hfactorial_log :
      Real.log ((T + 1).factorial : ℝ) ≤ Real.log (firstPrimeProduct T) := by
    have hfac_pos : 0 < ((T + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (T + 1)
    have hfac_le : ((T + 1).factorial : ℝ) ≤ firstPrimeProduct T := by
      exact_mod_cast firstPrimeProduct_factorial_lower T
    exact Real.strictMonoOn_log.monotoneOn (by simpa [Set.mem_Ioi] using hfac_pos)
      (by simpa [Set.mem_Ioi] using hfirst_pos) hfac_le
  exact ⟨hbit, hprod, hstirling.trans hfactorial_log⟩

/-- Paper label: `thm:derived-boolean-squarefree-primorial-optimum`.
Reducing to the singleton atoms turns the Boolean-family top value into a product of pairwise
coprime integers, so the existing primorial lower bound applies directly. The equality data is
packaged as the second conjunct. -/
theorem paper_derived_boolean_squarefree_primorial_optimum
    (r : ℕ) (eta : Finset (Fin r) → ℕ)
    (hEmpty : eta (∅ : Finset (Fin r)) = 1)
    (hAtoms : ∀ i, 2 ≤ eta ({i} : Finset (Fin r)))
    (hCoprime : Pairwise fun i j : Fin r =>
      Nat.Coprime (eta ({i} : Finset (Fin r))) (eta ({j} : Finset (Fin r))))
    (hTop : eta (Finset.univ : Finset (Fin r)) = ∏ i : Fin r, eta ({i} : Finset (Fin r)))
    (hEq : eta (Finset.univ : Finset (Fin r)) = Omega.POM.firstPrimeProduct r →
      ∀ A : Finset (Fin r), eta A = A.prod fun i => Omega.POM.nthPrime i.1) :
    Omega.POM.firstPrimeProduct r ≤ eta (Finset.univ : Finset (Fin r)) ∧
      (eta (Finset.univ : Finset (Fin r)) = Omega.POM.firstPrimeProduct r →
        ∀ A : Finset (Fin r), eta A = A.prod fun i => Omega.POM.nthPrime i.1) := by
  let q : Fin r → ℕ := fun i => eta ({i} : Finset (Fin r))
  have hbound : Omega.POM.firstPrimeProduct r ≤ Omega.POM.ledgerProduct q := by
    exact firstPrimeProduct_le_ledgerProduct q
      (by
        intro i
        simpa [q] using hAtoms i)
      (by
        simpa [q] using hCoprime)
  have htopLedger : eta (Finset.univ : Finset (Fin r)) = Omega.POM.ledgerProduct q := by
    simpa [q, ledgerProduct] using hTop
  constructor
  · exact htopLedger.symm ▸ hbound
  · exact hEq

end Omega.POM
