import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A concrete prime-slice assignment on the unordered edges of `Fin n`. -/
structure PrimeSliceEncoding (n : ℕ) where
  edgePrime : Sym2 (Fin n) → ℕ
  edgePrime_prime : ∀ e, Nat.Prime (edgePrime e)
  edgePrime_injective : Function.Injective edgePrime

/-- The fiber of the block label `b`. -/
def blockFiber {n k : ℕ} (π : Fin n → Fin k) (b : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun i => π i = b

/-- Unordered non-diagonal pairs lying inside the block `b`. -/
def blockPairSupport {n k : ℕ} (π : Fin n → Fin k) (b : Fin k) : Finset (Sym2 (Fin n)) :=
  (blockFiber π b).sym2.filter fun e => ¬ e.IsDiag

/-- The prime-slice support of the partition code: unordered edges inside some block. -/
def partitionPrimeSupport {n k : ℕ} (π : Fin n → Fin k) : Finset (Sym2 (Fin n)) :=
  Finset.biUnion Finset.univ (blockPairSupport π)

/-- Partition refinement seen through the encoded support. -/
def partitionRefines {n k : ℕ} (π σ : Fin n → Fin k) : Prop :=
  partitionPrimeSupport π ⊆ partitionPrimeSupport σ

/-- The squarefree prime-slice code attached to a block labeling. -/
def partitionPrimeCode {n k : ℕ} (E : PrimeSliceEncoding n) (π : Fin n → Fin k) : ℕ :=
  ∏ e ∈ partitionPrimeSupport π, E.edgePrime e

/-- The support-indicator valuation at a prime slice. -/
def primeSliceValuation {n k : ℕ} (E : PrimeSliceEncoding n) (π : Fin n → Fin k) (p : ℕ) : ℕ :=
  if p ∈ (partitionPrimeSupport π).image E.edgePrime then 1 else 0

/-- The blockwise sum of unordered pair counts. -/
def blockwisePairCount {n k : ℕ} (π : Fin n → Fin k) : ℕ :=
  ∑ b, Nat.choose ((blockFiber π b).card) 2

lemma mem_blockPairSupport_iff {n k : ℕ} {π : Fin n → Fin k} {b : Fin k} {e : Sym2 (Fin n)} :
    e ∈ blockPairSupport π b ↔ e ∈ (blockFiber π b).sym2 ∧ ¬ e.IsDiag := by
  simp [blockPairSupport]

lemma blockPairSupport_disjoint {n k : ℕ} (π : Fin n → Fin k) {b₁ b₂ : Fin k} (hb : b₁ ≠ b₂) :
    Disjoint (blockPairSupport π b₁) (blockPairSupport π b₂) := by
  refine Finset.disjoint_left.2 ?_
  intro e he1 he2
  revert he1 he2
  refine Sym2.inductionOn e ?_
  intro i j he1 he2
  rcases mem_blockPairSupport_iff.mp he1 with ⟨he1', _⟩
  rcases mem_blockPairSupport_iff.mp he2 with ⟨he2', _⟩
  have hi1 : i ∈ blockFiber π b₁ := by
    simpa using (Finset.mem_sym2_iff.mp he1') i (Sym2.mem_mk_left i j)
  have hi2 : i ∈ blockFiber π b₂ := by
    simpa using (Finset.mem_sym2_iff.mp he2') i (Sym2.mem_mk_left i j)
  rw [blockFiber, Finset.mem_filter] at hi1 hi2
  exact hb (hi1.2.symm.trans hi2.2)

lemma diag_filter_card {α : Type*} [DecidableEq α] (s : Finset α) :
    (s.sym2.filter Sym2.IsDiag).card = s.card := by
  have hset :
      s.sym2.filter Sym2.IsDiag = s.image Sym2.diag := by
    ext e
    refine Sym2.inductionOn e ?_
    intro a b
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hab, habdiag⟩
      rw [Sym2.mk_isDiag_iff] at habdiag
      subst b
      rw [Finset.mem_image]
      exact ⟨a, Finset.diag_mem_sym2_iff.mp hab, rfl⟩
    · intro h
      rw [Finset.mem_image] at h
      rcases h with ⟨c, hc, hce⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [← hce]
        exact Finset.diag_mem_sym2_iff.mpr hc
      · rw [← hce]
        simp
  rw [hset, Finset.card_image_of_injective _ Sym2.diag_injective]

lemma blockPairSupport_card {n k : ℕ} (π : Fin n → Fin k) (b : Fin k) :
    (blockPairSupport π b).card = Nat.choose ((blockFiber π b).card) 2 := by
  let s := blockFiber π b
  have hpartition :
      (s.sym2.filter fun e => ¬ e.IsDiag).card =
        s.sym2.card - (s.sym2.filter Sym2.IsDiag).card := by
    have hsum := Finset.card_filter_add_card_filter_not (s := s.sym2) (p := Sym2.IsDiag)
    omega
  calc
    (blockPairSupport π b).card = s.sym2.card - (s.sym2.filter Sym2.IsDiag).card := by
      simpa [blockPairSupport] using hpartition
    _ = Nat.choose (s.card + 1) 2 - s.card := by rw [Finset.card_sym2, diag_filter_card]
  have hchoose :
      Nat.choose (s.card + 1) 2 = s.card + Nat.choose s.card 2 := by
    simpa using (Nat.choose_succ_succ' s.card 1)
  rw [hchoose, Nat.add_sub_cancel_left]

lemma partitionPrimeSupport_card {n k : ℕ} (π : Fin n → Fin k) :
    (partitionPrimeSupport π).card = blockwisePairCount π := by
  classical
  calc
    (partitionPrimeSupport π).card = ∑ b, (blockPairSupport π b).card := by
      simpa [partitionPrimeSupport] using
        (Finset.card_biUnion (s := Finset.univ) (t := blockPairSupport π) <|
          by
            intro b₁ _ b₂ _ hb
            exact blockPairSupport_disjoint π hb)
    _ = ∑ b, Nat.choose ((blockFiber π b).card) 2 := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact blockPairSupport_card π b
    _ = blockwisePairCount π := rfl

lemma partitionPrimeCode_dvd_of_refines {n k : ℕ}
    (E : PrimeSliceEncoding n) {π σ : Fin n → Fin k} (h : partitionRefines π σ) :
    partitionPrimeCode E π ∣ partitionPrimeCode E σ := by
  exact Finset.prod_dvd_prod_of_subset (partitionPrimeSupport π) (partitionPrimeSupport σ)
    E.edgePrime h

lemma refines_of_partitionPrimeCode_dvd {n k : ℕ}
    (E : PrimeSliceEncoding n) {π σ : Fin n → Fin k}
    (h : partitionPrimeCode E π ∣ partitionPrimeCode E σ) :
    partitionRefines π σ := by
  intro e he
  have hp : E.edgePrime e ∣ partitionPrimeCode E σ := by
    exact dvd_trans (Finset.dvd_prod_of_mem E.edgePrime he) h
  rcases ((E.edgePrime_prime e).prime.dvd_finset_prod_iff E.edgePrime).mp hp with ⟨e', he', hp'⟩
  have heq :
      E.edgePrime e = E.edgePrime e' := by
    exact (Nat.prime_dvd_prime_iff_eq (E.edgePrime_prime e) (E.edgePrime_prime e')).mp hp'
  exact E.edgePrime_injective heq ▸ he'

lemma partitionRefines_iff_dvd {n k : ℕ}
    (E : PrimeSliceEncoding n) (π σ : Fin n → Fin k) :
    partitionRefines π σ ↔ partitionPrimeCode E π ∣ partitionPrimeCode E σ := by
  constructor
  · exact partitionPrimeCode_dvd_of_refines E
  · exact refines_of_partitionPrimeCode_dvd E

lemma primeSliceValuation_edgePrime {n k : ℕ}
    (E : PrimeSliceEncoding n) (π : Fin n → Fin k) (e : Sym2 (Fin n)) :
    primeSliceValuation E π (E.edgePrime e) =
      if e ∈ partitionPrimeSupport π then 1 else 0 := by
  classical
  by_cases he : e ∈ partitionPrimeSupport π
  · have himage : E.edgePrime e ∈ (partitionPrimeSupport π).image E.edgePrime :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    simp [primeSliceValuation, he, himage]
  · have hnot :
        E.edgePrime e ∉ (partitionPrimeSupport π).image E.edgePrime := by
      intro himage
      rcases Finset.mem_image.mp himage with ⟨e', he', hprime⟩
      exact he <| E.edgePrime_injective hprime ▸ he'
    simp [primeSliceValuation, he, hnot]

/-- Paper package: a squarefree prime-slice encoding rigidifies support inclusion as divisibility,
turns valuations into edge indicators, and counts the total support blockwise by binomial pair
counts.
    cor:conclusion-partition-primeslice-divisibility-valuation-paircount -/
theorem paper_conclusion_partition_primeslice_divisibility_valuation_paircount
    {n k : ℕ} (E : PrimeSliceEncoding n) (π σ : Fin n → Fin k) :
    (partitionRefines π σ ↔ partitionPrimeCode E π ∣ partitionPrimeCode E σ) ∧
      (∀ e : Sym2 (Fin n),
        primeSliceValuation E π (E.edgePrime e) =
          if e ∈ partitionPrimeSupport π then 1 else 0) ∧
      (partitionPrimeSupport π).card = blockwisePairCount π := by
  refine ⟨partitionRefines_iff_dvd E π σ, ?_, partitionPrimeSupport_card π⟩
  intro e
  exact primeSliceValuation_edgePrime E π e

end Omega.Conclusion
