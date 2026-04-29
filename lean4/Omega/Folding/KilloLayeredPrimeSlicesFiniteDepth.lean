import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Folding.GodelFiniteDictionaryBitlength

namespace Omega.Folding

open scoped BigOperators

/-- The `j`-th prime-slice index: numbers with `2`-adic valuation exactly `j`. -/
def primeSliceIndex (j n : ℕ) : ℕ :=
  2 ^ j * (2 * n + 1)

/-- The prime attached to layer `j` and local coordinate `n`. -/
noncomputable def layeredPrime (j n : ℕ) : ℕ :=
  nthPrime (primeSliceIndex j n)

/-- The `j`-th prime slice. -/
def primeSlice (j : ℕ) : Set ℕ :=
  Set.range (layeredPrime j)

/-- Finite-depth prime-product encoding: one prime factor from each layer. -/
noncomputable def layeredPrimeProductCode {k : ℕ} (x : Fin k → ℕ) : ℕ :=
  ∏ i : Fin k, layeredPrime i.1 (x i)

private lemma two_not_dvd_odd_index (n : ℕ) : ¬ 2 ∣ (2 * n + 1) := by
  intro h
  rcases h with ⟨m, hm⟩
  omega

lemma primeSliceIndex_factorization_two (j n : ℕ) :
    (primeSliceIndex j n).factorization 2 = j := by
  unfold primeSliceIndex
  have hnotdvd : ¬ 2 ∣ 2 * n + 1 := two_not_dvd_odd_index n
  have hcop : Nat.Coprime (2 ^ j) (2 * n + 1) := by
    simpa [Nat.coprime_comm] using Nat.prime_two.coprime_pow_of_not_dvd (m := j) hnotdvd
  rw [Nat.factorization_mul_of_coprime hcop, Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd hnotdvd]

lemma primeSliceIndex_injective {i j m n : ℕ}
    (h : primeSliceIndex i m = primeSliceIndex j n) : i = j ∧ m = n := by
  have hi : i = j := by
    have hfac := congrArg (fun t => t.factorization 2) h
    simpa [primeSliceIndex_factorization_two] using hfac
  subst i
  unfold primeSliceIndex at h
  have hpow : 0 < 2 ^ j := by positivity
  have hodd : 2 * m + 1 = 2 * n + 1 := Nat.eq_of_mul_eq_mul_left hpow h
  omega

lemma layeredPrime_injective {i j m n : ℕ}
    (h : layeredPrime i m = layeredPrime j n) : i = j ∧ m = n := by
  have hindex : primeSliceIndex i m = primeSliceIndex j n := by
    apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
    simpa [layeredPrime] using h
  exact primeSliceIndex_injective hindex

lemma primeSlice_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (primeSlice i) (primeSlice j) := by
  refine Set.disjoint_left.2 ?_
  intro p hp hp'
  rcases hp with ⟨m, rfl⟩
  rcases hp' with ⟨n, hEq⟩
  exact hij (layeredPrime_injective hEq).1.symm

lemma primeSlice_pairwise : Pairwise fun i j => Disjoint (primeSlice i) (primeSlice j) := by
  intro i j hij
  exact primeSlice_disjoint hij

lemma layeredPrimeProductCode_injective (k : ℕ) :
    Function.Injective (layeredPrimeProductCode (k := k)) := by
  intro x y hxy
  funext i
  let q := layeredPrime i.1 (x i)
  have hqprime : Nat.Prime q := by
    dsimp [q, layeredPrime]
    exact nthPrime_prime _
  have hqdvdx : q ∣ layeredPrimeProductCode x := by
    unfold layeredPrimeProductCode
    exact Finset.dvd_prod_of_mem (fun j : Fin k => layeredPrime j.1 (x j)) (by simp)
  have hqdvdy : q ∣ layeredPrimeProductCode y := hxy ▸ hqdvdx
  rcases (hqprime.prime.dvd_finset_prod_iff fun j : Fin k => layeredPrime j.1 (y j)).mp hqdvdy with
    ⟨j, _, hqj⟩
  have hjprime : Nat.Prime (layeredPrime j.1 (y j)) := nthPrime_prime _
  have hqeq : q = layeredPrime j.1 (y j) := (Nat.prime_dvd_prime_iff_eq hqprime hjprime).mp hqj
  rcases layeredPrime_injective hqeq with ⟨hij, hcoord⟩
  have hij' : i = j := Fin.ext hij
  subst hij'
  exact hcoord

/-- Paper-facing finite-depth prime-slice encoding: the prime slices are disjoint, and the finite
prime product admits a deterministic reverse reconstruction on its image.
    thm:killo-layered-prime-slices-finite-depth -/
theorem paper_killo_layered_prime_slices_finite_depth (k : ℕ) :
    Pairwise (fun i j => Disjoint (primeSlice i) (primeSlice j)) ∧
    ∃ decode : ℕ → Fin k → ℕ, Function.LeftInverse decode (layeredPrimeProductCode (k := k)) := by
  refine ⟨primeSlice_pairwise, ?_⟩
  exact (layeredPrimeProductCode_injective k).hasLeftInverse

/-- Paper label: `cor:killo-layered-necessity-minimality`. -/
theorem paper_killo_layered_necessity_minimality (k : ℕ) :
    (∀ j : Fin k, ∃ x y : Fin k → ℕ,
      x ≠ y ∧
        (∀ i : Fin k, i ≠ j → x i = y i) ∧
        layeredPrimeProductCode (k := k) x ≠ layeredPrimeProductCode (k := k) y) ∧
      ∃ decode : ℕ → Fin k → ℕ, Function.LeftInverse decode (layeredPrimeProductCode (k := k)) := by
  refine ⟨?_, (paper_killo_layered_prime_slices_finite_depth k).2⟩
  intro j
  refine ⟨fun _ => 0, fun i => if i = j then 1 else 0, ?_, ?_, ?_⟩
  · intro hxy
    have hj := congrArg (fun f : Fin k → ℕ => f j) hxy
    simp at hj
  · intro i hij
    simp [hij]
  · intro hcode
    have hxy : (fun i => if i = j then 1 else 0) = (fun _ : Fin k => 0) :=
      (layeredPrimeProductCode_injective k hcode).symm
    have hj := congrArg (fun f : Fin k → ℕ => f j) hxy
    simp at hj

end Omega.Folding
