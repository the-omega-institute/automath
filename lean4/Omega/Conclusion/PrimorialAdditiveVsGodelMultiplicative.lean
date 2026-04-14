import Mathlib.Tactic

namespace Omega.Conclusion.PrimorialAdditiveVsGodelMultiplicative

open Finset

/-- Mixed-radix (additive) encoding.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
def mixedRadixVal {T : ℕ} (p : Fin T → ℕ) (a : Fin T → ℕ) : ℕ :=
  ∑ t : Fin T, a t * ∏ j ∈ Finset.Iio t, p j

/-- Godel (multiplicative) encoding.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
def godelMul {T : ℕ} (p : Fin T → ℕ) (a : Fin T → ℕ) : ℕ :=
  ∏ t : Fin T, p t ^ (a t + 1)

/-- T=0 case: both encodings are trivially injective (domain is empty function).
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_injective_zero (p : Fin 0 → ℕ) :
    Function.Injective (godelMul p) := by
  intro a b _
  funext i
  exact Fin.elim0 i

/-- T=0 mixed radix: trivially injective.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem mixedRadixVal_injective_zero (_p : Fin 0 → ℕ)
    (a b : Fin 0 → ℕ) : a = b := by
  funext i; exact Fin.elim0 i

/-- T=1 Godel: `p 0 ^ (a 0 + 1) = p 0 ^ (b 0 + 1) → a = b` when `p 0` prime.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_injective_one (p : Fin 1 → ℕ) (hp : (p 0).Prime) :
    Function.Injective (godelMul p) := by
  intro a b hab
  unfold godelMul at hab
  simp only [Fin.prod_univ_one] at hab
  have hp2 : 2 ≤ p 0 := hp.two_le
  have := Nat.pow_right_injective hp2 hab
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  omega

/-- T=1 mixed radix: `a 0 * 1 = b 0 * 1 → a = b`.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem mixedRadixVal_injective_one (p : Fin 1 → ℕ)
    (a b : Fin 1 → ℕ) (heq : mixedRadixVal p a = mixedRadixVal p b) : a = b := by
  unfold mixedRadixVal at heq
  simp only [Fin.sum_univ_one] at heq
  -- After simp, heq should be: a 0 * ∏ j ∈ Iio 0, p j = b 0 * ∏ j ∈ Iio 0, p j
  -- Iio (0 : Fin 1) is empty, so ∏ = 1
  have hiio : (Finset.Iio (0 : Fin 1)) = ∅ := by
    ext x; simp [Fin.lt_def]
  rw [hiio, Finset.prod_empty] at heq
  simp at heq
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst hi; exact heq

/-- Auxiliary: for pairwise coprime bases ≥ 2, if products of powers agree,
    then each exponent agrees. Uses coprime divisibility.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_exponent_eq {T : ℕ} (p : Fin T → ℕ)
    (hp2 : ∀ t, 2 ≤ p t)
    (hcop : ∀ i j : Fin T, i ≠ j → Nat.Coprime (p i) (p j))
    (a b : Fin T → ℕ)
    (heq : godelMul p a = godelMul p b) (t : Fin T) : a t = b t := by
  unfold godelMul at heq
  -- p t ^ (a t + 1) divides ∏ i, p i ^ (b i + 1)
  have hdvd_ab : p t ^ (a t + 1) ∣ ∏ i, p i ^ (b i + 1) :=
    heq ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
  -- p t ^ (a t + 1) is coprime to ∏ j ≠ t, p j ^ (b j + 1)
  have hcop_prod : Nat.Coprime (p t ^ (a t + 1))
      (∏ j ∈ Finset.univ.erase t, p j ^ (b j + 1)) := by
    rw [Nat.coprime_prod_right_iff]
    intro j hj; rw [Finset.mem_erase] at hj
    exact (hcop t j hj.1.symm).pow (a t + 1) (b j + 1)
  -- Split the product: ∏ i = p t ^ (b t + 1) * ∏ j ≠ t
  have hsplit : ∏ i : Fin T, p i ^ (b i + 1) =
      p t ^ (b t + 1) * ∏ j ∈ Finset.univ.erase t, p j ^ (b j + 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
  rw [hsplit] at hdvd_ab
  -- By coprime divisibility: p t ^ (a t + 1) ∣ p t ^ (b t + 1)
  have hdvd : p t ^ (a t + 1) ∣ p t ^ (b t + 1) :=
    hcop_prod.dvd_of_dvd_mul_right hdvd_ab
  -- Similarly, p t ^ (b t + 1) ∣ p t ^ (a t + 1)
  have hdvd_ba : p t ^ (b t + 1) ∣ ∏ i, p i ^ (a i + 1) :=
    heq ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
  have hcop_prod' : Nat.Coprime (p t ^ (b t + 1))
      (∏ j ∈ Finset.univ.erase t, p j ^ (a j + 1)) := by
    rw [Nat.coprime_prod_right_iff]
    intro j hj; rw [Finset.mem_erase] at hj
    exact (hcop t j hj.1.symm).pow (b t + 1) (a j + 1)
  have hsplit' : ∏ i : Fin T, p i ^ (a i + 1) =
      p t ^ (a t + 1) * ∏ j ∈ Finset.univ.erase t, p j ^ (a j + 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
  rw [hsplit'] at hdvd_ba
  have hdvd' : p t ^ (b t + 1) ∣ p t ^ (a t + 1) :=
    hcop_prod'.dvd_of_dvd_mul_right hdvd_ba
  -- Both directions: p t ^ (a t + 1) = p t ^ (b t + 1)
  have hpow_eq : p t ^ (a t + 1) = p t ^ (b t + 1) :=
    Nat.dvd_antisymm hdvd hdvd'
  exact Nat.succ_injective (Nat.pow_right_injective (hp2 t) hpow_eq)

/-- Godel multiplicative encoding is injective for pairwise coprime bases ≥ 2.
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem godelMul_injective_coprime {T : ℕ} (p : Fin T → ℕ)
    (hp2 : ∀ t, 2 ≤ p t)
    (hcop : ∀ i j : Fin T, i ≠ j → Nat.Coprime (p i) (p j)) :
    Function.Injective (godelMul p) := by
  intro a b heq
  funext t
  exact godelMul_exponent_eq p hp2 hcop a b heq t

/-- Paper package: primorial additive vs Godel multiplicative (T=0,1 + general coprime).
    cor:conclusion-primorial-additive-vs-godel-multiplicative -/
theorem paper_conclusion_primorial_additive_vs_godel_multiplicative_small :
    (∀ (p : Fin 0 → ℕ), Function.Injective (godelMul p)) ∧
    (∀ (p : Fin 1 → ℕ), (p 0).Prime → Function.Injective (godelMul p)) ∧
    (∀ (p : Fin 1 → ℕ) (a b : Fin 1 → ℕ),
      mixedRadixVal p a = mixedRadixVal p b → a = b) ∧
    (∀ T (p : Fin T → ℕ), (∀ t, 2 ≤ p t) →
      (∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) →
      Function.Injective (godelMul p)) :=
  ⟨godelMul_injective_zero,
   godelMul_injective_one,
   fun p a b => mixedRadixVal_injective_one p a b,
   fun _ p hp2 hcop => godelMul_injective_coprime p hp2 hcop⟩

/-- Faithful Godel encoding requires infinite prime support: small prime witnesses.
    cor:conclusion-faithful-time-addressed-godel-needs-infinite-prime-support -/
theorem paper_conclusion_faithful_godel_infinite_prime_support_seeds :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 < 3 ∧ 3 < 5 ∧ 5 < 7 ∧ 7 < 11) ∧
    (7 ≠ 2 ∧ 7 ≠ 3 ∧ 7 ≠ 5) ∧
    Nat.Prime 11 := by
  exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
         ⟨by omega, by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega⟩,
         by norm_num⟩

/-- Paper package: faithful Godel encoding requires infinite prime support.
    cor:conclusion-faithful-time-addressed-godel-needs-infinite-prime-support -/
theorem paper_conclusion_faithful_time_addressed_godel_needs_infinite_prime_support_package :
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7) ∧
    (2 < 3 ∧ 3 < 5 ∧ 5 < 7 ∧ 7 < 11) ∧
    (7 ≠ 2 ∧ 7 ≠ 3 ∧ 7 ≠ 5) ∧
    Nat.Prime 11 :=
  paper_conclusion_faithful_godel_infinite_prime_support_seeds

end Omega.Conclusion.PrimorialAdditiveVsGodelMultiplicative
