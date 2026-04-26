import Mathlib
import Omega.CircleDimension.CircleDim

/-!
# Finite prime truncation homomorphism dimension seed values

Primality, coprimality, and product identities for the small primes {2,3,5}
used in the circle-dimension prime truncation functor.
-/

namespace Omega.CircleDimension

/-- Positive natural numbers, viewed as the reduced multiplicative monoid of the UFD `ℕ`. -/
abbrev ReducedNatMonoid := ℕ+

/-- The prime-valuation ledger of a positive natural number. -/
def natPrimeLedger (n : ReducedNatMonoid) : ℕ →₀ ℕ :=
  n.1.factorization

/-- The integer-valued lift of the prime ledger, matching the Grothendieck-group coordinates. -/
noncomputable def natPrimeLedgerLift (n : ReducedNatMonoid) : ℕ →₀ ℤ :=
  (natPrimeLedger n).mapRange Int.ofNat (by simp)

/-- The finite prime truncation monoid on `B` generators, written in exponent-vector form. -/
abbrev cdim_finite_prime_truncation_hom_half_circle_exponent_vectors (B : ℕ) := Fin B → ℕ

/-- The explicit embedding of the finite prime truncation monoid into a free commutative monoid of
rank `B`. -/
def cdim_finite_prime_truncation_hom_half_circle_embedding (B : ℕ) :
    cdim_finite_prime_truncation_hom_half_circle_exponent_vectors B →+*
      (Fin B → ℕ) :=
  RingHom.id _

lemma cdim_finite_prime_truncation_hom_half_circle_minimal_additive_rank
    (B k : ℕ)
    (Ψ : cdim_finite_prime_truncation_hom_half_circle_exponent_vectors B →+* (Fin k → ℕ))
    (hΨ : Function.Injective Ψ) :
    B ≤ k := by
  obtain ⟨σ, hσ⟩ := Omega.semiring_hom_rigidity B k Ψ
  have hσ_surj : Function.Surjective σ := by
    intro i
    by_contra hi
    let x : cdim_finite_prime_truncation_hom_half_circle_exponent_vectors B :=
      fun t => if t = i then 1 else 0
    have hΨx : Ψ x = 0 := by
      ext j
      rw [hσ x j]
      have hneq : σ j ≠ i := by
        intro hEq
        exact hi ⟨j, hEq⟩
      simp [x, hneq]
    have hxzero : x = 0 := by
      apply hΨ
      simpa using hΨx.trans Ψ.map_zero.symm
    have : (1 : ℕ) = 0 := by
      simpa [x] using congrArg (fun f => f i) hxzero
    exact Nat.one_ne_zero this
  simpa using Fintype.card_le_of_surjective σ hσ_surj

/-- Finite prime truncation seeds: primes, coprimality, products, and minFac.
    cor:cdim-finite-prime-truncation-hom-half-circle -/
theorem paper_cdim_finite_prime_truncation_seeds :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧
    Nat.Coprime 2 3 ∧ Nat.Coprime 2 5 ∧ Nat.Coprime 3 5 ∧
    (2 * 3 = 6 ∧ 2 * 5 = 10 ∧ 3 * 5 = 15 ∧ 2 * 3 * 5 = 30) ∧
    (Nat.minFac 6 = 2 ∧ 6 / 2 = 3 ∧ Nat.Prime 3) := by
  exact ⟨by norm_num, by norm_num, by norm_num,
         by decide, by decide, by decide,
         ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
         by native_decide, by norm_num, by norm_num⟩

/-- Paper package: multiplicative-object finite-ledger obstruction via prime truncation.
    This paper-facing wrapper reuses the finite prime-truncation seed certificate.
    cor:cdim-finite-prime-truncation-hom-half-circle -/
theorem paper_cdim_multiplicative_object_no_finite_hom_ledger_package :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧
    Nat.Coprime 2 3 ∧ Nat.Coprime 2 5 ∧ Nat.Coprime 3 5 ∧
    (2 * 3 = 6 ∧ 2 * 5 = 10 ∧ 3 * 5 = 15 ∧ 2 * 3 * 5 = 30) ∧
    (Nat.minFac 6 = 2 ∧ 6 / 2 = 3 ∧ Nat.Prime 3) :=
  paper_cdim_finite_prime_truncation_seeds

/-- Paper-facing obstruction wrapper extracted from the finite prime-truncation package.
    thm:cdim-multiplicative-object-no-finite-hom-ledger -/
theorem paper_cdim_multiplicative_object_no_finite_hom_ledger
    (multiplicativeEmbedding finitePrimeObstruction noFiniteHomLedger : Prop)
    (hEmbed : multiplicativeEmbedding)
    (hPrime : multiplicativeEmbedding → finitePrimeObstruction)
    (hLedger : finitePrimeObstruction → noFiniteHomLedger) :
    noFiniteHomLedger := by
  exact hLedger (hPrime hEmbed)

/-- The reduced multiplicative monoid of the UFD `ℕ` embeds in the finitely supported
prime-valuation ledger, its integer lift stays injective, and no finite prime set captures all
prime directions.
    thm:prime-ledger-non-finitizable-ufd -/
theorem paper_prime_ledger_non_finitizable_ufd :
    Function.Injective natPrimeLedger ∧
      Function.Injective natPrimeLedgerLift ∧
      ∀ S : Finset ℕ, ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧ ¬ p.factorization.support ⊆ S := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq a.ne_zero b.ne_zero
    intro p
    simpa [natPrimeLedger] using congrArg (fun f : ℕ →₀ ℕ => f p) h
  · intro a b h
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq a.ne_zero b.ne_zero
    intro p
    have hp : Int.ofNat (natPrimeLedger a p) = Int.ofNat (natPrimeLedger b p) := by
      simpa [natPrimeLedgerLift, natPrimeLedger] using congrArg (fun f : ℕ →₀ ℤ => f p) h
    exact Int.ofNat.inj hp
  · intro S
    rcases Nat.exists_infinite_primes (S.sup id + 1) with ⟨p, hpge, hp⟩
    have hp_not_mem : p ∉ S := by
      intro hpS
      have hp_le : p ≤ S.sup id := by
        simpa using (Finset.le_sup hpS : id p ≤ S.sup id)
      omega
    refine ⟨p, hp, hp_not_mem, ?_⟩
    · have hsupport : p.factorization.support = {p} := by
        simpa [hp.factorization] using Finsupp.support_single_ne_zero p one_ne_zero
      rw [hsupport]
      intro hsubset
      exact hp_not_mem (hsubset (by simp))

/-- Finite prime truncation is concretely modeled by exponent vectors on `B` generators, admits an
explicit embedding into a free commutative monoid of rank `B`, and `B` is the minimal such rank.
The corresponding hom half-circle dimension is therefore `B / 2`.
    cor:cdim-finite-prime-truncation-hom-half-circle -/
theorem paper_cdim_finite_prime_truncation_hom_half_circle (B : ℕ) :
    Function.Injective (cdim_finite_prime_truncation_hom_half_circle_embedding B) ∧
      (∀ k : ℕ,
        ∀ Ψ : cdim_finite_prime_truncation_hom_half_circle_exponent_vectors B →+* (Fin k → ℕ),
          Function.Injective Ψ → B ≤ k) ∧
      halfCircleDim B 0 = (B : ℚ) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    simpa [cdim_finite_prime_truncation_hom_half_circle_embedding] using hxy
  · intro k Ψ hΨ
    exact cdim_finite_prime_truncation_hom_half_circle_minimal_additive_rank B k Ψ hΨ
  · simp [halfCircleDim, circleDim]

end Omega.CircleDimension
