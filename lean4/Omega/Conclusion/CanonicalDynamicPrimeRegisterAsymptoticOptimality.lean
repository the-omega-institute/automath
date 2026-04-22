import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterFixed2adicAmbientVsFiniteLedger
import Omega.EA.DynamicPrimeRegisterBitlength

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Concrete data for the canonical dynamic prime-register package: two distinguished valuation
coordinates, a dynamic Gödel history, and the existing `T log T` bitlength witness. -/
structure conclusion_canonical_dynamic_prime_register_asymptotic_optimality_data where
  timeHorizon : ℕ
  timeHorizon_pos : 1 ≤ timeHorizon
  firstCoordinate : ℕ
  secondCoordinate : ℕ
  primes : ℕ → ℕ
  dynamicCode : List ℕ
  primes_gt_one : ∀ i, 1 < primes i
  primes_lower_bound :
    ∀ i, i < dynamicCode.length → i + 2 ≤ primes i
  dynamicCode_pos :
    ∀ i : Fin dynamicCode.length, 1 ≤ dynamicCode[i]
  bitWitness : GodelPrimeBitlengthWitness timeHorizon

/-- Canonical two-coordinate prime-power encoding. -/
def conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding
    (a b : ℕ) : ℕ :=
  2 ^ a * 3 ^ b

private lemma conclusion_canonical_dynamic_prime_register_asymptotic_optimality_factorization_two
    (a b : ℕ) :
    Nat.factorization
        (conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding a b)
        2 = a := by
  unfold conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))]
  simp [Nat.factorization_pow, show (Nat.factorization 2) 2 = 1 by native_decide,
    show (Nat.factorization 3) 2 = 0 by native_decide]

private lemma conclusion_canonical_dynamic_prime_register_asymptotic_optimality_factorization_three
    (a b : ℕ) :
    Nat.factorization
        (conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding a b)
        3 = b := by
  unfold conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))]
  simp [Nat.factorization_pow, show (Nat.factorization 2) 3 = 0 by native_decide,
    show (Nat.factorization 3) 3 = 1 by native_decide]

/-- The conclusion package exposes the canonical valuation recovery, the dynamic `T log T`
bitlength sandwich, and the faithful realization on the fixed rank-two two-adic ambient. -/
def conclusion_canonical_dynamic_prime_register_asymptotic_optimality_statement
    (D : conclusion_canonical_dynamic_prime_register_asymptotic_optimality_data) : Prop :=
  Nat.factorization
      (conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding
        D.firstCoordinate D.secondCoordinate) 2 = D.firstCoordinate ∧
    Nat.factorization
        (conclusion_canonical_dynamic_prime_register_asymptotic_optimality_canonical_encoding
          D.firstCoordinate D.secondCoordinate) 3 = D.secondCoordinate ∧
    Nat.factorial (D.dynamicCode.length + 1) ≤ godelEncoding D.primes 0 D.dynamicCode ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c * (D.timeHorizon : ℝ) * Real.log ((D.timeHorizon + 1 : ℕ) : ℝ) ≤
        D.bitWitness.maxBitlength ∧
      D.bitWitness.maxBitlength ≤
        C * (D.timeHorizon : ℝ) * Real.log ((D.timeHorizon + 1 : ℕ) : ℝ)) ∧
    Fintype.card (Fin 2) = 2 ∧
    Function.Injective primeRegisterAffineAction

/-- Paper label: `thm:conclusion-canonical-dynamic-prime-register-asymptotic-optimality`. -/
theorem paper_conclusion_canonical_dynamic_prime_register_asymptotic_optimality
    (D : conclusion_canonical_dynamic_prime_register_asymptotic_optimality_data) :
    conclusion_canonical_dynamic_prime_register_asymptotic_optimality_statement D := by
  rcases Omega.EA.paper_emergent_arithmetic_dynamic_prime_register_bitlength
      D.timeHorizon D.timeHorizon_pos D.primes D.dynamicCode D.primes_gt_one
      D.primes_lower_bound D.dynamicCode_pos D.bitWitness with
    ⟨hFactorial, hBits⟩
  rcases hBits with ⟨c, C, hc, hC, hLower, hUpper⟩
  have hAffine := paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger
  refine ⟨?_, ?_, hFactorial, ⟨c, C, hc, hC, hLower, hUpper⟩, hAffine.1, hAffine.2.1⟩
  · exact
      conclusion_canonical_dynamic_prime_register_asymptotic_optimality_factorization_two
        D.firstCoordinate D.secondCoordinate
  · exact
      conclusion_canonical_dynamic_prime_register_asymptotic_optimality_factorization_three
        D.firstCoordinate D.secondCoordinate

end Omega.Conclusion
