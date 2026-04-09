import Mathlib.Tactic

/-!
# Finite prime truncation homomorphism dimension seed values

Primality, coprimality, and product identities for the small primes {2,3,5}
used in the circle-dimension prime truncation functor.
-/

namespace Omega.CircleDimension

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

end Omega.CircleDimension
