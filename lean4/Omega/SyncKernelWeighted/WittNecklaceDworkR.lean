import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- The Möbius/Adams divisor sum appearing in the weighted Witt-necklace formula over a general
commutative coefficient ring. -/
def witt_necklace_dwork_r_mobius_sum {R : Type*} [CommRing R]
    (ψ : ℕ → R →+* R) (a : ℕ → R) (n : ℕ) : R :=
  Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℤ) • ψ d (a (n / d)))

/-- The prime-power difference term produced by the Dwork collapse of the Witt-necklace formula. -/
def witt_necklace_dwork_r_prime_power_difference {R : Type*} [CommRing R]
    (ψ : ℕ → R →+* R) (a : ℕ → R) (p k : ℕ) : R :=
  a (p ^ k) - ψ p (a (p ^ (k - 1)))

/-- Coefficient-ring version of the Witt-necklace divisibility package: if the Möbius/Adams
identity is available for every `n`, and the `n = p^k` specialization has been collapsed using
`μ(p^j) = 0` for `j ≥ 2`, then one gets both necklace divisibility and the Dwork-type
prime-power congruence.
    prop:witt-necklace-dwork-R -/
theorem paper_witt_necklace_dwork_r {R : Type*} [CommRing R]
    (ψ : ℕ → R →+* R) (a primitive : ℕ → R)
    (hmob :
      ∀ n : ℕ,
        (n : ℤ) • primitive n = witt_necklace_dwork_r_mobius_sum ψ a n)
    (hprimepow :
      ∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
        (p ^ k : ℤ) • primitive (p ^ k) =
          witt_necklace_dwork_r_prime_power_difference ψ a p k) :
    (∀ n : ℕ,
      ∃ q : R, witt_necklace_dwork_r_mobius_sum ψ a n = (n : ℤ) • q) ∧
      (∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
        ∃ q : R, witt_necklace_dwork_r_prime_power_difference ψ a p k = (p ^ k : ℤ) • q) := by
  refine ⟨?_, ?_⟩
  · intro n
    refine ⟨primitive n, (hmob n).symm⟩
  · intro p k hp hk
    refine ⟨primitive (p ^ k), (hprimepow p k hp hk).symm⟩

end Omega.SyncKernelWeighted
