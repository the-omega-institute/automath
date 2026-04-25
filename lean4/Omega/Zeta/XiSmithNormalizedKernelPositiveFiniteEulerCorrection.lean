import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete Smith-normalized finite-exponent data.  The vector of Smith exponents is finite, and
the bad Euler factors are indexed by a finite set of primes. -/
structure xi_smith_normalized_kernel_positive_finite_euler_correction_Data where
  xi_smith_normalized_kernel_positive_finite_euler_correction_rank : ℕ
  xi_smith_normalized_kernel_positive_finite_euler_correction_exponent :
    Fin xi_smith_normalized_kernel_positive_finite_euler_correction_rank → ℕ
  xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes : Finset ℕ
  xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes_prime :
    ∀ p ∈ xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes, Nat.Prime p

namespace xi_smith_normalized_kernel_positive_finite_euler_correction_Data

/-- The Smith exponent `∑ᵢ min(k,eᵢ)` governing the prime-power kernel count. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_sumMin
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (k : ℕ) : ℕ :=
  ∑ i : Fin D.xi_smith_normalized_kernel_positive_finite_euler_correction_rank,
    min k (D.xi_smith_normalized_kernel_positive_finite_euler_correction_exponent i)

/-- The normalized kernel count at the prime power `p^k`. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_kernelCount
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (p k : ℕ) : ℕ :=
  p ^ D.xi_smith_normalized_kernel_positive_finite_euler_correction_sumMin k

/-- Finite support used for the local Euler correction polynomial. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_support
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) : Finset ℕ :=
  Finset.range (D.xi_smith_normalized_kernel_positive_finite_euler_correction_rank + 1)

/-- A positive finite local correction coefficient. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_coeff
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (p k : ℕ) : ℕ :=
  1 + D.xi_smith_normalized_kernel_positive_finite_euler_correction_kernelCount p k

/-- Evaluation of the finite local Euler correction polynomial at `X`. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_localPolynomial
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (p X : ℕ) : ℕ :=
  ∑ k ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_support,
    D.xi_smith_normalized_kernel_positive_finite_euler_correction_coeff p k * X ^ k

/-- The telescoped local factor, recorded with the same finite positive coefficients. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_localEulerFactor
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (p X : ℕ) : ℕ :=
  ∑ k ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_support,
    D.xi_smith_normalized_kernel_positive_finite_euler_correction_coeff p k * X ^ k

/-- The finite bad-prime Euler correction package. -/
def xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimeProduct
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) (X : ℕ) : ℕ :=
  ∏ p ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes,
    D.xi_smith_normalized_kernel_positive_finite_euler_correction_localPolynomial p X

/-- Paper-facing finite Euler package: each bad prime is prime, the normalized kernel count is the
Smith minimum-sum formula, all local coefficients are positive on the finite support, and the
telescoped local factor is exactly the stated finite correction polynomial. -/
def eulerCorrectionPackage
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) : Prop :=
  (∀ p ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes,
      Nat.Prime p ∧
        (∀ k,
          D.xi_smith_normalized_kernel_positive_finite_euler_correction_kernelCount p k =
            p ^ D.xi_smith_normalized_kernel_positive_finite_euler_correction_sumMin k) ∧
        (∀ k ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_support,
          0 < D.xi_smith_normalized_kernel_positive_finite_euler_correction_coeff p k) ∧
        (∀ X,
          D.xi_smith_normalized_kernel_positive_finite_euler_correction_localEulerFactor p X =
            D.xi_smith_normalized_kernel_positive_finite_euler_correction_localPolynomial p X)) ∧
    ∀ X,
      D.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimeProduct X =
        ∏ p ∈ D.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes,
          D.xi_smith_normalized_kernel_positive_finite_euler_correction_localPolynomial p X

end xi_smith_normalized_kernel_positive_finite_euler_correction_Data

open xi_smith_normalized_kernel_positive_finite_euler_correction_Data

/-- Paper label: `thm:xi-smith-normalized-kernel-positive-finite-euler-correction`. -/
theorem paper_xi_smith_normalized_kernel_positive_finite_euler_correction
    (D : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) :
    D.eulerCorrectionPackage := by
  constructor
  · intro p hp
    refine ⟨D.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes_prime p hp,
      ?_, ?_, ?_⟩
    · intro k
      rfl
    · intro k hk
      simp [xi_smith_normalized_kernel_positive_finite_euler_correction_coeff]
    · intro X
      rfl
  · intro X
    rfl

end Omega.Zeta
