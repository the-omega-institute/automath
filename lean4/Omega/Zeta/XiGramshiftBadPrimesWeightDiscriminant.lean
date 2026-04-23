import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The concrete Vandermonde block used for the `ξ`-gramshift audit. -/
def xi_gramshift_bad_primes_weight_discriminant_V : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 4]

/-- The atomic weights in the audited two-node model. -/
def xi_gramshift_bad_primes_weight_discriminant_weights : Fin 2 → ℤ
  | 0 => 2
  | 1 => 5

/-- The first Hankel/Gram block `H₀ = V diag(w) Vᵀ`. -/
noncomputable def xi_gramshift_bad_primes_weight_discriminant_H0 : Matrix (Fin 2) (Fin 2) ℤ :=
  xi_gramshift_bad_primes_weight_discriminant_V *
    Matrix.diagonal xi_gramshift_bad_primes_weight_discriminant_weights *
      xi_gramshift_bad_primes_weight_discriminant_V.transpose

/-- Product of the two audited weights. -/
def xi_gramshift_bad_primes_weight_discriminant_weightProduct : ℕ := 10

/-- Discriminant of the monic quadratic with roots `1` and `4`, namely `(4 - 1)^2`. -/
def xi_gramshift_bad_primes_weight_discriminant_discriminant : ℕ := 9

/-- The audited bad-prime predicate: a prime is bad exactly when it divides the weight product or
the discriminant. -/
def xi_gramshift_bad_primes_weight_discriminant_badPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧
    (p ∣ xi_gramshift_bad_primes_weight_discriminant_weightProduct ∨
      p ∣ xi_gramshift_bad_primes_weight_discriminant_discriminant)

/-- Paper label: `thm:xi-gramshift-bad-primes-weight-discriminant`. In the concrete two-node
audit, the initial Gram/Hankel block factors as `V diag(w) Vᵀ`, its determinant is the weight
product times the quadratic discriminant, and the bad primes are exactly the primes dividing one
of those two scalar factors. -/
theorem paper_xi_gramshift_bad_primes_weight_discriminant :
    xi_gramshift_bad_primes_weight_discriminant_H0 =
      xi_gramshift_bad_primes_weight_discriminant_V *
        Matrix.diagonal xi_gramshift_bad_primes_weight_discriminant_weights *
          xi_gramshift_bad_primes_weight_discriminant_V.transpose ∧
      xi_gramshift_bad_primes_weight_discriminant_H0.det =
        ((xi_gramshift_bad_primes_weight_discriminant_weightProduct *
          xi_gramshift_bad_primes_weight_discriminant_discriminant : ℕ) : ℤ) ∧
      ∀ p : ℕ, Nat.Prime p →
        ((p ∣ Int.natAbs xi_gramshift_bad_primes_weight_discriminant_H0.det) ↔
          xi_gramshift_bad_primes_weight_discriminant_badPrime p) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [xi_gramshift_bad_primes_weight_discriminant_H0, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_transpose]
    norm_num [xi_gramshift_bad_primes_weight_discriminant_V,
      xi_gramshift_bad_primes_weight_discriminant_weights,
      xi_gramshift_bad_primes_weight_discriminant_weightProduct,
      xi_gramshift_bad_primes_weight_discriminant_discriminant, Matrix.det_fin_two]
  · intro p hp
    have hdet :
        Int.natAbs xi_gramshift_bad_primes_weight_discriminant_H0.det =
          xi_gramshift_bad_primes_weight_discriminant_weightProduct *
            xi_gramshift_bad_primes_weight_discriminant_discriminant := by
      rw [show xi_gramshift_bad_primes_weight_discriminant_H0.det =
          ((xi_gramshift_bad_primes_weight_discriminant_weightProduct *
            xi_gramshift_bad_primes_weight_discriminant_discriminant : ℕ) : ℤ) by
        rw [xi_gramshift_bad_primes_weight_discriminant_H0, Matrix.det_mul, Matrix.det_mul,
          Matrix.det_diagonal, Matrix.det_transpose]
        norm_num [xi_gramshift_bad_primes_weight_discriminant_V,
          xi_gramshift_bad_primes_weight_discriminant_weights,
          xi_gramshift_bad_primes_weight_discriminant_weightProduct,
          xi_gramshift_bad_primes_weight_discriminant_discriminant, Matrix.det_fin_two]]
      rw [Int.natAbs_natCast]
    simp [xi_gramshift_bad_primes_weight_discriminant_badPrime, hp, hdet]
    exact Nat.Prime.dvd_mul hp

end Omega.Zeta
