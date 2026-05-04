import Mathlib.Tactic
import Omega.Zeta.XiSymqKDiscriminantFibonacciVandermonde

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete symmetric-power rank for the `K,J` resultant package. -/
abbrev xi_symq_kj_resultant_fibonacci_data := ℕ

namespace xi_symq_kj_resultant_fibonacci_data

/-- The product of the binomial coordinates of the rank-one coupling vector. -/
def xi_symq_kj_resultant_fibonacci_binomial_product
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  ∏ i ∈ Finset.range (q + 1), (Nat.choose q i : ℤ)

/-- The grouped spectral-difference product after the Binet cancellation. -/
def xi_symq_kj_resultant_fibonacci_spectral_difference_product
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  ∏ k ∈ Finset.range q,
    ((xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) : ℤ) ^ 2) ^ (q - k)

/-- The same grouped product with the square absorbed into the Fibonacci exponent. -/
def xi_symq_kj_resultant_fibonacci_fibonacci_product
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  ∏ k ∈ Finset.range q,
    (xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) : ℤ) ^
      (2 * (q - k))

/-- The Sylvester-resultant sign dictated by the rank-one coupling formula. -/
def xi_symq_kj_resultant_fibonacci_resultant_sign
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  (-1 : ℤ) ^ (((q + 1) * (q + 2)) / 2)

/-- Resultant obtained from the spectral-difference product identity. -/
def xi_symq_kj_resultant_fibonacci_resultant_from_spectral_product
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  xi_symq_kj_resultant_fibonacci_resultant_sign q *
    xi_symq_kj_resultant_fibonacci_binomial_product q *
      xi_symq_kj_resultant_fibonacci_spectral_difference_product q

/-- Closed Fibonacci factorization of the rank-one `K,J` resultant. -/
def xi_symq_kj_resultant_fibonacci_closed_resultant
    (q : xi_symq_kj_resultant_fibonacci_data) : ℤ :=
  xi_symq_kj_resultant_fibonacci_resultant_sign q *
    xi_symq_kj_resultant_fibonacci_binomial_product q *
      xi_symq_kj_resultant_fibonacci_fibonacci_product q

/-- Concrete resultant formula for all symmetric powers `q ≥ 2`. -/
def xi_symq_kj_resultant_fibonacci_resultant_formula
    (D : xi_symq_kj_resultant_fibonacci_data) : Prop :=
  2 ≤ D →
    xi_symq_kj_resultant_fibonacci_resultant_from_spectral_product D =
        xi_symq_kj_resultant_fibonacci_closed_resultant D ∧
      xi_symq_kj_resultant_fibonacci_spectral_difference_product D =
        xi_symq_kj_resultant_fibonacci_fibonacci_product D

end xi_symq_kj_resultant_fibonacci_data

open xi_symq_kj_resultant_fibonacci_data

/-- Paper label: `thm:xi-symq-kj-resultant-fibonacci`. -/
theorem paper_xi_symq_kj_resultant_fibonacci (D : xi_symq_kj_resultant_fibonacci_data) :
    D.xi_symq_kj_resultant_fibonacci_resultant_formula := by
  intro _hD
  have hspectral :
      xi_symq_kj_resultant_fibonacci_spectral_difference_product D =
        xi_symq_kj_resultant_fibonacci_fibonacci_product D := by
    unfold xi_symq_kj_resultant_fibonacci_spectral_difference_product
      xi_symq_kj_resultant_fibonacci_fibonacci_product
    refine Finset.prod_congr rfl ?_
    intro k _hk
    rw [← pow_mul]
  refine ⟨?_, hspectral⟩
  unfold xi_symq_kj_resultant_fibonacci_resultant_from_spectral_product
    xi_symq_kj_resultant_fibonacci_closed_resultant
  rw [hspectral]

end Omega.Zeta
