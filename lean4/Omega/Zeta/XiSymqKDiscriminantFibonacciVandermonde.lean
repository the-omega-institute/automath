import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Fibonacci numbers used by the symmetric-power Vandermonde factor. -/
def xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci n +
        xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (n + 1)

/-- The gap-`k` factor after reducing the symmetric-power spectral ratio by Binet. -/
def xi_symq_k_discriminant_fibonacci_vandermonde_gap_factor (k : ℕ) : ℕ :=
  5 * xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci k ^ 2

/-- Vandermonde factors grouped by their spectral gap. -/
def xi_symq_k_discriminant_fibonacci_vandermonde_gap_product (q : ℕ) : ℕ :=
  ∏ k ∈ Finset.range q,
    xi_symq_k_discriminant_fibonacci_vandermonde_gap_factor (k + 1) ^ (q - k)

/-- The same grouped product with the powers of `5` and Fibonacci factors separated. -/
def xi_symq_k_discriminant_fibonacci_vandermonde_closed_product (q : ℕ) : ℕ :=
  (∏ k ∈ Finset.range q, 5 ^ (q - k)) *
    ∏ k ∈ Finset.range q,
      xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) ^ (2 * (q - k))

/-- Concrete statement for the Fibonacci--Vandermonde discriminant factorization. -/
def xi_symq_k_discriminant_fibonacci_vandermonde_statement (q : ℕ) : Prop :=
  xi_symq_k_discriminant_fibonacci_vandermonde_gap_product q =
    xi_symq_k_discriminant_fibonacci_vandermonde_closed_product q

/-- Paper label: `thm:xi-symq-k-discriminant-fibonacci-vandermonde`. -/
theorem paper_xi_symq_k_discriminant_fibonacci_vandermonde (q : ℕ) (hq : 2 ≤ q) :
    xi_symq_k_discriminant_fibonacci_vandermonde_statement q := by
  have _q_nontrivial := hq
  unfold xi_symq_k_discriminant_fibonacci_vandermonde_statement
  unfold xi_symq_k_discriminant_fibonacci_vandermonde_gap_product
  unfold xi_symq_k_discriminant_fibonacci_vandermonde_closed_product
  unfold xi_symq_k_discriminant_fibonacci_vandermonde_gap_factor
  calc
    (∏ k ∈ Finset.range q,
        (5 * xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) ^ 2) ^
          (q - k))
        =
        ∏ k ∈ Finset.range q,
          (5 ^ (q - k)) *
            (xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) ^ 2) ^
              (q - k) := by
          refine Finset.prod_congr rfl ?_
          intro k _hk
          rw [mul_pow]
    _ =
        ∏ k ∈ Finset.range q,
          (5 ^ (q - k)) *
            xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) ^
              (2 * (q - k)) := by
          refine Finset.prod_congr rfl ?_
          intro k _hk
          rw [← pow_mul]
    _ =
        (∏ k ∈ Finset.range q, 5 ^ (q - k)) *
          ∏ k ∈ Finset.range q,
            xi_symq_k_discriminant_fibonacci_vandermonde_fibonacci (k + 1) ^
              (2 * (q - k)) := by
          rw [Finset.prod_mul_distrib]

end Omega.Zeta
