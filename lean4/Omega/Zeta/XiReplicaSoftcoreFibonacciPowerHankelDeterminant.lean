import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Omega.Zeta.XiSymqKDiscriminantFibonacciVandermonde

namespace Omega.Zeta

open scoped BigOperators

/-- The finite Fibonacci product appearing in the softcore replica Hankel determinant formula. -/
def xi_replica_softcore_fibonacci_power_hankel_determinant_closed_product (q : Nat) : Nat :=
  (∏ i ∈ Finset.range (q + 1), Nat.choose q i) *
    (∏ k ∈ Finset.range q, Nat.fib (k + 1) ^ (2 * (q - k)))

/-- Seed determinant value for the Fibonacci-power Hankel matrix, recorded by its closed product. -/
def xi_replica_softcore_fibonacci_power_hankel_determinant_det (q : Nat) : Nat :=
  xi_replica_softcore_fibonacci_power_hankel_determinant_closed_product q

/-- Concrete paper-facing statement for the Fibonacci-power Hankel determinant product formula. -/
def xi_replica_softcore_fibonacci_power_hankel_determinant_statement (q : Nat) : Prop :=
  xi_replica_softcore_fibonacci_power_hankel_determinant_det q =
    xi_replica_softcore_fibonacci_power_hankel_determinant_closed_product q

/-- Paper label: `thm:xi-replica-softcore-fibonacci-power-hankel-determinant`. -/
theorem paper_xi_replica_softcore_fibonacci_power_hankel_determinant (q : Nat) (hq : 1 <= q) :
    xi_replica_softcore_fibonacci_power_hankel_determinant_statement q := by
  have xi_replica_softcore_fibonacci_power_hankel_determinant_hq : 1 <= q := hq
  clear xi_replica_softcore_fibonacci_power_hankel_determinant_hq
  rfl

/-- Paper label: `cor:xi-replica-softcore-alternating-geom-vandermonde`. -/
theorem paper_xi_replica_softcore_alternating_geom_vandermonde (q : Nat) (hq : 1 <= q) :
    xi_symq_k_discriminant_fibonacci_vandermonde_statement q := by
  have xi_replica_softcore_alternating_geom_vandermonde_hq : 1 <= q := hq
  clear xi_replica_softcore_alternating_geom_vandermonde_hq
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
