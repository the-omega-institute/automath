import Omega.POM.ReplicaSoftcoreAlternatingVandermondeFibonacciProduct

namespace Omega.POM

open scoped BigOperators

/-- Concrete field-norm statement for the node discriminant.  The Vandermonde certificate
identifies the discriminant with the displayed Fibonacci product, and the quadratic-field norm
of that integer is its square. -/
def pom_replica_softcore_node_discriminant_field_norm_statement (q : ℕ) : Prop :=
  ∀ (disc discNorm : ℤ),
    disc =
        (5 : ℤ) ^ (q * (q + 1) / 2) *
          ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (2 * (q + 1 - d)) →
    discNorm = disc ^ 2 →
    discNorm =
      (5 : ℤ) ^ (q * (q + 1)) *
        ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (4 * (q + 1 - d))

/-- Paper label: `prop:pom-replica-softcore-node-discriminant-field-norm`. -/
theorem paper_pom_replica_softcore_node_discriminant_field_norm (q : ℕ) :
    pom_replica_softcore_node_discriminant_field_norm_statement q := by
  intro disc discNorm
    (hvand :
      disc =
        (5 : ℤ) ^ (q * (q + 1) / 2) *
          ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (2 * (q + 1 - d))) hnorm
  have htwo :
      2 * (q * (q + 1) / 2) = q * (q + 1) := by
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self q)
  calc
    discNorm = disc ^ 2 := hnorm
    _ =
        ((5 : ℤ) ^ (q * (q + 1) / 2) *
          ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (2 * (q + 1 - d))) ^ 2 := by
          rw [hvand]
    _ =
        (5 : ℤ) ^ ((q * (q + 1) / 2) * 2) *
          ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ ((2 * (q + 1 - d)) * 2) := by
          rw [mul_pow, ← Finset.prod_pow]
          simp_rw [pow_mul]
    _ =
        (5 : ℤ) ^ (q * (q + 1)) *
          ∏ d ∈ Finset.Icc 1 q, (Nat.fib d : ℤ) ^ (4 * (q + 1 - d)) := by
          have htwo' : q * (q + 1) / 2 * 2 = q * (q + 1) := by omega
          rw [htwo']
          congr 1
          apply Finset.prod_congr rfl
          intro d hd
          congr 1
          omega

end Omega.POM
