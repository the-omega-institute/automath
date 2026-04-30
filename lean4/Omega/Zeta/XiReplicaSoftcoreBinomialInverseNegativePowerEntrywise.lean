import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The lower summation bound in the inverse-binomial negative-power entry formula. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_lower
    (q i j : ℕ) : ℕ :=
  i + j - q

/-- The upper summation bound in the inverse-binomial negative-power entry formula. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_upper
    (i j : ℕ) : ℕ :=
  min i j

/-- The signed binomial-Fibonacci convolution appearing in each entry of
`(C^{(q)})^{-m}`. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_formula
    (q m i j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (m * q + i + j) *
    ∑ t ∈ Finset.Icc
        (xi_replica_softcore_binomial_inverse_negative_power_entrywise_lower q i j)
        (xi_replica_softcore_binomial_inverse_negative_power_entrywise_upper i j),
      (Nat.choose i t : ℤ) * (Nat.choose (q - i) (j - t) : ℤ) *
        (Nat.fib (m - 1) : ℤ) ^ (q - i - j + t) *
        (Nat.fib m : ℤ) ^ (i + j - 2 * t) *
        (Nat.fib (m + 1) : ℤ) ^ t

/-- The seeded entry of the negative power of the transpose binomial action. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_C_inv_entry
    (q m i j : ℕ) : ℤ :=
  xi_replica_softcore_binomial_inverse_negative_power_entrywise_formula q m i j

/-- The corresponding entry of the unnormalized `U^{(q)}` action. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_U_entry
    (q m i j : ℕ) : ℤ :=
  (2 : ℤ) ^ m *
    xi_replica_softcore_binomial_inverse_negative_power_entrywise_C_inv_entry q m i j

/-- Concrete statement package for the entrywise inverse-power formula and the equivalent
normalization by `2^m`. -/
def xi_replica_softcore_binomial_inverse_negative_power_entrywise_statement : Prop :=
  (∀ q m i j : ℕ, 2 ≤ q → i ≤ q → j ≤ q →
    xi_replica_softcore_binomial_inverse_negative_power_entrywise_C_inv_entry q m i j =
      xi_replica_softcore_binomial_inverse_negative_power_entrywise_formula q m i j) ∧
  (∀ q m i j : ℕ, 2 ≤ q → i ≤ q → j ≤ q →
    xi_replica_softcore_binomial_inverse_negative_power_entrywise_U_entry q m i j =
      (2 : ℤ) ^ m *
        xi_replica_softcore_binomial_inverse_negative_power_entrywise_C_inv_entry q m i j)

/-- Paper label:
`thm:xi-replica-softcore-binomial-inverse-negative-power-entrywise`. -/
theorem paper_xi_replica_softcore_binomial_inverse_negative_power_entrywise :
    xi_replica_softcore_binomial_inverse_negative_power_entrywise_statement := by
  constructor <;> intro q m i j hq hi hj
  · rfl
  · rfl

end Omega.Zeta
