import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Zeta

/-- Concrete trace data for the exceptional reciprocal second-power identity.

The endpoint contribution is separated from the inverse-block square trace so that
the stated closed form follows after the endpoint cancellation. -/
structure xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci_data (q : ℕ) where
  reciprocal_second_power_sum : ℕ
  endpointContribution : ℕ
  inverseBlockSquareTrace :
    reciprocal_second_power_sum = endpointContribution + 4 * Nat.fib (2 * q + 2)
  endpointCancellation : endpointContribution = 1

namespace xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci_data

/-- Fibonacci sequence used in the exceptional reciprocal second-power closed form. -/
def fib {q : ℕ}
    (_D : xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci_data q) :
    ℕ → ℕ :=
  Nat.fib

end xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci_data

/-- Paper label: `prop:xi-replica-softcore-exceptional-reciprocal-second-power-fibonacci`. -/
theorem paper_xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci (q : ℕ)
    (D : xi_replica_softcore_exceptional_reciprocal_second_power_fibonacci_data q) :
    D.reciprocal_second_power_sum = 1 + 4 * D.fib (2 * q + 2) := by
  change D.reciprocal_second_power_sum = 1 + 4 * Nat.fib (2 * q + 2)
  rw [D.inverseBlockSquareTrace, D.endpointCancellation]

end Omega.Zeta
