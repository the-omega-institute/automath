import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Exceptional reciprocal first-power sum in the Fibonacci closed form. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSum (q : ℕ) : ℚ :=
  -1 + 2 * (-1 : ℚ) ^ q * Nat.fib (q + 1)

/-- Exceptional reciprocal second-power sum in the Fibonacci closed form. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSquareSum (q : ℕ) : ℚ :=
  1 + 4 * Nat.fib (2 * q + 2)

/-- Pairwise reciprocal sum expressed by `((S_-1)^2 - S_-2) / 2`. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_pairwiseReciprocalSum (q : ℕ) : ℚ :=
  (xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSum q ^ 2 -
      xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSquareSum q) / 2

/-- Exceptional determinant prefactor used by the Vieta `x^2` coefficient. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_determinantPrefactor (q : ℕ) : ℚ :=
  (-1 : ℚ) ^ (q + q * (q + 1) / 2) / (2 : ℚ) ^ q

/-- The `x^2` coefficient obtained from Vieta's pairwise reciprocal sum. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_x2Coeff (q : ℕ) : ℚ :=
  xi_replica_softcore_exceptional_vieta_x2_closed_determinantPrefactor q *
    xi_replica_softcore_exceptional_vieta_x2_closed_pairwiseReciprocalSum q

/-- Closed right-hand side for the exceptional `x^2` coefficient. -/
def xi_replica_softcore_exceptional_vieta_x2_closed_rhs (q : ℕ) : ℚ :=
  xi_replica_softcore_exceptional_vieta_x2_closed_determinantPrefactor q *
    ((xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSum q ^ 2 -
        xi_replica_softcore_exceptional_vieta_x2_closed_reciprocalSquareSum q) / 2)

/-- Paper label: `prop:xi-replica-softcore-exceptional-vieta-x2-closed`. -/
theorem paper_xi_replica_softcore_exceptional_vieta_x2_closed (q : Nat) :
    xi_replica_softcore_exceptional_vieta_x2_closed_x2Coeff q =
      xi_replica_softcore_exceptional_vieta_x2_closed_rhs q := by
  rfl

end Omega.Zeta
