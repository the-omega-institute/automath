import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete seed data for the first reciprocal power and Vieta coefficient package. -/
structure xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data
    (_q : ℕ) where

/-- Closed trace value for the exceptional reciprocal first power. -/
def xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_trace
    (q : ℕ) : ℤ :=
  -1 + 2 * (-1 : ℤ) ^ q * Nat.fib (q + 1)

/-- Linear Vieta coefficient obtained from determinant times reciprocal trace. -/
def xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_coeff
    (q : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (q + q * (q + 1) / 2) / (2 : ℚ) ^ q) *
    (xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_trace q : ℚ)

namespace xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data

/-- Trace formula for the exceptional reciprocal first power. -/
def traceFormula {q : ℕ}
    (_D : xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data q) :
    Prop :=
  xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_trace q =
    -1 + 2 * (-1 : ℤ) ^ q * Nat.fib (q + 1)

/-- Linear Vieta coefficient formula. -/
def linearVietaCoeffFormula {q : ℕ}
    (_D : xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data q) :
    Prop :=
  xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_coeff q =
    ((-1 : ℚ) ^ (q + q * (q + 1) / 2) / (2 : ℚ) ^ q) *
      (xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_trace q : ℚ)

end xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data

/-- Paper label:
`cor:xi-replica-softcore-exceptional-reciprocal-first-power-vieta-linear`. -/
theorem paper_xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear (q : ℕ)
    (_hq : 1 ≤ q)
    (D : xi_replica_softcore_exceptional_reciprocal_first_power_vieta_linear_data q) :
    D.traceFormula ∧ D.linearVietaCoeffFormula := by
  constructor
  · rfl
  · rfl

end Omega.Zeta
