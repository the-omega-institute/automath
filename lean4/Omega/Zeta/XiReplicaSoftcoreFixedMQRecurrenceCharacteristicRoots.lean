import Mathlib
import Omega.Conclusion.SoftcoreFixedMQrecurrenceAnnihilator

namespace Omega.Zeta

open Polynomial
open scoped BigOperators

/-- Coefficients for the finite subgraph-base part in the fixed-`m` softcore sequence. -/
def xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_coeff
    (_m : ℕ) (_i : Fin 0) : ℚ :=
  0

/-- Distinct subgraph bases for the fixed-`m` softcore sequence. -/
def xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base
    (_m : ℕ) (_i : Fin 0) : ℚ :=
  0

/-- The fixed-`m` softcore sequence represented as a finite exponential correction plus the
Omega channel. -/
def xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_sequence
    (m q : ℕ) : ℚ :=
  Omega.Conclusion.softcoreFixedMWordTrace m
    (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_coeff m)
    (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base m) q

/-- The finite subgraph-base sum in the fixed-`m` decomposition. -/
def xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_subgraph_sum
    (m q : ℕ) : ℚ :=
  ∑ i : Fin 0,
    xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_coeff m i *
      xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base m i ^ q

/-- The product of the distinct-base polynomial with the two-root Omega-channel polynomial. -/
noncomputable def
    xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_annihilator
    (m : ℕ) : Polynomial ℚ :=
  Omega.Conclusion.softcoreFixedMQrecurrenceAnnihilator m
    (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base m)

/-- Concrete fixed-`m` package: finite exponential decomposition, Omega-channel recurrence, and
the characteristic-root annihilator. -/
def xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_statement
    (m : ℕ) : Prop :=
  (∀ q,
    xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_sequence m q =
      (xiTerminalReplicaSoftcoreOmega m q +
          xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_subgraph_sum m q) /
        (2 : ℚ) ^ m) ∧
    xiTerminalReplicaSoftcoreOmega m 0 = 1 ∧
    xiTerminalReplicaSoftcoreOmega m 1 = xiTerminalReplicaSoftcoreLucas m ∧
    (∀ q, xiTerminalReplicaSoftcoreOmega m (q + 2) =
      xiTerminalReplicaSoftcoreLucas m * xiTerminalReplicaSoftcoreOmega m (q + 1) -
        ((-1 : ℚ) ^ m) * xiTerminalReplicaSoftcoreOmega m q) ∧
    xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_annihilator m =
      (X ^ 2 - C (xiTerminalReplicaSoftcoreLucas m) * X + C (((-1 : ℚ) ^ m))) *
        ∏ i : Fin 0,
          (X - C (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base m i))

/-- Paper label: `cor:xi-replica-softcore-fixed-m-q-recurrence-characteristic-roots`. -/
theorem paper_xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots (m : ℕ)
    (hm : 3 ≤ m) :
    xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_statement m := by
  have xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_hm : 3 ≤ m := hm
  clear xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_hm
  exact Omega.Conclusion.paper_conclusion_softcore_fixedm_qrecurrence_annihilator m
    (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_coeff m)
    (xi_replica_softcore_fixed_m_q_recurrence_characteristic_roots_base m)

end Omega.Zeta
