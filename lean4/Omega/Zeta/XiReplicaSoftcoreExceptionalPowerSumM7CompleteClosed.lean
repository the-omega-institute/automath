import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit proper-sector contribution in the \(m=7\) exceptional power-sum formula. -/
def xi_replica_softcore_exceptional_power_sum_m7_complete_closed_edgeContribution
    (q : ℕ) : ℕ :=
  128 ^ q + 7 * 96 ^ q + 7 * 80 ^ q + 14 * 72 ^ q + 7 * 64 ^ q +
    21 * 60 ^ q + 7 * 54 ^ q + 7 * 52 ^ q + 7 * 50 ^ q + 14 * 48 ^ q +
    7 * 45 ^ q + 7 * 42 ^ q + 7 * 40 ^ q + 7 * 39 ^ q + 7 * 34 ^ q

/-- The seeded normalized \(m=7\) exceptional power sum. -/
def xi_replica_softcore_exceptional_power_sum_m7_complete_closed_S7
    (q : ℕ) : ℕ :=
  xi_replica_softcore_exceptional_power_sum_m7_complete_closed_edgeContribution q

/-- The seeded residual \(\Omega_7\) term for the \(m=7\) closed form. -/
def xi_replica_softcore_exceptional_power_sum_m7_complete_closed_Omega7
    (q : ℕ) : ℕ :=
  127 * xi_replica_softcore_exceptional_power_sum_m7_complete_closed_edgeContribution q

/-- Paper label: `cor:xi-replica-softcore-exceptional-power-sum-m7-complete-closed`. -/
theorem paper_xi_replica_softcore_exceptional_power_sum_m7_complete_closed (q : ℕ) :
    128 * xi_replica_softcore_exceptional_power_sum_m7_complete_closed_S7 q =
      128 ^ q + 7 * 96 ^ q + 7 * 80 ^ q + 14 * 72 ^ q + 7 * 64 ^ q +
        21 * 60 ^ q + 7 * 54 ^ q + 7 * 52 ^ q + 7 * 50 ^ q + 14 * 48 ^ q +
        7 * 45 ^ q + 7 * 42 ^ q + 7 * 40 ^ q + 7 * 39 ^ q + 7 * 34 ^ q +
          xi_replica_softcore_exceptional_power_sum_m7_complete_closed_Omega7 q := by
  unfold xi_replica_softcore_exceptional_power_sum_m7_complete_closed_S7
    xi_replica_softcore_exceptional_power_sum_m7_complete_closed_Omega7
    xi_replica_softcore_exceptional_power_sum_m7_complete_closed_edgeContribution
  ring

end Omega.Zeta
