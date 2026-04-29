import Omega.Zeta.XiTerminalReplicaSoftcoreExceptionalPowerSumM2ClosedForm

namespace Omega.Zeta

/-- Paper label: `thm:xi-replica-softcore-exceptional-power-sum-m2-complete-closed`. -/
theorem paper_xi_replica_softcore_exceptional_power_sum_m2_complete_closed (q : ℕ) :
    4 * xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q =
      (4 : ℚ) ^ q + 2 * 3 ^ q + Nat.fib (2 * q + 2) := by
  exact paper_xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form q

end Omega.Zeta
