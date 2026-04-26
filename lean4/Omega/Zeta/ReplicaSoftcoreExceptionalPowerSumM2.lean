import Omega.Zeta.XiTerminalReplicaSoftcoreExceptionalPowerSumM2ClosedForm

namespace Omega.Zeta

/-- The `m = 2` exceptional power sum in the Fibonacci-closed normalization. -/
def xi_terminal_replica_softcore_exceptional_power_sum_m2_fibonacci_closed_S2 (q : ℕ) : ℚ :=
  xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q

/-- Paper label:
`cor:xi-terminal-replica-softcore-exceptional-power-sum-m2-fibonacci-closed`. -/
theorem paper_xi_terminal_replica_softcore_exceptional_power_sum_m2_fibonacci_closed
    (q : ℕ) (_hq : 2 ≤ q) :
    xi_terminal_replica_softcore_exceptional_power_sum_m2_fibonacci_closed_S2 q =
      (((4 : ℚ) ^ q + 2 * (3 : ℚ) ^ q + (Nat.fib (2 * q + 2) : ℚ)) / 4) := by
  have hclosed := paper_xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form q
  unfold xi_terminal_replica_softcore_exceptional_power_sum_m2_fibonacci_closed_S2
  calc
    xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q =
        (4 * xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q) / 4 := by
          ring
    _ = (((4 : ℚ) ^ q + 2 * (3 : ℚ) ^ q + (Nat.fib (2 * q + 2) : ℚ)) / 4) := by
          rw [hclosed]

end Omega.Zeta
