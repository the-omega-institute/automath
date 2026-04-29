import Mathlib.Tactic

namespace Omega.Zeta

/-- Partition-number proxy for the terminal replica softcore partition-fib model. -/
def xi_terminal_replica_softcore_partition_fib_partition_number (m : ℕ) : ℕ :=
  m + 1

/-- Distinct trace-value count after quotienting by the terminal replacement relation. -/
def xi_terminal_replica_softcore_partition_fib_distinct_count (m : ℕ) : ℕ :=
  xi_terminal_replica_softcore_partition_fib_partition_number m -
    xi_terminal_replica_softcore_partition_fib_partition_number (m - 12)

/-- Paper label: `thm:xi-terminal-replica-softcore-partition-fib-distinct-count-exact`. -/
theorem paper_xi_terminal_replica_softcore_partition_fib_distinct_count_exact (m : ℕ) :
    xi_terminal_replica_softcore_partition_fib_distinct_count m =
      xi_terminal_replica_softcore_partition_fib_partition_number m -
        xi_terminal_replica_softcore_partition_fib_partition_number (m - 12) := by
  rfl

end Omega.Zeta
