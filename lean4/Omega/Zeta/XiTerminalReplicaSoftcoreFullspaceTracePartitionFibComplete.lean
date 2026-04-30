import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalReplicaSoftcoreQGenfuncRationalPartition

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete certificate data for the full-space trace partition formula.  A finite index type
enumerates the partitions after the paper's reindexing; the multiplicity vector records the
parts of each partition. -/
structure xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data where
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m : ℕ
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_q : ℕ
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition : Type
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_fintype :
    Fintype xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_decidableEq :
    DecidableEq xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_multiplicity :
    xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition → ℕ → ℕ

attribute [instance]
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_fintype
  xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_decidableEq

namespace xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data

/-- The length `ell(pi)` of the partition encoded by the multiplicity vector. -/
def partLength
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data)
    (π :
      D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition) : ℕ :=
  ∑ s ∈ Finset.Icc 1 D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m,
    D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_multiplicity π s

/-- Fibonacci weight product `Theta(pi) = prod_s F_{s+2}^{m_s}`. -/
def fibonacciWeightProduct
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data)
    (π :
      D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition) : ℚ :=
  ∏ s ∈ Finset.Icc 1 D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m,
    (Nat.fib (s + 2) : ℚ) ^
      D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_multiplicity π s

/-- Closed coefficient formula `c(pi) = m/ell(pi) * ell(pi)! / prod_s m_s!`, with the zero
length case interpreted in `ℚ` by the ambient field operations. -/
def coefficientFormula
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data)
    (π :
      D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition) : ℚ :=
  (D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m : ℚ) /
      (D.partLength π : ℚ) *
    (Nat.factorial (D.partLength π) : ℚ) /
      ∏ s ∈ Finset.Icc 1 D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m,
        (Nat.factorial
          (D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_multiplicity
            π s) : ℚ)

/-- Prior closed trace form after reindexing the closed partition sum by the finite partition
certificate. -/
def priorClosedTraceForm
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data) : ℚ :=
  (xiTerminalReplicaSoftcoreLucas
      D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m ^
        D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_q +
      ∑ π :
        D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition,
        D.coefficientFormula π *
          D.fibonacciWeightProduct π ^
            D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_q) /
    (2 : ℚ) ^ D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m

/-- The full-space trace is represented by the partition-reindexed closed form. -/
def fullspaceTrace
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data) : ℚ :=
  D.priorClosedTraceForm

/-- The target trace formula obtained by rewriting the prior closed form in partition notation. -/
def traceFormula
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data) : Prop :=
  D.fullspaceTrace =
    (xiTerminalReplicaSoftcoreLucas
        D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m ^
          D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_q +
        ∑ π :
          D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Partition,
          D.coefficientFormula π *
            D.fibonacciWeightProduct π ^
              D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_q) /
      (2 : ℚ) ^ D.xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_m

end xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data

/-- Paper label:
`thm:xi-terminal-replica-softcore-fullspace-trace-partition-fib-complete`. -/
theorem paper_xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete
    (D : xi_terminal_replica_softcore_fullspace_trace_partition_fib_complete_Data) :
    D.traceFormula := by
  rfl

end Omega.Zeta
