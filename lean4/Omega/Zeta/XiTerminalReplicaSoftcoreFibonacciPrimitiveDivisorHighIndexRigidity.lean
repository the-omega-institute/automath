import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-terminal-replica-softcore-fibonacci-primitive-divisor-high-index-rigidity`. -/
theorem paper_xi_terminal_replica_softcore_fibonacci_primitive_divisor_high_index_rigidity
    (A B : Multiset ℕ) (hcount : ∀ n, 12 < n → A.count n = B.count n) :
    A.filter (fun n => 12 < n) = B.filter (fun n => 12 < n) := by
  rw [Multiset.ext]
  intro n
  by_cases hn : 12 < n
  · simp [hn, hcount n hn]
  · simp [hn]

end Omega.Zeta
