import Omega.Core.Fib

namespace Omega

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Fibonacci-value witness used in the local
parallel lower-bound argument for Zeckendorf normalization.
    thm:zeckendorf-parallel-propagation-lower-bound -/
theorem paper_zeckendorf_parallel_propagation_lower_bound
    (n : Nat) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) = Nat.fib (2 * n + 1) - 1) ∧
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) + Nat.fib 2 = Nat.fib (2 * n + 1)) :=
  paper_parallel_propagation_value_pair n hn

end Omega
