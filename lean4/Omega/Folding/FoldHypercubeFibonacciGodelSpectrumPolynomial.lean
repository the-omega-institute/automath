import Mathlib.Tactic
import Omega.Folding.FoldHypercubeFibonacciEpsEntropyUpper

namespace Omega.Folding

/-- Paper label: `cor:fold-hypercube-fibonacci-godel-spectrum-polynomial`.
This is the counting corollary obtained by unfolding the cutoff mode count into the Fibonacci
Godel radius family cardinality. -/
theorem paper_fold_hypercube_fibonacci_godel_spectrum_polynomial (R k : Nat)
    (hk : Nat.fib (k + 1) ≤ R ∧ R < Nat.fib (k + 2)) :
    2 ^ (k - 2) ≤ foldHypercubeFibonacciCutoffModeCount R ∧
      foldHypercubeFibonacciCutoffModeCount R ≤ 2 ^ k := by
  simpa [foldHypercubeFibonacciCutoffModeCount] using
    paper_fold_hypercube_fibonacci_godel_radius_count R k hk

end Omega.Folding
