import Omega.Folding.Rewrite

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Fibonacci local-weight rigidity lemma in
the resolution-folding paper.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem paper_resolution_folding_local_weight_rigidity_fibonacci
    (w : Nat → Nat)
    (hadj : ∀ k, w k + w (k + 1) = w (k + 2))
    (hw0 : w 0 = 1) (hw1 : w 1 = 2) :
    ∀ k, w k = Nat.fib (k + 2) := by
  intro k
  simpa [Omega.Rewrite.digitWeight] using
    (Omega.Rewrite.weight_rigidity_fibonacci w hadj hw0 hw1 k)

/-- Paper label: `lem:fold-local-weight-rigidity-fibonacci`. -/
theorem paper_fold_local_weight_rigidity_fibonacci
    (w : Nat → Nat)
    (hadj : ∀ k, w k + w (k + 1) = w (k + 2))
    (hw0 : w 0 = 1) (hw1 : w 1 = 2) :
    ∀ k, w k = Nat.fib (k + 2) :=
  paper_resolution_folding_local_weight_rigidity_fibonacci w hadj hw0 hw1

end Omega.Folding
