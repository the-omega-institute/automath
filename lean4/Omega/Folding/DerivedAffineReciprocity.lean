import Omega.Folding.FiberWeightCountComplement

namespace Omega

/-- Paper-facing wrapper for the affine reciprocity involution
`r ↦ F_{m+1} - 2 - r` on the fold fiber count spectrum.
    thm:derived-fold-affine-reciprocity -/
theorem paper_derived_fold_affine_reciprocity (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ Nat.fib (m + 1) - 2) :
    weightCongruenceCount m r = weightCongruenceCount m (Nat.fib (m + 1) - 2 - r) := by
  exact (paper_fold_fiber_count_reciprocity m hm r hr).2

end Omega
