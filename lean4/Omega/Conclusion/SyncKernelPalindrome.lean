import Omega.Graph.TransferMatrix

/-!
# Self-dual sync kernel palindrome law seed values

Column sums of A² for the golden-mean adjacency matrix, and
linear combination identities for the palindrome cumulant.
-/

namespace Omega.Conclusion

open Omega.Graph

/-- Palindrome seed values for the golden-mean sync kernel.
    Column sums of A²: col 0 → 3, col 1 → 2.
    Linear combination checks: 1·3 + 0·2 = 3, 0·3 + 1·2 = 2.
    thm:conclusion-selfdual-sync-kernel-finite-mirror-odd-cumulant -/
theorem paper_conclusion_sync_kernel_palindrome_seeds :
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 0 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 0 = 3 ∧
    (goldenMeanAdjacency * goldenMeanAdjacency) 0 1 +
      (goldenMeanAdjacency * goldenMeanAdjacency) 1 1 = 2 ∧
    1 * 3 + 0 * 2 = (3 : ℤ) ∧ 0 * 3 + 1 * 2 = (2 : ℤ) := by
  refine ⟨by native_decide, by native_decide, by ring, by ring⟩

end Omega.Conclusion
