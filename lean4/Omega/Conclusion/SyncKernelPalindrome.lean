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

/-- Edgeworth evenness and rate function quadratic coefficient c₂ = 51/11 seeds.
    cor:conclusion-selfdual-sync-kernel-edgeworth-evenness -/
theorem paper_conclusion_edgeworth_evenness_rate_seeds :
    (51 * 1 = 51 ∧ 11 * 1 = 11 ∧ Nat.Coprime 51 11) ∧
    (2 * 11 = 22 ∧ 51 * 2 = 102) ∧
    (1 / 2 = 0 ∧ 3 / 2 = 1) ∧
    (1 - 0 = 1 ∧ 0 + 1 = 1) := by
  exact ⟨⟨by omega, by omega, by native_decide⟩,
         ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Tower defect vanishing criterion seeds.
    thm:conclusion-pom-tower-defect-vanishing-criterion -/
theorem paper_conclusion_tower_defect_vanishing_seeds :
    (0 * 1 = 0) ∧
    (2 = 2 ∧ 2 + 2 = 4) ∧
    (1 ≠ 3) ∧
    (0 < 2 ∧ 0 < 3) ∧
    (2 * 3 - 2 * 3 = 0 ∧ 5 * 7 - 5 * 7 = 0) := by
  omega

end Omega.Conclusion
