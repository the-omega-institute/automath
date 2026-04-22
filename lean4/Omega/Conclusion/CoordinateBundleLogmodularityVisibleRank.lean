import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleKernelSlabDecomposition

namespace Omega.Conclusion

/-- The visible defect `Δₘ(J)` depends only on the number of hidden coordinates. -/
def conclusion_coordinate_bundle_logmodularity_visible_rank_delta (m n : Nat)
    (J : Finset (Fin n)) : Nat :=
  2 ^ (m * (n - J.card))

/-- The visible rank is total top-cell count minus the kernel rank. -/
def conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank (m n : Nat)
    (J : Finset (Fin n)) : Nat :=
  2 ^ (m * n) - conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n J

/-- Logmodularity of the coordinate-bundle defect and the resulting visible-rank formula. -/
theorem paper_conclusion_coordinate_bundle_logmodularity_visible_rank (m n : Nat)
    (J K : Finset (Fin n)) :
    conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n (J ∩ K) *
        conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n (J ∪ K) =
      conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n J *
        conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n K ∧
    conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J =
      2 ^ (m * n) - 2 ^ (m * (n - J.card)) := by
  refine ⟨?_, rfl⟩
  have hJ : J.card ≤ n := by simpa using J.card_le_univ
  have hK : K.card ≤ n := by simpa using K.card_le_univ
  have hI : (J ∩ K).card ≤ n := by simpa using (J ∩ K).card_le_univ
  have hU : (J ∪ K).card ≤ n := by simpa using (J ∪ K).card_le_univ
  have hcard : (J ∪ K).card + (J ∩ K).card = J.card + K.card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Finset.card_union_add_card_inter J K
  have hhidden :
      (n - (J ∩ K).card) + (n - (J ∪ K).card) = (n - J.card) + (n - K.card) := by
    omega
  have hexp :
      m * (n - (J ∩ K).card) + m * (n - (J ∪ K).card) =
        m * (n - J.card) + m * (n - K.card) := by
    calc
      m * (n - (J ∩ K).card) + m * (n - (J ∪ K).card) =
          m * ((n - (J ∩ K).card) + (n - (J ∪ K).card)) := by
            rw [Nat.left_distrib]
      _ = m * ((n - J.card) + (n - K.card)) := by rw [hhidden]
      _ = m * (n - J.card) + m * (n - K.card) := by rw [Nat.left_distrib]
  calc
    conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n (J ∩ K) *
        conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n (J ∪ K) =
      2 ^ (m * (n - (J ∩ K).card)) * 2 ^ (m * (n - (J ∪ K).card)) := by
        rfl
    _ = 2 ^ (m * (n - (J ∩ K).card) + m * (n - (J ∪ K).card)) := by
        rw [← Nat.pow_add]
    _ = 2 ^ (m * (n - J.card) + m * (n - K.card)) := by rw [hexp]
    _ = 2 ^ (m * (n - J.card)) * 2 ^ (m * (n - K.card)) := by
        rw [Nat.pow_add]
    _ =
        conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n J *
          conclusion_coordinate_bundle_logmodularity_visible_rank_delta m n K := by
        rfl

end Omega.Conclusion
