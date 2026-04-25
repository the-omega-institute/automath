import Omega.Conclusion.CoordinateBundleLogmodularityVisibleRank
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing exact supplement statement: the visible rank misses exactly the defect
`2^(m * (n - |J|))`, every smaller supplement is still rank-deficient, and the slab coordinates
from the kernel decomposition achieve the bound. -/
def conclusion_relative_linear_holography_exact_supplement_dimension_statement
    (m n : Nat) (J : Finset (Fin n)) : Prop :=
  (∀ L : Nat,
      L < 2 ^ (m * (n - J.card)) →
        conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J + L <
          2 ^ (m * n)) ∧
    conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J +
        2 ^ (m * (n - J.card)) =
      2 ^ (m * n) ∧
    Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n J.card - 1 =
      2 ^ (m * (n - J.card))

/-- Paper label: `thm:conclusion-relative-linear-holography-exact-supplement-dimension`. -/
theorem paper_conclusion_relative_linear_holography_exact_supplement_dimension
    (m n : Nat) (J : Finset (Fin n)) :
    conclusion_relative_linear_holography_exact_supplement_dimension_statement m n J := by
  have hrank :
      conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J =
        2 ^ (m * n) - 2 ^ (m * (n - J.card)) :=
    (paper_conclusion_coordinate_bundle_logmodularity_visible_rank m n J J).2
  have hexp_le : m * (n - J.card) ≤ m * n := by
    exact Nat.mul_le_mul_left m (Nat.sub_le _ _)
  have hdef_le :
      2 ^ (m * (n - J.card)) ≤ 2 ^ (m * n) := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp_le
  have hsum :
      conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J +
        2 ^ (m * (n - J.card)) =
        2 ^ (m * n) := by
    rw [hrank]
    exact Nat.sub_add_cancel hdef_le
  refine ⟨?_, hsum, ?_⟩
  · intro L hL
    have hlt :
        conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J + L <
          conclusion_coordinate_bundle_logmodularity_visible_rank_visible_rank m n J +
            2 ^ (m * (n - J.card)) :=
      Nat.add_lt_add_left hL _
    simpa [hsum] using hlt
  · simpa using paper_conclusion_coordinate_bundle_kernel_slab_decomposition m n J.card

end Omega.Conclusion
