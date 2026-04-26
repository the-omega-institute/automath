import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- Concrete data for the Hausdorff-dimension monotonicity argument. The singular support sits
inside the nonanalytic set, and `dimH` is any monotone dimension functional on subsets of the
ambient space. -/
structure SingularHairHausdorffLowerBoundData where
  α : Type
  singularSupport : Set α
  nonanalyticSet : Set α
  dimH : Set α → ℝ
  singularSupport_subset_nonanalytic : singularSupport ⊆ nonanalyticSet
  dimH_mono : Monotone dimH

/-- Paper label: `con:discussion-singular-hair-hausdorff-lower-bound`. Inclusion of the singular
support in the nonanalytic set and monotonicity of Hausdorff dimension give the claimed lower
bound immediately. -/
theorem paper_discussion_singular_hair_hausdorff_lower_bound
    (D : SingularHairHausdorffLowerBoundData) :
    D.singularSupport ⊆ D.nonanalyticSet ∧
      D.dimH D.singularSupport ≤ D.dimH D.nonanalyticSet := by
  exact ⟨D.singularSupport_subset_nonanalytic, D.dimH_mono D.singularSupport_subset_nonanalytic⟩

end Omega.Discussion
