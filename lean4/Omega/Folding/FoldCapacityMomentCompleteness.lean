import Mathlib.Tactic
import Omega.Folding.OracleCapacityTailEquivalence
import Omega.Folding.OracleCapacityTailMoments

namespace Omega.Folding

/-- Capacity-side completeness package: the continuous capacity curve is equivalent to the tail
profile via the layer-cake identity. -/
def fold_capacity_moment_completeness_capacity_side (m : ℕ) : Prop :=
  FoldCapacityTailEquivalenceStatement m

/-- Moment-side completeness package: the audited first moment is recovered by the Mellin-Stieltjes
tail integral. -/
def fold_capacity_moment_completeness_moment_side (m : ℕ) : Prop :=
  FoldMomentMellinStieltjesStatement m 1

/-- Concrete two-way completeness statement tying together the capacity-tail and moment
reconstruction packages. -/
def fold_capacity_moment_completeness_statement (m : ℕ) : Prop :=
  fold_capacity_moment_completeness_capacity_side m ∧
    fold_capacity_moment_completeness_moment_side m ∧
    (fold_capacity_moment_completeness_capacity_side m ↔
      fold_capacity_moment_completeness_moment_side m)

/-- Paper label: `cor:fold-capacity-moment-completeness`. The audited continuous capacity profile
and the Mellin-Stieltjes moment reconstruction are both available, so each side is sufficient for
the same concrete finite-support completeness package. -/
theorem paper_fold_capacity_moment_completeness (m : ℕ) :
    fold_capacity_moment_completeness_statement m := by
  have hCapacity : fold_capacity_moment_completeness_capacity_side m :=
    paper_fold_capacity_tail_equivalence m
  have hMoment : fold_capacity_moment_completeness_moment_side m :=
    paper_fold_moment_mellin_stieltjes m
  refine ⟨hCapacity, hMoment, ?_⟩
  constructor
  · intro _
    exact hMoment
  · intro _
    exact hCapacity

end Omega.Folding
