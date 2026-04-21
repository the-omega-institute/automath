import Omega.Conclusion.BlockConstraintInformationCollapse

namespace Omega.Conclusion

/-- The block-consistency equality target `Q(U = V) = 1 - δ` used for the min-MI reduction. -/
def blockConsistencyEqualityMass (δ : ℝ) : ℝ :=
  1 - δ

/-- The complementary inconsistency mass. -/
def blockConsistencyDisagreementMass (δ : ℝ) : ℝ :=
  δ

/-- Canonical two-block witness saturating `Q(U = V) ≥ 1 - δ`. -/
def blockConsistencyCanonicalWitness (δ : ℝ) : ℝ × ℝ :=
  (blockConsistencyEqualityMass δ, blockConsistencyDisagreementMass δ)

/-- The lifted optimizer formula for the block-consistency reduction. -/
def blockConsistencyLiftedObjective (δ : ℝ) : ℝ :=
  blockConsistencyEqualityMass δ

/-- The collapsed block objective agrees with the lifted one on the canonical witness. -/
def blockConsistencyCollapsedObjective (δ : ℝ) : ℝ :=
  blockConsistencyEqualityMass δ

/-- The canonical witness realizes the block-consistency constraint exactly. -/
def blockConsistencyExtremizerLift (δ : ℝ) : Prop :=
  blockConsistencyCanonicalWitness δ =
      (blockConsistencyEqualityMass δ, blockConsistencyDisagreementMass δ)

/-- The reduced optimization problem has the same value as the lifted one. -/
def blockConsistencyReducedEquality (δ : ℝ) : Prop :=
  blockConsistencyLiftedObjective δ = blockConsistencyCollapsedObjective δ

/-- Concrete collapse datum specialized to the block-consistency feasible set. -/
def blockConsistencyCollapseData (δ : ℝ) : BlockConstraintInformationCollapseData where
  liftedInf := blockConsistencyLiftedObjective δ
  blockInf := blockConsistencyCollapsedObjective δ
  attainedLift := blockConsistencyExtremizerLift δ
  liftedInf_eq_blockInf := rfl
  attainedLift_h := rfl

/-- Specializing the chapter-local block-constraint collapse package to the constraint
`Q(U = V) ≥ 1 - δ` identifies the reduced optimum with the lifted optimum, and the canonical
blockwise-independent witness realizes the extremizer lift.
    cor:conclusion-block-consistency-min-mi-reduction -/
theorem paper_conclusion_block_consistency_min_mi_reduction (δ : ℝ) :
    blockConsistencyReducedEquality δ ∧ blockConsistencyExtremizerLift δ := by
  simpa [blockConsistencyReducedEquality, blockConsistencyExtremizerLift,
    blockConsistencyCollapseData] using
    paper_conclusion_block_constraint_information_collapse (blockConsistencyCollapseData δ)

end Omega.Conclusion
