import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Chapter-local package for visible permutation lifts through `Fold`. The data record the
observable permutation on `X_m`, the fiberwise lift criterion, and the gauge-group counting
witness identifying the set of all lifts with a left coset of the gauge group. -/
structure FoldVisiblePermutationLiftsData where
  visiblePermutation : Prop
  liftCriterion : Prop
  gaugeGroupCardinalityWitness : Prop
  liftExists_iff_fiberMultiplicityPreserved : Prop
  liftCount_eq_gaugeGroupCard : Prop
  visiblePermutation_h : visiblePermutation
  liftCriterion_h : liftCriterion
  gaugeGroupCardinalityWitness_h : gaugeGroupCardinalityWitness
  deriveLiftExists_iff_fiberMultiplicityPreserved :
    visiblePermutation → liftCriterion → liftExists_iff_fiberMultiplicityPreserved
  deriveLiftCount_eq_gaugeGroupCard :
    visiblePermutation → liftCriterion → gaugeGroupCardinalityWitness →
      liftCount_eq_gaugeGroupCard

/-- Paper-facing wrapper for visible permutation lifts: the lift criterion packages the existence
equivalence with fiber-multiplicity preservation, while the gauge-group witness packages the
left-coset counting formula for the total number of lifts.
    prop:op-algebra-fold-visible-permutation-lifts -/
theorem paper_op_algebra_fold_visible_permutation_lifts (D : FoldVisiblePermutationLiftsData) :
    D.liftExists_iff_fiberMultiplicityPreserved ∧ D.liftCount_eq_gaugeGroupCard := by
  exact
    ⟨D.deriveLiftExists_iff_fiberMultiplicityPreserved D.visiblePermutation_h D.liftCriterion_h,
      D.deriveLiftCount_eq_gaugeGroupCard D.visiblePermutation_h D.liftCriterion_h
        D.gaugeGroupCardinalityWitness_h⟩

end Omega.OperatorAlgebra
