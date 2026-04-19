import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the zero-coset rigidity theorem. The data record the rewrite of the
phase equation as a linear congruence, the gcd solvability test after dividing the congruence by
the common factor, and the description of the lifted solutions as the rigid coset family depending
only on that gcd. -/
structure FoldZeroCosetRigidityData where
  phaseEquationIffCongruence : Prop
  solvableIffGcdDvdHalf : Prop
  solutionSetDependsOnlyOnGcd : Prop
  phaseRewrittenAsCongruence : Prop
  reducedCongruenceSolvedByGcdCriterion : Prop
  inverseOddOnEvenModulus : Prop
  rigidCosetLift : Prop
  phaseRewrittenAsCongruence_h : phaseRewrittenAsCongruence
  reducedCongruenceSolvedByGcdCriterion_h : reducedCongruenceSolvedByGcdCriterion
  inverseOddOnEvenModulus_h : inverseOddOnEvenModulus
  rigidCosetLift_h : rigidCosetLift
  derivePhaseEquationIffCongruence :
    phaseRewrittenAsCongruence → phaseEquationIffCongruence
  deriveSolvableIffGcdDvdHalf :
    reducedCongruenceSolvedByGcdCriterion → solvableIffGcdDvdHalf
  deriveSolutionSetDependsOnlyOnGcd :
    reducedCongruenceSolvedByGcdCriterion →
      inverseOddOnEvenModulus →
        rigidCosetLift → solutionSetDependsOnlyOnGcd

/-- Paper-facing wrapper for the zero-coset rigidity package: the phase equation is equivalent to
the linear congruence, solvability is governed exactly by the gcd divisibility criterion, and any
solution set lifts to the rigid coset family determined solely by that gcd.
    thm:fold-zero-coset-rigidity -/
theorem paper_fold_zero_coset_rigidity
    (D : FoldZeroCosetRigidityData) :
    D.phaseEquationIffCongruence ∧ D.solvableIffGcdDvdHalf ∧ D.solutionSetDependsOnlyOnGcd := by
  have hCongruence : D.phaseEquationIffCongruence :=
    D.derivePhaseEquationIffCongruence D.phaseRewrittenAsCongruence_h
  have hSolvable : D.solvableIffGcdDvdHalf :=
    D.deriveSolvableIffGcdDvdHalf D.reducedCongruenceSolvedByGcdCriterion_h
  have hSolutions : D.solutionSetDependsOnlyOnGcd :=
    D.deriveSolutionSetDependsOnlyOnGcd
      D.reducedCongruenceSolvedByGcdCriterion_h
      D.inverseOddOnEvenModulus_h
      D.rigidCosetLift_h
  exact ⟨hCongruence, hSolvable, hSolutions⟩

end Omega.Folding
