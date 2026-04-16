import Omega.GU.CyclotomicSpecializationRigidity

namespace Omega.GU

/-- Chapter-local package for the specialization-gcd stability argument.  After factoring every
specialization through the common rigid part, an extra gcd on infinitely many cyclotomic levels
would force a nontrivial common factor for the residual family, contradicting residual-gcd
triviality. -/
structure CyclotomicGcdStabilityData extends CyclotomicSpecializationRigidityData where
  residualGcdTrivial : Prop
  extraGcdAtInfinitelyManyLevels : Prop
  extraGcdForcesInfinitelyManyCommonSlowModes :
    extraGcdAtInfinitelyManyLevels → infinitelyManyCommonSlowModes
  residualGcdExcludesNontrivialCommonFactor :
    residualGcdTrivial → ¬ ∃ H : BivariatePolynomial, nontrivialCommonFactor H

/-- Paper-facing wrapper for specialization-gcd stability: once the residual family has trivial
gcd, no extra common factor can appear on infinitely many cyclotomic levels.
    thm:cyclotomic-gcd-stability -/
theorem paper_gut_cyclotomic_gcd_stability (D : CyclotomicGcdStabilityData) :
    D.residualGcdTrivial → ¬ D.extraGcdAtInfinitelyManyLevels := by
  intro hResidual hExtra
  obtain ⟨H, hH⟩ :=
    paper_gut_cyclotomic_specialization_rigidity D.toCyclotomicSpecializationRigidityData
      (D.extraGcdForcesInfinitelyManyCommonSlowModes hExtra)
  exact (D.residualGcdExcludesNontrivialCommonFactor hResidual) ⟨H, hH⟩

end Omega.GU
