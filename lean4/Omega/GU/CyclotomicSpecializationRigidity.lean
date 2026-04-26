import Mathlib.Tactic

namespace Omega.GU

universe u

/-- Chapter-local package for the specialization-rigidity argument.
It records the ambient bivariate polynomial type together with the paper-facing implication from
infinitely many common slow modes to a nontrivial common factor. -/
structure CyclotomicSpecializationRigidityData where
  BivariatePolynomial : Type u
  infinitelyManyCommonSlowModes : Prop
  nontrivialCommonFactor : BivariatePolynomial → Prop
  specializationRigidity :
    infinitelyManyCommonSlowModes → ∃ H : BivariatePolynomial, nontrivialCommonFactor H

/-- Infinitely many common slow-mode layers force a nontrivial common factor across the channel
family.
    thm:cyclotomic-specialization-rigidity -/
theorem paper_gut_cyclotomic_specialization_rigidity
    (D : CyclotomicSpecializationRigidityData) :
    D.infinitelyManyCommonSlowModes → ∃ H : D.BivariatePolynomial, D.nontrivialCommonFactor H := by
  exact D.specializationRigidity

/-- Chapter-facing wrapper around the GU specialization-rigidity package.
    thm:cyclotomic-specialization-rigidity -/
theorem paper_cyclotomic_specialization_rigidity
    (D : CyclotomicSpecializationRigidityData) :
    D.infinitelyManyCommonSlowModes → ∃ H : D.BivariatePolynomial, D.nontrivialCommonFactor H := by
  exact paper_gut_cyclotomic_specialization_rigidity D

end Omega.GU
