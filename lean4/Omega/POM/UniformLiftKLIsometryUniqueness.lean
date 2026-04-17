import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local certificate package for the uniform-lift KL isometry and uniqueness statement.
The fields isolate the finite-surjection witness, the fiberwise expansion/collapse used for the
isometry, and the Dirac/support/two-point checks used to force uniqueness of the affine section. -/
structure UniformLiftKlIsometryUniquenessData where
  isometry : Prop
  uniqueness : Prop
  finiteSurjectionWitness : Prop
  fiberwiseUniformLiftExpansion : Prop
  innerFiberSumCollapse : Prop
  diracMassSectionTest : Prop
  pushforwardSupportSeparation : Prop
  twoPointMixtureKlPreservation : Prop
  finiteSurjectionWitness_h : finiteSurjectionWitness
  fiberwiseUniformLiftExpansion_h : fiberwiseUniformLiftExpansion
  innerFiberSumCollapse_h : innerFiberSumCollapse
  diracMassSectionTest_h : diracMassSectionTest
  pushforwardSupportSeparation_h : pushforwardSupportSeparation
  twoPointMixtureKlPreservation_h : twoPointMixtureKlPreservation
  deriveIsometry :
    finiteSurjectionWitness →
      fiberwiseUniformLiftExpansion → innerFiberSumCollapse → isometry
  deriveUniqueness :
    finiteSurjectionWitness →
      diracMassSectionTest →
        pushforwardSupportSeparation → twoPointMixtureKlPreservation → uniqueness

/-- Paper-facing wrapper for the uniform-lift KL isometry and its uniqueness characterization.
    thm:pom-uniform-lift-kl-isometry-uniqueness -/
theorem paper_pom_uniform_lift_kl_isometry_uniqueness
    (h : UniformLiftKlIsometryUniquenessData) : h.isometry ∧ h.uniqueness := by
  have hIsometry : h.isometry :=
    h.deriveIsometry h.finiteSurjectionWitness_h h.fiberwiseUniformLiftExpansion_h
      h.innerFiberSumCollapse_h
  have hUniqueness : h.uniqueness :=
    h.deriveUniqueness h.finiteSurjectionWitness_h h.diracMassSectionTest_h
      h.pushforwardSupportSeparation_h h.twoPointMixtureKlPreservation_h
  exact ⟨hIsometry, hUniqueness⟩

end Omega.POM
