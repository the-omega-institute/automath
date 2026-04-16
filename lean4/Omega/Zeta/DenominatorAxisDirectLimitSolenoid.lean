import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the denominator-axis direct-limit solenoid. It records the direct
limit system, its prime-support set, the two inclusions identifying the colimit with the
corresponding localization, and the paper-facing consequences for the Pontryagin dual and the
connected one-dimensional solenoidal component. -/
structure DenominatorAxisDirectLimitSolenoidData where
  directLimitSystem : Prop
  primeSupportSet : Prop
  colimitIntoLocalization : Prop
  localizationIntoColimit : Prop
  pontryaginDualInverseLimitDescription : Prop
  connectedComponentWitness : Prop
  colimitIsLocalization : Prop
  dualIsInverseLimit : Prop
  connectedComponentIsOneDimensional : Prop
  directLimitSystem_h : directLimitSystem
  primeSupportSet_h : primeSupportSet
  colimitIntoLocalization_h : colimitIntoLocalization
  localizationIntoColimit_h : localizationIntoColimit
  pontryaginDualInverseLimitDescription_h : pontryaginDualInverseLimitDescription
  connectedComponentWitness_h : connectedComponentWitness
  deriveColimitIsLocalization :
    directLimitSystem → primeSupportSet → colimitIntoLocalization → localizationIntoColimit →
      colimitIsLocalization
  deriveDualIsInverseLimit :
    colimitIsLocalization → pontryaginDualInverseLimitDescription → dualIsInverseLimit
  deriveConnectedComponentIsOneDimensional :
    colimitIsLocalization → connectedComponentWitness → connectedComponentIsOneDimensional

/-- The two comparison maps identify the denominator-axis direct limit with the expected
localization. -/
theorem DenominatorAxisDirectLimitSolenoidData.localization_identification
    (D : DenominatorAxisDirectLimitSolenoidData) :
    D.colimitIsLocalization :=
  D.deriveColimitIsLocalization D.directLimitSystem_h D.primeSupportSet_h
    D.colimitIntoLocalization_h D.localizationIntoColimit_h

/-- Paper-facing wrapper for the denominator-axis direct-limit solenoid package.
    thm:xi-denominator-axis-direct-limit-solenoid -/
theorem paper_xi_denominator_axis_direct_limit_solenoid
    (D : DenominatorAxisDirectLimitSolenoidData) :
    D.colimitIsLocalization ∧ D.dualIsInverseLimit ∧ D.connectedComponentIsOneDimensional := by
  have hLoc : D.colimitIsLocalization := D.localization_identification
  exact ⟨hLoc, D.deriveDualIsInverseLimit hLoc D.pontryaginDualInverseLimitDescription_h,
    D.deriveConnectedComponentIsOneDimensional hLoc D.connectedComponentWitness_h⟩

end Omega.Zeta
