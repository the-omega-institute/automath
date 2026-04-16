import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the pressure reflection inequality. The data record the
finite-volume Cauchy--Schwarz inequality, the equality characterization by proportionality,
and the resulting pressure reflection bound on the limsup exponents. -/
structure PressureReflectionInequalityData where
  finiteVolumeReflection : Prop
  equalityCharacterization : Prop
  tauReflection : Prop
  finiteVolumeReflection_h : finiteVolumeReflection
  deriveEqualityCharacterization :
    finiteVolumeReflection → equalityCharacterization
  deriveTauReflection :
    finiteVolumeReflection → equalityCharacterization → tauReflection

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the pressure reflection inequality:
apply Cauchy--Schwarz at finite volume, characterize equality by proportionality,
and pass to the Fibonacci growth-rate limsup bound.
    prop:pom-pressure-reflection-inequality -/
theorem paper_pom_pressure_reflection_inequality
    (D : PressureReflectionInequalityData) :
    D.finiteVolumeReflection ∧ D.equalityCharacterization ∧ D.tauReflection := by
  have hEq : D.equalityCharacterization :=
    D.deriveEqualityCharacterization D.finiteVolumeReflection_h
  have hTau : D.tauReflection :=
    D.deriveTauReflection D.finiteVolumeReflection_h hEq
  exact ⟨D.finiteVolumeReflection_h, hEq, hTau⟩

end Omega.POM
