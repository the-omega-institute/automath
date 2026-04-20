import Mathlib.Tactic

namespace Omega.Multiscale

/-- Concrete data for realizing the limiting Stokes functional by a Radon measure on a solenoidal
inverse limit. The structure stores finite-level normalized masses, the cylinder masses of the
inverse-limit measure, the Stokes functional on top-degree forms, and its `L¹` extension. -/
structure SolenoidStokesRadonMeasureData where
  Level : Type
  TopDegreeForm : Type
  l1Completion : Type
  finiteLevelMass : Level → ℝ
  inverseLimitCylinderMass : Level → ℝ
  topDegreeIntegral : TopDegreeForm → ℝ
  stokesFunctional : TopDegreeForm → ℝ
  l1Functional : l1Completion → ℝ
  densityLift : TopDegreeForm → l1Completion
  finiteLevelCompatibility :
    ∀ ℓ, inverseLimitCylinderMass ℓ = finiteLevelMass ℓ
  stokesEqualsIntegral :
    ∀ ω, stokesFunctional ω = topDegreeIntegral ω
  l1ExtensionAgrees :
    ∀ ω, l1Functional (densityLift ω) = stokesFunctional ω

/-- The inverse-limit measure has the prescribed compatible finite-level pushforwards. -/
def SolenoidStokesRadonMeasureData.compatiblePushforwards
    (D : SolenoidStokesRadonMeasureData) : Prop :=
  ∀ ℓ, D.inverseLimitCylinderMass ℓ = D.finiteLevelMass ℓ

/-- The top-degree Stokes functional is represented by integration against the realized measure. -/
def SolenoidStokesRadonMeasureData.topDegreeFormsIntegrateAgainstMeasure
    (D : SolenoidStokesRadonMeasureData) : Prop :=
  ∀ ω, D.stokesFunctional ω = D.topDegreeIntegral ω

/-- The Stokes functional extends to the `L¹` completion and still agrees with the realized
measure on dense cylindrical test forms. -/
def SolenoidStokesRadonMeasureData.l1ExtensionOfStokesFunctional
    (D : SolenoidStokesRadonMeasureData) : Prop :=
  ∀ ω, D.l1Functional (D.densityLift ω) = D.topDegreeIntegral ω

/-- Paper-facing wrapper for the Radon-measure realization of the limiting solenoidal Stokes
functional.
    thm:app-solenoid-stokes-radon-measure-realization -/
theorem paper_app_solenoid_stokes_radon_measure_realization (D : SolenoidStokesRadonMeasureData) :
    D.compatiblePushforwards ∧
      D.topDegreeFormsIntegrateAgainstMeasure ∧
      D.l1ExtensionOfStokesFunctional := by
  refine ⟨D.finiteLevelCompatibility, D.stokesEqualsIntegral, ?_⟩
  intro ω
  exact (D.l1ExtensionAgrees ω).trans (D.stokesEqualsIntegral ω)

end Omega.Multiscale
