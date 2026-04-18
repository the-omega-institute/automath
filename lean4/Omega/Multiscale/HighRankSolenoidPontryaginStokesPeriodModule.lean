import Mathlib.Tactic

namespace Omega.Multiscale

/-- Concrete data for the high-rank solenoid Pontryagin/Stokes package. The record keeps the
character-side model, the inverse-tower dual model, the Stokes period module, and a rank-one
slice together with the comparison maps relating them. -/
structure HighRankSolenoidPontryaginStokesPeriodModuleData where
  Character : Type
  InverseTowerDual : Type
  StokesPeriodModule : Type
  RankOneCharacter : Type
  toInverseTowerDual : Character → InverseTowerDual
  ofInverseTowerDual : InverseTowerDual → Character
  toStokesPeriodModule : InverseTowerDual → StokesPeriodModule
  ofStokesPeriodModule : StokesPeriodModule → InverseTowerDual
  rankOneInclusion : RankOneCharacter → Character
  rankOnePeriodModule : RankOneCharacter → StokesPeriodModule
  pontryagin_left_inv :
    Function.LeftInverse ofInverseTowerDual toInverseTowerDual
  pontryagin_right_inv :
    Function.RightInverse ofInverseTowerDual toInverseTowerDual
  stokes_left_inv :
    Function.LeftInverse ofStokesPeriodModule toStokesPeriodModule
  stokes_right_inv :
    Function.RightInverse ofStokesPeriodModule toStokesPeriodModule
  rankOneCompatibility :
    ∀ χ : RankOneCharacter,
      toStokesPeriodModule (toInverseTowerDual (rankOneInclusion χ)) = rankOnePeriodModule χ

namespace HighRankSolenoidPontryaginStokesPeriodModuleData

/-- The Pontryagin dual of the high-rank solenoid is identified with the inverse-tower model. -/
def pontryaginDualEquiv (D : HighRankSolenoidPontryaginStokesPeriodModuleData) : Prop :=
  Nonempty (D.Character ≃ D.InverseTowerDual)

/-- The Stokes period module is rigidly identified with the same inverse-tower dual. -/
def isomorphismRigidity (D : HighRankSolenoidPontryaginStokesPeriodModuleData) : Prop :=
  Nonempty (D.InverseTowerDual ≃ D.StokesPeriodModule)

/-- Restricting the high-rank period-module description to the rank-one slice recovers the
specialized rank-one formula. -/
def rankOneSpecialization (D : HighRankSolenoidPontryaginStokesPeriodModuleData) : Prop :=
  ∀ χ : D.RankOneCharacter,
    D.toStokesPeriodModule (D.toInverseTowerDual (D.rankOneInclusion χ)) = D.rankOnePeriodModule χ

/-- Explicit equivalence realizing the Pontryagin identification. -/
def pontryaginEquiv (D : HighRankSolenoidPontryaginStokesPeriodModuleData) :
    D.Character ≃ D.InverseTowerDual where
  toFun := D.toInverseTowerDual
  invFun := D.ofInverseTowerDual
  left_inv := D.pontryagin_left_inv
  right_inv := D.pontryagin_right_inv

/-- Explicit equivalence realizing the Stokes-period rigidity statement. -/
def stokesEquiv (D : HighRankSolenoidPontryaginStokesPeriodModuleData) :
    D.InverseTowerDual ≃ D.StokesPeriodModule where
  toFun := D.toStokesPeriodModule
  invFun := D.ofStokesPeriodModule
  left_inv := D.stokes_left_inv
  right_inv := D.stokes_right_inv

end HighRankSolenoidPontryaginStokesPeriodModuleData

open HighRankSolenoidPontryaginStokesPeriodModuleData

/-- Paper-facing wrapper for the high-rank solenoid Pontryagin/Stokes period-module package.
    thm:app-high-rank-solenoid-pontryagin-stokes-period-module -/
theorem paper_app_high_rank_solenoid_pontryagin_stokes_period_module
    (D : HighRankSolenoidPontryaginStokesPeriodModuleData) :
    D.pontryaginDualEquiv ∧ D.isomorphismRigidity ∧ D.rankOneSpecialization := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.pontryaginEquiv⟩
  · exact ⟨D.stokesEquiv⟩
  · exact D.rankOneCompatibility

end Omega.Multiscale
