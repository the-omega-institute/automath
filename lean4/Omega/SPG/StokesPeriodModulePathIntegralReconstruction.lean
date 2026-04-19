import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local package for the inverse-tower path-integral reconstruction of the Stokes period
module. The structure records the ambient period-vector type together with the two paper-facing
submodules and their equality witness. -/
structure StokesPeriodModulePathIntegralReconstructionData where
  PeriodVector : Type
  pathIntegralPeriodModule : Set PeriodVector
  stokesPeriodModule : Set PeriodVector
  pathIntegral_eq_stokes : pathIntegralPeriodModule = stokesPeriodModule

/-- Paper-facing wrapper identifying the path-integral period module with the Stokes period module.
    prop:app-stokes-period-module-path-integral-reconstruction -/
theorem paper_app_stokes_period_module_path_integral_reconstruction
    (D : StokesPeriodModulePathIntegralReconstructionData) :
    D.pathIntegralPeriodModule = D.stokesPeriodModule := by
  exact D.pathIntegral_eq_stokes

end Omega.SPG
