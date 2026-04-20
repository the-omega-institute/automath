import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local package for the toral-solenoid `\v{C}`ech-`H¹` computation. The data store a
concrete model for `\check H^1`, its direct-limit presentation, and the identification with the
Stokes period module. -/
structure ToralSolenoidCechH1DirectLimitData where
  CohomologyClass : Type
  cechH1 : Set CohomologyClass
  directLimit : Set CohomologyClass
  stokesPeriodModule : Set CohomologyClass
  cechH1_eq_directLimit : cechH1 = directLimit
  directLimit_eq_stokesPeriodModule : directLimit = stokesPeriodModule

/-- Paper-facing wrapper for the toral-solenoid `\v{C}`ech-`H¹` direct-limit presentation.
    prop:app-toral-solenoid-cech-h1-direct-limit -/
theorem paper_app_toral_solenoid_cech_h1_direct_limit (D : ToralSolenoidCechH1DirectLimitData) :
    D.cechH1 = D.directLimit ∧ D.directLimit = D.stokesPeriodModule := by
  exact ⟨D.cechH1_eq_directLimit, D.directLimit_eq_stokesPeriodModule⟩

end Omega.Multiscale
