import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local package for the covector normalization of the Stokes period
module. The data record the definitional rewrite
`Π_St(S) = ⋃ D_n⁻¹ ℤ^r` together with the integrality of the successive
transition matrices `D_n⁻¹ D_{n+1}`. -/
structure StokesPeriodModuleCovectorNormalizationData where
  PeriodVector : Type
  stokesPeriodModule : Set PeriodVector
  covectorUnion : Set PeriodVector
  successiveTransitionIntegral : Prop
  stokesPeriodModule_eq_covectorUnion : stokesPeriodModule = covectorUnion
  successiveTransitionIntegral_h : successiveTransitionIntegral

/-- Paper-facing wrapper for the covector normalization of the Stokes period
module.
    cor:app-stokes-period-module-covector-normalization -/
theorem paper_app_stokes_period_module_covector_normalization
    (D : StokesPeriodModuleCovectorNormalizationData) :
    D.stokesPeriodModule = D.covectorUnion ∧ D.successiveTransitionIntegral := by
  exact ⟨D.stokesPeriodModule_eq_covectorUnion, D.successiveTransitionIntegral_h⟩

end Omega.Multiscale
