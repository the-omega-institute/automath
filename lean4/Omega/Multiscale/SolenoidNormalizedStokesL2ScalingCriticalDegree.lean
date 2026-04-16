import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local data for the normalized Stokes--`L²` scaling law on the `N`-adic solenoid model.
The package tracks the pullback scaling of coordinate one-forms, the induced scaling on `q`-forms,
the Jacobian contribution under the covering map, and the resulting critical-degree dichotomy for
the normalized energy. -/
structure SolenoidNormalizedStokesL2ScalingCriticalDegreeData where
  pullbackOfCoordinateForms : Prop
  qFormNormScaling : Prop
  changeOfVariablesScaling : Prop
  normalizedEnergyClosedForm : Prop
  criticalDegreeInvariance : Prop
  subcriticalDegreeDecay : Prop
  pullbackOfCoordinateForms_h : pullbackOfCoordinateForms
  deriveQFormNormScaling :
    pullbackOfCoordinateForms → qFormNormScaling
  deriveChangeOfVariablesScaling :
    qFormNormScaling → changeOfVariablesScaling
  deriveNormalizedEnergyClosedForm :
    qFormNormScaling → changeOfVariablesScaling → normalizedEnergyClosedForm
  deriveCriticalDegreeInvariance :
    normalizedEnergyClosedForm → criticalDegreeInvariance
  deriveSubcriticalDegreeDecay :
    normalizedEnergyClosedForm → subcriticalDegreeDecay

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the normalized Stokes--`L²` scaling law on the `N`-adic solenoid:
pullback multiplies coordinate one-forms by `N`, `q`-form norms pick up the corresponding factor,
change of variables contributes the Jacobian, and the normalized energy is critical exactly in top
degree.
    thm:app-solenoid-normalized-stokes-l2-scaling-critical-degree -/
theorem paper_app_solenoid_normalized_stokes_l2_scaling_critical_degree
    (D : SolenoidNormalizedStokesL2ScalingCriticalDegreeData) :
    D.pullbackOfCoordinateForms ∧
      D.qFormNormScaling ∧
      D.changeOfVariablesScaling ∧
      D.normalizedEnergyClosedForm ∧
      D.criticalDegreeInvariance ∧
      D.subcriticalDegreeDecay := by
  have hQ : D.qFormNormScaling := D.deriveQFormNormScaling D.pullbackOfCoordinateForms_h
  have hJac : D.changeOfVariablesScaling := D.deriveChangeOfVariablesScaling hQ
  have hEnergy : D.normalizedEnergyClosedForm := D.deriveNormalizedEnergyClosedForm hQ hJac
  exact ⟨D.pullbackOfCoordinateForms_h, hQ, hJac, hEnergy,
    D.deriveCriticalDegreeInvariance hEnergy, D.deriveSubcriticalDegreeDecay hEnergy⟩

end Omega.Multiscale
