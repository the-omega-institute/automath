# Omega.Multiscale.SolenoidNormalizedStokesL2ScalingCriticalDegree

- File: `Omega/Multiscale/SolenoidNormalizedStokesL2ScalingCriticalDegree.lean`
- Struct: `SolenoidNormalizedStokesL2ScalingCriticalDegreeData`
- Paper label: `thm:app-solenoid-normalized-stokes-l2-scaling-critical-degree`
- Goal theorem: `paper_app_solenoid_normalized_stokes_l2_scaling_critical_degree`

## Structure docstring

Chapter-local data for the normalized Stokes--`L²` scaling law on the `N`-adic solenoid model.
The package tracks the pullback scaling of coordinate one-forms, the induced scaling on `q`-forms,
the Jacobian contribution under the covering map, and the resulting critical-degree dichotomy for
the normalized energy.

## Goal

`D.pullbackOfCoordinateForms ∧ D.qFormNormScaling ∧ D.changeOfVariablesScaling ∧ D.normalizedEnergyClosedForm ∧ D.criticalDegreeInvariance ∧ D.subcriticalDegreeDecay`

## Theorem docstring

Paper-facing wrapper for the normalized Stokes--`L²` scaling law on the `N`-adic solenoid:
pullback multiplies coordinate one-forms by `N`, `q`-form norms pick up the corresponding factor,
change of variables contributes the Jacobian, and the normalized energy is critical exactly in top
degree.
    thm:app-solenoid-normalized-stokes-l2-scaling-critical-degree

## DAG

Nodes (Prop fields):
- `pullbackOfCoordinateForms` (leaf)
- `qFormNormScaling` (derived)
- `changeOfVariablesScaling` (derived)
- `normalizedEnergyClosedForm` (derived)
- `criticalDegreeInvariance` (derived)
- `subcriticalDegreeDecay` (derived)

Edges:
- pullbackOfCoordinateForms  →  **qFormNormScaling**
- qFormNormScaling  →  **changeOfVariablesScaling**
- qFormNormScaling + changeOfVariablesScaling  →  **normalizedEnergyClosedForm**
- normalizedEnergyClosedForm  →  **criticalDegreeInvariance**
- normalizedEnergyClosedForm  →  **subcriticalDegreeDecay**

## Imports
- `Mathlib.Tactic`
