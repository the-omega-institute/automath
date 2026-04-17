# Omega.POM.PressureReflectionInequality

- File: `Omega/POM/PressureReflectionInequality.lean`
- Struct: `PressureReflectionInequalityData`
- Paper label: `prop:pom-pressure-reflection-inequality`
- Goal theorem: `paper_pom_pressure_reflection_inequality_package`

## Structure docstring

Chapter-local package for the pressure reflection inequality. The data record the
finite-volume Cauchy--Schwarz inequality, the equality characterization by proportionality,
and the resulting pressure reflection bound on the limsup exponents.

## Goal

`D.finiteVolumeReflection ∧ D.equalityCharacterization ∧ D.tauReflection`

## Theorem docstring

Package wrapper for the pressure reflection data record:
apply Cauchy--Schwarz at finite volume, characterize equality by proportionality,
and pass to the Fibonacci growth-rate limsup bound.
    prop:pom-pressure-reflection-inequality

## DAG

Nodes (Prop fields):
- `finiteVolumeReflection` (leaf)
- `equalityCharacterization` (derived)
- `tauReflection` (derived)

Edges:
- finiteVolumeReflection  →  **equalityCharacterization**
- finiteVolumeReflection + equalityCharacterization  →  **tauReflection**

## Imports
- `Mathlib.Tactic`
