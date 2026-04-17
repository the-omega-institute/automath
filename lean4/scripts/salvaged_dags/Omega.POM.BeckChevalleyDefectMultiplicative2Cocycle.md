# Omega.POM.BeckChevalleyDefectMultiplicative2Cocycle

- File: `Omega/POM/BeckChevalleyDefectMultiplicative2Cocycle.lean`
- Struct: `BeckChevalleyDefectMultiplicative2CocycleData`
- Paper label: `thm:pom-bc-defect-multiplicative-2cocycle`
- Goal theorem: `paper_pom_bc_defect_multiplicative_2cocycle`

## Structure docstring

Chapter-local package for the Beck--Chevalley multiplicative defect theorem. The data record
the pointwise comparison of the two lifted measures, the identification of their ratio with the
defect function, and the cocycle and logarithmic closedness consequences of reassociating triple
compositions.

## Goal

`D.pointwiseFactorization ∧ D.normalizedTwoCocycle`

## Theorem docstring

Paper-facing wrapper for the Beck--Chevalley defect package: the lifted measures differ by the
pointwise defect factor, and the reassociated triple lift yields the normalized multiplicative
`2`-cocycle together with the equivalent logarithmic closedness statement.
    thm:pom-bc-defect-multiplicative-2cocycle

## DAG

Nodes (Prop fields):
- `pointwiseFactorization` (derived)
- `normalizedTwoCocycle` (derived)
- `liftedMeasuresComparedPointwise` (leaf)
- `defectRatioIdentified` (leaf)
- `cocycleIdentity` (leaf)
- `logClosedness` (leaf)

Edges:
- liftedMeasuresComparedPointwise + defectRatioIdentified  →  **pointwiseFactorization**
- cocycleIdentity + logClosedness  →  **normalizedTwoCocycle**

## Imports
- `Mathlib.Tactic`
