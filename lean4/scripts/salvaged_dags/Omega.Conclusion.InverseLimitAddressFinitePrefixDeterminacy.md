# Omega.Conclusion.InverseLimitAddressFinitePrefixDeterminacy

- File: `Omega/Conclusion/InverseLimitAddressFinitePrefixDeterminacy.lean`
- Struct: `InverseLimitAddressFinitePrefixDeterminacyData`
- Paper label: `thm:conclusion-inverse-limit-address-finite-prefix-determinacy`
- Goal theorem: `paper_conclusion_inverse_limit_address_finite_prefix_determinacy`

## Structure docstring

Data package encoding the compactness proof that a continuous address map to a discrete
codomain depends only on a finite prefix. The fields follow the paper proof: local constancy on
clopen cylinders, extraction of a finite cylinder cover, a maximal prefix depth, and the induced
factor map on the corresponding finite stage.

## Goal

`D.factorsThroughFinitePrefix`

## Theorem docstring

Paper package: a continuous inverse-limit address map to a discrete codomain factors through
some finite prefix stage. `thm:conclusion-inverse-limit-address-finite-prefix-determinacy`

## DAG

Nodes (Prop fields):
- `locallyConstantOnCylinderBasis` (leaf)
- `finiteCylinderCover` (derived)
- `maximalPrefixDepth` (derived)
- `finiteStageFactorMap` (derived)
- `factorsThroughFinitePrefix` (derived)

Edges:
- locallyConstantOnCylinderBasis  →  **finiteCylinderCover**
- finiteCylinderCover  →  **maximalPrefixDepth**
- maximalPrefixDepth  →  **finiteStageFactorMap**
- locallyConstantOnCylinderBasis + finiteStageFactorMap  →  **factorsThroughFinitePrefix**

## Imports
- `Mathlib.Tactic`
