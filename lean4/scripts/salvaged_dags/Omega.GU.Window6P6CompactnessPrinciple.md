# Omega.GU.Window6P6CompactnessPrinciple

- File: `Omega/GU/Window6P6CompactnessPrinciple.lean`
- Struct: `Window6P6CompactnessPrincipleData`
- Paper label: `?`
- Goal theorem: `paper_window6_p6_compactness_principle`

## Structure docstring

Chapter-local wrapper for the compactness principle attached to the reversible window-`6`
pushforward kernel. The fields encode the detailed-balance input, the resulting self-adjointness
of the induced operator, the finite-dimensionality of its commutant, and the closed-subgroup
argument inside `U(21)` that yields compactness of the unitary commutant.

## Goal

`D.selfAdjointOperator ∧ D.commutantFiniteDimensional ∧ D.unitaryGroupCompact`

## Theorem docstring

Paper-facing wrapper for the window-`6` compactness principle: detailed balance gives a
self-adjoint Markov operator on `ℓ²(X₆, π₆)`, its commutant is a finite-dimensional `*`-algebra,
and the unitary commutant is therefore a closed subgroup of `U(21)`, hence compact.
    cor:window6-p6-compactness-principle

## DAG

Nodes (Prop fields):
- `detailedBalance` (leaf)
- `selfAdjointOperator` (derived)
- `commutantFiniteDimensional` (derived)
- `closedSubgroupOfU21` (derived)
- `unitaryGroupCompact` (derived)

Edges:
- detailedBalance  →  **selfAdjointOperator**
- selfAdjointOperator  →  **commutantFiniteDimensional**
- selfAdjointOperator + commutantFiniteDimensional  →  **closedSubgroupOfU21**
- closedSubgroupOfU21  →  **unitaryGroupCompact**

## Imports
- `Mathlib.Tactic`
