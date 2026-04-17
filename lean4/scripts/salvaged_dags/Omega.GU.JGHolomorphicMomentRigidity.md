# Omega.GU.JGHolomorphicMomentRigidity

- File: `Omega/GU/JGHolomorphicMomentRigidity.lean`
- Struct: `HolomorphicMomentRigidityData`
- Paper label: `thm:group-jg-holomorphic-moment-rigidity`
- Goal theorem: `paper_group_jg_holomorphic_moment_rigidity`

## Structure docstring

Chapter-local audited package for the holomorphic moment rigidity computation on the unit
circle. The witness fields record the two paper-facing consequences extracted from the
pushforward moment calculation: odd moments vanish, and even moments match the central binomial
coefficients.

## Goal

`D.oddMomentsVanish ∧ D.evenMomentsCentralBinomial`

## Theorem docstring

Paper-facing wrapper for the holomorphic moment rigidity package.
    thm:group-jg-holomorphic-moment-rigidity

## DAG

Nodes (Prop fields):
- `oddMomentsVanish` (leaf)
- `evenMomentsCentralBinomial` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
