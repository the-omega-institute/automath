# Omega.GU.JoukowskyGodelPullbackFactorization

- File: `Omega/GU/JoukowskyGodelPullbackFactorization.lean`
- Struct: `JoukowskyGodelPullbackFactorizationData`
- Paper label: `thm:group-jg-pullback-factorization`
- Goal theorem: `paper_group_jg_pullback_factorization`

## Structure docstring

Chapter-local package for the Joukowsky--Gödel pullback factorization identity. The data store
the resultant product formula, the reciprocal-polynomial rewrite, and the final pullback identity;
the derivation field records the paper's substitution-and-factorization argument as an abstract
implication between these chapter-local statements.

## Goal

`D.pullbackFactorization`

## Theorem docstring

Paper-facing wrapper for the Joukowsky--Gödel pullback factorization identity: after
substituting `w = r z + r⁻¹ z⁻¹` into the resultant product formula and rewriting the reciprocal
factor as `Pᵛ(r² z)`, the pullback splits as the product `P(z) Pᵛ(r² z)`.
    thm:group-jg-pullback-factorization

## DAG

Nodes (Prop fields):
- `resultantProductFormula` (leaf)
- `reciprocalPolynomialRewrite` (leaf)
- `pullbackFactorization` (derived)

Edges:
- resultantProductFormula + reciprocalPolynomialRewrite  →  **pullbackFactorization**

## Imports
- `Mathlib.Tactic`
