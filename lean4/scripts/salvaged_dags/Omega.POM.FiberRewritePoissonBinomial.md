# Omega.POM.FiberRewritePoissonBinomial

- File: `Omega/POM/FiberRewritePoissonBinomial.lean`
- Struct: `FiberRewritePoissonBinomialData`
- Paper label: `?`
- Goal theorem: `paper_pom_fiber_rewrite_poisson_binomial`

## Structure docstring

Chapter-local package for the Poisson--binomial rewriting of the fiber rewrite-count law. The
fields encode the normalized PGF factorization, identification with a Poisson--binomial law, the
resulting mean and variance formulas, and the unified Bernstein tail estimate.

## Goal

`h.normalizedPgfFactorization ∧ h.poissonBinomialLaw ∧ h.meanFormula ∧ h.varianceFormula ∧ h.bernsteinTailBound`

## Theorem docstring

Paper-facing wrapper for the fiber rewrite-count Poisson--binomial package.
    cor:pom-fiber-rewrite-poisson-binomial

## DAG

Nodes (Prop fields):
- `normalizedPgfFactorization` (leaf)
- `poissonBinomialLaw` (leaf)
- `meanFormula` (leaf)
- `varianceFormula` (leaf)
- `bernsteinTailBound` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
