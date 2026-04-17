# Omega.POM.SufficientStatisticResidualNoninvertibility

- File: `Omega/POM/SufficientStatisticResidualNoninvertibility.lean`
- Struct: `PomSufficientStatisticResidualData`
- Paper label: `prop:pom-sufficient-statistic-residual-noninvertibility`
- Goal theorem: `paper_pom_sufficient_statistic_residual_noninvertibility`

## Structure docstring

Chapter-local package for the sufficient-statistic residual noninvertibility criterion. The
paper argument bounds the residual image on each fiber by the rewrite-count degree plus one, then
rewrites the fiber multiplicity and degree in the closed forms tracked by these fields.

## Goal

`h.imageCardLeDegreeSucc ∧ h.notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc ∧ h.fiberFactorizationClosedForms`

## Theorem docstring

Paper-facing wrapper for the sufficient-statistic residual noninvertibility package.
    prop:pom-sufficient-statistic-residual-noninvertibility

## DAG

Nodes (Prop fields):
- `imageCardLeDegreeSucc` (leaf)
- `notFiberwiseInjectiveWhenMultiplicityExceedsDegreeSucc` (leaf)
- `fiberFactorizationClosedForms` (leaf)

Edges:
- (none)

## Imports
- `Mathlib.Tactic`
