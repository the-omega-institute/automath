# Seed Packet: MetaCIC Closed-Normal Consistency

## Proposed Paper Unit

A mechanized type-theory note on a mathlib-free Lean formalization of a
closed-normal consistency theorem for a scoped CIC fragment, with explicit
dependent-codomain boundary hypotheses.

## Priority

P1.

## Source of Truth

- Repo: `D:/omega/newmath`
- Ref: `origin/dev`
- Commit: `3fb3d6a0641767388a401883062aa522ea0b397b`

## Candidate Claim

The paper claims a mechanically checked scoped consistency result for closed
normal terms at false in a MetaCIC development, with strict axiom-purity and a
clear boundary at dependent-codomain subject-reduction obligations.

## Non-Claims

- It does not claim full CIC consistency.
- It does not claim the dependent-codomain case is discharged.
- It does not claim novelty over all MetaCoq or type-theory meta-theory until
  related work has been audited.
- It does not rely on Rule 110 or AI consciousness material.

## Key Source Paths

- `docs/dossier/metacic-first-main-result.qmd`
- `lean4/BEDC/MetaCIC/`
- `papers/bedc/parts/`
- `lean4/scripts/bedc_ci.py`

## Evidence to Extract

- Exact Lean target for closed-normal consistency.
- Exact hypotheses and dependent-codomain boundary fields.
- Axiom-purity status for MetaCIC declarations.
- Related-work comparison against MetaCoq, Autosubst, Lean/Coq formalizations
  of substitution, subject reduction, confluence, normalization, and
  consistency fragments.

## Promotion Target

Candidate active directory:

`papers/publication/2026_metacic_closed_normal_consistency/`

