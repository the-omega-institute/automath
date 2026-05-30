# Diagnostic Route Memo: BEDC Rule 110 Finite Witness

This memo records how the seed could proceed if the collision audit remains
partial or failing after a dynamic rerun. It is not a promotion command.

- seed:
  `papers/publication/newmath_intake/seeds/bedc_rule110_finite_witness`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- memo date: 2026-05-31

## Default Decision

Do not promote this seed before dynamic artifact evidence exists.

## Diagnostic Alternative

If `make`, `make test`, and materialization pass but
`make test-collision-audit` remains partial or failing, the paper may only be
considered as a diagnostic finite-witness artifact. The limitation must be
visible in the abstract, introduction, trust-chain table, and conclusion.

Allowed diagnostic claim:

> The artifact gives a finite witness and reproducibility surface for selected
> BEDC-to-cyclic-tag/Rule110 manifests, while isolating the Cook/Martinez
> collision audit as an explicit diagnostic limitation rather than a passed
> certificate.

## Prohibited Diagnostic Claims

The diagnostic route must not claim:

- complete phase-exact Cook validation;
- all 33 collision rows strictly pass if the rerun reports otherwise;
- Rule110 validates all BEDC or CIC statements;
- generated manifests are complete unless the rerun materializes them;
- the limitation is irrelevant to the paper's trust chain.

## Decision Matrix

| Dynamic result | Route |
|---|---|
| full build/test pass and collision audit consistent | full artifact/workshop route may be discussed |
| full build/test pass but collision audit remains `26/33 PASS, 7 FAIL` or similar | diagnostic finite-witness route only |
| build/test fails before manifest materialization | park or repair source/toolchain |
| source commit changes | source update note required before route choice |

## Human Decision Required

A human must decide whether a diagnostic route is acceptable for the target
venue. If not, the seed remains parked until the source/toolchain issue is
fixed and the dynamic audit is rerun.

