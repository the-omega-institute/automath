# Evidence Separation Note: BEDC Rule 110 Finite Witness

This note separates reported, static, and dynamic evidence for the Rule 110
finite-witness seed. It is intake-only and does not promote the seed.

- seed:
  `papers/publication/newmath_intake/seeds/bedc_rule110_finite_witness`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- note date: 2026-05-31

## Evidence Classes

| Evidence class | What it can support | What it cannot support | Current status |
|---|---|---|---|
| Reported source status | A historical description of what `rule110/STATUS.md` reports | Artifact validation in the current environment | Present in `artifact_inventory.md`, but internally inconsistent on collision audit status |
| Static source-tree counts | A baseline for source files and checked-in manifests at the pinned tree | Generated-manifest counts after `make test`; command pass/fail claims | Present in `recheck_results.md`; several counts drift from older notes |
| Dynamic build/test logs | Reproducible artifact validation, generated manifest materialization, collision-audit result, and scale frontier | Universal theorem-proving claims or replacement-foundation claims | Missing because `make` and C compiler are not available in the current Windows/WSL environment |
| Limitation ledger | Scope control and disclosure obligations | A claim that limitations are fixed | Present in `limitation_ledger.md` |

## Current Safe Claim Boundary

The seed may be described as a finite-witness artifact candidate with static
intake evidence and a prepared rerun packet. It must not be described as a
validated artifact paper until a toolchain-equipped dynamic rerun exists.

Safe language:

- static source counts have been rechecked at the pinned source snapshot;
- generated Rule 110 manifests were not materialized in the current run;
- collision-audit status is unresolved for promotion;
- dynamic `make` evidence is required before full artifact claims.

Forbidden language:

- the Rule 110 artifact suite has passed in the current environment;
- all generated manifests are present after materialization;
- the collision audit is complete and strictly passed;
- the finite witness is a universal proof engine or a replacement for existing
  foundations.

## Decision Table After Dynamic Rerun

| Rerun outcome | Publication consequence |
|---|---|
| `make`, `make test`, `make test-collision-audit`, and `make test-scale` pass, with consistent collision rows | Proceed to human promotion discussion for an artifact/workshop route |
| Build and core tests pass, but collision audit remains partial or failing | Consider only a diagnostic finite-witness route with explicit disclosure |
| Build fails or generated manifests do not materialize | Do not promote; repair source/toolchain or park as artifact-infrastructure support |
| Source commit changes before rerun | Add a source update note before using the rerun as promotion evidence |

## Minimum Trust-Chain Fields

When dynamic evidence exists, record:

- source commit and branch;
- toolchain versions;
- command exit codes;
- paths to raw logs in the source workspace;
- manifest counts before and after materialization;
- collision-audit row summary;
- largest scale case reached;
- limitation status and promotion consequence.

