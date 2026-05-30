# P0 Readiness Matrix: Newmath BEDC Intake

This is a human-facing readiness matrix for the three P0 newmath-derived BEDC
seeds.  It is not a machine queue and does not promote any seed into an active
paper track.

- matrix date: 2026-05-31
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- automath intake root: `papers/publication/newmath_intake`

## Summary

| Seed | Current readiness | Can promote now? | Blocking item | Next owner/action |
|---|---|---:|---|---|
| `bedc_automation_pipeline` | CICM presentation-only packet prepared; case evidence and gate table ready | only with human approval | final human promotion decision; final live CICM page re-check; source commit/update choice | Human decides whether to promote as `2026_auditable_theory_to_paper_pipeline` |
| `bedc_finite_kernel_calculus` | exact statements read; theorem spine selected; packaging work order prepared | no for journal route | add or identify upstream packaging theorem in `D:/omega/newmath` | Source-side theorem work using `upstream_packaging_work_order.md` |
| `bedc_rule110_finite_witness` | static recheck done; count drift and collision-audit contradiction recorded; rerun packet prepared | no | install/use `make` plus C compiler and rerun dynamic artifact suite | Toolchain/artifact rerun using `artifact_rerun_packet.md` |

## Route Decisions

| Seed | Recommended first route | Fallback route | Park condition |
|---|---|---|---|
| `bedc_automation_pipeline` | CICM 2026 presentation-only, narrow work-in-progress claim | COLM workshop, ICTAI, later JAR/JFR | Park if no human promotion before the CICM window or if live CFP check closes the route |
| `bedc_finite_kernel_calculus` | short logic/workshop note only after packaging theorem; journal later | APAL/LMCS/Studia Logica only with stronger theorem spine and related-work audit | Park as support material for automation paper if no packaging theorem is added |
| `bedc_rule110_finite_witness` | artifact/workshop route after full dynamic rerun | JFR/JAR only with stable trust-chain table | Park if build toolchain cannot be supplied or collision audit remains unresolved and undisclosed |

## Promotion Preconditions By Seed

### `bedc_automation_pipeline`

Already prepared:

- `cicm_two_page_packet.md`
- `cicm_promotion_brief.md`
- `case_evidence_note.md`
- `gate_table.md`
- `failure_modes.md`
- `promotion_decision_memo.md`
- `active_creation_dry_run.md`
- `bibliography_scope_seed.md`
- `source_verification_note.md`

Still required before active paper creation:

- explicit human approval to promote;
- active slug confirmation, currently suggested as
  `2026_auditable_theory_to_paper_pipeline`;
- final live CICM page check immediately before submission;
- source decision: pinned commit as-is or documented source update note.

### `bedc_finite_kernel_calculus`

Already prepared:

- `theorem_spine_selection.md`
- `exact_statement_note.md`
- `non_claim_registry.md`
- `packaging_theorem_proposal.md`
- `upstream_packaging_work_order.md`
- `current_declaration_map.md`

Still required before journal-style promotion:

- source-side packaging theorem or theorem family in `D:/omega/newmath`;
- exact source path and exact statement summary after the source change;
- decision on GroundCompiler material: appendix/interface only or main section;
- live venue re-check.

### `bedc_rule110_finite_witness`

Already prepared:

- `artifact_inventory.md`
- `limitation_ledger.md`
- `recheck_plan.md`
- `recheck_results.md`
- `build_environment_plan.md`
- `artifact_rerun_packet.md`

Still required before promotion:

- `make` plus C compiler available in WSL or another Unix-like environment;
- dynamic rerun logs for `make`, `make test`, `make test-collision-audit`, and
  `make test-scale`;
- refreshed manifest and LOC counts after materialization;
- explicit decision on whether collision-audit failures are blockers or scoped
  diagnostics;
- trust-chain table with final command results and limitations.

## Deterministic Guard

Before any promotion work or after adding new seed files, run:

```powershell
python papers\publication\newmath_intake\check_intake.py
```

The guard must pass with no active-paper trigger files in the seed directories.

## Human Decision Queue

1. Decide whether to promote `bedc_automation_pipeline` now for CICM
   presentation-only.
2. Decide whether to allocate source-side time in `D:/omega/newmath` for the
   finite-kernel packaging theorem.
3. Decide whether to install/use a Rule110 build toolchain and run the artifact
   suite.

Until one of these decisions is made, all three seeds remain intake-only and
must not enter the daemon paper pipeline.
