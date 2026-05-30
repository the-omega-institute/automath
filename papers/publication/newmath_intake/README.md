# Newmath Publication Intake

This directory stages publication candidates sourced from `D:/omega/newmath`.
It is an intake queue, not an active paper pipeline.

The directories under `seeds/` deliberately do not use the `2026_*` naming
pattern and do not contain `main.tex` or `PIPELINE.md`. They are therefore not
eligible for `pipeline_auto.py` stage execution until a human promotes a seed
into a formal `papers/publication/2026_*` paper track.

## Source Snapshot

- Source repo: `D:/omega/newmath`
- Source ref: `origin/dev`
- Source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- Intake created from automath commit: `45b83891689f7f942f482665e326969858d50e3a`
- Intake date: 2026-05-30

## Operating Rules

1. Agents may read seed packets for scope, source-map, theorem, artifact, and
   venue planning.
2. Agents must not run Stage A, P0-P7, or manuscript rewrite tasks against a
   seed directory.
3. A seed becomes active only after promotion into a `2026_*` directory with
   `README.md`, `PIPELINE.md`, `research_directive.md`, `SOURCE_MAP.md`,
   `THEOREM_LIST.md` or `ARTIFACT_INVENTORY.md`, `BIB_SCOPE.md`, and
   `main.tex`.
4. Formal manuscripts must pin a source commit. They must not cite a floating
   `newmath` branch as their source of truth.
5. If `newmath` changes after promotion, record the delta in a source update
   note rather than silently editing the source-map commit.
6. If `newmath` changes before promotion, copy
   `SOURCE_UPDATE_NOTE_TEMPLATE.md` into the relevant seed under a descriptive
   name and record the old/new commits before editing any seed source-map.

## Intake Guard

Run the deterministic intake guard before promotion work or after adding new
seed materials:

```powershell
python papers\publication\newmath_intake\check_intake.py
```

The guard fails if a seed contains `main.tex`, `PIPELINE.md`, or a `2026_*`
subdirectory, and it checks that the intake indexes still state the non-active
boundary.

## Seed Priorities

| Seed | Priority | Status | Intended first action |
|---|---:|---|---|
| `bedc_automation_pipeline` | P0 | ready for human promotion decision; not active | Human decides whether to promote for CICM presentation-only as `2026_auditable_theory_to_paper_pipeline` |
| `bedc_finite_kernel_calculus` | P0 | exact statements read; not active | Use `packaging_theorem_proposal.md` to add or identify an upstream packaging theorem before journal-style promotion |
| `bedc_rule110_finite_witness` | P0 | static recheck found count drift and missing build toolchain; not active | Use `build_environment_plan.md` to run the full Rule110 suite in a toolchain-equipped environment before promotion |
| `metacic_closed_normal_consistency` | P1 | intake-ready | Related-work and theorem-scope audit |
| `observer_state_semantics` | P1 | intake-ready | Workshop/position-paper framing audit |

## Venue Timing

Current verified venue timing is tracked in `VENUE_DEADLINES.md`. Agents must
read that file before writing a venue ladder, promotion memo, or submission
plan.

The current P0 decision state is summarized in `P0_READINESS_MATRIX.md`.

Use `SOURCE_UPDATE_NOTE_TEMPLATE.md` for any source commit movement, whether the
candidate is still a seed or has already been promoted.
