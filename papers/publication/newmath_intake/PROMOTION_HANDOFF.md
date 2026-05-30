# Promotion Handoff: Newmath BEDC Seeds

This file is an intake handoff only. It is not a promotion command, not a
daemon queue, and not permission to create an active paper track.

- intake root: `papers/publication/newmath_intake`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- handoff date: 2026-05-31

## Global Non-Promotion Rules

Until a human explicitly approves a named seed and active slug:

- do not create any `papers/publication/2026_*` directory from these seeds;
- do not add `main.tex` to any seed directory;
- do not add `PIPELINE.md` to any seed directory;
- do not run Stage A, Stage B, Stage C, or P0-P7 automation on a seed;
- do not cite a newer `D:/omega/newmath` commit without a source update note.

## Handoff Table

| Seed | Current gate | First eligible active slug | Earliest route | Promotion trigger | First active-paper actions after approval |
|---|---|---|---|---|---|
| `bedc_automation_pipeline` | promotion-decision gate | `2026_auditable_theory_to_paper_pipeline` | CICM 2026 presentation-only, two pages plus bibliography | Human says to promote this seed and confirms the slug | Create one active directory; convert `cicm_two_page_packet.md` to `main.tex`; create `PIPELINE.md`, `research_directive.md`, `SOURCE_MAP.md`, `ARTIFACT_INVENTORY.md`, and `BIB_SCOPE.md`; re-check the live CICM page before submission |
| `bedc_finite_kernel_calculus` | source-theorem gate | not selected | short logic/workshop note after packaging theorem; journal route later | Human approves source-side theorem work and a packaging theorem is added or identified | Add source update note if the source commit changes; record exact theorem path/name/statement; then choose active slug and route |
| `bedc_rule110_finite_witness` | artifact-rerun gate | not selected | artifact/workshop route after dynamic rerun | Human provides or approves a toolchain-equipped rerun environment and dynamic evidence is recorded | Record command logs and counts; resolve or disclose collision-audit contradiction; write trust-chain table; then choose active slug and route |

## Current Safe Work

Safe work remains intake-only:

- keep seed packets, source maps, theorem/artifact inventories, venue ladders,
  risk registers, and handoff notes synchronized;
- refine `bedc_automation_pipeline` case tables and bibliography scope;
- refine `bedc_finite_kernel_calculus` theorem-spine summaries without claiming
  that the packaging theorem already exists;
- refine `bedc_rule110_finite_witness` rerun templates and limitation ledgers
  without treating static counts as dynamic validation;
- run `python papers\publication\newmath_intake\check_intake.py`.

## Stop Conditions

Stop and ask for an explicit human decision when the next action would:

- create active-paper files;
- change `D:/omega/newmath`;
- run the Rule110 dynamic artifact suite;
- fetch or rely on live venue pages;
- submit, upload, or prepare final submission materials.

