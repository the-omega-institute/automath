# Source Decision Note: BEDC Automation Pipeline

This is an intake-level note.  It does not promote the seed, does not create an
active paper directory, and must not be treated as `SOURCE_MAP.md`.

- decision date: 2026-05-31
- seed:
  `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- pinned source repo: `D:/omega/newmath`
- pinned source ref: `origin/dev`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Decision

Keep the pinned source commit as the default evidence base for any CICM
presentation-only promotion unless a separate source update note is written
before promotion.

Reason:

- the proposed CICM route is a narrow workflow-architecture claim, not a full
  Lean artifact audit;
- `source_verification_note.md` has already path-checked the source surfaces
  needed for the narrow claim at the pinned commit;
- using the current local `D:/omega/newmath` tree without a source update note
  would mix evidence levels and make the seed harder for agents to audit.

## When To Use A Source Update Instead

Use `../../SOURCE_UPDATE_NOTE_TEMPLATE.md` before promotion only if the
promoted paper needs evidence from a newer `D:/omega/newmath` commit, for
example:

- a new automation gate or audit script added after the pinned commit;
- a revised BEDC source workflow that changes the case-study evidence;
- a source-side fix that materially changes one of the four selected case
  studies.

The update note must record the old commit, new commit, changed source paths,
and whether the two-page CICM claim changes.

## Promotion Consequence

If no source update note exists at promotion time, the active paper should cite
the pinned commit above and carry forward the narrow evidence boundary:

- source-path verification and case-study evidence may be cited;
- a fresh full-tree `lake build`, axiom-purity audit, or Rule110 rerun must not
  be claimed;
- final venue timing still requires a live re-check immediately before
  submission.

## Guardrail

This note is not authorization to create:

- `papers/publication/2026_*`;
- `main.tex` in this seed;
- `PIPELINE.md` in this seed.

