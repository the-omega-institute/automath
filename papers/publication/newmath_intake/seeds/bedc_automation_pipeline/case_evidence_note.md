# Case Evidence Note: BEDC Automation Pipeline

This intake note records exact evidence for the four case studies selected in
`cicm_promotion_brief.md`.  It is not manuscript prose and does not promote the
seed.

## Evidence Snapshot

- note date: 2026-05-31
- automath branch: `dev-automation-integration`
- newmath source commit used by intake:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- active-trigger check for `newmath_intake`: no files matched `main.tex`,
  `PIPELINE.md`, or a path containing `\2026_`

## Case 1: Newmath Intake Isolation

Evidence:

- `papers/publication/newmath_intake/BOARD.md` states that seeds are
  `INTAKE-NOT-ACTIVE` and must not be picked up by paper-stage automation until
  promoted.
- The active-trigger check returned no files:

```powershell
Get-ChildItem -Recurse -File papers\publication\newmath_intake |
  Where-Object { $_.Name -in @('main.tex','PIPELINE.md') -or $_.FullName -match '\\2026_' }
```

Manuscript use:

- Cite this as an architectural boundary: candidate source packets can be
  prepared without being visible to active publication automation.

## Case 2: Upper-Fibers Overlap Block

Evidence from `PROGRAM_BOARD_MACHINE.md`:

- `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj` is
  `A-BLOCKED` because of overlap with earlier submitted/current routes.
- `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint` records
  exact duplicate risk with the RJ upper-fibers route.
- `2026_upper_fibers_witness_covers_fibonacci_apparition_fq` is `A-BLOCKED`
  and must include the RJ rejection reason and RINT duplicate history before
  any Stage A prompt.

Evidence from `inner.log`:

- The daemon preserved the hard Stage A block and reported that the later FQ
  draft must be deferred until the board explicitly closes, supersedes, merges,
  or withdraws the earlier route.

Manuscript use:

- Cite this as a submitted/overlap governance case: the scheduler must not
  randomly advance a later venue route when an earlier route or sibling remains
  unresolved.

## Case 3: Fake-Extension Block After Theoremization

Evidence from `PROGRAM_BOARD_MACHINE.md`:

- `2026_single_primitive_universality_hierarchy` was marked `A-BLOCKED` for an
  A2 fake extension: no new theorems and content delta below the threshold.
- `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` was marked
  `A-BLOCKED` for an A2 fake extension with delta below threshold.
- `2026_elliptic_normalization_branch_geometry_quartic_spectral` was marked
  `A-BLOCKED` for an A2 fake extension with delta below threshold.

Manuscript use:

- Cite one or two of these rows as examples that an agent can produce
  compile-looking or prose-looking edits without adding substantive theorem
  content.
- Keep the claim narrow: the automation detects shallow growth by delta and
  theorem-content checks; it does not judge deep mathematical value by itself.

## Case 4: Rule110 Finite-Witness Limitation

Evidence from `bedc_rule110_finite_witness/recheck_results.md`:

- The local machine did not have `make`, so the dynamic artifact suite was not
  re-run.
- Static counts drifted relative to `rule110/STATUS.md`; top-level C LOC was
  recomputed as `23914` against the previously recorded `20167`.
- Generated Rule 110 manifests were not materialized because `make test` could
  not be run.
- `rule110/STATUS.md` contains a consistency issue: one section says all 33
  Martinez collision rows pass strict audit, while the audit section reports
  `26/33 PASS, 7 FAIL`.

Evidence from `limitation_ledger.md`:

- The collision audit limitation must be disclosed or fixed before promotion.

Manuscript use:

- Cite this as an artifact-honesty case.  The correct response is not to hide
  the limitation, but to block or narrow the paper claim until a full artifact
  recheck resolves the issue.

## Excluded From the Two-Page Version

The C-INFRA-STUCK and C-NEAR-PASS cases are useful but should stay out of the
first CICM presentation-only version unless space remains.  They belong in a
longer systems or journal paper about terminal-state classification.
