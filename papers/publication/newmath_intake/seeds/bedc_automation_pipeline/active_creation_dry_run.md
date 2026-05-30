# Active Creation Dry Run: BEDC Automation Pipeline

This file is a dry run only.  It does not promote the seed, does not create a
`2026_*` directory, and must not be treated as `PIPELINE.md`.

## Promotion Command Required

Promotion requires an explicit human command approving both:

- active slug: `2026_auditable_theory_to_paper_pipeline`;
- route: CICM 2026 presentation-only, 2 pages plus bibliography.

Until that command is given, this seed remains intake-only.

## Files To Create After Promotion

If promotion is approved, create exactly one active paper directory:

`papers/publication/2026_auditable_theory_to_paper_pipeline/`

The first active files should be:

| File | Source material | Purpose |
|---|---|---|
| `README.md` | `seed_packet.md`, `promotion_decision_memo.md` | Human summary of the route and claim boundary |
| `PIPELINE.md` | this dry run plus active gate policy | Daemon-visible stage plan |
| `research_directive.md` | `cicm_promotion_brief.md` | Scope-bound writing directive |
| `SOURCE_MAP.md` | `source_map.md`, `source_verification_note.md` | Pinned source paths and source-update rule |
| `ARTIFACT_INVENTORY.md` | `artifact_inventory.md`, `case_evidence_note.md` | Evidence table and case-study inputs |
| `BIB_SCOPE.md` | `venue_ladder.md`, `submission_memo.md` | Bibliography boundary and related-work targets |
| `main.tex` | `cicm_two_page_packet.md` | Two-page CICM manuscript draft |

No other new active paper should be created for this seed unless the human
explicitly chooses a different slug.

## Initial Active Gate Sequence

The promoted paper should start with a conservative pre-Stage-A gate sequence:

1. **Source pin gate.** Confirm whether the active manuscript cites the pinned
   newmath commit `3fb3d6a0641767388a401883062aa522ea0b397b` or a documented
   source update.
2. **Venue live gate.** Re-check CICM presentation-only timing immediately
   before submission and record the access date.
3. **Claim-boundary gate.** Assert only the workflow claim allowed in
   `promotion_decision_memo.md`; reject any added claim that the full Lean tree,
   Rule110 suite, or axiom-purity audit was freshly rerun.
4. **Case-table gate.** Reduce `case_evidence_note.md` to a compact table with
   no uncited examples.
5. **Intake-overlap gate.** Confirm the promoted paper is about publication
   workflow architecture, not a second Rule110 artifact paper or finite-kernel
   theorem paper.

Only after these gates pass should the ordinary paper-writing pipeline prepare
the final two-page manuscript.

## Codex-Only Work Available Before Promotion

The following work may continue inside this seed without promotion:

- refine `BIB_SCOPE` candidates in prose form without creating `BIB_SCOPE.md`;
- tighten the case-study table in `cicm_two_page_packet.md`;
- add source-update notes when `D:/omega/newmath` changes;
- run `papers/publication/newmath_intake/check_intake.py`.

The following work is forbidden before promotion:

- creating any `papers/publication/2026_*` directory for this seed;
- adding `main.tex` or `PIPELINE.md` to this seed;
- invoking daemon stages against this seed directory.
