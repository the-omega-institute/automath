# Case Table Seed: BEDC Automation Pipeline

This is an intake-level case table for a possible CICM presentation-only
promotion.  It does not promote the seed and must not be treated as manuscript
text.

- table date: 2026-05-31
- seed:
  `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- source evidence note: `case_evidence_note.md`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Four-Case Table

| Case | Gate | Observed issue | Evidence source | Safe manuscript lesson |
|---|---|---|---|---|
| Newmath intake isolation | active-paper detector | `newmath_intake` is deliberately not daemon-visible: no seed-local `main.tex`, no seed-local `PIPELINE.md`, and no `2026_*` active paper directory under the intake tree. | `BOARD.md`; `case_evidence_note.md`; `check_intake.py` guard output | Candidate source packets can be prepared without becoming active manuscript jobs. |
| Upper-fibers overlap block | overlap/submitted gate | A later Fibonacci route was blocked because earlier RJ/RINT-related routes overlapped and required explicit closure, merge, supersession, or withdrawal. | `PROGRAM_BOARD_MACHINE.md` rows named in `case_evidence_note.md`; corresponding `inner.log` block records | Venue selection must be stateful; the scheduler cannot randomly advance a similar manuscript. |
| Fake-extension block | theorem-content and delta gate | Prior Stage A rounds produced prose-looking or compile-looking edits without substantive theorem growth, causing A-BLOCKED fake-extension outcomes. | `PROGRAM_BOARD_MACHINE.md` rows for the single-primitive, Joukowsky, and elliptic examples listed in `case_evidence_note.md` | Agent progress is not accepted merely because a file changed or a draft compiles. |
| Rule110 limitation gate | artifact recheck and limitation ledger | Static counts drifted, generated manifests were not materialized locally, and collision-audit text conflicted with reported pass status. | `../bedc_rule110_finite_witness/recheck_results.md`; `../bedc_rule110_finite_witness/limitation_ledger.md` | Honest artifact pipelines disclose or block limitations rather than laundering them into claims. |

## Use In A Promoted Two-Page Draft

If a human later approves promotion, this table can be copied into the active
paper's `ARTIFACT_INVENTORY.md` or reduced into the manuscript case-study
paragraph.  Before manuscript use, re-run or re-read the evidence commands
listed in `case_evidence_note.md`.

## Non-Claims

This table does not claim:

- that all named historical paper routes are mathematically failed;
- that the full `D:/omega/newmath` source tree was freshly rebuilt;
- that Rule110 artifacts passed dynamic validation;
- that deterministic gates judge deep novelty by themselves;
- that AI-generated text is proof evidence.

## Guardrail

This file is not authorization to create:

- `papers/publication/2026_*`;
- `main.tex` in this seed;
- `PIPELINE.md` in this seed.

