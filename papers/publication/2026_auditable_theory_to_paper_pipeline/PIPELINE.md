# Pipeline: Auditable Theory-to-Paper Pipeline

## Metadata

- paper slug: `2026_auditable_theory_to_paper_pipeline`
- target journal: CICM presentation-only / mathematical software workshop route
- fallback venues: COLM workshop; ICTAI-style AI systems venue; later JAR/JFR
  systems paper after stronger artifact evidence
- source seed: `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- public source URL: `https://github.com/the-omega-institute/newmath`
- newmath source ref: `origin/dev`
- newmath source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- promoted: 2026-05-31

## Current Stage

P4 complete: the promoted draft has been assembled, the CICM
presentation-only route has been checked, initial related-work citations have
been added, the manuscript compiles under LNCS style, and an evidence-boundary
review has been recorded.  The next step is final human submission decision.

## P0 Promotion Checklist

- [x] Human approved promotion from seed.
- [x] Active directory created under `papers/publication/2026_*`.
- [x] `main.tex` created.
- [x] `PIPELINE.md` created.
- [x] `research_directive.md` created.
- [x] `SOURCE_MAP.md` created from intake evidence.
- [x] `THEOREM_LIST.md` created as discovery-gate theorem spine.
- [x] `ARTIFACT_INVENTORY.md` created from gate and case-study evidence.
- [x] `BIB_SCOPE.md` created from seed bibliography scope.
- [x] Live venue page rechecked.
- [x] Related-work citations verified and tightened.
- [x] LNCS style conversion compiled.
- [x] P4 evidence-boundary review recorded.
- [ ] Source command rerun decision finalized.

## P1 Manuscript Assembly

P1 complete on 2026-06-01.

- `main.tex` now has a stable short-paper structure: problem/contribution,
  architecture, gate summary, case studies, evidence boundary, and scope.
- The draft compiles as 2 content pages plus bibliography under the current
  article format.
- The central contribution is the discovery-gate discipline, not a generic
  project report.

## P2 Venue Check

Venue page checked on 2026-06-01.  See `VENUE_CHECK.md`.

- CICM 2026 presentation-only route is open until 2026-06-15.
- Page budget is 2 pages plus bibliography.
- The official call points to EasyChair and Springer LNCS style files.

P2 complete on 2026-06-01.

- CICM 2026 presentation-only route is open until 2026-06-15.
- Page budget is 2 pages plus bibliography.
- The official call points to EasyChair and Springer LNCS style files.
- Related-work seeds were added for Lean, LeanDojo, Draft--Sketch--Prove, and
  AFP.

Submission-format conversion remains open for P3.

## P3 Format Check

P3 complete on 2026-06-01.

- `main.tex` now uses `llncs`.
- Bibliography style is `splncs04`.
- The manuscript compiles as 2 body pages plus bibliography.
- Remaining layout warnings are small table underfull boxes caused by narrow
  short-paper tables.

## P4 Review

P4 complete on 2026-06-01.  See `P4_REVIEW.md`.

Submission-blocking decisions remaining:

- source-command rerun decision or explicit no-rerun statement;
- final author/affiliation confirmation in the CICM form;
- AI disclosure if the form asks for one.

Resolved artifact/source link decision:

- use the public newmath repository
  `https://github.com/the-omega-institute/newmath` at pinned commit
  `3fb3d6a0641767388a401883062aa522ea0b397b` as the source link for the
  imported theorem spine;
- upload `review_bundle/` and `main.tex` as supplemental review material for
  the CICM presentation-only route;
- do not claim a fresh full rebuild or full artifact evaluation unless the
  relevant command logs are rerun and recorded.

## Route Decision

Use a narrow workshop/presentation claim first.  The first draft should not
wait for a full rebuild of the entire newmath source tree, provided the paper
states that it is reporting path-verified architecture, deterministic gate
design, and case studies.  If the manuscript claims current command results,
the relevant commands in `SOURCE_MAP.md` must be rerun and logged first.

## Non-Claims

- AI output is not proof evidence.
- This paper does not introduce a new theorem prover.
- This paper does not claim complete verification of all BEDC declarations.
- This paper does not claim successful dynamic rerun of the Rule110 suite.
- This paper does not claim automatic journal acceptance or automatic novelty
  judgment.

## Submission Blockers

1. Final source-command rerun decision or explicit no-rerun statement.
2. Decide whether to rerun the newmath command suite or explicitly keep the
   evidence claim at path-verified architecture plus case studies.
3. Confirm author list, affiliations, competing interests, and AI disclosure
   expected by the selected venue.

## Next Actions

- Final: make submission decision after the remaining human-facing items are
  resolved.
- Later review gate: run independent review and Oracle final-review gate after
  drafting, venue review, and formatting have finished.
