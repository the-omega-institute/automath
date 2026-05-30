# Promotion Decision Memo: BEDC Automation Pipeline

This memo records the remaining human decision before this seed can become an
active paper.  It does not itself promote the seed and does not create a
`2026_*` directory.

## Current Intake State

The seed is ready for a promotion decision under a narrow CICM
presentation-only route:

- venue: CICM 2026 presentation-only
- verified deadline: 2026-06-15
- format: 2 pages plus bibliography
- proposed active slug: `2026_auditable_theory_to_paper_pipeline`

The seed has:

- source paths verified at the pinned newmath snapshot;
- official first-route timing verified;
- four selected case studies;
- exact evidence notes for the case studies;
- scope and non-claim boundaries;
- a two-page promotion brief.

## Decision: Source-Gate Rerun vs Narrowed Claim

The recommended route is **narrowed claim promotion**, not full source-gate
rerun before promotion.

Reason:

- CICM presentation-only is a short work-in-progress route, not a journal
  artifact paper.
- The selected claim is about the workflow architecture and case-study
  evidence, not about certifying every BEDC formal theorem in the source tree.
- Full `lake build`, axiom-purity, and BEDC audit reruns are appropriate for an
  extended artifact appendix or later JAR/JFR version, but they are not required
  to state the narrow two-page claim if the manuscript is honest about the
  evidence level.

## Allowed Narrow Claim

The promoted two-page manuscript may claim:

> The BEDC/automath workflow separates AI-generated suggestions from
> load-bearing evidence by using source maps, intake/active-paper boundaries,
> deterministic gates, and case-level failure records.

It may cite:

- path-verified source architecture;
- selected case evidence from `case_evidence_note.md`;
- gate taxonomy from `gate_table.md` and `failure_modes.md`;
- the active-paper boundary check showing no `main.tex`, no `PIPELINE.md`, and
  no `2026_*` under `newmath_intake`.

## Claims Deferred to an Extended Artifact Version

The promoted CICM version must not claim:

- the full newmath Lean tree was freshly rebuilt for the CICM submission;
- every BEDC declaration is axiom-pure in the current workspace;
- the Rule110 artifact suite was rerun;
- the workflow guarantees mathematical novelty;
- AI-generated outputs are proof evidence.

## Promotion Preconditions Remaining

Before creating the active paper directory, the human must approve promotion and
the active slug.  After promotion, the first active-paper tasks are:

1. copy `cicm_promotion_brief.md` into the paper workspace as the draft plan;
2. convert `case_evidence_note.md` into a compact case-study table;
3. create `SOURCE_MAP.md`, `ARTIFACT_INVENTORY.md`, `BIB_SCOPE.md`,
   `PIPELINE.md`, and `main.tex`;
4. re-check the CICM page immediately before submission.
