# Pipeline: Auditable Theory-to-Paper Pipeline

## Metadata

- paper slug: `2026_auditable_theory_to_paper_pipeline`
- target journal: CICM presentation-only / mathematical software workshop route
- fallback venues: COLM workshop; ICTAI-style AI systems venue; later JAR/JFR
  systems paper after stronger artifact evidence
- source seed: `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- newmath source ref: `origin/dev`
- newmath source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- promoted: 2026-05-31

## Current Stage

P0 complete: active paper directory created from approved newmath intake
promotion.  The next step is P1 manuscript assembly followed by P2
literature and venue verification.

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
- [ ] Live venue page rechecked.
- [ ] Related-work citations verified and tightened.
- [ ] Source command rerun decision finalized.

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

1. Live venue check for presentation-only availability, page limit,
   bibliography policy, and submission mechanics.
2. Bibliography pass for proof-assistant workflows, AI-assisted
   formalization, mathematical knowledge management, and artifact
   reproducibility.
3. Decide whether to rerun the newmath command suite or explicitly keep the
   evidence claim at path-verified architecture plus case studies.
4. Confirm author list, affiliations, competing interests, and AI disclosure
   expected by the selected venue.

## Next Actions

- P1: strengthen `main.tex` into a polished two-page draft.
- P2: perform live venue and bibliography verification.
- P3: compile and fix formatting.
- Later review gate: run independent review and Oracle final-review gate after
  drafting, venue review, and formatting have finished.
