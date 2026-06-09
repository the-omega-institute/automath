# Auditable Auto-Formalization Method

## Snapshot

- Working title: `An Auditable Method for AI-Assisted Auto-Formalization`
- Primary route: `CICM presentation-only / mathematical software workshop route`
- Source seed: `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- Source repo: `D:/omega/newmath`
- Source ref: `origin/dev`
- Source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- Current status: promoted active paper track from newmath intake

## Positioning

This is a systems and mathematical-software note about a rigorous
auto-formalization research method developed across `automath` and
`newmath/BEDC`.  The paper studies how structured mathematical source, formal
interfaces, finite evidence records, agent proposals, and publication-facing
claims can be kept as separate audit axes.

The contribution is not a new theorem prover, not a claim that Lean alone is the
full trust boundary, and not a claim that AI output is proof evidence.  The
load-bearing claim is a portable research discipline: AI-assisted
formalization targets should be decomposed into typed records, with agents
restricted to proposal and repair roles and deterministic gates deciding what
counts as accepted source theory, checked code, finite evidence, or exposition.

## Scope Kept

- `newmath/BEDC` as a structured-theory and mathlib-free formalization instance;
- `automath` as an automated-research, review, and publication instance;
- typed records for source theory, formalization, finite evidence, agent work,
  and reader-facing claims;
- deterministic gates for theorem content, assumptions, markers, artifacts,
  overlap, route state, and submission packets;
- blocked or failed routes as structured research data rather than silent churn.

## Scope Cut

- no claim of fully automatic theorem proving;
- no claim that Lean verification creates BEDC object-language closure;
- no claim of complete rebuild of all BEDC source declarations;
- no claim that substrate artifacts have been dynamically rerun for this note;
- no claim of automatic venue acceptance or automatic novelty judgment.

## Immediate Pipeline Goal

Keep the promoted intake packet framed as a compact two-page system note about
the auditable auto-formalization method, with the longer supplement carrying
exact source interfaces, case evidence, and command-run boundaries.
