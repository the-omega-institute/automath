# Research Directive

This file is the stable directive for the promoted active paper
`2026_auditable_theory_to_paper_pipeline`.

## Publication Goal

Prepare a compact workshop/presentation paper on a rigorous auditable method
for AI-assisted auto-formalization.  The paper should be suitable for a
CICM-style mathematical software or formal-methods venue after live venue and
bibliography verification.

## Central Claim

Large AI-assisted mathematics projects need a research discipline that keeps
source theory, formalization, finite evidence, agent proposals, and
publication-facing claims separate.  In the `newmath/BEDC` and `automath`
workflow, the same discipline appears in two forms: `newmath` supplies a
structured-theory and mathlib-free formalization instance, while `automath`
supplies automated derivation, review, publication packaging, and route
governance.  The intended contribution is to make this auto-formalization method
portable, not merely to describe one local publication pipeline.

## Required Spine

The manuscript must center the auto-formalization method:

- generated material is not evidence until it has a typed record and a gate;
- BEDC is finite-kernel theory plus proof obligations plus separate
  implementation contracts;
- theoretical closure and formal verification are distinct audit axes;
- Lean markers are meaningful verification records but do not create
  object-language closure;
- finite substrate claims are carried by manifest rows and evaluator outcomes;
- agents may propose/search/review/repair but cannot certify theory increments;
- automath and newmath are two instances of one research discipline: structured
  source, typed formalization targets, finite evidence, deterministic gates, and
  human promotion boundaries.

## Case-Study Discipline

The two-page CICM version should not be organized around individual rejected
papers, overlap incidents, or local route names.  Concrete case evidence belongs
in `main.tex` and `review_bundle/`.  The short paper may mention blocked or
failed routes only as evidence that the method converts agent churn into
structured research data such as overlap, hollow-theorem growth, novelty
failure, or insufficient artifact evidence.

## Scope Discipline

Do not broaden this draft into a general AI safety paper, a Lean hammer paper,
or a complete BEDC theory paper.  The target contribution is a rigorous
auto-formalization methodology in which Lean is necessary but not the sole trust
boundary, and publication automation is one output layer rather than the whole
story.

## Verification Rule

If the draft states that a command was run for this submission, the exact
command, source commit, environment, exit code, and log path must be recorded.
Otherwise, phrase the evidence as path-verified source architecture and
historical case evidence.
