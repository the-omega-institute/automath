# Research Directive

This file is the stable directive for the promoted active paper
`2026_auditable_theory_to_paper_pipeline`.

## Publication Goal

Prepare a compact workshop/presentation paper on an auditable theory compiler
for AI-assisted formal mathematics.  The paper should be suitable for a
CICM-style mathematical software or formal-methods venue after live venue and
bibliography verification.

## Central Claim

Large AI-assisted mathematics projects need a compiler-level architecture that
keeps source theory, formal verification, finite substrate witnesses, discovery
automation, and publication-facing claims separate.  In the BEDC/newmath and
automath workflow, BEDC supplies the structured mathematical source theory,
Lean supplies an independent verification axis, manifest/evaluator records
supply finite-witness substrate evidence, agents supply proposals and review,
and automath compiles accepted increments into reviewable paper tracks.

## Required Spine

The manuscript must center the theory-compiler architecture:

- BEDC is finite-kernel theory plus proof obligations plus separate
  implementation contracts;
- theoretical closure and formal verification are distinct audit axes;
- Lean markers are meaningful verification records but do not create
  object-language closure;
- finite substrate claims are carried by manifest rows and evaluator outcomes;
- agents may propose/search/review but cannot certify theory increments;
- automath is the final publication compiler, not the whole contribution.

## Case-Study Discipline

The two-page CICM version should not be organized around individual rejected
papers, overlap incidents, or local route names.  Concrete case evidence belongs
in `main.tex` and `review_bundle/`.  The short paper may mention examples only
when they illustrate a system layer such as finite witnesses, theorem-content
gates, or route governance.

## Scope Discipline

Do not broaden this draft into a general AI safety paper, a Lean hammer paper,
or a complete BEDC theory paper.  The target contribution is an auditable theory
compiler architecture in which Lean is necessary but not the sole trust
boundary, and publication automation is one output layer rather than the whole
story.

## Verification Rule

If the draft states that a command was run for this submission, the exact
command, source commit, environment, exit code, and log path must be recorded.
Otherwise, phrase the evidence as path-verified source architecture and
historical case evidence.
