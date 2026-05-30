# Scope Contract: BEDC Automation Pipeline

## Paper Unit

This seed is an intake-stage candidate for a systems and methodology paper on
audit-driven AI assistance for a Lean-backed mathematical project and its
publication pipeline.  The paper unit is the workflow architecture: how local
agents propose changes, how deterministic gates reject weak or unsafe changes,
how source maps keep manuscripts tied to formal artifacts, and how publication
work is kept separate from theorem-source development.

## Central Claim

The central claim is that a large formalization-and-publication project can use
parallel AI assistance without treating AI output as evidence, provided each
increment is routed through explicit audit gates: Lean build checks, axiom
audits, marker existence checks, transitive axiom-purity checks, hard lints for
shallow theorem growth, critical-path scheduling, source-map discipline, and
submission-stage manuscript checks.

## In-Scope Evidence

| Evidence unit | Source path | Intake use |
|---|---|---|
| Lean and paper audit surface | `lean4/scripts/bedc_ci.py` | Gate table and marker/axiom audit examples |
| Critical-path scheduler | `lean4/scripts/critical_path.py` | Scheduling section and dispatch-window table |
| Phase-D lint | `lean4/scripts/phase_d_lint.py` | Failure-mode examples for shallow theorem growth |
| Lean round orchestrator | `lean4/scripts/codex_formalize.py` | Agent-loop architecture and worktree isolation |
| Paper round orchestrator | `papers/bedc/scripts/codex_revise.py` | Manuscript revision loop comparison |
| Quality packet layer | `papers/bedc/tools/auto-ai-quality/README.md` | Deterministic reviewer-packet layer |
| Self-heal daemon | `tools/auto_heal_base.py` | Gate-storm and routine repair layer |
| Publication pipeline | `D:/omega/automath/papers/publication/AUTOMATION.md` | P0-P7 publication workflow comparison |
| Publication scheduler | `D:/omega/automath/papers/publication/pipeline_auto.py` | Active-paper detection boundary |
| Publication checks | `D:/omega/automath/papers/publication/pub_check.py` | Manuscript-stage quality gate list |

## Out-of-Scope Claims

- The paper must not claim to be a general theorem prover, Lean hammer, or ATP
  integration.
- The paper must not claim that AI output is proof evidence.
- The paper must not claim that generated theorem counts imply mathematical
  value.
- The paper must not claim that journal submission or acceptance is automated.
- The paper must not present BEDC's mathematical theory as the contribution of
  this paper except as a motivating case study.
- The paper must not merge the Rule 110 finite-witness artifact paper or the
  finite-kernel calculus paper into this unit unless a later human promotion
  decision explicitly changes the scope.

## Required Promotion Evidence

Promotion to an active `2026_*` paper track requires all of the following:

1. A gate-by-gate architecture table with source paths and failure classes.
2. At least five concrete failure modes, including at least one Lean-source
   failure, one paper-source failure, one publication-pipeline failure, and one
   scheduling or stuck-task failure.
3. A case-study table with three to six tracks showing an issue detected by the
   automation and the resulting corrective action.
4. A short comparison section positioning the system against AI-for-theorem-
   proving and formalization-assistance work without overstating novelty.
5. A venue-specific submission memo for the first target venue.
6. A source snapshot note confirming whether the promoted paper uses the pinned
   `D:/omega/newmath` `origin/dev` commit
   `3fb3d6a0641767388a401883062aa522ea0b397b` or a documented source update.

## First Route

The first practical route is a presentation/workshop-style paper.  The strongest
short-window candidate is CICM 2026 presentation-only if the paper remains a
concise workflow and artifact presentation.  COLM workshop and ICTAI routes are
fallbacks for an AI-systems framing.  A journal route should wait until the
artifact tables and comparison section are substantially stronger.
