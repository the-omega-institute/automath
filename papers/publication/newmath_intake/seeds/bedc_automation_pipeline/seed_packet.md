# Seed Packet: BEDC Automation Pipeline

## Proposed Paper Unit

An audit-driven systems paper on AI-assisted Lean formalization and
theory-to-paper publication automation under strict proof and manuscript gates.

## Priority

P0.

## Source of Truth

- Repo: `D:/omega/newmath`
- Ref: `origin/dev`
- Commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- Companion repo for publication-workflow comparison: `D:/omega/automath`

## Candidate Claim

The paper claims that a large Lean-backed theory project can be advanced by
parallel AI agents when every increment is routed through mechanical gates:
Lean build, axiom keyword checks, transitive axiom-purity, paper-Lean marker
audits, anti-hollow lints, critical-path scheduling, and source-map based
publication tracking.

## Non-Claims

- It does not claim that AI replaces mathematicians.
- It does not claim that generated theorems are valuable merely because they
  compile.
- It does not claim to be a Lean hammer or a general ATP integration.
- It does not claim journal acceptance is automated.

## Key Source Paths

- `docs/dossier/discovery-loop.qmd`
- `docs/dossier/formalization-routes.qmd`
- `lean4/scripts/bedc_ci.py`
- `lean4/scripts/critical_path.py`
- `lean4/scripts/phase_d_lint.py`
- `lean4/scripts/codex_formalize.py`
- `papers/bedc/scripts/codex_revise.py`
- `papers/bedc/tools/auto-ai-quality/README.md`
- `tools/auto_heal_base.py`
- `D:/omega/automath/papers/publication/AUTOMATION.md`
- `D:/omega/automath/papers/publication/pipeline_auto.py`
- `D:/omega/automath/papers/publication/pub_check.py`

## Evidence to Extract

- Gate list and failure modes: `axiom-purity --strict`, marker drift,
  duplicate labels, shape saturation, parameter echo, missing BEDC touchpoint.
- Scheduling logic: critical-path scores, top-window dispatch, capstone
  candidates, formal-axis targets.
- Publication workflow: `SOURCE_MAP.md`, `THEOREM_LIST.md`, `WORKBOARD.md`,
  `JOURNAL_PROFILE.md`, and `PIPELINE.md` conventions from automath.
- Case studies from 6-10 tracks showing missing theorem maps, venue-fit issues,
  overlap blockers, citation gaps, or manuscript-stage gates found by the
  automation.

## Intake Artifacts Added

- `scope_contract.md`: exact scope, non-claims, and promotion evidence.
- `gate_table.md`: gate/source/failure/recovery table for the promoted draft.
- `failure_modes.md`: concrete failure-mode taxonomy and case-study schema.
- `submission_memo.md`: first-route strategy, fallback routes, and blockers.
- `promotion_checklist.md`: explicit intake status and hard no-promotion rules.
- `case_studies.md`: six concrete candidate case-study rows grounded in current
  automath/newmath evidence.
- `source_verification_note.md`: path-level verification for pinned source
  references, with command and venue checks still blocked.
- `cicm_promotion_brief.md`: a two-page CICM presentation-only shape with four
  selected case studies and remaining promotion blockers.

## Current First Route

First route: CICM 2026 presentation-only, subject to official deadline
re-verification before submission.  COLM workshop and ICTAI are fallback routes
if the framing is shifted toward AI systems or LLM-governed formal reasoning.
Journal routes such as JAR/JFR should wait for stronger case-study evidence.

## Promotion Target

Candidate active directory:

`papers/publication/2026_auditable_theory_to_paper_pipeline/`
