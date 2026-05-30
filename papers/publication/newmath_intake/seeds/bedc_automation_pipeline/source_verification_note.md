# Source Verification Note: BEDC Automation Pipeline

This is an intake-level verification note for the proposed automation-pipeline
paper.  It does not promote the seed.

- verification date: 2026-05-31
- newmath source repo: `D:/omega/newmath`
- newmath source ref: `origin/dev`
- newmath source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- automath companion repo: `D:/omega/automath`

## Pinned Source Path Check

The following source paths were checked for existence at the pinned newmath
commit:

| Path | Exists at pinned ref | Intended use |
|---|---|---|
| `docs/dossier/discovery-loop.qmd` | yes | Narrative for discovery loops and failure taxonomy. |
| `docs/dossier/formalization-routes.qmd` | yes | Comparison axes for formalization routes. |
| `lean4/scripts/bedc_ci.py` | yes | BEDC audit, inventory, marker, and axiom-purity gates. |
| `lean4/scripts/critical_path.py` | yes | Critical-path scheduling evidence. |
| `lean4/scripts/phase_d_lint.py` | yes | Hard lint against shallow theorem growth. |
| `lean4/scripts/codex_formalize.py` | yes | Lean formalization orchestration. |
| `papers/bedc/scripts/codex_revise.py` | yes | BEDC paper revision orchestration. |
| `papers/bedc/tools/auto-ai-quality/README.md` | yes | AI quality packet and load-bearing review layer. |
| `tools/auto_heal_base.py` | yes | Self-heal daemon evidence. |

The following automath companion paths were checked in the current workspace:

| Path | Exists locally | Intended use |
|---|---|---|
| `papers/publication/AUTOMATION.md` | yes | Publication workflow and P-stage conventions. |
| `papers/publication/pipeline_auto.py` | yes | Active-paper detection and scheduler logic. |
| `papers/publication/pub_check.py` | yes | Publication quality gates. |

## Commands Not Yet Re-Run

The source paths exist, but this note does not claim that the full source
verification suite has been re-run.  These commands remain promotion blockers:

```powershell
cd D:/omega/newmath/lean4; lake build
cd D:/omega/newmath; python tools/check-axioms.py
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py audit
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py inventory
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py axiom-purity --strict
cd D:/omega/automath/papers/publication; python pipeline_auto.py status
```

## Venue Verification Not Yet Done

The first-route strategy names CICM 2026 presentation-only as the preferred
fast route, with COLM workshop and ICTAI-style routes as fallbacks.  This note
does not verify current official deadlines or submission rules.  Before
promotion, check the live venue pages and record exact deadlines, submission
format, page limits, archival status, and whether presentation-only submission
is still open.

## Promotion Consequence

This seed is source-path verified but not gate-verified and not
venue-verified.  It may proceed to promotion discussion only after either:

1. the full source command suite is re-run successfully; or
2. the promoted manuscript explicitly narrows its evidence claims to the
   path-verified source architecture plus case studies already recorded in
   `case_studies.md`.
