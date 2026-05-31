# Source Map

- source seed:
  `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- source repo: `D:/omega/newmath`
- source ref: `origin/dev`
- source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- publication repo: `D:/omega/automath`

## Source Paths

| Role | Path | Source | Use |
|---|---|---|---|
| discovery loop narrative | `docs/dossier/discovery-loop.qmd` | newmath | failure taxonomy and discovery-loop framing |
| formalization route map | `docs/dossier/formalization-routes.qmd` | newmath | comparison axes for formalization workflows |
| core audit script | `lean4/scripts/bedc_ci.py` | newmath | inventory, marker, and axiom-purity gates |
| scheduler | `lean4/scripts/critical_path.py` | newmath | critical-path and formal-axis targeting |
| anti-hollow lint | `lean4/scripts/phase_d_lint.py` | newmath | parameter echo and shallow-growth rejection |
| Lean orchestration | `lean4/scripts/codex_formalize.py` | newmath | worktree-based formalization rounds |
| paper orchestration | `papers/bedc/scripts/codex_revise.py` | newmath | worktree-based paper revision rounds |
| AI quality packet | `papers/bedc/tools/auto-ai-quality/README.md` | newmath | load-bearing review packets |
| self-heal daemon | `tools/auto_heal_base.py` | newmath | bounded repair and gate-storm response |
| discovery-gate calculus | `papers/bedc/parts/visions/audit_map_methodology/automated_theory_discovery_pipeline_calculus.tex` | newmath | formal/expository theorem spine |
| publication automation | `papers/publication/AUTOMATION.md` | automath | publication workflow conventions |
| active-paper detector | `papers/publication/pipeline_auto.py` | automath | `2026_*`, `main.tex`, `PIPELINE.md` active-track detection |
| publication quality checks | `papers/publication/pub_check.py` | automath | submission-pack checks |

## Commands To Rerun Before Stronger Claims

These are not claimed as freshly rerun by this promoted draft unless a later
log is added.

```powershell
git -C D:/omega/newmath rev-parse origin/dev
cd D:/omega/newmath/lean4; lake build
cd D:/omega/newmath; python tools/check-axioms.py
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py audit
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py inventory
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py axiom-purity --strict
cd D:/omega/automath/papers/publication; python pipeline_auto.py status
```

## Source Update Rule

If the manuscript adopts any `D:/omega/newmath` commit newer than
`3fb3d6a0641767388a401883062aa522ea0b397b`, record a source update note before
changing manuscript claims.
