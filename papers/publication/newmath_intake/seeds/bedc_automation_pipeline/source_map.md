# Source Map: BEDC Automation Pipeline

| Role | Path | Source | Notes |
|---|---|---|---|
| AI formalization loop | `docs/dossier/discovery-loop.qmd` | newmath | Public-facing narrative and failure taxonomy |
| formalization route map | `docs/dossier/formalization-routes.qmd` | newmath | Comparison axes for formalization systems |
| core audit script | `lean4/scripts/bedc_ci.py` | newmath | Marker existence, inventory, axiom-purity, closurestatus |
| scheduler | `lean4/scripts/critical_path.py` | newmath | Critical-path and formal-axis targeting |
| hard lint | `lean4/scripts/phase_d_lint.py` | newmath | Parameter-echo and shallow-growth rejection |
| Lean orchestrator | `lean4/scripts/codex_formalize.py` | newmath | Worktree-based R rounds |
| paper orchestrator | `papers/bedc/scripts/codex_revise.py` | newmath | Worktree-based P rounds |
| quality layer | `papers/bedc/tools/auto-ai-quality/README.md` | newmath | Load-bearing review packets |
| self-heal daemon | `tools/auto_heal_base.py` | newmath | Auto-heal and gate-storm response |
| publication pipeline | `papers/publication/AUTOMATION.md` | automath | P0-P7 workflow |
| publication scheduler | `papers/publication/pipeline_auto.py` | automath | Stage detection and prompts |
| publication checks | `papers/publication/pub_check.py` | automath | Manuscript quality gates |

## Verification Commands

The paper should report commands as evidence, not as commands run from this
intake directory.

```bash
cd D:/omega/newmath/lean4 && lake build
cd D:/omega/newmath && python3 tools/check-axioms.py
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py audit
cd D:/omega/newmath && python3 lean4/scripts/bedc_ci.py axiom-purity --strict
cd D:/omega/automath/papers/publication && python pipeline_auto.py status
```

