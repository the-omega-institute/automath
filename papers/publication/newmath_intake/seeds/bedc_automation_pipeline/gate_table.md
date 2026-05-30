# Gate Table: BEDC Automation Pipeline

This intake file records the gates that a promoted manuscript may cite.  It is
not a claim that every command has been re-run from this intake directory.  The
source snapshot is `D:/omega/newmath` `origin/dev`
`3fb3d6a0641767388a401883062aa522ea0b397b`, plus the automath publication
pipeline in `D:/omega/automath`.

| Gate | Source path | Input surface | Failure caught | Recovery action in the paper narrative |
|---|---|---|---|---|
| Lean build | `D:/omega/newmath/lean4/lakefile.*`, Lean source tree | Full Lean project | Type errors, missing declarations, broken imports | Treat as a hard stop; no manuscript claim may cite the broken target |
| Zero-axiom check | `D:/omega/newmath/tools/check-axioms.py` | Compiled Lean declarations | Use of axioms or trusted escapes outside the allowed policy | Reject the round or move the affected claim to partial/statement-only status |
| BEDC audit | `lean4/scripts/bedc_ci.py audit` | Lean and BEDC paper sources | Forbidden constructs, origin/closure-status problems, structural mismatch | Open a deterministic repair task before any agent rewrite |
| Declaration inventory | `lean4/scripts/bedc_ci.py inventory` | Lean declarations, fields, paper labels, Lean markers | Drift between paper labels, Lean targets, and available declarations | Refresh source map and theorem inventory before writing claims |
| Marker-existence audit | `lean4/scripts/bedc_ci.py marker-existence-audit` | Paper Lean-marker macros and Lean declarations | A paper marker points to a nonexistent Lean target | Fix marker or downgrade the manuscript claim |
| Axiom-purity audit | `lean4/scripts/bedc_ci.py axiom-purity --strict` | BEDC declaration dependency surface | Transitive axiom leakage in targets claimed as verified | Block promotion until the target is axiom-clean or explicitly marked partial |
| MetaCIC purity audit | `lean4/scripts/bedc_ci.py metacic-purity` | MetaCIC-specific targets | Axioms or impurity in a mechanized type-theory slice | Keep MetaCIC claims out of this systems paper unless the audit passes |
| Phase-D hard lint | `lean4/scripts/phase_d_lint.py` | New declarations in a worker branch | Parameter echo, missing BEDC anchor, shallow duplicate conclusion | Reject shallow theorem growth even if the file compiles |
| Critical-path scheduling | `lean4/scripts/critical_path.py` | Formalization backlog and dispatch state | Convergence on duplicated low-value tasks, missed high-impact blockers | Use scored dispatch windows instead of random paper or theorem selection |
| Lean round orchestration | `lean4/scripts/codex_formalize.py` | Worktree-based formalization rounds | Dirty worktrees, duplicate labels, failed build/lint stages | Isolate worker branches and require post-round gates |
| Paper round orchestration | `papers/bedc/scripts/codex_revise.py` | BEDC manuscript parts | Unreviewed paper edits, missing deepening target, weak revision packets | Generate review/deepening packets before source edits |
| AI quality packet | `papers/bedc/tools/auto-ai-quality/README.md` | Candidate AI outputs | Low load-bearing score, weak theorem content, review-only output | Keep the LLM as advisory; promote only deterministic, source-tied work |
| Self-heal daemon | `tools/auto_heal_base.py` | Routine Lean/paper failures | Gate storms, duplicate labels, stuck dirt, repeated mechanical failures | Apply bounded deterministic repairs; escalate nonroutine failures |
| Active-paper detector | `D:/omega/automath/papers/publication/pipeline_auto.py` | `papers/publication/*` directories | Seed directories accidentally becoming active pipeline papers | Require `2026_*`, `main.tex`, and `PIPELINE.md` only after promotion |
| Publication quality check | `D:/omega/automath/papers/publication/pub_check.py` | Active paper directory | Missing pipeline metadata, citation/style/proof checklist failures | Block submission pack until P-stage checks pass |

## Commands to Re-Verify Before Promotion

These commands belong to the source workspaces, not to this intake directory.

```powershell
git -C D:/omega/newmath rev-parse origin/dev
cd D:/omega/newmath/lean4; lake build
cd D:/omega/newmath; python tools/check-axioms.py
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py audit
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py inventory
cd D:/omega/newmath; python lean4/scripts/bedc_ci.py axiom-purity --strict
cd D:/omega/automath/papers/publication; python pipeline_auto.py status
```

If the source commit changes, record a source update note before using new
results in a promoted manuscript.
