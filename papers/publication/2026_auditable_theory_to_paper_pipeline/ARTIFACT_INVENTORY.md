# Artifact Inventory

## Gate Inventory

This table is a path catalogue for gates used by the workflow. It is not a command-run record: the current package does not include fresh Lean build, zero-axiom, BEDC audit, marker-existence audit, axiom-purity audit, daemon-run, or dynamic artifact-validation logs unless a separate row supplies command, source state, environment, exit code, and log path.

| Gate | Source path | Failure prevented | Manuscript use |
|---|---|---|---|
| Lean build | `D:/omega/newmath/lean4` | broken formal source | hard stop for verified claims |
| zero-axiom check | `D:/omega/newmath/tools/check-axioms.py` | hidden trusted escapes | proof-source trust boundary |
| BEDC audit | `lean4/scripts/bedc_ci.py audit` | forbidden constructs and closure-status problems | source-quality gate |
| declaration inventory | `lean4/scripts/bedc_ci.py inventory` | stale paper labels or missing declarations | source-map discipline |
| marker-existence audit | `lean4/scripts/bedc_ci.py marker-existence-audit` | paper marker points to nonexistent source target | citation/provenance gate |
| axiom-purity audit | `lean4/scripts/bedc_ci.py axiom-purity --strict` | transitive axiom leakage | verified-claim gate |
| phase-D hard lint | `lean4/scripts/phase_d_lint.py` | parameter echo and shallow theorem growth | anti-hollow theoremization gate |
| critical-path scheduling | `lean4/scripts/critical_path.py` | duplicated or random dispatch | backlog and priority discipline |
| paper revision orchestration | `papers/bedc/scripts/codex_revise.py` | weak revision packets | review/deepening discipline |
| AI quality packet | `papers/bedc/tools/auto-ai-quality/README.md` | low load-bearing score | advisory-AI boundary |
| active-paper detector | `D:/omega/automath/papers/publication/pipeline_auto.py` | seed treated as active paper | promotion boundary |
| publication check | `D:/omega/automath/papers/publication/pub_check.py` | missing submission metadata | submission-pack gate |

## Case Studies

| Case | Gate | Observed issue | Safe manuscript lesson |
|---|---|---|---|
| Newmath intake isolation | active-paper detector | intake seed material is not active until human promotion creates `2026_*`, `main.tex`, and `PIPELINE.md` | candidate material can be prepared without entering the daemon |
| Upper-fibers overlap block | overlap/submitted gate | a later Fibonacci route was blocked because earlier related routes overlapped and required closure, merge, supersession, or waiting | venue selection must be stateful |
| Fake-extension block | theorem-content and delta gate | edits that looked like progress did not add substantive theorem content | compilation or file churn is not sufficient |
| Rule110 limitation gate | artifact recheck and limitation ledger | count drift and a collision-audit contradiction prevented clean artifact claims | limitations must be disclosed or block promotion |

## Current Evidence Boundary

The current draft may cite these artifacts as source-path and workflow
evidence.  It must not claim a fresh full-source rebuild or a fresh Rule110
dynamic artifact rerun until command logs are added.
