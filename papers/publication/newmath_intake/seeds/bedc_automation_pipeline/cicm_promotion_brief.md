# CICM Promotion Brief: BEDC Automation Pipeline

This is an intake-level brief for a possible CICM 2026 presentation-only
submission.  It is not a promoted manuscript and must not be treated as an
active `2026_*` paper.

## Venue Constraint

- target route: CICM 2026 presentation-only
- verified deadline: 2026-06-15
- format constraint: work-in-progress paper, 2 pages plus bibliography
- implication: the first draft must be table-driven and must avoid broad
  journal-style claims

## Proposed Two-Page Claim

Parallel AI assistance can be useful in a Lean-backed mathematical project only
when AI proposals are kept advisory and every load-bearing increment is routed
through deterministic gates.  The BEDC/automath workflow demonstrates a
source-mapped architecture that separates theory-source development, intake
planning, active paper promotion, overlap/submitted blocking, and manuscript
readiness checks.

## Minimal Paper Shape

| Section | Target length | Content |
|---|---:|---|
| Problem and contribution | 0.25 page | AI agents can scale drafting and formalization work, but ungated output creates shallow theorems, marker drift, overlap errors, and premature submissions. |
| Architecture | 0.45 page | Newmath source workspace, automath publication workspace, intake seeds, active paper directories, daemon/oracle review loop, and deterministic gates. |
| Gate table | 0.50 page | Lean build, axiom checks, marker existence, phase-D lint, critical-path scheduler, active-paper detector, publication checks. |
| Case-study table | 0.55 page | Four concrete cases: intake isolation, overlap block, fake-extension block, Rule110 limitation gate. |
| Scope and non-claims | 0.15 page | No AI-as-proof, no Lean hammer, no automated acceptance, no Rule110 universality claim. |
| Artifact note | 0.10 page | Pinned source commit, source paths, and commands to re-run. |

## Recommended Case Studies

Use exactly four cases in the first two-page version:

| Case | Why it fits two pages | Evidence status |
|---|---|---|
| Newmath intake isolation | Shows the architectural boundary between candidate material and active publication automation. | Current intake check verifies no `main.tex`, no `PIPELINE.md`, and no `2026_*` under `newmath_intake`. |
| Upper-fibers overlap block | Shows deterministic submitted/overlap gate preventing random venue hopping. | Exact machine-board and log evidence summarized in `case_evidence_note.md`. |
| Fake-extension block after theoremization | Shows why compile-looking or rewrite-looking progress is insufficient. | Exact machine-board examples summarized in `case_evidence_note.md`. |
| Rule110 finite-witness limitation | Shows artifact honesty and non-claim enforcement. | Intake recheck found count drift and a collision-audit contradiction; evidence summarized in `case_evidence_note.md`. |

Do not include C-INFRA-STUCK or C-NEAR-PASS in the first CICM version unless
space remains.  They are better for a longer systems paper.

## Gate Table Spine

| Gate | Source | Failure prevented | Paper role |
|---|---|---|---|
| Lean build | `D:/omega/newmath/lean4` | Broken formal source | Hard proof-source stop |
| Axiom and purity checks | `tools/check-axioms.py`, `lean4/scripts/bedc_ci.py axiom-purity --strict` | Hidden trusted escapes | Verified-claim boundary |
| Marker and inventory audits | `lean4/scripts/bedc_ci.py` | Paper labels pointing to missing or stale Lean facts | Source-map discipline |
| Phase-D lint | `lean4/scripts/phase_d_lint.py` | Parameter echo and shallow theorem growth | Anti-hollow theoremization |
| Critical-path scheduling | `lean4/scripts/critical_path.py` | Random or duplicated agent dispatch | Backlog control |
| Active-paper detector | `papers/publication/pipeline_auto.py` | Intake seed treated as active paper | Promotion boundary |
| Publication check | `papers/publication/pub_check.py` | Missing submission metadata or manuscript readiness gaps | Submission-pack gate |

## Promotion Blockers Remaining

The seed can be promoted only after a human explicitly approves creating an
active paper directory.  Before that approval, the following blockers remain:

- choose whether the promoted paper uses the pinned newmath commit or a source
  update note;
- decide whether to re-run the source command suite before the two-page CICM
  submission or explicitly narrow the evidence claim to path-verified
  architecture plus case studies;
- carry `case_evidence_note.md` into the promoted manuscript workspace and
  reduce it to a compact case-study table;
- re-check the CICM page immediately before submission.

## Suggested Promotion Slug

`2026_auditable_theory_to_paper_pipeline`
