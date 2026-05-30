# CICM Two-Page Packet: Auditable Theory-to-Paper Pipeline

This is an intake-level packet for a possible CICM 2026 presentation-only
submission.  It is not `main.tex`, not `PIPELINE.md`, and not an active paper
track.  Its purpose is to make a later human-approved promotion mechanically
fast without letting the daemon treat this seed as active.

- packet date: 2026-05-31
- seed: `papers/publication/newmath_intake/seeds/bedc_automation_pipeline`
- pinned newmath source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- proposed active slug after human approval:
  `2026_auditable_theory_to_paper_pipeline`

## Working Title

Auditable Theory-to-Paper Pipelines for AI-Assisted Formal Mathematics

## One-Paragraph Abstract Draft

Large formal-mathematics projects increasingly use AI agents for drafting,
review, theorem search, and manuscript preparation, but ungated agent output can
produce shallow theorem growth, stale source references, duplicated submission
routes, and premature paper promotion.  This work-in-progress note reports an
auditable theory-to-paper pipeline used around a Lean-backed BEDC/newmath
project and its automath publication workspace.  The architecture separates
source development, intake packets, active paper directories, Oracle review
loops, deterministic gates, and human promotion decisions.  Four case studies
show the role of these gates: an intake boundary preventing seed material from
entering the active manuscript daemon, an overlap/submitted gate preventing
random venue hopping, a fake-extension gate blocking theorem-looking but
content-poor edits, and a Rule 110 artifact gate exposing count drift and an
unresolved collision-audit discrepancy.  The claim is deliberately narrow: AI
outputs are advisory, while load-bearing evidence must remain tied to source
paths, command logs, deterministic checks, and human-approved promotion.

## Two-Page Section Budget

| Section | Target length | Required content | Source intake file |
|---|---:|---|---|
| Problem and contribution | 0.25 page | AI assistance scales review and drafting but creates shallow, stale, and duplicate outputs unless gated. | `scope_contract.md` |
| Architecture | 0.40 page | `D:/omega/newmath` source workspace, automath intake queue, active `2026_*` paper tracks, Oracle review, deterministic gates, human promotion. | `source_map.md`, `source_verification_note.md` |
| Gate table | 0.45 page | Lean build, axiom checks, marker inventory, Phase-D lint, critical-path scheduling, active-paper detection, publication checks. | `gate_table.md` |
| Case-study table | 0.60 page | Intake isolation, upper-fibers overlap block, fake-extension block, Rule110 limitation gate. | `case_evidence_note.md` |
| Scope and non-claims | 0.15 page | No AI-as-proof, no Lean hammer, no automated acceptance, no Rule110 universality or full-source rebuild claim. | `scope_contract.md`, `risk_register.md` |
| Artifact note | 0.15 page | Pinned commit, source paths, commands deferred or required before extended artifact version. | `source_verification_note.md` |

## Compact Gate Table Draft

| Gate | Evidence surface | Failure prevented | Recovery rule |
|---|---|---|---|
| Lean build | `D:/omega/newmath/lean4` | broken formal source | no verified manuscript claim cites a broken target |
| Axiom and purity checks | `tools/check-axioms.py`, `bedc_ci.py axiom-purity --strict` | hidden trusted escapes | mark partial or block verified-status claims |
| Marker and inventory audits | `bedc_ci.py inventory`, marker-existence audit | paper labels pointing to missing source facts | refresh source map or downgrade the claim |
| Phase-D lint | `phase_d_lint.py` | parameter echo and shallow theorem growth | reject and route to theorem-deepening |
| Critical-path scheduling | `critical_path.py` | duplicated or random agent dispatch | score backlog and lock active claims |
| Active-paper detector | automath `pipeline_auto.py` conventions | intake seed entering manuscript daemon | require human promotion plus `2026_*`, `main.tex`, and `PIPELINE.md` |
| Publication check | automath `pub_check.py` | submission-pack metadata gaps | block final submission pack until fixed |

## Four Case Studies

| Case | Gate | Observed issue | Manuscript lesson |
|---|---|---|---|
| Newmath intake isolation | active-paper detector | `newmath_intake` contains no active-trigger files: no `main.tex`, no `PIPELINE.md`, no `2026_*` seed path. | Candidate theory packets can be prepared without becoming active paper jobs. |
| Upper-fibers overlap block | overlap/submitted gate | Later Fibonacci route was blocked because earlier RJ/RINT-related routes overlapped and required explicit closure or merge. | Venue selection must be stateful; the scheduler cannot randomly advance a similar manuscript. |
| Fake-extension block | theorem-content and delta gate | Prior Stage A rounds produced prose-looking or compile-looking changes with no substantive theorem growth. | Agent progress is not accepted merely because a file changed or a draft compiles. |
| Rule110 limitation gate | artifact recheck and limitation ledger | Static counts drifted and collision-audit text conflicted with the reported pass status; the local toolchain could not rerun `make`. | Honest artifact pipelines disclose or block limitations rather than laundering them into claims. |

## Claims Allowed in the CICM Version

- The workflow separates AI-generated suggestions from load-bearing evidence.
- Intake packets are intentionally not active papers until a human promotion
  decision creates a `2026_*` paper track.
- Deterministic gates catch several concrete failure classes: missing source
  references, shallow theorem growth, duplicated submission routes, and
  unresolved artifact evidence.
- The reported source paths and case studies are evidence for workflow
  architecture, not proof of all BEDC mathematical claims.

## Claims Excluded From the CICM Version

- AI output is proof evidence.
- The system is a general theorem prover or Lean hammer.
- The full newmath Lean tree has been freshly rebuilt for this submission.
- Every BEDC declaration is currently axiom-pure.
- The Rule110 artifact suite has been rerun successfully.
- The workflow guarantees mathematical novelty or journal acceptance.

## Promotion-Ready Inputs

If a human approves promotion, copy or adapt these intake materials into the
new active directory:

| Active artifact | Intake source |
|---|---|
| `research_directive.md` | this packet plus `cicm_promotion_brief.md` |
| `SOURCE_MAP.md` | `source_map.md` and `source_verification_note.md` |
| `ARTIFACT_INVENTORY.md` | `gate_table.md`, `case_evidence_note.md`, and source paths |
| `BIB_SCOPE.md` | comparison scope from `risk_register.md` and `submission_memo.md` |
| `PIPELINE.md` | promotion checklist plus CICM presentation-only route |
| `main.tex` | only after promotion; two-page draft based on this packet |

## Final Checks Before Any Submission

1. Re-check the official CICM page for presentation-only availability, page
   limit, bibliography policy, and submission mechanics.
2. Decide whether the two-page note uses the pinned newmath commit as-is or
   records a source update note.
3. Confirm whether the claim remains path-verified architecture plus case
   studies, or whether additional command reruns are required.
4. Confirm author list, affiliations, competing-interest statement, and any AI
   disclosure required by the venue.
