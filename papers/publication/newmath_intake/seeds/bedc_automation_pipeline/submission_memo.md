# Submission Memo: BEDC Automation Pipeline

## Current Status

Status: intake-only, not promoted.  This seed should not enter the P0-P7 paper
pipeline until the promotion checklist is complete and a human explicitly
creates an active `2026_*` paper directory.

The source snapshot pinned in this intake is `D:/omega/newmath` `origin/dev`
commit `3fb3d6a0641767388a401883062aa522ea0b397b`.  The local `D:/omega/newmath`
working tree may move ahead of that snapshot; promoted manuscripts must either
use the pinned commit or record a source update note.

## Recommended First Route

Primary fast route: CICM 2026 presentation-only paper.

Rationale:

- The candidate is a mathematical-software and formal-knowledge-management
  workflow paper.
- The presentation-only route can show the architecture and gate evidence
  without needing a full archival journal treatment.
- The paper can gather feedback before a stronger JAR/JFR submission.

Venue check: re-verified on 2026-05-31 against the official CICM 2026 CFP.  The
presentation-only deadline is 2026-06-15, and the route is for
work-in-progress papers of 2 pages plus bibliography.  Agents must still
re-check the official page immediately before submission.

## Fallback Routes

| Route | When to use | Required framing |
|---|---|---|
| COLM workshop contribution | If a workshop accepts AI-for-formal-reasoning or AI-for-science tooling papers | Emphasize LLM governance, deterministic gates, and evaluation of load-bearing outputs |
| ICTAI 2026 | If the paper is broadened into a double-blind AI tools/workflow paper | Emphasize agent orchestration, failure recovery, and reproducibility rather than BEDC theory; use IEEE full/short format |
| JAR | After workshop feedback and stronger artifact tables | Emphasize automated reasoning methodology and proof-assistant gate architecture |
| JFR | If the formalization-workflow evidence becomes central | Emphasize formalized reasoning workflow, source traceability, and reproducibility |

## Draft Shape

The first promoted draft should be short and table-driven:

1. Problem: parallel AI assistance is useful but unsafe without gates.
2. Architecture: source workspace, intake workspace, worker branches, gate
   layers, and publication pipeline.
3. Gates: Lean build, axiom checks, marker existence, phase-D lint,
   critical-path scheduler, quality packet, and publication checks.
4. Failure modes: five to eight concrete failures and recovery actions.
5. Case studies: three to six source or paper tracks.
6. Scope and non-claims: no Lean hammer, no AI-as-proof, no automated
   acceptance claim.
7. Artifact access: source commit, scripts, and verification commands.

## Promotion Blockers

Do not promote until:

- `gate_table.md` is converted into a manuscript-ready table;
- at least three concrete case studies are selected from actual automath or
  newmath history;
- venue page is re-checked again immediately before submission;
- source snapshot is confirmed or updated with a note;
- a human chooses the first venue and approves the active paper slug.
