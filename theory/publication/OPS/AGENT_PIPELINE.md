# Publication Agent Pipeline

This directory is the operational surface for publication work.

The goal is not to build a heavier Python layer. The goal is to let
multiple agents push real manuscripts toward submission by claiming
bounded tasks inside real paper directories.

## Core rule

- Scripts may generate diagnostics.
- Publication progress happens by editing paper directories directly.
- Every stage must leave a file artifact that the next agent can read.

## Stage order

1. `P0 Intake`
   Required files: `README.md`, `main.tex`, target-journal note.
2. `P1 Traceability`
   Required files: `SOURCE_MAP.md`, `THEOREM_LIST.md`.
3. `P2 Research Extension`
   Required file: `TASK_CARD_P2_RESEARCH_EXTENSION.md`.
4. `P3 Journal Rewrite`
   Required file: `TASK_CARD_P3_JOURNAL_REWRITE.md`.
5. `P4 Editorial Review`
   Required file: `TASK_CARD_P4_EDITORIAL_REVIEW.md`.
6. `P5 Integration`
   Required file: `TRACK_BOARD.md` updated with decisions and remaining blockers.
7. `P6 Lean Sync`
   Required output: mismatch notes or formalization backlog update.
8. `P7 Submission Pack`
   Required output: final checklist and status promotion in the program board.

## Role split

- Orchestrator: owns `OPS/ACTIVE_WAVE.md` and `OPS/AGENT_CLAIMS.md`.
- Traceability agent: owns `SOURCE_MAP.md` and `THEOREM_LIST.md`.
- Research agent: strengthens statements, cuts weak material, proposes sharper theorem packaging.
- Journal rewrite agent: rewrites title, abstract, introduction, roadmap, and section flow for the target journal.
- Editorial review agent: writes a decision-grade review with blockers.
- Integrator: merges accepted changes into the manuscript and updates the track board.
- Lean sync agent: checks paper statements against Lean labels or backlog where applicable.

## Handoff rule

No agent finishes a stage by chat message alone. A stage is done only when
the paper directory contains the artifact that records what changed, what
remains open, and what the next agent should do.

## Default wave

The first active wave on this branch is:

- `2026_conservative_extension_chain_state_forcing_apal`
- `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
- `2026_projection_ontological_mathematics_core_tams`

These three tracks are first because they already have real manuscripts
and are marked as first-batch targets in the publication program.
