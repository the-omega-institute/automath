# Agent Roles

The pipeline is designed for parallel execution. Agents should own a
stage or a bounded write scope, not an abstract topic.

## 1. Orchestrator

- chooses which papers enter the pipeline
- assigns owners
- enforces stage order and handoffs
- resolves collisions and reprioritizes

## 2. Traceability Agent

- owns `SOURCE_MAP.md`
- owns `THEOREM_LIST.md`
- links source sections and Lean anchors

## 3. Research Agent

- owns theorem-level deepening
- proposes stronger statements or sharper cuts
- does not rewrite full exposition unless explicitly assigned

## 4. Journal Rewrite Agent

- rewrites abstract, introduction, theorem roadmap, section flow
- aligns the paper with target-journal style

## 5. Editorial Review Agent

- performs decision-grade review
- identifies blockers, weak claims, and structural problems

## 6. Bibliography / Recon Agent

- studies recent target-journal papers
- updates bibliography scope and related-work positioning

## 7. Lean Sync Agent

- checks labels and declarations against Lean inventory
- updates formalization backlog and mismatch notes

## 8. Integrator

- applies review findings
- merges stage outputs into the manuscript
- prepares the submission package

## Role Boundary

- One manuscript may have multiple agents, but only one agent should own
  a given file group at a time.
- Research and rewrite work should not mutate Lean files directly.
- Lean sync should not rewrite prose except for statement-alignment notes.
