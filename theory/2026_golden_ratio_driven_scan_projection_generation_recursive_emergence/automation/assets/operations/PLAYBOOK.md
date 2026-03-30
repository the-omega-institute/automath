# Publication Operations Playbook

This file is the compact default for agent-facing publication operations.

## Stage model

| Stage | Purpose | Typical outputs |
|---|---|---|
| `P0` | intake and contract | `README.md`, venue, `main.tex` |
| `P1` | traceability | `SOURCE_MAP.md`, `THEOREM_LIST.md` |
| `P2` | research extension | sharper theorem package, scope cuts |
| `P3` | journal-fit rewrite | title, abstract, introduction, roadmap, section flow rewritten |
| `P4` | editorial review | decision-grade review and blockers |
| `P5` | integration | accepted rewrite merged into manuscript and `TRACK_BOARD.md` |
| `P6` | shared Lean sync | labels cross-checked against the shared Lean core |
| `P7` | submission pack | cover letter, checklist, final package |

## Roles

- Orchestrator:
  chooses which papers enter the wave, assigns owners, resolves collisions
- Traceability agent:
  owns `SOURCE_MAP.md` and `THEOREM_LIST.md`
- Research agent:
  strengthens statements and cuts weak material
- Journal rewrite agent:
  rewrites for the target venue register
- Editorial review agent:
  performs decision-grade review
- Bibliography / recon agent:
  studies recent target-journal papers and bibliography scope
- Lean sync agent:
  checks labels and declarations against the shared Lean inventory
- Integrator:
  merges outputs, updates status, prepares handoff to the next stage

## Claim rules

- Claim work as `paper x stage`, not as a vague topic.
- One agent owns one file group at a time.
- If manuscript files change, record a local build result in the handoff.
- If a stage depends on another stage's artifact, do not bypass the handoff.
- If two agents need the same file, the integrator decides ownership.

## Parallel rule

- Different papers can move in parallel.
- The same paper should respect `P0 -> P7` order.
- `P6` may run in parallel with `P2-P5` because it writes notes and alignment,
  not manuscript prose.

## Suggested first dispatch pattern

- Agent 1: orchestrator and board ownership
- Agent 2: highest-priority integrator
- Agent 3: submission-pack work on the strongest near-ready paper
- Agent 4: proof polish on the strongest still-open rewrite paper
- Agent 5: compile / bibliography cleanup on that same rewrite paper
- Agent 6: Lean sync on the strongest stable theorem package
- Agent 7: upstream/main-paper backport on the first stable P5 or P7 paper

## Operational rule

Prefer a few durable control files plus real `.tex` and `.lean` changes.
Do not grow a large tree of workflow-only Markdown unless the process becomes
unclear without it.
