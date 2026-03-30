# Program Board

Root dispatch table for the publication workspace.

## Pipeline Progress (2026-03-30)

| Paper | Target | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | Live status |
|---|---|---|---|---|---|---|---|---|---|---|
| APAL | Ann. Pure Appl. Logic | done | done | done | done | done | done | done | blocked | **Technical pack verified; waiting only on author metadata** |
| ETDS | Ergodic Th. Dyn. Sys. | done | done | done | done | done | done | done | done | **Submission-ready once author metadata is inserted** |
| TAMS | Trans. AMS | done | done | done | done | done | done | done | pending | **P7 is the next real task** |
| JFA | J. Funct. Anal. | done | done | done | pending | pending | pending | pending | pending | **Needs P5 proof polish and first live build** |
| ETDS-zeta | Ergodic Th. Dyn. Sys. | done | done | done | done | done | pending | pending | pending | **P4 accepted; move to P5** |

## Operational reading

- APAL and ETDS are no longer research-blocked. They are human-metadata blocked.
- TAMS is the strongest paper that can still gain a concrete submission upgrade
  without new mathematics.
- JFA is the clearest proof-polish candidate.
- ETDS-zeta is the best current testbed for multi-agent editorial plus
  integration workflow.

## Quantitative Summary

| Metric | Value |
|---|---|
| Total active papers on board | 5 |
| Papers past P4 editorial gate | 4 |
| Papers with a completed Lean sync note | 3 |
| Papers with a real local PDF build rechecked in this round | 4 |
| Papers blocked only on human metadata | 2 |
| Papers needing new mathematical work before submission | 0 among APAL/ETDS/TAMS; JFA and ETDS-zeta still need manuscript-stage work |

## Lane legend

- `compile`: manuscript compiles and basic document integrity
- `repro`: supplied scripts, constants, or tables can be regenerated or audited
- `editorial`: theorem chain, scope, target-journal fit, and manuscript polish
- `formal`: paper-to-Lean alignment and backlog extraction
- `submission-pack`: cover letter, checklist, and final status pack

## Current next actions

1. `ETDS-zeta`: integrate the accepted P4 pass and decide whether to add a
   paper-local reproducibility artifact for the `S_3` constants.
2. `TAMS`: assemble the true P7 submission pack and freeze the final archive.
3. `JFA`: split or compress the oversized precision-potential section, then run
   the first clean live build.
4. `APAL` and `ETDS`: hold technical state; close P7 immediately once author
   metadata is supplied.

## Dispatch rule

When an agent starts work, update `OPS/AGENT_CLAIMS.md` first.
When the task is done, update the local paper `TRACK_BOARD.md` and then
append one handoff note to `OPS/AGENT_CLAIMS.md`.
