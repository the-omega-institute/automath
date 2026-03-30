# Claim Rules

The pipeline only scales if agents can claim work cleanly.

## Claim granularity

- Prefer `paper x phase` ownership over vague topical ownership.
- Good claim: `E2 / Stage P3 Journal-Fit Rewrite`.
- Bad claim: `work on ETDS style a bit`.

## Required claim record

Each claimed task should record:

- paper directory
- stage
- owner
- write scope
- upstream dependency
- backport target
- expected output artifact
- build check requirement when manuscript files change

## Conflict policy

- If two agents need the same file, the integrator decides ownership.
- If a stage depends on another stage's artifact, do not bypass the handoff.
- Agents should not silently overwrite another agent's work.

## Stop conditions

- Missing target journal
- Missing `main.tex`
- No source mapping for theorem-heavy work
- No bibliography source for rewrite / review stages
- No upstream return path for a stage that changes theorem packaging
- No formalization classification for a claimed P6 task

In those cases, revert to P0 or P1 instead of pretending the later stage can proceed.
