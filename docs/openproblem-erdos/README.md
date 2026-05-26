# Open Problem Erdos Stage Notes

Date: 2026-05-26

This directory records the current stage results for the open-problem branch.
It intentionally contains only distilled notes, not Oracle response logs,
evaluator logs, browser state, generated queue files, or other intermediate
runtime artifacts.

## Files

- `T-32-primitive-c4-frontier.md`
  - Records the C4 frontier for the Litt common finite etale cover target.
  - Keeps the failed cusp-ratio and incomplete Deliverable B routes from being
    retried as if they were still live.
- `T-43-eg-summand-a5-certificate.md`
  - Records the E-G direct-summand bridge, failed Scholl/source-gap route, and
    the live A5 same-`W` higher-rank certificate candidate.
- `T-44-kp-prym-route-log.md`
  - Records the retired boundary-twist route, retired KP2 bridge, and the live
    level-3 / `F_3` Fox/Prym transporter direction.

## Branch Status

None of the three target problems is closed.

Current strongest stage result:

- T-43 has the most publication-like stage artifact: a rank-4 A5 same-`W`
  finite-monodromy certificate candidate awaiting source replay.

Current useful negative results:

- T-44's named `T_d` route and KP2 stabilizer-fiber route should not be retried
  without new source-grade evidence.
- T-32's C4 frontier cannot move by prose alone; it needs an actual divisor
  basis certificate or primitive C4 point-count audit.

## Commit Hygiene

These notes are suitable for version control. Raw artifacts under
`tools/community-outreach/state/`, Oracle response dumps, evaluator output
files, and incomplete JSON/checker claims are not included here.
