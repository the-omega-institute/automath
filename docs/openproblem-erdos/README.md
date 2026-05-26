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


## Monitoring Update 2026-05-26 19:03 SGT

Current strongest stage results have shifted since the initial notes.

- T-32 now has a live primitive C4 global-congruence route: the `d4 mod 8` obstruction is the main candidate for excluding the remaining PE2/sign formal survivor. This is not closed until the claimed torsor proof and any new row audits are locally replayed.
- T-44 has moved beyond framework obstruction prose in the KP level-3 route. Oracle supplied a concrete `A2=T_{a2}` block for `W_chi0`; it still needs local Fox/source-window replay and a materialized `kp_level3_source_matrices.json` entry.
- T-43 remains a negative theorem-boundary result: no theorem-numbered primary source has been identified proving finite monodromy for arbitrary E-G geometric-origin summands/subquotients with almost-all zero `p`-curvature.

Pipeline status at this checkpoint was active but imperfect: all three workers were assigned tasks, while the T-32 browser agent was marked stale by the supervisor. No raw runtime artifacts are recorded here.


## Monitoring Update 2026-05-26 21:26 SGT

Current pipeline health changed from the previous checkpoint: the supervisor is idle with `queue_length=0` and `agents_busy=0/3`, while all three browser poll agents remain recent and compatible. This is not a browser-agent crash, but the automated loop is not currently feeding new work.

New durable stage result:

- T-43 now has a local standalone negative-boundary memo at `tools/community-outreach/targets/problemsilike_02/t43_research_note.md` in the main worktree. The field audit passed with `PASS_T43_RESEARCH_NOTE_FIELD_AUDIT` and payload sha256 `27dd2ac294f380075b05a354cd75ac22a075a5faa99948fb92a5691a06410010`.

No closure change:

- T-32 remains at the primitive C4 `d4 mod 8` frontier. The latest fourth-row claim is still not accepted without local replay and duplicate-row checking.
- T-44 remains on the KP level-3 source-matrix route. Recent turns repeated B2 evidence rather than delivering the active A3 block.
