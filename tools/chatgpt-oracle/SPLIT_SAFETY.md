# Split Safety Gate

The publication pipeline must not create a new submission that republishes the
same theorem package under a different title, venue, or narrative framing.

## Deterministic Gate

Run the split-overlap harness before any agent theoremization or journal rewrite:

```powershell
python tools/chatgpt-oracle/split_overlap_harness.py --current-paper papers/publication/<paper_dir>
```

For a full corpus audit without blocking the caller:

```powershell
python tools/chatgpt-oracle/split_overlap_harness.py --report-only
```

The harness reads only local source files and `papers/publication/PROGRAM_BOARD.md`.
It emits:

- `tools/chatgpt-oracle/reports/split_overlap_report.json`
- `tools/chatgpt-oracle/reports/split_overlap_report.md`
- for Stage A blockers, `<paper>/semantic_overlap_blockers.json`
- for Stage A blockers, `<paper>/semantic_overlap_blockers.md`

## Hard Rule

A split can advance only if one of these is true:

- The theorem package is deterministically distinct from every active,
  submitted, rejected, or archived sibling.
- The board explicitly records that the overlapping route is closed, merged,
  superseded, or parked.
- An earlier overlapping paper has already been submitted or is under review;
  in that case submission chronology wins and the later draft is paused until
  the prior route receives editorial feedback, or until the board explicitly
  closes, merges, supersedes, or withdraws that route.

Renaming the paper, changing the target journal, moving the motivation from
number theory to dynamics, or paraphrasing theorem statements does not make a
safe split.

## Classification

- `blocker`: overlap with a submitted/rejected/under-review sibling whose route
  is not explicitly resolved on the board and where the harness cannot assign a
  deterministic prior-submission winner.
- `deferred_wait_for_prior_submission`: overlap where one side is already
  submitted, under review, or has a local submission marker. The earlier/current
  submission is primary; the later draft is not processed for now and waits for
  editorial feedback or an explicit board resolution.
- `needs_human_resolution`: overlap between active drafts without a board-level
  decision.
- `resolved`: overlap is present, but the board explicitly says the old route is
  closed, merged, superseded, or parked.
- `informational`: weak/background overlap that does not currently block.

The pipeline treats `blocker`, `deferred_wait_for_prior_submission`, and
`needs_human_resolution` as failing gate classes.

## Supervisor Boundary

The outer supervisor stays thin. It manages process lifecycle, health checks,
soft restarts, log surfacing, and auto-commit. It does not decide mathematical
overlap.

The inner pipeline calls this deterministic harness before Stage A agent work.
Agents may only receive the structured report after the gate has decided what
requires mathematical reasoning or manuscript edits.
