# Current Status: Newmath BEDC Intake

This is an intake-only status snapshot for agents.  It is not a promotion
command, not a daemon queue, and not permission to create an active paper
track.  In particular, this file is not a promotion command.

- status date: 2026-05-31
- intake root: `papers/publication/newmath_intake`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Global Rule

No seed may be promoted unless the human writes an explicit command of the
form:

```text
promotion <seed> as <active_slug>
```

Discussions of slugs, venue ladders, decision packets, handoff files, or
submission plans are not promotion approval.

## P0 State

| Seed | Current gate | Safe automath-only action | Blocked action |
|---|---|---|---|
| `bedc_automation_pipeline` | promotion-decision gate | Maintain the CICM packet, case table, source notes, and bibliography scaffold | Active paper creation until exact promotion command |
| `bedc_finite_kernel_calculus` | source-theorem gate | Maintain theorem-spine notes, blocker ledger, and short-note memo | Journal-style promotion until a source-side packaging theorem is added or identified |
| `bedc_rule110_finite_witness` | artifact-rerun gate | Maintain rerun packet, static status map, limitation ledger, and trust-chain template | Artifact-paper promotion until dynamic rerun logs exist |

## Exact Next Human Commands

Fastest visible route:

```text
promotion bedc_automation_pipeline as 2026_auditable_theory_to_paper_pipeline
```

Finite-kernel route:

```text
approve source-side finite-kernel packaging theorem work in D:\omega\newmath
```

Rule110 route:

```text
approve Rule110 dynamic artifact rerun in a make/C-compiler environment
```

## Non-Active Boundary

Until an exact promotion command is present, agents must not:

- create any `papers/publication/2026_*` directory for these seeds;
- add `main.tex` or `PIPELINE.md` to a seed directory;
- add active-paper files such as `research_directive.md`, `SOURCE_MAP.md`,
  `THEOREM_LIST.md`, `ARTIFACT_INVENTORY.md`, or `BIB_SCOPE.md`;
- do not run Stage A, Stage B, Stage C, or P0-P7 automation against a seed;
- rely on a newer `D:/omega/newmath` commit without a source update note.

## Verification

After any intake edit, run:

```powershell
python papers\publication\newmath_intake\check_intake.py
```

Expected result:

```text
OK: newmath intake seeds are not active paper tracks
```
