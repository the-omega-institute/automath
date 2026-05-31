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
| `bedc_automation_pipeline` | promoted | Maintain seed as archive/source packet for active track `2026_auditable_theory_to_paper_pipeline` | Running Stage A/P0-P7 against the seed itself |
| `bedc_finite_kernel_calculus` | source-theorem gate | Maintain theorem-spine notes, blocker ledger, and short-note memo | Journal-style promotion until a source-side packaging theorem is added or identified |
| `bedc_rule110_finite_witness` | artifact-rerun gate | Maintain rerun packet, static status map, limitation ledger, and trust-chain template | Artifact-paper promotion until dynamic rerun logs exist |

## Current Intake Pass

The safe automath-only P0 intake pass is complete as of 2026-05-31:

- `bedc_automation_pipeline` has been promoted to active paper track
  `2026_auditable_theory_to_paper_pipeline`. The next meaningful action is
  active-paper P1/P2 work in that directory, not another seed-level rewrite.
- `bedc_finite_kernel_calculus` has exact-statement notes, theorem-spine
  selection, GroundCompiler placement, blocker ledger, bibliography scaffold,
  short-note memo, and upstream packaging work order prepared. The next
  meaningful action is source-side theorem work or an explicit modest
  short-note decision.
- `bedc_rule110_finite_witness` has static recheck results, count-drift
  disclosure, limitation ledger, rerun packet, build-environment plan,
  trust-chain template, and diagnostic route memo prepared. The next meaningful
  action is a dynamic artifact rerun in a `make` plus C compiler environment.

Agents should therefore avoid repeatedly re-auditing these P0 seeds as if they
were missing intake scaffolding. Continue only with synchronization edits,
guard checks, source-update notes after an approved source commit movement, or
the explicit human decisions listed below.

## Exact Next Human Commands

Promoted route:

```text
2026_auditable_theory_to_paper_pipeline
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

For unpromoted seeds, and for the archived `bedc_automation_pipeline` seed
itself, agents must not:

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
