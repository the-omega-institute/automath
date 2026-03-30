# Publication Workflow

This is the agent-neutral execution contract for the publication layer.

The publication workspace is not a static archive of split papers. It is the
execution layer between:

- the upstream main theory and main paper
- the shared Lean core library under `lean4/Omega/...`
- active paper tracks moving toward submission

## Minimal control surface

Any agent taking over this workflow only needs to read:

1. `theory/publication/README.md`
2. `theory/publication/OPS/BOARD.md`
3. the target paper's `TRACK_BOARD.md`
4. the target paper's `SOURCE_MAP.md` and `THEOREM_LIST.md` when present

## Stage order

| Stage | Name | Required artifact |
|---|---|---|
| `P0` | Intake | `README.md` + `main.tex` + target venue |
| `P1` | Traceability | `SOURCE_MAP.md` + `THEOREM_LIST.md` |
| `P2` | Research extension | `P2_EXTENSION_NOTE_*.md` or accepted theorem-package edits |
| `P3` | Journal rewrite | accepted manuscript rewrite in place |
| `P4` | Editorial review | `P4_EDITORIAL_REVIEW_*.md` |
| `P5` | Integration | `TRACK_BOARD.md` updated after accepted integration |
| `P6` | Shared Lean sync | `LEAN_SYNC_NOTE_*.md` plus board update |
| `P7` | Submission pack | cover letter + checklist + final status update |

Do not skip stages. `P6` may run in parallel with `P2-P5`, but it does not
replace them.

## Side lanes

- `U-lane` upstream sync:
  what must flow back into the parent theory source
- `M-lane` main-paper backport:
  what must be written back into the canonical main paper
- `F-lane` formalization sync:
  how the paper's kernel theorem package maps into the shared Lean core
- `S-lane` sequel / split:
  what should become a child track rather than stay in the current paper

## Shared Lean policy

- There is one formalization library: `lean4/Omega/...`
- Publication tracks do not own separate Lean projects.
- `P6` only classifies and aligns a paper kernel theorem package into that
  shared library and its backlog.
- A low verified percentage is not automatically blocking.
- Ambiguous or unclassified theorem packages are blocking.

## Main-paper backport policy

- Stable paper-side improvements must not remain paper-local forever.
- If a paper sharpens the canonical theorem ladder, roadmap, or exposition,
  that change must be recorded as a main-paper backport target.
- Publication is an execution layer, not the final knowledge store.

## Agent roles

- Orchestrator:
  chooses paper/stage ownership and keeps the board current
- Traceability agent:
  owns `SOURCE_MAP.md` and `THEOREM_LIST.md`
- Research agent:
  strengthens statements and cuts weak material
- Journal rewrite agent:
  rewrites title, abstract, introduction, roadmap, and section flow
- Editorial review agent:
  writes a decision-grade review with blockers
- Integrator:
  applies accepted P2-P4 outputs into the manuscript and track board
- Lean sync agent:
  classifies paper claims against the shared Lean core
- Upstream sync agent:
  records source return paths and main-paper backport targets

## Handoff rule

A stage is done only when:

1. the paper-local artifact exists or the accepted manuscript diff is in place
2. `TRACK_BOARD.md` states the resulting status
3. `OPS/BOARD.md` reflects the new live state
4. the next owner can continue without rediscovering context

## Persistent note artifacts

Paper-local note families:

- `LEAN_SYNC_NOTE_YYYY-MM-DD.md`
- `UPSTREAM_SYNC_NOTE_YYYY-MM-DD.md`
- `MAIN_PAPER_BACKPORT_YYYY-MM-DD.md`

Use `OPS/SYNC_NOTE.template.md` as the common schema for all three.

## Practical rule

Prefer fewer durable files and more real manuscript/Lean changes.

- keep global state in `OPS/BOARD.md`
- keep rules in this file
- keep paper-local state in each paper's `TRACK_BOARD.md`
- do not create new global ops files unless the workflow cannot remain legible
  without them
