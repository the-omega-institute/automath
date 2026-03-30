# Formalization Board

This board turns `P6` from an isolated note into a durable lane feeding the
single shared Lean formalization library.

## Core policy

- There is one formalization library: `lean4/Omega/...`
- Publication tracks do not own separate Lean projects.
- A paper contributes a kernel theorem package, not a paper-specific Lean tree.
- `P6` exists to align that kernel package with the shared library and its
  backlog.

## Active paper-to-core status

| Track | Paper state | P6 status | Current core status | What the gate means | Next core wave |
|---|---|---|---|---|---|
| APAL | technical pack verified; waiting on metadata | complete | `0/13 verified`, no direct core counterparts yet | manuscript may proceed, but the theorem package is entirely backlog-level in the core library | create a kernel target list for the four-layer chain; no fake coverage claims |
| ETDS | submission-ready; waiting on metadata | complete | `0 verified`, `27% partial` (`4/15`) | submission is allowed, but paper claims still need a real extraction into core-library tasks | prioritize the sigma-nonexpansion core and transfer theorem package |
| TAMS | P7 next | complete | `4/16 verified`, `5/16 partial` | this is the strongest current bridge into the shared core library | push the transfer, Gibbs-selection, and arithmetic-window core claims |
| JFA | P5/P6 open | pending | one simplified partial match only; no stable core package yet | no formalization gate yet because the theorem package is not frozen | wait for P5 proof polish, then extract the final kernel package before any Lean wave |
| ETDS-zeta | P5 next | pending | no durable paper-local P6 record yet | paper can continue editorially, but the core target is still undefined | after P5, extract a strict theorem list and classify the finite-part core |

## P6 gate rules

`P6` is real only when all three exist:

1. a paper-local `LEAN_SYNC_NOTE_YYYY-MM-DD.md`
2. a claim classification for the active theorem package
3. an update to this board

Use `lean4/scripts/omega_ci.py paper-coverage --tex-root theory/publication/<paper> --paper-id <id>`
to generate the machine-readable coverage anchor for a publication draft.
That command does **not** create a paper-local proof project; it only measures
how the paper's claim labels align with the shared registry labels.

## Claim classes

- `verified`
  the paper claim or a faithful specialization already exists in the core library
- `partial`
  some ingredients or a weaker specialization exist in the core library
- `backlog`
  no usable core theorem exists yet, but the theorem target is now exact
- `paper-external`
  the item belongs to a sequel, appendix-only branch, or non-core side lane

## Gate semantics

- A low verified percentage does **not** automatically block submission.
- What blocks the paper is ambiguity, not incompleteness.
- If the active theorem package has not been classified at all, `P6` is not done.
- If the theorem package has been classified precisely, the paper may proceed
  while the Lean wave continues in parallel.

## Required contents of a paper-local `LEAN_SYNC_NOTE`

- theorem-count basis used for the percentages
- exact `verified / partial / backlog / paper-external` split
- which claims are next in the core Lean wave
- which claims matter to the parent main theory
- which shared modules or backlog files should absorb the next proof work
