# Formalization Board

This board turns `P6` from an isolated note into a durable program lane.

## Active paper-to-Lean status

| Track | Paper state | P6 status | Current Lean status | What the gate means | Next Lean wave |
|---|---|---|---|---|---|
| APAL | technical pack verified; waiting on metadata | complete | `0/13 verified`, no direct Lean counterparts yet | manuscript may proceed, but the theorem package is entirely backlog-level for Lean | create a theorem-target list for the four-layer chain; no fake coverage claims |
| ETDS | submission-ready; waiting on metadata | complete | `0 verified`, `27% partial` (`4/15`) | submission is allowed, but paper claims still need a real extraction into Lean tasks | prioritize the sigma-nonexpansion core and transfer theorem package |
| TAMS | P7 next | complete | `4/16 verified`, `5/16 partial` | this is the strongest current formalization bridge; use it as the first serious publication-to-Lean testbed | push the transfer, Gibbs-selection, and arithmetic-window core claims |
| JFA | P5/P6 open | pending | one simplified partial match only; no paper-grade coverage | no formalization gate yet because the theorem package is not frozen | wait for P5 proof polish, then extract the final theorem package before any Lean wave |
| ETDS-zeta | P5 next | pending | no durable paper-local P6 record yet | paper can continue editorially, but the formalization target is still undefined | after P5, extract a strict theorem list and classify the finite-part core |

## P6 gate rules

`P6` is real only when all three exist:

1. a paper-local `LEAN_SYNC_NOTE_YYYY-MM-DD.md`
2. a claim classification for the active theorem package
3. an update to this board

Use `lean4/scripts/omega_ci.py paper-coverage --tex-root theory/publication/<paper> --paper-id <id>`
to generate the machine-readable coverage anchor for a publication draft.

## Claim classes

- `verified`
  the paper claim or a faithful specialization already exists in Lean
- `partial`
  some ingredients or a weaker specialization exist in Lean
- `backlog`
  no usable Lean object exists yet, but the theorem target is now exact
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
- which claims are next in the Lean wave
- which claims matter to the parent main theory
- whether the current paper creates a new formalization branch
