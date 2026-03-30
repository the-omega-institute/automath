# Upstream Board

This board tracks how publication work feeds back into the upstream theory.

## Active upstream links

| Track | Upstream source roots | Current paper state | Required upstream feedback | Main-paper write-back | Possible child / sequel | Status |
|---|---|---|---|---|---|---|
| APAL | `logic_expansion_chain/` | technically ready, waiting on metadata | backport the four-layer packaging, forcing-necessity theorem framing, and the contextuality bridge as explicit source-level anchors | rewrite the canonical logic-expansion-chain narrative around the four-layer package | `K` observer-spacetime logic sequel | pending first `UPSTREAM_SYNC_NOTE` |
| ETDS | `spg/` + `recursive_addressing/` | submission-ready, waiting on metadata | backport the weighted-boundary transfer theorem, open-system specialization, Poisson collision threshold, and entropy-ledger phrasing | rewrite the SPG + recursive-addressing core around the ETDS theorem ladder | `F` depends directly; no new child needed right now | pending first `UPSTREAM_SYNC_NOTE` |
| TAMS | `pom/` core + certified generated tables | P7 is next | backport the principalization -> irreducibility -> full symmetric group -> linear disjointness -> product-density chain as the canonical arithmetic route | rewrite the canonical POM arithmetic line to match the stabilized TAMS chain | arithmetic side branches can split later if they become independently stable | pending first `UPSTREAM_SYNC_NOTE` |
| JFA | `circle_dimension_phase_gate/` | P5/P6 still open | backport the interface-theorem packaging, explicit analytic bundle, and portable section split for the precision-potential material | rewrite the main-paper circle-dimension exposition around the interface/analytic split | `S4/Prym` and other algebraic side branches stay separate | pending first `UPSTREAM_SYNC_NOTE` |
| ETDS-zeta | `zeta_finite_part/{syntax,online_kernel,operator,finite_part}` | P5 is next | backport the finite-part chain as a single explicit theorem ladder and keep `xi/` out of the parent-line main claims | rewrite the main-paper zeta finite-part chapter to foreground the stabilized finite-part ladder | `H1`, `H2`, `H3`, and `J` remain real child candidates | pending first `UPSTREAM_SYNC_NOTE` |

## Upstream sync contract

When a paper reaches a stable `P5` state:

1. write `UPSTREAM_SYNC_NOTE_YYYY-MM-DD.md` in the paper directory
2. write `MAIN_PAPER_BACKPORT_YYYY-MM-DD.md` when the paper has improved the
   canonical main-paper exposition
3. summarize:
   - what theorem packaging changed
   - what should be backported upstream
   - what must be written back into the main paper
   - what should remain paper-local only
   - what should split into a new child track
4. update this board with the resulting status

## Status meanings

- `pending first UPSTREAM_SYNC_NOTE`
  no durable backport artifact exists yet
- `backport-ready`
  the paper has a concrete upstream sync note and the source-level edits can be planned
- `main-paper-update-pending`
  the source-level backport is known and a main-paper write-back note exists, but the
  main paper has not absorbed it yet
- `synced`
  the upstream source and the main paper have already absorbed the accepted paper-side improvement
- `split-registered`
  a child track has been formally registered from this paper
