# Publication Pipeline Advance

Advance the publication pipeline for all active Wave papers.

## Workflow

1. Read `papers/publication/OPS/BOARD.md` to identify active papers and wave priorities
2. For each paper, read its `TRACK_BOARD.md` to determine current stage
3. Determine the next stage based on which gate artifacts exist:
   - P1 done if `SOURCE_MAP.md` + `THEOREM_LIST.md` exist
   - P2 done if `P2_EXTENSION_NOTE_*.md` exists
   - P3 done if `P3_REWRITE_NOTE_*.md` exists
   - P4 done if `P4_EDITORIAL_REVIEW_*.md` exists
   - P5 done if TRACK_BOARD.md shows integration complete
   - P6 done if `LEAN_SYNC_NOTE_*.md` exists
   - P7 done if submission checklist + cover letter exist
4. For each paper that has an unblocked next stage, launch the appropriate agent:
   - P2: pub-research agent
   - P3: pub-journal-rewrite agent
   - P4: pub-editorial agent
   - P5: pub-integrator agent
   - P6: pub-lean-sync agent
   - P7: pub-submission agent
5. After agents complete, update `OPS/BOARD.md`
6. Commit and push results

## Parallel dispatch rules

- Different papers can run in parallel (APAL + ETDS + TAMS simultaneously)
- Same paper: P2→P3→P4→P5 must be sequential; P6 can run in parallel with P2-P5
- Bibliography recon (pub-biblio) can run in parallel with anything

## Paper directories

All papers are under `papers/publication/`. The three Wave 1 papers are:
- `2026_conservative_extension_chain_state_forcing_apal` (APAL)
- `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` (ETDS)
- `2026_projection_ontological_mathematics_core_tams` (TAMS)
