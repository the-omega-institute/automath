# Split Overlap Report

- Generated: `2026-05-13T14:48:25+00:00`
- Publication dir: `D:\omega\automath\papers\publication`
- Current paper: `2026_recursive_addressing_prefix_sites_tac`
- Gate failed: `true`

## Summary

| classification | count |
|---|---:|
| `blocker` | 0 |
| `deferred_wait_for_prior_submission` | 0 |
| `needs_human_resolution` | 2 |
| `resolved` | 0 |
| `informational` | 1 |

## Findings

| class | paper A | paper B | action | primary | deferred | shared markers | token Jaccard | board A | board B |
|---|---|---|---|---|---|---|---:|---|---|
| needs_human_resolution | `2026_recursive_addressing_prefix_sites_tac` | `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | record_board_resolution_before_advancing | `` | `` | homological_visibility_pullback, sliding_overlap_reconstruction, visible_quotient_gluing | 0.2243 | TAC \| P0 \| triaged 2026-05-13: substantial prefix-sites / inverse-limits manuscript; needs journal-fit and novelty gate | APAL \| A-BLOCKED (max Stage A rounds exhausted; final audit failed (score=7)) \| — |
| needs_human_resolution | `2026_recursive_addressing_prefix_sites_tac` | `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | record_board_resolution_before_advancing | `` | `` | homological_visibility_pullback, sliding_overlap_reconstruction, visible_quotient_gluing | 0.2085 | TAC \| P0 \| triaged 2026-05-13: substantial prefix-sites / inverse-limits manuscript; needs journal-fit and novelty gate | APAL \| B-STUCK (Oracle: minor revision, 20 rounds — needs human review) \| — |
| informational | `2026_recursive_addressing_prefix_sites_tac` | `2026_finite_observation_escape_rates_cyclotomic_resonances_etds` | no_action_required | `` | `` | sliding_overlap_reconstruction, visible_quotient_gluing | 0.1648 | TAC \| P0 \| triaged 2026-05-13: substantial prefix-sites / inverse-limits manuscript; needs journal-fit and novelty gate | ETDS \| A-BLOCKED (max Stage A rounds exhausted; final audit failed (score=7)) \| — |

## Policy

A split is publishable only when its theorem package is distinct, or when the board explicitly records that the overlapping route is closed, merged, superseded, or parked. When an earlier overlapping paper has already been submitted or is under review, submission chronology wins: the later draft is deferred until the prior route receives feedback. Renaming, journal reframing, or prose rewriting is not enough to pass this gate.
