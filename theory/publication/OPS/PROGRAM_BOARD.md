# Program Board

This board is the root dispatch table for the imported publication workspace.

## Lane legend

- `compile`: manuscript compiles and basic document integrity
- `repro`: supplied scripts and tables can be regenerated or audited
- `editorial`: theorem chain, scope, target-journal fit, and manuscript polish
- `formal`: paper-to-Lean alignment and backlog extraction
- `submission-pack`: cover letter, checklist, and final status pack

## Active lanes (Wave 1)

| Paper | Tier | Completed stages | Current stage | Next artifact |
|---|---|---|---|---|
| `APAL` | wave 1 | P0 P1 P2 P6 | **P3 in progress** | P3_REWRITE_NOTE + tex edits |
| `ETDS` | wave 1 | P0 P1 P2 P3 P4 P6 | **P5 in progress** | Integrated manuscript, clean bibliography |
| `TAMS` | wave 1 | P0 P1 P2 P6 | **P3 in progress** | P3_REWRITE_NOTE + tex edits |

## Quantitative progress (2026-03-30)

| Paper | Artifacts produced | Tex files edited | Lean coverage |
|---|---|---|---|
| APAL | P2_EXTENSION_NOTE, LEAN_SYNC_NOTE, TRACK_BOARD | 0 (P3 pending) | 0/13 (0%) |
| ETDS | P2_EXTENSION_NOTE, P3_REWRITE_NOTE, P4_EDITORIAL_REVIEW, LEAN_SYNC_NOTE | 7 files rewritten | 0/15 verified, 4 partial |
| TAMS | P2_EXTENSION_NOTE, LEAN_SYNC_NOTE, TRACK_BOARD | 0 (P3 pending) | 4/16 (25%), 5 partial |

## Consolidated lanes

- `APAL lane`
  treat these as one coordinated lane until deduplicated:
  - `2026_conservative_extension_chain_state_forcing_apal`
  - `2026_conservative_extension_chain_state_forcing_apal_focused`
  - `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal`

## Repro pilot lanes

| Paper | Lane | Status | Next artifact |
|---|---|---|---|
| `submitted_2026_branch_cubic_regular_s4_closure_prym_ray_class_jnt` | repro | ready | reproducibility run log |
| `submitted_2026_folded_rotation_histogram_certificates_siads` | repro | ready-with-risk | repro packaging audit |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | repro | ready-for-test | run log and package note |

## Deferred / backlog

- `2026_circle_dimension_haar_pullback_cauchy_weight_jfa` — mature, TeX path issues
- `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds` — mature, not on wave 1
- `2026_group_unification_fibonacci_prime_window_entropy_time` — README-only stub
- `2026_zeta_completion_xi_zero_audit` — README-only stub
- `2026_yang_lee_quartic_spectral_curve_discriminant_factorization_lee_yang_edge_singularity` — needs review

## Dispatch rule

When an agent starts work, update `OPS/AGENT_CLAIMS.md` first.
When the task is done, update the local paper `TRACK_BOARD.md` and then
append one handoff note to `OPS/AGENT_CLAIMS.md`.
