# Program Board

This board is the root dispatch table for the imported publication workspace.

## Lane legend

- `compile`: manuscript compiles and basic document integrity
- `repro`: supplied scripts and tables can be regenerated or audited
- `editorial`: theorem chain, scope, target-journal fit, and manuscript polish
- `formal`: paper-to-Lean alignment and backlog extraction
- `submission-pack`: cover letter, checklist, and final status pack

## Active lanes

| Paper | Tier | Lane | Owner | Status | Immediate blocker | Expected next artifact |
|---|---|---|---|---|---|---|
| `2026_conservative_extension_chain_state_forcing_apal` | wave 1 | `editorial` | `unassigned` | `active` | traceability not yet explicit | `SOURCE_MAP.md`, `THEOREM_LIST.md`, APAL rewrite pass |
| `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | wave 1 | `editorial` | `unassigned` | `active` | scope may still be too broad for one ETDS paper | theorem roadmap rewrite and scope decision |
| `2026_projection_ontological_mathematics_core_tams` | wave 1 | `editorial` | `unassigned` | `active` | missing bibliography repair and theorem compression | main theorem order and bibliography repair note |
| `submitted_2026_branch_cubic_regular_s4_closure_prym_ray_class_jnt` | repro pilot | `repro` | `unassigned` | `ready` | no root lane owner yet | reproducibility run log |
| `submitted_2026_folded_rotation_histogram_certificates_siads` | repro pilot | `repro` | `unassigned` | `ready-with-risk` | supplementary path packaging may be fragile | repro packaging audit |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | repro pilot | `repro` | `unassigned` | `ready-for-test` | no README/review notes | run log and package note |

## Consolidated lanes

- `APAL lane`
  treat these as one coordinated lane until deduplicated:
  - `2026_conservative_extension_chain_state_forcing_apal`
  - `2026_conservative_extension_chain_state_forcing_apal_focused`
  - `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal`

## Deferred / backlog

- `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`
  mature, but TeX environment path issues make it a second-wave pilot
- `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds`
  mature, but not yet on the first editorial wave
- `2026_group_unification_fibonacci_prime_window_entropy_time`
  README-only stub
- `2026_zeta_completion_xi_zero_audit`
  README-only stub

## Dispatch rule

When an agent starts work, update `OPS/AGENT_CLAIMS.md` first.
When the task is done, update the local paper `TRACK_BOARD.md` and then
append one handoff note to `OPS/AGENT_CLAIMS.md`.
