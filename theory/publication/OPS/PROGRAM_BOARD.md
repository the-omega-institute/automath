# Program Board

Root dispatch table for the publication workspace.

## Pipeline Progress (2026-03-30)

### Wave 1

| Paper | Target | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | Status |
|---|---|---|---|---|---|---|---|---|---|---|
| APAL | Ann. Pure Appl. Logic | done | done | done | done | MAJOR_REV | done | done | pending | **P5 complete, ready for P7** |
| ETDS | Ergodic Th. Dyn. Sys. | done | done | done | done | done | done | done | done | **SUBMISSION-READY** |
| TAMS | Trans. AMS | done | done | done | done | MINOR_REV | pending | done | pending | **P4 complete, needs P5** |

### Wave 2

| Paper | Target | P0 | P1 | P2 | Status |
|---|---|---|---|---|---|
| JFA (circle dimension) | J. Funct. Anal. | done | done | done | **P1+P2 complete** |
| ETDS-zeta (dynamical zeta) | Ergodic Th. Dyn. Sys. | done | done | done | **P1+P2 complete** |

## Quantitative Summary

| Metric | Value |
|---|---|
| Total papers in pipeline | 5 (3 Wave 1 + 2 Wave 2) |
| Papers submission-ready | 1 (ETDS) |
| Papers past P4 editorial | 3 (APAL, ETDS, TAMS) |
| Total commits this session | 14 |
| Total .tex files edited | 25+ |
| Net line change | ~1500+ insertions, ~1800+ deletions |
| Lean Sync coverage reports | 3 (all Wave 1) |
| Editorial reviews produced | 2 (APAL: MAJOR_REV, TAMS: MINOR_REV) |
| Submission packs produced | 1 (ETDS: cover letter + checklist) |

## Lane legend

- `compile`: manuscript compiles and basic document integrity
- `repro`: supplied scripts and tables can be regenerated or audited
- `editorial`: theorem chain, scope, target-journal fit, and manuscript polish
- `formal`: paper-to-Lean alignment and backlog extraction
- `submission-pack`: cover letter, checklist, and final status pack

## Repro pilot lanes

| Paper | Lane | Status |
|---|---|---|
| `submitted_2026_branch_cubic_regular_s4_closure_prym_ray_class_jnt` | repro | ready |
| `submitted_2026_folded_rotation_histogram_certificates_siads` | repro | ready-with-risk |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | repro | ready-for-test |

## Deferred / backlog

- `2026_circle_dimension_haar_pullback_cauchy_weight_jfa` — now Wave 2, P2 complete
- `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds` — now Wave 2, P2 complete
- `2026_group_unification_fibonacci_prime_window_entropy_time` — README-only stub
- `2026_zeta_completion_xi_zero_audit` — README-only stub
- `2026_yang_lee_quartic_spectral_curve_discriminant_factorization_lee_yang_edge_singularity` — needs review

## Dispatch rule

When an agent starts work, update `OPS/AGENT_CLAIMS.md` first.
When the task is done, update the local paper `TRACK_BOARD.md` and then
append one handoff note to `OPS/AGENT_CLAIMS.md`.
