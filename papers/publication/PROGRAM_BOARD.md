# Program Board

全量论文状态表。管线 (`oracle_pipeline.py`) 读此文件决定调度：跳过已投/已发表/骨架，处理 P0–P7 阶段论文。

更新日期：2026-04-20

## 状态编码

- `已投 MM-DD` — 已投稿，等待编辑决定
- `已投 MM-DD 审稿中` / `R&R` / `接收` / `拒稿` — 投稿后续
- `P0`–`P7` — 管线阶段（未投稿）
- `P4-MAJOR` — P4 门禁返回 MAJOR_REVISION
- `待分诊` — 有 main.tex 但未入管线
- `骨架` — 无 main.tex

## 全量状态表

| 目录 | 目标期刊 | 状态 | 改投记录 |
|------|---------|------|---------|
| `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt` | JNT | 已投 04-07 | ETDS→JNT |
| `submitted_2026_folded_rotation_histogram_certificates_siads` | SIADS | 已投 04-07 | — |
| `submitted_2026_folded_rotation_histogram_etds` | ETDS | 已投 04-07 | — |
| `submitted_2026_zeckendorf_streaming_normalization_automata_rairo_ita` | RAIRO-ITA | 已投 04-07 | — |
| `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint` | Res. Number Theory | 已投 04-07 | — |
| `submitted_2026_fibonacci_stabilization_sharp_threshold_conjugacy_nonlinearity` | Nonlinearity | 已投 04-07 | — |
| `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp` | QTDS | 已投 04-07 | — |
| `submitted_2026_branch_cubic_regular_s4_closure_prym_ray_class_jnt` | JNT | 已投 04-07 | — |
| `submitted_2026_grg_shell_geometry_from_stationary_detector_thermality_grg` | GRG | 已投 04-07 | — |
| `2026_projection_ontological_mathematics_core_tams` | Trans. AMS | P7 可投 | — |
| `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | ETDS | P7 待投 | — |
| `2026_conservative_extension_chain_state_forcing_apal` | APAL | C-DONE (Claude: submit, 3 rounds) | — |
| `2026_conservative_extension_chain_state_forcing_apal_focused` | APAL | P7 精简版 | — |
| `2026_circle_dimension_haar_pullback_cauchy_weight_jfa` | JFA | C-DONE (Claude: submit, 3 rounds) | — |
| `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds` | ETDS | P5 done | — |
| `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta` | J. Spectral Theory | P5 done | — |
| `2026_prime_languages_sofic_obstructions_dynamical_zeta` | Monatshefte | P3 返工 | — |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | IMRN | P4-MAJOR | — |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | ETDS | P1 | — |
| `2026_JphisComm_待投稿` | J. Phys. Comm. | P0 | — |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | APAL | P0 | — |
| `2026_chebotarev_quotient_entropy_fold_groupoid_rigidity` | — | 待分诊 | — |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | JDDE | 待分诊 | — |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | — | 待分诊 | — |
| `2026_fold_truncation_defect_stokes_dynamical_systems` | Dynamical Systems | 待分诊 | — |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | — | 待分诊 | — |
| `2026_recursive_addressing_prefix_sites_tac` | TAC | 待分诊 | — |
| `2026_yang_lee_quartic_spectral_curve_discriminant_factorization_lee_yang_edge_singularity` | — | 待分诊 | — |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | — | 待分诊 | — |
| `2026_single_primitive_universality_hierarchy` | Proc. AMS | 待分诊 | — |
| `2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge` | — | 待分诊 | — |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | — | 待分诊 | — |
| `2026_JphisComm` | — | 骨架 | — |
| `2026_group_unification_fibonacci_prime_window_entropy_time` | — | 骨架 | — |
| `2026_zeta_completion_xi_zero_audit` | — | 骨架 | — |

## Pipeline 阶段说明

| Stage | 描述 | 工具 |
|-------|------|------|
| P0 | Intake: scope, target journal | `publication_sync.py` |
| P1 | Traceability: theorem inventory, source map | `research_cycle.py` |
| P2 | Research extension: deepen results | ChatGPT oracle + agent |
| P3 | Journal-fit rewrite: abstract, intro, style | Agent (Claude/etc) |
| P4 | Editorial review: referee-grade assessment | ChatGPT oracle + `pub_check.py` |
| P5 | Integration: apply P4 fixes | Agent |
| P6 | Lean sync: cross-check against lean4/Omega/ | `omega_ci.py` |
| P7 | Submission pack: cover letter + checklist | Template + agent |

Oracle pipeline stages (within P2–P5):

| Stage | 描述 |
|-------|------|
| F | Fit check: journal match + initial scope |
| A | Codex optimization: style, proofs, depth |
| B | Oracle review: ChatGPT Pro acceptance gate |
| C | Fix oracle issues: iterate until ACCEPT |
| D | Final polish + commit |
