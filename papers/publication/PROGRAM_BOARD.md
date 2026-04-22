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
| `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq` | Fibonacci Q. | 拒稿 04-20, 转投 FQ | ETDS→JNT→FQ | JNT editor 推荐 FQ; fallback: JSC (IF 1.1) |
| `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` | ETDS | A-DONE (best 5/10, 5 rounds (max)) | SIADS→ETDS | fallback: Israel J. Math (IF 1.0), DCDS-A (IF 1.1) |
| `submitted_2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | ETDS | 已投 04-07 | — |
| `submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita` | RAIRO-ITA | 已投 04-07 | — |
| `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj` | Ramanujan J. | 拒稿 04-20, 转投 RJ | RNT→RJ | 两位 editor 均推荐 FQ; fallback: FQ, Bull. Malaysian (IF 1.2) |
| `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` | DCDS-A | A-DONE (best 5/10, 5 rounds (max)) | Nonlinearity→DCDS-A | fallback: J. Diff. Eqs. Apps. (IF 1.1), Dynamical Systems |
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | J. Theoret. Probab. | 已投, peer review 中 (7 reviewers invited) | QTDS→JTP | 标题改为 "Exponential Tilting and Information Fluctuations for One-Step Markov Measures on Shifts of Finite Type" |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | JNT | 已投 04-07 | — |
| `2026_finite_window_zeckendorf_fibers_discrete_thermodynamics_tams` | Trans. AMS | C-DONE (Claude: submit, 2 rounds) | — |
| `2026_finite_observation_escape_rates_cyclotomic_resonances_etds` | ETDS | C-DONE (Claude: submit, 2 rounds) | — |
| `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | APAL | C-DONE (Claude: submit, 3 rounds) | — |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | APAL | B-STUCK (Oracle: reject, 99 rounds — needs human review) | — |
| `2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa` | JFA | C-DONE (Claude: submit, 3 rounds) | — |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | ETDS | B-STUCK (Oracle: major revision, 99 rounds — needs human review) | — |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | J. Spectral Theory | P5 done | — |
| `2026_prime_languages_finite_state_obstructions_monatshefte` | Monatshefte | P3 返工 | — |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | IMRN | C-DONE (Claude: submit, 1 rounds) | — |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | C-DONE (Claude: submit, 2 rounds) | — |
| `2026_detector_shells_click_record_kms_jphyscomm` | J. Math. Phys. | B-STUCK (Oracle: major revision, 99 rounds — needs human review) | GRG desk reject→JPhysComm desk reject 03-23→JMP | fallback: CQG (IF 3.6), Ann. Phys. (IF 3.0) |

| `2026_single_primitive_universality_hierarchy` | Proc. AMS | P0 | — |
| `2026_chebotarev_quotient_entropy_fold_groupoid_rigidity` | — | 待分诊 | — |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | JDDE | 待分诊 | — |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | — | 待分诊 | — |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | Dynamical Systems | 待分诊 | — |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | — | 待分诊 | — |
| `2026_recursive_addressing_prefix_sites_tac` | TAC | 待分诊 | — |
| `2026_elliptic_normalization_branch_geometry_quartic_spectral` | — | 待分诊 | — |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | — | 待分诊 | — |
| `2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge` | — | 待分诊 | — |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | — | 待分诊 | — |
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
