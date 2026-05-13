# Program Board

全量论文状态表。管线 (`oracle_pipeline.py`) 读此文件决定调度：跳过已投/已发表/骨架，处理 P0–P7 阶段论文。

更新日期：2026-05-10

## 状态编码

- `已投 MM-DD` — 已投稿，等待编辑决定
- `已投 MM-DD 审稿中` / `R&R` / `接收` / `拒稿` — 投稿后续
- `✅ 可投稿` — 管线终审通过 (Oracle accept + Claude submit)，等用户手动 submit
- `P0`–`P7` — 管线阶段（未投稿）
- `P4-MAJOR` — P4 门禁返回 MAJOR_REVISION
- `待分诊` — 有 main.tex 但未入管线
- `骨架` — 无 main.tex

## 手动投稿队列 (2026-05-10 快照)

| 论文 | 目标期刊 | 备注 |
|------|---------|------|
| — | — | 当前无待手动投稿项；已投稿稿件移至全量状态表，C-RUNNING 稿件等终审通过后再自动入队 |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Journal of Spectral Theory | C-DONE round 4: Oracle accept + Codex submit; 需准备 cover letter + metadata |

## 全量状态表

| 目录 | 目标期刊 | 状态 | 改投记录 |
|------|---------|------|---------|
| `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq` | Fibonacci Q. | 拒稿 05-01；FQ/JNT 路线关闭；不回 Stage A | ETDS→JNT→FQ; FQ editor: 更适合 dynamical systems; core 已并入/重叠 DCDS-A 在审稿件 `260511-Zhang-2` |
| `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` | ETDS | C-STUCK (Oracle+Claude exhausted 15 rounds) | SIADS→ETDS | fallback: Israel J. Math (IF 1.0), DCDS-A (IF 1.1) |
| `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | ETDS | A-BLOCKED (overlap deferred; wait for prior submitted/current sibling feedback) | prior routes include folded-histograms / DCDS-A / submitted folded siblings; do not advance until board explicitly closes or merges those routes |
| `submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita` | RAIRO-ITA | 已投 04-07 | — |
| `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint` | RINT归档 | 归档；与RJ upper-fibers稿完全重复；不处理 | exact duplicate of `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj` |
| `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj` | RJ归档 | 归档；RJ拒稿 05-11；路线关闭；不回 Stage A | active FQ deep-revision fork: `2026_upper_fibers_witness_covers_fibonacci_apparition_fq` |
| `2026_upper_fibers_witness_covers_fibonacci_apparition_fq` | Fibonacci Quarterly | A-READY-FQ-DEEPEN | RJ→FQ深改候选；先修正n=30/八类型问题并新增实质结果；不在手动投稿队列 |
| `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` | DCDS-A | 已投 05-11 审稿中 | Nonlinearity→DCDS-A; MSP/EditFlow Paper ID: 260511-Zhang-2 |
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | J. Theoret. Probab. | 已投, peer review 中 (7 reviewers invited) | QTDS→JTP | 标题改为 "Exponential Tilting and Information Fluctuations for One-Step Markov Measures on Shifts of Finite Type" |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | JNT | 已投 04-07 | — |
| `2026_finite_window_zeckendorf_fibers_discrete_thermodynamics_tams` | Trans. AMS | A-BLOCKED (overlap needs_human_resolution before Stage A) | overlaps `2026_projection_ontological_mathematics_core_tams`; record canonical route before advancing |
| `2026_finite_observation_escape_rates_cyclotomic_resonances_etds` | ETDS | A-BLOCKED (overlap needs_human_resolution before Stage A) | overlaps `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`; record canonical route before advancing |
| `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | APAL | B-STUCK (Oracle: minor revision, 20 rounds — needs human review) | — |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` | APAL | A-BLOCKED (overlap needs_human_resolution before Stage A) | overlaps homological-visibility / recursive-addressing routes; record canonical route before advancing |
| `2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa` | JFA | A-BLOCKED (max Stage A rounds exhausted; final audit real block (score=6)) | — |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | ETDS | 已投 05-10 | ScholarOne ETDS; Oracle+Claude pass, 9 rounds |
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | J. Spectral Theory | C-DONE round 4: Oracle accept + Codex submit; needs cover letter + metadata | synced from pipeline_state DONE; manual-submit candidate, not auto-pipeline |
| `2026_prime_languages_finite_state_obstructions_monatshefte` | Monatshefte | C-RUNNING (Stage C final gate active 2026-05-13; B passed; awaiting final Oracle/Codex confirmation) | — |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | IMRN | B-STUCK (Oracle: reject, 20 rounds — needs human review) | IMRN→Exp. Math 候选 |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | ✅ 可投稿 — C-8 (Oracle accept + Claude submit, 4/5 轮一致；需 cover letter + metadata) | Oracle: deepen=minor revision, fresh=minor revision, 13 rounds |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | legacy archive | 归档；parked；canonical ETDS route is `2026_scan_error_prefix_partitions_convergence_rates_etds` | overlap resolved by `2026_scan_error_prefix_partitions_convergence_rates_etds/cross_paper_dedup.md`; do not process independently |
| `2026_detector_shells_click_record_kms_jphyscomm` | J. Math. Phys. | A-BLOCKED (overlap deferred; wait for prior submitted sibling feedback) | prior submitted route: `submitted_2026_shell_geometry_detector_thermality_kms_grg`; do not advance until editorial feedback / closure |

| `2026_single_primitive_universality_hierarchy` | Proc. AMS | A-BLOCKED (max Stage A rounds exhausted; final audit unclear failure) | — |
| `2026_chebotarev_quotient_entropy_fold_groupoid_rigidity` | — | 待分诊 | — |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | JDDE | P0 | triaged 2026-05-13: substantial main.tex; canonical route for centered homotopy / cubical Stokes coefficient-bound manuscript |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | — | 待分诊 | — |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | Dynamical Systems | A-BLOCKED (overlap deferred; wait for prior submitted/current sibling feedback) | prior routes include folded-histograms / DCDS-A / submitted folded siblings; also has unresolved overlap findings |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | — | 待分诊 | — |
| `2026_recursive_addressing_prefix_sites_tac` | TAC | A-BLOCKED (overlap needs_human_resolution before Stage A) | overlaps gluing-failure / homological-visibility routes; record canonical route before advancing |
| `2026_elliptic_normalization_branch_geometry_quartic_spectral` | — | 待分诊 | — |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | — | 待分诊 | — |
| `2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge` | — | 待分诊 | — |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | — | 待分诊 | — |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | legacy archive | 归档；parked；duplicate of canonical JDDE route `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | identical main.tex hash as canonical route; do not process independently |
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
