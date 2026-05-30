# Publication Board

更新日期：2026-05-21

这张表只给人看：一篇论文或一条投稿路线一行。机器调度状态放在本地 `PROGRAM_BOARD_MACHINE.md`；这里不放内部 hard marker。

处理原则：拒稿路线优先处理。若拒稿稿件和其他稿件重叠很大，就合并成一个 canonical 重写稿再投；若它和仍在审的稿件高度重叠，就先等在审稿件反馈。

## Newmath intake candidates

`newmath` 来源的候选投稿单元先进入
`papers/publication/newmath_intake/`。这些目录不是 active paper track，
不进入 Stage A/P0-P7，只有 promotion checklist 通过后才创建正式
`2026_*` 论文目录。

| seed | 优先级 | 当前状态 | 下一步 |
|------|------|------|------|
| `newmath_intake/seeds/bedc_automation_pipeline` | P0 | intake-hardened；系统/自动化论文候选；仍非 active paper track | 补 3-6 个真实 case-study rows，提交前复核 CICM presentation-only / COLM / ICTAI CFP，然后再决定是否 promotion |
| `newmath_intake/seeds/bedc_finite_kernel_calculus` | P0 | intake-ready；有限核逻辑论文候选 | 抽取 FKernel/GroundCompiler/NameCert theorem inventory |
| `newmath_intake/seeds/bedc_rule110_finite_witness` | P0 | intake-ready；Rule110 finite-witness artifact 论文候选 | 复核 artifact counts、验证命令、limitation ledger |
| `newmath_intake/seeds/metacic_closed_normal_consistency` | P1 | intake-ready；MetaCIC 类型论 note 候选 | 做 related-work audit 和 exact theorem boundary |
| `newmath_intake/seeds/observer_state_semantics` | P1 | intake-ready；observer-state semantics 候选 | 降调成 workshop/position framing，避免 AI-consciousness 强主张 |

## 已投稿：等待反馈

| 论文或路线 | 期刊 | 当前状态 | 下一步 |
|------|------|------|------|
| `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` | Journal of Theoretical Probability | 路线：QTDS → JTP；已投稿 JTP，peer review 中；7 reviewers invited；题名已改为 “Exponential Tilting and Information Fluctuations for One-Step Markov Measures on Shifts of Finite Type” | 等编辑/审稿反馈；不要处理重叠的 zero-jitter route |
| `submitted_2026_canonical_zeckendorf_normalization_berstel_adder_rairo_ita` | RAIRO-Theor. Inf. Appl. | 路线：RAIRO-ITA；已投稿；无反馈，等待结果 | 等反馈 |
| `submitted_2026_quartic_cover_37a1_regular_s4_closure_jnt` | Journal of Number Theory | 路线：JNT；2026-03-14 submitted，2026-03-25 under review；题名：A quartic cover of 37a1 and its regular S4-closure | 等反馈 |
| `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` | DCDS-A | 路线：Nonlinearity → DCDS-A；已投稿 2026-05-11，审稿中；Paper ID `260511-Zhang-2` | 等反馈；相关 Fibonacci/Zeckendorf finite-window 稿件先暂停 |
| `2026_scan_error_prefix_partitions_convergence_rates_etds` | ETDS | 路线：canonical ETDS；已投稿；提交日期和编号待补；旧 `prefix_scan_error...` 目录是 legacy route | 补 submission ID；旧 `prefix_scan_error...` 目录只作历史记录 |

## 正在发展或可继续推进

| 论文或路线 | 期刊 | 当前状态 | 下一步 |
|------|------|------|------|
| `2026_fredholm_determinants_cyclic_block_spectral_rigidity_jst` | Integral Equations and Operator Theory；备选：Operators and Matrices / Complex Analysis and Operator Theory | JST 已拒 2026-05-21；David Damanik/EditFlow：editors concluded it was not suitable for Journal of Spectral Theory；无技术审稿意见。Codex-only retarget：IEOT fit=8/10；no-Oracle Stage A 已推进到第 8 轮并多次本地增补，但最终 A2 只产生 +313 chars 且无新增 theorem，被 deterministic fake-extension gate 拦截 | 在原文件夹中改，不新建文件夹；需要人工 theorem-deepening/重写 operator-theory framing 后再回 Stage A；暂不触发 Oracle |
| `upperfiber` | Fibonacci Quarterly | RJ 已拒；RJ 反馈：贡献偏形式包装、算术深度不足，且 n=30 数据不支持“八类型”说法；RINT 是重复历史路线 | 在原 upper-fibers/FQ 文件夹中改，不新建文件夹；目标 FQ；从 Stage A 重新深改，修正 n=30/八类型并加入新实质结果 |
| `2026_detector_shells_click_record_kms_jphyscomm` | 待重新选物理/数学物理期刊 | canonical merged rewrite route；GRG 和 JPhysComm 都已拒；JPhysComm 版本是 GRG route 后续版本；overlap resolved；需要带着两次拒稿背景重新处理 | 在现有文件夹中改；从 Stage A 重新走，prompt 需附 GRG/JPhysComm 拒稿背景和应用/期刊适配问题；不拆成两篇 |
| `2026_finite_parts_dynamical_zeta_shifts_finite_type_etds` | 待重新选 dynamical systems / symbolic dynamics 期刊 | ETDS 已拒 2026-05-26；Submission ID `ETDS-2026-0139`；题名 “Adams-Mobius primitive inversion for finite-group extensions of shifts of finite type”；Ian Melbourne/quick expert opinion: not appropriate for ETDS, needs true advance/new phenomenon/surprising result/notable contribution and closer ETDS fit | 在现有文件夹中改；从 Stage A 重新走，带上 ETDS 拒稿原因；优先做 novelty escalation 和 venue retarget，不要只做润色 |
| `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` | ETDS / symbolic dynamics venue | SIADS 已拒；理由是缺少应用影响，不是技术审稿；建议转投。当前 ETDS 版本与 Zeckendorf-fold/Sturmian-Parry 稿高度重叠 | 合并 `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` 素材，从 Stage A 进入深改；不要拆成两篇同时投 |
| `2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa` | Journal of Functional Analysis | Oracle 审稿门已过；还不是投稿包 | 进入最终投稿确认 |
| `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | JDDE | Oracle 审稿门已过；还不是投稿包 | 进入最终投稿确认 |
| `2026_single_primitive_universality_hierarchy` | Proceedings of the AMS | 需要实质 theorem-deepening | 让管线补强数学内容 |
| `2026_chebotarev_quotient_entropy_fold_groupoid_rigidity` | 待选 | split-overlap gate 未发现硬重复，但之前路径较旧 | 需要人工 theorem review 后再跑 |
| `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity` | 待选 | 需要实质 theorem-deepening | 让管线补强数学内容 |
| `2026_elliptic_normalization_branch_geometry_quartic_spectral` | 待选 | split-overlap gate clean；需要 theorem-deepening | 让 Stage F 选期刊并推进 |

## 手动分诊后可恢复

| 论文或路线 | 期刊 | 当前状态 | 下一步 |
|------|------|------|------|
| `2026_homological_visibility_gluing_obstructions_state_forcing_apal` | APAL | 可恢复；PDF 可编译。旧 pipeline 记录主要 blocker 是 APAL 作者信息缺失；Stage A audit 已通过，仅剩 label/prose 小一致性和 ledger/backflow 项 | 不应重做数学深改；从 submission-pack / Stage C-final polish 进入，补作者元数据和低风险编辑一致性后准备投稿 |
| `2026_prime_languages_finite_state_obstructions_monatshefte` | Monatshefte | 已手动处理 Stage C polish；Oracle 已 accept，独立终审之前要求 revise 的问题主要是 bibliography wording、source artifact scan、overfull boxes、journal register | 放回 Stage C final gate，从 C12 继续；不从头重写 |
| `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | 改投候选：J. Algebraic Combinatorics / Experimental Mathematics / ETDS | 可恢复但不宜继续按 IMRN 强投；PDF 可编译。旧 P4 blocker 是 kernel 动机不足、S6/光滑性证书未展示、bibliography 太薄；Stage A audit 显示数学主体已通过但有证书可追溯性和小证明措辞项 | 从 Stage A retarget/polish 进入，先降目标或重选 venue，补动机、证书展示和参考文献，再进审稿门 |

## 重叠、归档或暂停

| 论文或路线 | 期刊 | 当前状态 | 下一步 |
|------|------|------|------|
| `submitted_2026_finite_window_rigidity_fibonacci_numeration_fq` | Fibonacci Quarterly | FQ 于 2026-05-01 拒稿；本地 decision 指出它与 DCDS-A 在审稿件 `260511-Zhang-2` 高度重叠；已决定暂不改 | 不单独改投；等 DCDS-A 反馈后决定是否吸收、删减成不同短文，或彻底关闭 |
| `2026_zeckendorf_folds_sturmian_rigidity_parry_divergence_etds` | ETDS | 与 folded-histograms SIADS/ETDS route 重叠；已并入 folded-histograms 合并处理 | 暂停独立处理；作为 canonical ETDS 合并深改素材 |
| `submitted_2026_folded_histograms_sampling_certificates_parry_mismatch_siads` | SIADS | SIADS 已拒；已并入 folded-histograms canonical route | 不独立处理 |
| `submitted_2026_folded_rotation_histogram_etds` | ETDS | 这条就是 folded-histograms/SIADS 拒稿路线的历史记录；已并入 canonical folded-histograms route | 不独立处理 |
| `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt` | Journal of Number Theory | 已拒；后续由 DCDS-A `2026_sharp_three_window_threshold_fibonacci_conjugacy_dcds` 转投承接 | DCDS-A 在审期间不独立处理 |
| `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp` | Journal of Theoretical Probability | 已拒；后续由 `submitted_2026_tilt_dynamics_cylinder_information_parry_measure_qtds` 转投承接 | tilt-dynamics JTP 在审期间不独立处理 |
| `submitted_2026_shell_geometry_detector_thermality_kms_grg` | GRG | rejected history route；parked；superseded by canonical active route `2026_detector_shells_click_record_kms_jphyscomm` | GRG/JPhysComm both rejected；do not process independently；background feeds the canonical detector-shells rewrite |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | 待选 | 与 DCDS-A / folded-histograms / Zeckendorf-fold routes 重叠 | 暂停 |
| `2026_deterministic_telescoping_fold_truncation_defects_dynamical_systems` | Dynamical Systems | 与 folded symbolic dynamics family 重叠 | 暂停 |
| `2026_golden_mean_folding_stable_types_auditable_addressing` | 待选 | 与 DCDS-A three-window route 重叠 | 等 DCDS-A 反馈 |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | legacy | 旧目录；canonical route 是 `2026_scan_error_prefix_partitions_convergence_rates_etds` | 不独立处理 |
| `2026_finite_window_zeckendorf_fibers_discrete_thermodynamics_tams` / `2026_projection_ontological_mathematics_core_tams` | Transactions AMS | 两条 TAMS route 重叠 | 需要先定 canonical route |
| `2026_finite_observation_escape_rates_cyclotomic_resonances_etds` / `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | ETDS | 两条 observation/escape-rate route 重叠 | 需要先定 canonical route |
| `2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal` / `2026_recursive_addressing_prefix_sites_tac` | APAL / TAC | 与 homological-visibility route 重叠 | 需要先定 canonical route |
| `2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online` | 待选 | 会复现 Fibonacci modulus-chain quotient 或转入 online-normalization/transducer manuscript | 暂停 |
| `2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge` | 待选 | semantic overlap 需人工解决 | 暂停 |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | legacy | 与 canonical JDDE route 重复 | 不独立处理 |
| `2026_golden_ratio_driven_scan_projection_generation_recursive_emergence` | missing source | board 中有记录但本地缺源目录 | 源目录恢复前不处理 |

## 骨架

| 论文或路线 | 期刊 | 当前状态 | 下一步 |
|------|------|------|------|
| `2026_group_unification_fibonacci_prime_window_entropy_time` | 待选 | 骨架 | 暂不处理 |
| `2026_zeta_completion_xi_zero_audit` | 待选 | 骨架 | 暂不处理 |
