# Publication Workspace

更新日期：2026-03-23

详细投稿计划见 `pubplan.md`。

对应总稿：`docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence`

每个目录至少包含 `README.md`（目标期刊、边界、定位）。已完成的目录还包含 `OUTLINE.md`、`SOURCE_MAP.md`、`MIN_SKELETON.md`、`MAIN_PAPER_POSITION.md`、`THEOREM_LIST.md`、`CONTENT_NOTES.md`、`BIB_SCOPE.md`、`main.tex`。

---

## 已投稿（7 篇）

| # | 目录 | 期刊 | 覆盖总稿章节 | 状态 |
|---|---|---|---|---|
| 1 | `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt` | JNT | `folding/` 核心 | 已投稿 |
| 2 | `submitted_2026_folded_rotation_histogram_certificates_siads` | SIADS | `experiments/` + `statistical_stability/` | 已投稿 -> fall back 转投etds已投 |
| 3 | `submitted_2026_zeckendorf_streaming_normalization_automata_rairo_ita` | RAIRO-ITA | `emergent_arithmetic/` Zeckendorf 算法 | 已投稿 |
| 4 | `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint` | RINT | `emergent_arithmetic/` 模结构 | 已投稿 |
| 5 | `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp` | QTDS → 改投 J. Theoretical Probability (Springer) | `group_unification/` Parry 基线 | 已投稿（改投中） |
| 6 | `submitted_2026_branch_cubic_regular_s4_closure_prym_ray_class_jnt` | JNT | `circle_dimension_phase_gate/` S4/Prym | 已投稿 |
| 7 | `submitted_2026_grg_shell_geometry_from_stationary_detector_thermality_grg` | GRG | 物理应用 | 已投稿 |

---

## 下一批投稿：第一批（最高优先，2026-04 至 2026-06）

框架优先：先发表定义范式的论文，再发表范式内的技术结果。

| 代号 | 目录 | 论文标题 | 首选期刊 | 核心材料 |
|---|---|---|---|---|
| E₁ | `2026_conservative_extension_chain_state_forcing_apal` | 无公理结构扩张链与状态 Forcing | Annals of Pure and Applied Logic | `logic_expansion_chain/` |
| E₂ | `2026_scan_projection_address_semantics_sigma_nonexpansion_etds` | 扫描-投影地址语义与 σ-代数不扩张 | ETDS | `spg/` + `recursive_addressing/` |
| F | `2026_projection_ontological_mathematics_core_tams` | 投影本体数学核心 | Trans. AMS | `pom/` 核心子集 |

## 下一批投稿：第二批（高优先，2026-06 至 2026-08）

| 代号 | 目录 | 论文标题 | 首选期刊 | 核心材料 |
|---|---|---|---|---|
| G | `2026_circle_dimension_haar_pullback_cauchy_weight_jfa` | 圆维与 Haar 回拉 | J. Functional Analysis | `circle_dimension_phase_gate/` 核心子集 |
| H | `2026_dynamical_zeta_finite_part_spectral_fingerprint_etds` | 动力学 ζ 有限部与谱指纹 | ETDS | `zeta_finite_part/` (不含 xi/) |
| H₁（涌现稿） | `2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists` | 自对偶同步核、completed determinant 与 cyclotomic twists | 待定 | 由 H 的 `online_kernel` / torsion-completion 支线拆出 |
| H₂（涌现稿） | `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta` | Fredholm--Witt bridge、循环块实现与谱刚性 | 待定 | 由 H 的 `operator` 支线拆出 |
| H₃（涌现稿） | `2026_prime_languages_sofic_obstructions_dynamical_zeta` | 素数语言、sofic 障碍与动力学 ζ | 待定 | 由 H 的 `syntax` 支线拆出 |

## 下一批投稿：第三批（2026-08 以后，待 E/F/G/H 审稿反馈后定稿）

| 代号 | 目录 | 论文标题 | 首选期刊 | 核心材料 |
|---|---|---|---|---|
| I | `2026_group_unification_fibonacci_prime_window_entropy_time` | 群论统一窗与熵率时间协议 | J. Algebra | `group_unification/` 超出论文 #5 部分 |
| J | `2026_zeta_completion_xi_zero_audit` | ζ-Completion 与 Ξ 零点审计 | Inventiones | `zeta_finite_part/xi/` 核心子集 |
| K | `2026_observer_spacetime_logic_dynamic_update_causal_forcing` | 观察者时空逻辑：动态更新、多观察者通信与事件-区域 forcing | J. Philosophical Logic / Foundations of Physics | `logic_expansion_chain/` L₇–L₁₀^OST（E₁ 续篇） |

---

## 逻辑依赖链

```
已发表: #1(Folding) #2(Experiments) #3(Zeckendorf) #4(FibMod) #5(Parry) #6(S4/Prym) #7(GRG)

    ┌──────────────────────────────────────┐
    │  E₁ cohomological visibility (APAL)  │
    └──────────┬───────────────────────────┘
               │
               ├──────────────────────────────────────┐
               │                                      │
    ┌──────────▼───────────────────────┐   ┌──────────▼──────────────────────┐
    │  E₂ 地址语义 (ETDS)              │   │  K 观察者时空逻辑 (第三批)       │
    └──────────┬───────────────────────┘   │  L₇–L₁₀^OST                    │
               │                           │  J.Phil.Logic / FoP / APAL     │
    ┌──────────▼───────────────────────┐   └─────────────────────────────────┘
    │  F  POM 核心 (Trans. AMS)        │
    └──────┬───────────┬───────────────┘
           │           │
┌──────────▼──┐  ┌─────▼──────────────┐
│ G 圆维 (JFA) │  │ H ζ有限部 (ETDS)   │
└─────────────┘  └─────┬──────────────┘
                        │
                ┌───────▼──────────────┐
                │ J ζ-completion       │
                └──────────────────────┘

    ┌──────────────────────────────────────┐
    │ I 群论统一窗 (J.Algebra) 弱依赖 E/F  │
    └──────────────────────────────────────┘
```

E₁ 是全部后续论文的逻辑基础；K 是 E₁ 的续篇（L₇–L₁₀ 物理桥接层，硬依赖 E₁，弱依赖 #7 GRG）；F 是 G/H/J 的必要前驱；G/H/I 之间无硬依赖。

---

## 旧计划目录（存档）

以下目录属于 2026-03-06 版旧拆稿计划。其中部分内容已被新方向 E₂/F 吸收，部分为独立技术稿。

| 目录 | 旧计划定位 | 当前状态 |
|---|---|---|
| `2026_fold_truncation_defect_stokes_dynamical_systems` | 旧第二批：折叠截断缺陷 | 独立技术稿，可后续评估 |
| `2026_prefix_scan_error_boundary_rates_dynamical_systems` | 旧第二批：扫描误差边界率 | 独立技术稿，可后续评估 |
| `2026_cubical_stokes_inverse_boundary_readout_jdsgt` | 旧第二批：Cubical Stokes 逆 | 独立技术稿，可后续评估 |
| `2026_recursive_addressing_prefix_sites_tac` | 旧第三批：递归寻址（TAC） | **已被 E₂ 取代**（SPG + recursive_addressing 合并） |
| `2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints` | 旧草案 | 内容已被论文 #1/#3 覆盖 |

---

## 显式冻结

以下总稿章节在当前投稿周期内不独立立项（但部分内容已被上述新方向覆盖）：

- `sections/body/conclusion/` (65,949 行) — 待分批消化
- `sections/body/discussion/` (2,743 行) — 待总稿最终版
- `sections/body/high_dimensional_cut_project/` (12 行) — 仅背景定位
- `sections/body/fold_residual_time/` (280 行) — 可并入 E₂ 或独立短稿
