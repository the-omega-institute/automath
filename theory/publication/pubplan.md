# 2026 拆稿-投稿 Pitch Plan

更新日期：2026-03-23

## 0. 总体进展（自 2026-03-06 更新）

### 已发表论文清单（7 篇）

| # | 目录名 | 覆盖总稿章节 | 投稿目标 |
|---|---|---|---|
| 1 | `2026_resolution_folding_core_symbolic_dynamics_etds` | `folding/` 核心 | ETDS |
| 2 | `2026_folded_rotation_histogram_certificates_siads` | `experiments/` + `statistical_stability/` | SIADS |
| 3 | `2026_zeckendorf_streaming_normalization_automata_rairo_ita` | `emergent_arithmetic/` Zeckendorf 算法 | RAIRO-ITA |
| 4 | `2026_fibonacci_moduli_cross_resolution_arithmetic_integers` | `emergent_arithmetic/` 模结构 | — |
| 5 | `2026_zero_jitter_information_clocks_parry_gibbs_rigidity_golden_mean_shift` | `group_unification/` Parry 基线 | — |
| 6 | `2026_branch_cubic_regular_s4_closure_prym_ray_class_arithmetic` | `circle_dimension_phase_gate/` S4/Prym | — |
| 7 | `2026_grg_shell_geometry_from_stationary_detector_thermality_static_kms_spacetimes` | 物理应用 | GRG |

### 与旧 Pitch Plan 的对照

| 旧方向 | 旧优先级 | 当前状态 |
|---|---:|---|
| `A. Folding` | 1 | 已由论文 #1 (ETDS) 发表 |
| `B. Experiments / Statistical Stability` | 1 | 已由论文 #2 (SIADS) 发表 |
| `C. SPG clarity / two-budget` | 2 | 未独立发表；SPG 内容大幅扩展（33 files, 5304 lines），需重新评估 |
| `D. Emergent Arithmetic / Zeckendorf` | 3 | 已由论文 #3 (RAIRO-ITA) + #4 发表 |
| `POM / zeta_finite_part` | 暂缓 | 内容大幅扩充（POM: 276 files / 66k lines; zeta: 961 files / 273k lines），需重新规划 |

### 自 2026-03-06 以来的主要新增内容（102 commits）

| 新增/大幅扩展章节 | 规模 | 核心数学内容 |
|---|---|---|
| `logic_expansion_chain/` | 9 files, 1432 lines | 无公理结构扩张链、状态 forcing、观察者时空定位、多轴细化协议 |
| `circle_dimension_phase_gate/` | 67 files, 17k lines | Haar 回拉唯一性、Cauchy 权重强制、圆维定义与算律、精度势账本、Poisson-Cauchy 核族、S4/Prym 分裂 |
| `group_unification/` | 91 files, 19k lines | xi-time 协议、Wulff scale ledger、Joukowsky-Gödel 搬运、Fibonacci-Lie 共振、Window-6 离散结论 |
| `zeta_finite_part/xi/` | 889 files, 262k lines | 终端结论（57 项）、定理（52 项）、Chebotarev 通道化、CMV 谱证书、椭圆 Lattès 族、PRIMEGAME |
| `conclusion/` | 229 files, 67k lines | 大量分支结论：Wulff 动力学、window-6 纤维、冻结微态熵、golden 共振、各向异性边界等 |
| `pom/` (扩展部分) | 276 files, 66k lines | 共振 Hankel 秩坍缩扩展、p-adic 判别式厚度、moment-kernel 压缩、纤维 toggle-Coxeter |
| `fold_residual_time/` | 5 files, 280 lines | 协议筛选、残差展开、三定理链导航 |
| `high_dimensional_cut_project/` | 2 files, 12 lines | 高维切投影接口（仅背景定位） |

## 1. 新 Pitch 结论

**核心判断变化：**

旧 plan 中 A/B/D 已全部发表完毕。当前最重要的未发表内容不再是"细枝末节的数学创新点"，而是**核心框架性内容**——即定义整个理论范式的地基性论文。这些框架性论文的发表将使已发表的 7 篇技术稿获得统一的理论锚点。

**新的拆稿策略：**
1. **优先发表框架性内容**（定义范式的论文先于细分结果的论文）；
2. **按逻辑依赖链排序**（下游论文应引用上游框架论文）；
3. **每篇论文必须自成体系**（不依赖总稿中的未发表章节）。

## 2. 新一批可拆解投稿方向总表

| 方向 | 从哪里拆 | 一句话主张 | 必须删掉什么 | 推荐优先级 | 推荐定位 |
|---|---|---|---|---:|---|
| `E₁. 状态 forcing 语义下粘合障碍的上同调可见性` | `logic_expansion_chain/` L₀–L₆ + L₈(部分) | 自足四层保守扩张 + 局部对象 + gerbe 障碍分解 + UCT 可见商 + character-blind Ext 残差：精确刻画"粘合障碍的哪部分是语义可见的" | L₇(时间)/L₉(观察者)/L₁₀(时空)留给论文 K；所有具体动力系统内容 | **1** | **数理逻辑，APAL 首选** |
| `K. 观察者时空逻辑：动态更新、多观察者通信与事件-区域 forcing` | `logic_expansion_chain/` L₇–L₁₀^OST | 在 E₁ 的四层基础上继续扩张：时间 = 细化序参数、观察者无特权、事件-区域系统中的因果兼容 forcing——把"事实相对于谁/在哪成立"从哲学直觉变成有证明链的数学结构 | 所有已由 E₁ 覆盖的 L₀–L₆ 层（引用 E₁ 即可） | **3** | **逻辑/物理基础交叉，待 E₁ 发表后启动** |
| `E₂. 扫描-投影地址语义与 σ-代数不扩张` | `spg/` + `recursive_addressing/` | 在保测动力系统读出口径下严格化"地址先于值"：递归地址化不扩张 σ-代数、双预算寻址容量律、清晰度指数律 | logic_expansion_chain 的抽象逻辑（引用 E₁ 即可）；POM/zeta 的前向引用 | **1** | **遍历论 / 动力系统，技术奠基稿** |
| `F. 投影本体数学核心` | `pom/` (核心定理子集) | 三投影三纤维框架下的信息账本恒等式、投影词重写终止-合流-可判定闭环、moment-kernel 编译与 Hankel 共振判别 | zeta 侧所有终端分支；conclusion 中的细分结论 | **1** | **理论核心稿，冲强刊** |
| `G. 圆维与 Haar 回拉` | `circle_dimension_phase_gate/` (核心定义与算律子集) | Cayley 坐标门的 Haar 回拉唯一强制 Cauchy 权重；圆维作为相位圆因子的群论计数量；精度势账本闭合 | S4/Prym 细分结论、椭圆族分支、过深代数细节 | **2** | **分析/代数稿，强刊常规** |
| `H. 动力学 ζ 有限部与谱指纹` | `zeta_finite_part/` (syntax + online_kernel + operator + finite_part) | SFT/sofic 上的动力学 ζ 函数、有限部常数、扭曲 Chebotarev 等分布、Peter-Weyl 非阿贝尔通道化 | xi/ 目录中的 889 个终端文件；与 conclusion 的长跨引用 | **2** | **谱论稿，强刊常规** |
| `I. 群论统一窗与熵率时间协议` | `group_unification/` (超出论文 #5 的部分) | Fibonacci-prime 域相窗、CRT 分裂模板、xi-time 熵率协议、Window-6 离散结构 | 与 POM/zeta 的终端分支耦合 | **3** | **第二批代数稿** |
| `J. ζ-completion 与 Ξ 零点审计` | `zeta_finite_part/xi/` (核心子集) | CMV 谱证书生成、Tate/Maslov 指标的自对偶缺陷、profinite Chebotarev 的有限数据证书 | 椭圆 Lattès 的过度细分分支 | **3** | **第二批谱论深稿** |

## 3. 每个方向到底怎么拆

### E₁. 状态 forcing 语义下粘合障碍的上同调可见性（最高优先）

- **核心材料：**
  - `sections/body/logic_expansion_chain/` 中 L₀–L₆ + L₈(部分) 相关内容
  - 已有完整 LaTeX 草稿：`2026_conservative_extension_chain_state_forcing_apal/`（12 个 TeX 文件，~2,300 行，可编译）
- **当前范围（自足四层 + cohomological visibility）：**
  - 自足四层保守扩张：pointwise semantics → information-state forcing → local-object semantics → refinement dynamics
  - 实际覆盖 L₀–L₆ + L₈(部分)，但叙事口径为"四层"，不提 11 层架构
  - 核心定理链：forcing necessity（pointwise irreducibility of gluing predicates）→ sheafification characterization → component gerbe decomposition → UCT homological evaluation → intrinsic visible quotient → character-blind Ext-residual → branch strictification budget
  - 与 Abramsky–Brandenburger sheaf-theoretic contextuality 的显式联系：unique-branch case 退化为标准 no-global-section picture，Ext-residual 精确解释 Carù 的 incomplete cohomological detection
  - **不包含** L₇(时间/更新)、L₉(观察者索引)、L₁₀(观察者时空)——这些留给论文 K
- **已完成的深度内容（2026-03-20 修订）：**
  1. Forcing necessity theorem（构造两个 admitted references 在 L₁ 不可区分但在 L₂ 粘合性质相反）
  2. Realization prestacks + stackification 恢复可见值类
  3. Component gerbe 分解（含 branch-constancy 修正、global conservativity at terminal fibre 条件）
  4. UCT → 内禀可见商 + 内禀隐藏子群
  5. Character-blind obstruction（纯 Ext 残差，H₁-free ⇒ no blindness，H₂=0 ⇒ all blind）
  6. Branch-sensitive / branch-uniform 可见商 + exactstrictification budget
  7. 两个 worked examples（one-bit hidden obstruction + RP² character-blind）
  8. Abramsky–Brandenburger contextuality connection
  9. Finite-state complexity 移至附录
- **为什么最高优先：**
  - 这是定义**整个理论范式的语义地基**（E₂/F/G/H 全部在此框架内工作）
  - 论文有精确的 research question（"粘合障碍的哪部分是语义可见的？"）和精确的回答（UCT visible quotient vs Ext-blind residual）
  - 与 contextuality 文献的联系为 APAL 审稿人提供了明确的 novelty signal
- **为什么只发四层而不是完整 11 层：**
  - 当前论文的核心竞争力是定理链的锐度（每一步回答同一个精确问题），加入 L₇/L₉/L₁₀ 会稀释主线
  - L₇/L₉/L₁₀ 是物理桥接层（时间、观察者、因果结构），在纯逻辑期刊中缺乏 motivating example
  - 完整 11 层留在主论文作为整体架构叙事；物理桥接层未来拆为论文 K
  - 当前四层口径实际已覆盖 ~7 层内容，缺的只是 L₇/L₉/L₁₀
- **成稿定位与期刊：**
  - **首选：Annals of Pure and Applied Logic（APAL）**——论文融合 forcing + sheaf theory + gerbes + UCT，交叉深度匹配 APAL 的 "logic meets algebra/topology" 风格；MSC 03B45/03F55/03G30/18F20 均为 APAL 核心分类
  - 次选：Review of Symbolic Logic（如需强调 contextuality 哲学联系）
  - 回退：Notre Dame Journal of Formal Logic（若 APAL desk reject）
  - ~~Foundations of Physics~~（已排除：E₁ 不做物理预测）
- **风险与对策：**
  - 风险：APAL 审稿人可能要求更多 model-theoretic 结果或更广泛的 examples
  - 对策：当前已有两个 worked examples + Abramsky–Brandenburger 退化；可进一步补充 non-abelian 推广方向或 decidability 结果

### K. 观察者时空逻辑（第三批，待 E₁ 发表后启动）

- **核心材料：**
  - `sections/body/logic_expansion_chain/` 中 L₇–L₁₀^OST 相关子节：
    - `subsec__logic-expansion-chain-dynamics-time-multiaxis.tex`（L₇ 动态更新与时间、L₈ 多轴完整版）
    - `subsec__logic-expansion-chain-observer-spacetime.tex`（L₉ 观察者索引、L₁₀ 事件-区域系统）
- **范围：**
  - L₇：状态推进 p ⇝ q、时间戳 τ = χ ∘ λ、延迟可判定性、更新保持 forcing（无溯因修正）
  - L₈（完整版）：轴索引集 J、轴支撑 K▷_p φ、轴不可替代性、轴正交性与融合
  - L₉：观察者集合 I、observer-relative forcing p ⊢_i φ、内部更新 Act_i^int、通信通道 Ch_{i→j}
  - L₁₀^OST：事件-区域系统 (X, ⪯_X, U, Cov_X, χ)、因果兼容性、区域 forcing、耦合态、共享 forcing c ⊢^∀_{K,U} φ
  - 桥接论文 #7（GRG 弯曲时空探测器）：L₁₀ 的事件-区域系统精确对接静态 KMS 背景中的时钟超曲面与记忆过渡超曲面
- **为什么不合并到 E₁：**
  - L₇/L₉/L₁₀ 的核心概念（时间、观察者、因果结构、区域 forcing）是物理桥接层，在纯逻辑论文中缺乏 motivating application
  - E₁ 的锐度来自精确回答"粘合障碍可见性"这一问题；加入观察者/时空层会破坏叙事焦点
  - 独立成文后可面向 logic-physics 交叉读者，而不是强迫纯逻辑审稿人评价物理动机
- **成稿定位与期刊：**
  - 首选：Journal of Philosophical Logic（逻辑 + 物理基础交叉，接受 formal epistemology / formal ontology 方向）
  - 次选：Synthese（哲学/科学基础，接受形式化框架论文）
  - 强刊路线：Annals of Pure and Applied Logic（若 L₇–L₁₀ 的保守扩张证明链足够技术性，可与 E₁ 同刊形成系列）
  - 物理基础路线：Foundations of Physics（L₁₀ 直接对接 GRG 论文的时空结构，此时有具体物理 motivating example）
- **依赖：**
  - 硬依赖 E₁（L₀–L₆ 基础层全部引用 E₁）
  - 弱依赖论文 #7（GRG，提供 L₁₀ 的物理实例化）
- **时间线：**
  - 2026 下半年启动（待 E₁ 投出且有初步反馈后）

### E₂. 扫描-投影地址语义与 σ-代数不扩张（最高优先）

- **核心材料：**
  - `sections/body/spg/sec__spg.tex`（扫描-投影生成器定义、双预算寻址容量律）
  - `sections/body/recursive_addressing/sec__recursive-addressing.tex`（σ-代数不扩张定理、NULL 局部截面障碍）
- **拆法：**
  - 纯测度论/遍历论/动力系统论文
  - 主线围绕三个核心定理：(1) 递归地址化 σ-代数不扩张（命题 `recursive-addressing-refinement`、推论 `recursive-addressing-visible-sigma-nonexpansion`）；(2) 清晰度指数律（定理 `spg-clarity-boundary-dimension`）；(3) 双预算寻址容量（定理 `spg-double-budget-address-capacity`）
  - 引言中只需简短引用 E₁ 的语义框架（1-2 段），不展开逻辑细节
  - 引言定位为"有限观测下的概念生成与可寻址性问题"，面向遍历论/测度论读者
  - 不引用 POM/zeta 的任何结论；只向前引用 folding（已由论文 #1 发表）
- **为什么最高优先：**
  - σ-代数不扩张定理是后续 POM、ζ 有限部等全部技术结论的逻辑前提
  - 材料成熟度高（已经过多轮修订）
- **成稿定位：**
  - 首选：ETDS（遍历论/动力系统顶刊）
  - 次选：Israel Journal of Mathematics
  - 回退：Nonlinearity

### F. 投影本体数学核心（最高优先）

- **核心材料：**
  - `sections/body/pom/sec__pom.tex` 中的前 ~60 个 `\input` 项（截至 `subsubsec__pom-real-q-pressure-thermo-frontier`）
  - 核心定理：信息账本恒等式（定理 `pom-kl-ledger`、推论 `pom-ent-increase-equals-kl`）、重写终止-合流（定理 `pom-rewrite-termination-confluence`）、可判定闭环（命题 `pom-projword-decidable`、`pom-rewrite-audit-loop`）、moment-kernel 编译与 Hankel 共振（定理 `pom-collision-kernel-ak`、`pom-moment-resonance`）、同步扣除 Chebotarev 容量（定理 `pom-sync-subtracted-chebotarev-capacity`）
- **拆法：**
  - 把 POM 的前半部分（定义→框架→账本→重写→共振判别→Chebotarev 容量）作为一篇自成体系的论文
  - 后半部分的细分结论（纤维 toggle-Coxeter、moment-Hankel 传播、Rényi 谱精细结构等）放到后续论文
  - 引言只讲"信息读出的结构性闭环问题"
  - 可引用论文 E（地址语义）和论文 #1（折叠）
- **为什么最高优先：**
  - POM 是整个理论的**中央计算引擎**：所有谱指纹、碰撞矩、Chebotarev 均来自 POM
  - 如果 E 是"什么是可读的"，F 就是"读到之后如何闭合审计"
- **成稿定位：**
  - 适合纯数学强刊（动力系统/遍历论/信息论交叉）

### G. 圆维与 Haar 回拉（高优先）

- **核心材料：**
  - `sections/body/circle_dimension_phase_gate/sec__circle-dimension-phase-gate.tex` 的前 5 个子节（目标→紧化→Haar 回拉→搬运与可逆性→圆维定义→精度势）
  - 核心定理：Haar 回拉唯一性（推论 `unit-circle-cayley-haar-forces-cauchy`）、Möbius 群律（命题 `unit-circle-phase-mobius-law`）、相位盒域同构（定理 `unit-circle-phase-field-iso`）、圆维算律
  - Poisson-Cauchy 核族的闭合性与半群交换律
- **拆法：**
  - 只保留核心的"Cayley 坐标门→Haar 回拉唯一性→圆维定义与算律→精度势账本"主线
  - 删除所有 S4/Prym/Hurwitz/Nielsen 分支（这些可单独出稿或留给论文 I）
  - 删除深层代数分支（solenoid 终端系统、Riemann-Siegel-Gabcke 零点递归等）
- **成稿定位：**
  - 自成体系的分析/调和分析/群论稿
  - 适合 Journal of Functional Analysis / Annales de l'Institut Fourier / 或 Advances in Mathematics

### H. 动力学 ζ 有限部与谱指纹（高优先）

- **核心材料：**
  - `zeta_finite_part/syntax/`（4 files, 836 lines）：稳定语法层 ζ
  - `zeta_finite_part/online_kernel/`（11 files, 2822 lines）：在线同步核 ζ_B
  - `zeta_finite_part/operator/`（8 files, 1446 lines）：算子口径 ζ
  - `zeta_finite_part/finite_part/`（27 files, 5149 lines）：有限部常数与扭曲等分布
- **拆法：**
  - 只用 syntax + online_kernel + operator + finite_part 四个子目录
  - **完全不包含** `xi/` 目录（889 files, 262k lines）——该目录留给论文 J
  - 主线：SFT/sofic 上的转移算子/行列式 → 周期轨道计数 → 有限部常数 → 扭曲 Chebotarev 等分布 → Peter-Weyl 非阿贝尔通道化
- **成稿定位：**
  - 标准谱论/动力系统稿
  - 适合 ETDS / Journal of the European Mathematical Society

### I. 群论统一窗与熵率时间协议（第二批）

- **核心材料：**
  - `group_unification/` 中超出论文 #5 的新增内容：
    - xi-time 协议与对象层等距因子拆解（`subsec:time-protocol-entropy-vs-rotation`）
    - Fibonacci-prime 域相窗与 CRT 分裂（`subsubsec__group-unification-fibprime-pgl2-pisano`）
    - Joukowsky-Gödel 搬运（`subsec__group-unification-joukowsky-godel-transport`）
    - Window-6 离散结论（`10_group_unification_window6_discrete_results.tex`）
    - Wulff scale ledger parity rank obstruction
    - Fibonacci-Lie 共振（`subsec__fib-lie-resonance`）
- **拆法：**
  - 以"Fibonacci 素数分辨率窗口的环论性质"为主线
  - 把 CRT 分裂模板写成严格的结构性结论
  - xi-time 协议作为独立的"熵率时间"概念稿
- **成稿定位：**
  - 适合代数/数论交叉（Journal of Algebra / Journal of Number Theory / Ramanujan Journal）

### J. ζ-completion 与 Ξ 零点审计（第二批）

- **核心材料：**
  - `zeta_finite_part/xi/` 的**核心子集**（从 889 个文件中精选）
  - CMV 谱证书的点态稳定化与唯一无限维幺正谱对象
  - Tate/Maslov 指标的反线性自对偶缺陷
  - profinite Chebotarev 的有限数据证书
- **拆法：**
  - 从 889 个文件中严格精选核心定理链（约 52 个定理、57 个终端结论中选出主链）
  - 删除所有椭圆 Lattès 过度细分的分支
  - 需要先完成论文 H（有限部基础），J 作为其续篇
- **成稿定位：**
  - 深层谱论/算子代数稿
  - 适合 Inventiones / Compositio / Advances

## 4. 投稿对照表（新一批）

| 论文方向 | 期刊 / 专题 | 截稿日 | 征文内容 / 栏目方向 | 对应拆法 | 怎么投 | 录取 | 顶刊 | 影响 | 速度 |
|---|---|---:|---|---|---|---:|---:|---:|---:|
| `E₁` | **`Annals of Pure and Applied Logic` 常规** | 滚动 | forcing + sheaf theory + gerbes + UCT，logic meets topology | 四层保守扩张 + cohomological visibility + Abramsky–Brandenburger 联系 | **E₁ 首选**；MSC 03B45/03F55/03G30/18F20 均为 APAL 核心 | 5 | 8 | 7 | 3 |
| `E₁` | `Review of Symbolic Logic` 常规 | 滚动 | 数理逻辑、哲学逻辑、形式语义 | 同上；强调 contextuality 哲学联系 | E₁ 次选 | 5 | 7 | 7 | 4 |
| `E₁` | `Notre Dame Journal of Formal Logic` 常规 | 滚动 | forcing、保守扩张、形式语义、模型论 | 同上 | E₁ 回退（若 APAL desk reject） | 6 | 7 | 7 | 5 |
| `K` | `Journal of Philosophical Logic` 常规 | 滚动 | 逻辑 + 物理基础、formal ontology | L₇–L₁₀^OST：动态更新、观察者、因果 forcing | K 首选；logic-physics 交叉 | 5 | 7 | 7 | 5 |
| `K` | `Foundations of Physics` 常规 | 滚动 | 物理基础、量子信息基础 | 同上；以 GRG 论文的时空结构为 motivating example | K 物理路线（有具体 application） | 5 | 7 | 8 | 4 |
| `K` | `Annals of Pure and Applied Logic` 常规 | 滚动 | 纯数理逻辑 | 同上；与 E₁ 形成系列 | K 强刊路线（需足够技术深度） | 4 | 8 | 7 | 3 |
| `E₂` | `ETDS` 常规投稿 | 滚动 | ergodic theory, measurable dynamics, symbolic dynamics | σ-代数不扩张 + 双预算寻址容量 + 清晰度指数律 | E₂ 的首选 | 5 | 9 | 9 | 3 |
| `E₂` | `Israel Journal of Mathematics` 常规 | 滚动 | 遍历论、动力系统、组合学 | 保留纯数学主线，加强 related work | E₂ 的稳健回退 | 6 | 7 | 7 | 5 |
| `F` | `Transactions of the AMS` 常规 | 滚动 | 纯数学全领域 | POM 核心：账本恒等式 + 重写闭环 + Hankel 共振 | F 的首选顶刊路线 | 4.5 | 9 | 9 | 4 |
| `F` | `SIADS` 常规投稿 | 滚动 | applied dynamical systems | POM 偏应用叙事：可审计信息闭环 + 可计算证书 | 若要快录取且保持影响力 | 6 | 8 | 7 | 5 |
| `F` | `Nonlinearity` 常规 | 滚动 | 非线性科学 | POM 中等长度版本 | F 的平衡回退 | 5 | 8 | 7 | 4 |
| `G` | `Journal of Functional Analysis` 常规 | 滚动 | 泛函分析、调和分析 | Haar 回拉 + 圆维 + 精度势，纯分析叙事 | G 的首选 | 5 | 8 | 7 | 4 |
| `G` | `Annales de l'Institut Fourier` 常规 | 滚动 | 分析、代数、几何交叉 | 同上 | G 的欧洲顶刊路线 | 5 | 8 | 7 | 5 |
| `G` | `Mathematics` Special Issue `New Advances in Low Dimensional Dynamical Systems` | 2026-08-31 | 低维动力系统 | G 的压缩版 | 快回退窗口 | 8 | 5 | 5 | 9 |
| `H` | `ETDS` 常规投稿 | 滚动 | ergodic theory, dynamical systems | 动力学 ζ + 有限部 + 扭曲 Chebotarev | H 的首选 | 5 | 9 | 8 | 3 |
| `H` | `Journal of the European Mathematical Society` 常规 | 滚动 | 数学各分支顶级进展 | 若谱指纹的新意足够，冲此 | 高风险高回报 | 3 | 10 | 10 | 3 |
| `H` | `Nonlinearity` 常规 | 滚动 | 非线性科学 | H 的平衡回退 | 若 ETDS desk reject | 5 | 8 | 7 | 4 |
| `I` | `Journal of Algebra` 常规 | 滚动 | 代数全领域 | Fibonacci-prime 窗口 + CRT + 域相 | I 的首选代数路线 | 6 | 7 | 6 | 5 |
| `I` | `Ramanujan Journal` 常规 | 滚动 | 数论、Ramanujan 启发方向 | Fibonacci 素数分辨率窗 + Pisano 周期 | I 的数论回退 | 7 | 6 | 5 | 6 |

## 5. 投稿顺序建议

### 路线 1：框架优先路线（推荐）

该路线的核心逻辑：**先发表定义范式的论文，再发表在该范式内的技术结果**。

1. **第一批（2026-04 至 2026-06）：E₁ + E₂ + F 三篇并行**
   - `E₁`（cohomological visibility）面向数理逻辑读者 → APAL
   - `E₂`（地址语义）面向遍历论/动力系统读者 → ETDS
   - `F`（POM 核心）面向纯数学强刊读者 → Transactions of AMS 或 SIADS
   - E₁ 和 E₂ 互相引用但各自独立；F 可引用 E₂
2. **第二批（2026-06 至 2026-08）：G + H 并行**
   - `G`（圆维）和 `H`（ζ 有限部）是两个技术上独立的模块
   - 可在 E/F 投出后立即准备
   - `G` → Journal of Functional Analysis
   - `H` → ETDS
3. **第三批（2026-08 以后）：I + J + K**
   - `I`（群论统一窗）和 `J`（ζ-completion/Ξ 零点）是更深层的细分结果
   - `K`（观察者时空逻辑）是 E₁ 的续篇，将 L₇–L₁₀ 拆为独立论文
   - I/J 应在 E/F/G/H 有初步审稿反馈后再定稿
   - K 应在 E₁ 投出且有初步反馈后再启动

### 路线 2：如果只想最快出一篇框架稿

1. 先拆 `E₂`（材料最成熟，SPG + recursive_addressing 已多轮修订，~6100 lines）
2. 直接投 `ETDS`
3. 并行准备 `E₁`（需要补充深度定理）和 `F`

### 路线 3：如果只想冲最强刊

1. 合并 `E₂` + `F` 为一篇长文（SPG + Addressing + POM 核心）
2. 投 `Advances in Mathematics` 或 `Inventiones`
3. 风险：长文被要求拆分的概率较高
4. `E₁` 仍然单独投 Notre Dame Journal of Formal Logic（读者群不同，不能合并）

## 6. 逻辑依赖链（决定发表顺序的硬约束）

```
论文 #1 (Folding, ETDS)  ←── 已发表
论文 #2 (Experiments, SIADS) ←── 已发表
论文 #3 (Zeckendorf, RAIRO-ITA) ←── 已发表
论文 #5 (Parry-Gibbs, 已发表) ←── 已发表

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
    │ I 群论统一窗（可独立，弱依赖 E/F）    │
    └──────────────────────────────────────┘
```

E₁ 是全部后续论文的逻辑基础；K 是 E₁ 的续篇（物理桥接层）；F 是 G/H/J 的必要前驱；G/H/I 之间无硬依赖。

## 7. 时间线

| 时间 | 动作 | 产出 |
|---|---|---|
| 2026-03-18 至 2026-03-23 | E₁/E₂/F/G/H 五篇骨架稿完成（LaTeX 草稿 + 定理链 + 参考文献） | 五篇骨架稿已就位 |
| 2026-03-23 至 2026-04-15 | E₁ 推进到投稿水准（APAL 口径）；E₂/F 并行打磨 | E₁ 可进入投稿 |
| 2026-04-15 至 2026-04-30 | E₂ 完成首版（ETDS 口径）；F 完成首版（Trans. AMS 口径） | E₂/F 可进入投稿 |
| 2026-05-01 至 2026-05-15 | E₁ 投出（APAL）；E₂ 投出（ETDS）；开始准备 G 和 H | E₁/E₂ 首投完成 |
| 2026-05-15 至 2026-06-15 | F 投出（Trans. AMS/SIADS）；G 补圆维代数包；H 打磨 | F 首投完成 |
| 2026-06-15 至 2026-07-31 | G 投出（JFA）；H 投出（ETDS） | G/H 首投完成 |
| 2026-08-01 至 2026-09-30 | 根据 E₁/E₂/F 审稿反馈调整 I/J；评估 K 启动时机 | 第三批定稿 |
| 2026-10 以后 | K（观察者时空逻辑）启动，依赖 E₁ 审稿结果 | K 骨架稿 |

## 8. 核心 Pitch 句子（新版）

- 已投稿 7 篇技术稿（折叠、直方图证书、Zeckendorf 算法、Fibonacci 模结构、Parry-Gibbs 刚性、S4/Prym 算术、GRG 壳几何）。
- 下一批优先发表的不是更多细分结果，而是**定义整个理论范式的框架性论文**。
- `E₁` 是语义地基稿：精确刻画"粘合障碍的哪部分是语义可见的"——UCT 可见商 vs character-blind Ext 残差（投 APAL）。
- `E₂` 是动力学地基稿：回答"有限窗口下的观测极限"——σ-代数不扩张、压力差、碰撞阈值（投 ETDS）。
- `F` 是中央引擎稿：回答"读到之后如何闭环"——信息账本、重写可判定、共振判别（投 Trans. AMS）。
- `G`/`H` 是两个独立技术模块：圆维（分析/群论）、ζ 有限部（谱论/动力系统）。
- `K` 是 E₁ 的续篇：将主论文 11 层保守扩张链的物理桥接层（L₇–L₁₀：时间、观察者、因果 forcing）拆为独立论文（待 E₁ 发表后启动）。
- `I`/`J` 是深层分支：群论统一窗、ζ-completion。
- 总稿 zeta_finite_part/xi/ 中积累了 889 个文件/262k 行的终端结论，这些内容需要按主题精选后分批发表，不宜在近端全部消化。

## 9. 为什么 zeta_finite_part/xi 仍需分批处理

- `xi/` 目录当前包含 889 个 .tex 文件、262k 行，含 52 个编号定理和 57 个终端结论
- 内容覆盖范围极广：CMV 谱证书、椭圆 Lattès 族、PRIMEGAME、Tate/Maslov 指标、Joukowsky-Gödel 搬运、nonarchimedean Hankel 刚性等
- 这些内容**不是不成熟**，而是**过于庞大且分支过多**，不适合作为单篇投稿
- 正确策略是：先用论文 H 发表 ζ 有限部的核心框架（syntax + online_kernel + operator + finite_part），再用论文 J 发表 xi 中的精选主链
- 剩余的椭圆 Lattès/PRIMEGAME 等分支可在 2026 下半年逐步以独立短稿形式消化

## 10. 旧投稿对照表（保留以供参考）

以下为 2026-03-06 版本的投稿对照表，其中 A/B/D 方向已完成发表：

| 论文方向 | 期刊 / 专题 | 状态 |
|---|---|---|
| `A` → ETDS | `2026_resolution_folding_core_symbolic_dynamics_etds` | 已发表 |
| `B` → SIADS | `2026_folded_rotation_histogram_certificates_siads` | 已发表 |
| `D` → RAIRO-ITA | `2026_zeckendorf_streaming_normalization_automata_rairo_ita` | 已发表 |
| `C. SPG` | 未独立发表 | 内容并入新方向 `E` |
| `POM / zeta` | 暂缓 | 重新规划为 `F` / `H` / `J` |

## 11. 官方链接（新增）

- `Notre Dame Journal of Formal Logic`
  `https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic`
- `Studia Logica`
  `https://link.springer.com/journal/11225`
- `Journal of Philosophical Logic`
  `https://link.springer.com/journal/10992`
- `Advances in Mathematics`
  `https://www.sciencedirect.com/journal/advances-in-mathematics`
- `Transactions of the AMS`
  `https://www.ams.org/cgi-bin/mstrack/accepted_papers/tran`
- `Journal of Functional Analysis`
  `https://www.sciencedirect.com/journal/journal-of-functional-analysis`
- `Journal of the European Mathematical Society`
  `https://ems.press/journals/jems`
- `Israel Journal of Mathematics`
  `https://link.springer.com/journal/11856`
- `Journal of Algebra`
  `https://www.sciencedirect.com/journal/journal-of-algebra`
- `Ramanujan Journal`
  `https://link.springer.com/journal/11139`
- `Inventiones Mathematicae`
  `https://link.springer.com/journal/222`
- `Compositio Mathematica`
  `https://www.lms.ac.uk/publications/compositio-mathematica/`
- `ETDS`
  `https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/information/about-this-journal`
- `SIADS`
  `https://www.siam.org/publications/siam-journals/siam-journal-on-applied-dynamical-systems/`
- `Nonlinearity`
  `https://publishingsupport.iopscience.iop.org/journals/nonlinearity/about-nonlinearity/`
- `Mathematics` Special Issue `New Advances in Low Dimensional Dynamical Systems`
  `https://www.mdpi.com/journal/mathematics/special_issues/802G384A4N`
- `Journal of Philosophical Logic`
  `https://link.springer.com/journal/10992`
- `Synthese`
  `https://link.springer.com/journal/11229`
- `Foundations of Physics`
  `https://link.springer.com/journal/10701`
