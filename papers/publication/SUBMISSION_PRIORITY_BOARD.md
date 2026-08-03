# Next-Step Plan — Submission & Deepening

纯**前向建设计划**：深化已有真结果 + 提取全新内容。核心资产是 `lean4/Omega`（9,786 文件、**zero `sorry`**）。方法：两套独立 scout（Claude 3-agent 深挖 + codex）+ 5-agent 评审。

**规划原则（铁律）：每篇都先深入挖掘，不丢不降档。** 每篇统一流程：**① 深入挖掘（补一条新定理）→ ② 机器验证（`lake build` + 数值反例）→ ③ 打磨（referee 循环）→ ④ 选刊（凭强化后的结果争对应档次，不预降档）→ ⑤ 投递。** 选刊在深化之后。运行载体 = **fkst + 本地大脑**（fkst 编排、本地 F→A→B→C→D 计算）。下表"候选刊"是深化前的方向参考，最终档次以强化后的结果为准。

> ⚠️ **关键可信度校正（codex）**：`zero sorry` 只是"能编译"，**不等于定理名所声称的数学**。库中相当一部分"paper theorem"要么把关键递推当作**假设**、要么在已含结论的结构上量化、要么结论就是 `True`。**因此每个 Lean 种子在投入前必须逐条核验:陈述是 object-level 且无条件的**（下面 B/C 的种子已标注哪些需先验无条件性）。

---

## 冲刺状态 · 停跑论文的最终目标期刊（滚动更新）

深化冲刺（ChatGPT 5.6 sol pro chat 模式多轮追问 + codex 逐条检验 + 独立复核）。**一篇论文在 Oracle 开始复述已整合内容（即新一轮全判 `ALREADY-IN-PAPER`）时判定饱和、停跑**，此表随即记录其最终目标期刊。

| 篇 | 冲刺状态 | 停跑判据 | 最终目标期刊 |
|---|---|---|---|
| **A5** `finite_parts` | ⏹ **已停跑（饱和）** | 第 2 轮 11 条声称 (A)–(K) **全部 `ALREADY-IN-PAPER`，零整合** | **PRIMARY: Dynamical Systems (T&F)**<br>BACKUP: Qualitative Theory of Dynamical Systems · Monatshefte für Mathematik<br>⚠️ **勿回投 ETDS**（已拒其前身）|
| A2 `cayley_chebyshev` | 🔄 第 2 轮进行中 | — | 待定（原评 JFA）|
| A3 `sharp_three_window` | 🔄 第 2 轮检验中 | — | 待定（原评 DCDS-A）|
| A4 `prime_languages` | 🔄 第 2 轮进行中 | — | 待定（原评 Monatshefte）|
| A6 `zeckendorf_fibers` | 🔄 第 2 轮进行中 | — | 待定（原评 JNT）|
| A7 `upper_fibers` | 🔄 第 2 轮进行中 | — | 待定（原评 Fibonacci Q.）|
| A8 `detector_shells` | 🔄 第 2 轮进行中 | — | 待定（原评 Stochastic Models）|

**A5 冲刺产出（已提交）**：精确商覆盖分裂因子、恒等类普遍 Artin 失效、指数精度调和重正规化；标量 Bernoulli 展开优先权明确归 Hasegawa–Saito（arXiv:1507.00498）；"Fourier 刚性"一组经检验仅为已有定理逆线性形式，拒绝写入。

---

## 现状定稿 · 目标期刊（2026-08，深化 + Oracle 外审后，codex 选刊评估）

6 篇核心 Track A 均已完成：**深化新定理（verifier 验证）→ 前沿门 → Oracle referee 外审 → 修订**（A2/A3/A7/A8 首轮已提交；A5/A6 二轮已提交）。目标期刊依**修订后实际内容 + 外审新颖性天花板**定稿（以本表为准，下方各表"候选刊"列为深化前参考）：

| 篇 | 目标 PRIMARY | BACKUP | 状态 / 备注 |
|---|---|---|---|
| A2 `cayley_chebyshev` | **JFA** | Bernoulli · EJP | 两项 HIGH-rated 尖锐熵阈值结果达 JFA 级；71→40–45 页待压缩 |
| A3 `sharp_three_window` | **DCDS-A** | JNT · Dynamical Systems | ⚠️ **DCDS 曾拒旧版**——重投前须确认可行或转 backup（JNT）|
| A5 `finite_parts` | **Dynamical Systems** | QTDS · DCDS | 聚焦 20 页修正 note（Frobenius 积常数修正 $F_\rho$/$L_\rho$）；逆刚性留背景 |
| A6 `finite_window_zeckendorf` | **JNT** | Adv. Appl. Math · EJC | TAMS 原过高；冻结定理 + affine 对应属 JNT 专业层级 |
| A7 `upper_fibers` | **Fibonacci Quarterly** | J. Integer Seq. · INTEGERS | 37→20–25 页 + 计算附录 |
| A8 `detector_shells` | **Stochastic Models** | MCAP · JPhysComm | 由物理框架转对口应用概率（D-MAP/更新理论）|
| A1 `tilt`（banked）| JTP（在审，不动）| — | 深化以 `_deepening_notes/tilt_interior_nongibbs/` 归档，待 JTP 结果后再定 |

**选刊原则**：凭修订后实际达到的层级对口投递——A2 凭 HIGH 结果守住 JFA；A5/A6 回落至其真实专业层级（外审判为 medium novelty），非武断降档。**投前共性动作**：多数篇需按外审压缩页数（A2/A7 尤甚）并把 certificate/comparator 材料移入 supplement。

---

# Track A — 深化已有真结果（最高 ROI，方法已在手）

对已有的 modest 结果，不原样重投，而是补一条**新定理**把它抬成强论文，深化+验证后再选刊。按"深化后成强稿的把握"排序。

> **深化阶段状态（2026-08-01，manual codex + 独立复核 + commit）**：✅ **A2/A5/A7/A3/A6/A8 已完成并提交**（每篇都独立重跑 verifier + 一手核验，非采信 codex 自报）。⏸ **A1 未应用**（深化目标已在 JTP 在审稿中，仅得一条小增量=k-态端点律，已另存 `_deepening_notes/tilt_general_sft/` 待 revision，不动 live 投稿）。下一步：这批进入 **polish（F→A→B→C→D referee）+ Lean 有限阶恒等式 + fresh-Oracle + 选刊 → 投递**。

| # | 起点论文 | 下一步要证的定理（深化） | 难度 | 候选刊（深化+验证后再定）|
|---|---|---|---|---|
| A1 ⭐ | `tilt_dynamics` | zero asymptotic variance of cylinder-information ⟺ 测度为最大熵测度（**任意 mixing SFT**，脱离黄金壳）——**是他们自己提的 open problem**，cohomology 判据 alphabet-agnostic | 可行 | ETDS / Nonlinearity |
| A2 ⭐ | `cayley_chebyshev` | **去水后**补全全阶矩-系数等价：$A_{2m}(\nu)<\infty \iff \mathbb{E}|X_c|^{2m-2}<\infty$（每阶带 converse）——把一个阈值升成熵-Laurent 矩层级 | 可行（多为重整）| JFA / Bernoulli / EJP |
| A3 | `sharp_three_window` | 阈值函数 $m^*(\beta)$ 跨 metallic/β 族分类，证黄金基是唯一达 $m^*=3$ 的极值 + 熵/zeta 不变量解释 | 可行（同方法）| ETDS / Nonlinearity |
| A4 | `prime_languages` | REG-immunity ⟹ **CF-immunity**（Ogden 升级）+ 从 Zeckendorf 推广到**所有 Pisot 数系**——base-independent"素数在任何 Pisot 数系不可识别" | 可行 | Monatshefte / TCS / RAIRO-ITA |
| A5 | `finite_parts` ζ | **inverse-rigidity 框架（codex 更优）**：刻画 cocycles-mod-gauge $\to\{\det(I-zB_\rho)\}_{\rho\in\hat G}$ 的核——给出行列式相等 ⟹ Livšic 上同调的精确图假设 + 最小反例。（现结果只重建周期数据，这才是真反问题定理）。可选再推紧群扩张 | 中–高 | ETDS / J. Modern Dynamics |
| A6 | `finite_window_zeckendorf_fibers` | 完整**大偏差原理** + 可微 rate function（Gärtner–Ellis），解析化 $q\to\infty$ 零温极限 | 中 | JNT / Monatshefte / Trans. AMS |
| A7 | `upper_fibers` | **先修 n=30 数据 bug**（8 型只实现 5 型）；再证 $\#\mathcal{M}_n$ / 平均阶的渐近（Sperner/Wigert 界）| 投机 | Fibonacci Q. / JNT |
| A8 | `detector_shells` | 深化路径最难：目标是**n-态 killed-leakage D-MAP 的可辨识性/quotient 结构定理**（把 2×2 quotient-inverse 升成一般 n 态的结构刻画）。先做可行性探查再定；最低优先，但不丢 | 高/待定 | 强化后定（应用概率刊）|

# Track B — 提取全新、未被任何论文覆盖的 Lean 验证种子（可信度最高）

这些在 `lean4/Omega` 已验证、且 grep 全部 paper body 零命中——纯新，直接可写。

| # | 种子（Lean dir/files）| 已验证主结果 | Lean | 目标刊 |
|---|---|---|---|---|
| B1 ⭐ | Fibonacci-cube / 独立集枚举 `Omega/Combinatorics`（`PathIndSet.lean`, `FibonacciCube*.lean`）| 路径图 $P_n$ 独立集数 $=F_{n+2}$（container 双射）；Fibonacci cube $\Gamma_m$ 结构。深化：独立多项式/谱、自同构群 | ✅ | Fibonacci Q. / Discrete Math. / Australas. J. Comb. |
| B2 ⭐ | Metallic-gap `Omega/Kronecker`（`MetallicGap.lean`, `W1DenominatorClosedForm.lean`）| $\kappa(A)=A/\log\lambda_A$（$\lambda_A$ 金属 Perron 根）在 $A\ge1$ **严格递增**（隐式代数族上的超越单调性）+ 有理 α 的 $W_1$ 传输精确闭式 | ✅ | Nonlinearity / ETDS / JNT |
| B3 | Resonance-window Galois 证书 `Omega/POM`, `Omega/RootUnitCharacterPressureTensor` | 两个共振窗数域 Gal$=S_{13}$（Jordan 判据，分歧素 59/62927）；显式 $S_4$；$S_4\times S_7$ 线性无关 | ✅ | Math. Comp. / LMS JCM / JNT ⚠️须对 37a1 说清区分 |
| B4 ⭐ | Lucas 幂 Hankel char-p `conclusion`（`thm:conclusion-lucas-charp-shifted-hankel-geometric-ratio` 等）| $a_n=L_n^q$、char $p>q$ 下 Hankel 秩塌缩到 $m=\mathrm{ord}(\beta/\alpha)$，平移 Hankel 几何比 | ✅ | JNT / Integers / Fibonacci Q. |
| B5 | 单次 Stokes 探针读 Minkowski 维 `spg`（`thm:spg-dyadic-outer-approx-stokes-gain-minkowski-readout`）| $|\int_{\partial U_m}\omega|\le C\,2^{-m(n-d)}\|d\omega\|_\infty$（比朴素界好一个余维）| ✗ | J. Fractal Geom. / Real Anal. Exchange / JGA |

# Track C — 把理论核的 vein 推到新定理（需真推理，部分 Lean 背书）

起点已在库中，但强定理需要投入更多本地推理。

| # | 起点（file）| 深化目标定理 | 难度 | 目标刊 |
|---|---|---|---|---|
| C1 ⭐ | rank-1 fusion defect `body/pom/parts/lem__pom-shifted-fib-fusion-defect-positive.tex`（$F_{a+2}F_{b+2}=F_{a+b+2}+F_aF_b$ + 刚性已证）| **rank-$r$ 对称 defect 分类**：$G(a)G(b)=G(a+b)+\sum_{i\le r}u_i(a)u_i(b)$ 的次指数解是否塌缩到有限 Fibonacci/Lucas 族 | 中 | JNT / Aequationes Math. |
| C2 | Cartwright 零点间隙 `appendix/fold_multiplicity/...cartwright_gaps.tex`（$\delta(R)\le\varphi^4/(4R)$ i.o.）| 闭合两侧到 **sharp constant** $\delta(R)=\frac{\varphi^4}{4R}(1+o(1))$（证 Lucas 对为极值）| 中 | J. Approx. Theory / CMFT |
| C3 | Dyadic 病态 `body/spg/thm__spg-dyadic-...ill-conditioning.tex`（只有上界 $\sigma_{\min}\le\sqrt{2n}2^{-m/2}$）| 匹配下界 → 两侧 $\kappa(\partial_n)\asymp 2^{m/2}$，再扩到非均匀 cell 几何 | 中 | SIAM J. Matrix Anal. / Numer. Math. |
| C4 | Lee–Yang double-resultant `body/group_unification/cor__group-jg-leyang-holography-double-resultant.tex` | 多元提升：环面上 Lee–Yang $P(x_1,\dots,x_k)$ 的传输可逆性 + Newton 多胞形有效恢复度 | 高 | Math. Ann. / Res. Math. Sci. |
| C5 ⭐ | **Fold-tower 算子代数（codex 新增）** `Omega/OperatorAlgebra/FoldConditionalExpectation.lean`, `FiniteCondexpVarianceDecomposition.lean`, `Omega/Folding/InverseLimit.lean`（已真证有限条件期望 + $L^2$-Pythagoras）| 证有限 **Pimsner–Popa 指数 = 最大纤维重数**；把各分辨率的期望拼成 Bratteli/AF 塔，算其有序 $K_0$ 与指数增长率——把组合纤维增长变成算子代数不变量 | 中–高 | J. Operator Theory / IEOT |

---

## 排除（纯灌水/条件包装，不投）
- `Omega/Zeta`、`Omega/Conclusion`（合计 ~5000 文件）绝大部分是**条件 RH 重述**（`*ImpliesRh*`/`*Certificate*`）——非定理。
- `Omega/OperatorAlgebra/*NPHard*`——假设"存在具目标 index gap 的 SAT 电路"，是包装非归约。
- `Omega/Frontier`（`Conjectures.lean`/`Assumptions.lean` 是假设，`Conditional.lean` 全部条件依赖）。
- `typed_address_biaxial_completion`、`fold-gauge-anomaly-*` boilerplate、pom 280 文件的大多数（Pisano/矩有限验证）。
- **库约 88–92% 是脚手架/定义/有限值证书**；真定理集中在 `Combinatorics`、`Kronecker`、`RootUnitCharacterPressureTensor`、`SyncKernelRealInput`、`EA`、`SPG` 的高信噪小目录。
- ⚠️ **两 scout 分歧待裁**：`RatioResultant` 被 Claude-scout 判 ~60% 真、被 codex 判**死胡同**（dummy splitting data、平凡子群、假设的非平凡特征）——**投入前先核验**；`Frontier` 含 `True` 占位；B2/B3 的 Kronecker/POM 种子须先确认 Lean 陈述**无条件**（codex 指出部分 parity/extremal 结果把递推当假设）。

> **codex 补充的统一视角**：A3（three-window 族）+ A6（Zeckendorf 热力学）其实是**同一个更大纲领**——"**Real Ostrowski thermodynamics beyond the golden mean**"：对每个纯周期二次无理数 $[0;\overline{a_1,\dots,a_r}]$ 建真正的有限归一化 transducer，证 $S_q(n)\sim C_{n\bmod r,q}\lambda_q^n$（$\lambda_q$ 代数）+ 解析压力 + CLT/LDP + 零温极限。把强黄金理论迁移到一整个结构分类的无限数系族。目标 **ETDS / Acta Arithmetica / TCS**。可作为 Wave 2–3 的合并大目标。另 codex 强调 A6 的真正缺口是**把极值纤维公式做成无条件**（现假设 two-step/forbidden 递推）：证 $D_m=D_{m-2}+D_{m-4}$（$m\ge6$）+ 最大化子分类 → **Adv. Appl. Math / EJC**。

## 建议执行波次

- **Wave 1（最快见效，方法在手/Lean 背书）**：A1 tilt 深化 · A2 cayley 去水补全 · B4 Lucas-Hankel 提取。
- **Wave 2**：A3 three-window 族分类 · B1 Fibonacci-cube · B2 metallic-gap · C1 rank-$r$ 分类。
- **Wave 3（高难高回报）**：A5 finite_parts 紧群扩张 · C4 Lee–Yang 多元 · A4 prime-languages 全 Pisot。
- **随手先做**：修 A7 的 n=30 数据 bug（无论是否深化）。

## 对接清单（等待人工确认）
1. Wave 1 三项（tilt 深化 / cayley 去水 / Lucas-Hankel 提取）是否批准启动？（Codex 出初版 → Claude 审）
2. A3/A5/A6 的降刊目标（ERA·AIMS Math·CMP·JNT）是否认可？
3. B3 resonance-Galois 与已投 37a1 的区分度，是否需要先做一次撞车核查再动手？
4. A8 detector_shells：确认降为 note 或直接弃？
