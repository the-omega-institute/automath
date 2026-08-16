# Next-Step Plan — Submission & Deepening

纯**前向建设计划**：深化已有真结果 + 提取全新内容。核心资产是 `lean4/Omega`（9,786 文件、**zero `sorry`**）。方法：两套独立 scout（Claude 3-agent 深挖 + codex）+ 5-agent 评审。

**规划原则（铁律）：每篇都先深入挖掘，不丢不降档。** 每篇统一流程：**① 深入挖掘（补一条新定理）→ ② 机器验证（`lake build` + 数值反例）→ ③ 打磨（referee 循环）→ ④ 选刊（凭强化后的结果争对应档次，不预降档）→ ⑤ 投递。** 选刊在深化之后。运行载体 = **fkst + 本地大脑**（fkst 编排、本地 F→A→B→C→D 计算）。下表"候选刊"是深化前的方向参考，最终档次以强化后的结果为准。

> ⚠️ **关键可信度校正（codex）**：`zero sorry` 只是"能编译"，**不等于定理名所声称的数学**。库中相当一部分"paper theorem"要么把关键递推当作**假设**、要么在已含结论的结构上量化、要么结论就是 `True`。**因此每个 Lean 种子在投入前必须逐条核验:陈述是 object-level 且无条件的**（下面 B/C 的种子已标注哪些需先验无条件性）。

---

## 冲刺状态 · 停跑论文的最终目标期刊（滚动更新）

深化冲刺（ChatGPT 5.6 sol pro chat 模式多轮追问 + codex 逐条检验 + 独立复核）。**一篇论文在 Oracle 开始复述已整合内容（即新一轮全判 `ALREADY-IN-PAPER`）时判定饱和、停跑**，此表随即记录其最终目标期刊。

### 冲刺后目标期刊（codex 依"实际通过验证并入稿"的内容重评，2026-08）

| 篇 | 页 | 最新裁决 | **去向** |
|---|--:|---|---|
| **A2** `cayley_chebyshev` | **87+33** | ✅ 签字项完成;**查出 1 条伪造 + 3 条错配引用并修** | **JFA** |
| **A3** `sharp_three_window` | **67+15** | ⚠️ **估值裁决:拆。A 篇 20–24 页 ETDS 74%** | **待作者定夺:拆(A→ETDS)**|
| **A4** `prime_languages` | **37+43** | ✅ 定位 + 有效基数界(0.94)均已入库 | **Monatshefte**(档位不变)|
| **A5** `finite_parts` | 43+19 | ✅ 已按三层重新配重;文献 81/84 已核 | ETDS(理由落在动力学定理)|
| **A6** `zeckendorf_fibers` | **73+20** | ⚠️ **估值裁决:拆。A 篇 30–34 页 TAMS 55–65%** | **待作者定夺:拆(A→TAMS, B→JNT)**|
| **A7** `upper_fibers` | **36+36** | ✅ 定理入库;**查出第二条伪造引用并删** | **Fibonacci Quarterly**(档位不变)|
| **A8** `detector_shells` | **72+19** | ⚠️ **估值裁决:重构。EJS 24%→51%** | **待作者定夺:重构后投 EJS**|
| **A9** `homological_visibility` | 38+6 | ⛔ 天花板;**6 条引用指向他人论文,已修** | Cahiers |






**八篇外审全部走完、全部修复入库、投稿包七项齐备。A2 是唯一从拒稿走到 tier-2 的一篇。**


**八篇外审全部走完并修复入库;A2 是唯一拿到"不因数学正确性拒稿"的一篇。**


**八篇全部完成外审并修复入库。**


**七篇外审全部走完;六篇已修复入库,余 A7、A9 在改。**


**七篇全部走完外审。六篇存在优先权遗漏，三篇因补充材料未随投而被扣分。**
















> **TICK 163 — 空转。** 池 0/6、无 agent、无 stdin 孤儿、无未提交论文改动、内存 0.97 GB、缺页 0。六项待作者事项无变化,见 tick 117 条目。





































































































































































> **Oracle 协议已变更(2026-08-14 实测)**：worker 升级到 `cdp-2.5-chat-work-media-gate` 后加了 `submission-gate` 前置校验。**新会话必须在 `--tag` 里显式写 `mode:chat` 或 `mode:work`**（v1 通过 tag 传模式，`--mode` 参数不再被接受）；**续接会话必须省略模式控制与附件**，原 worker/账号与控制项自动保留；首轮只能带 `--pdf` 或 `--attach-file` 其一。不合规的任务会一直排队且**永不派发**——症状是 worker 全空闲、Queued 不降。


**目标期刊在整轮冲刺后没有变化。** 深化显著增厚了内容（见下），但没有哪一篇因此跨过档次线；PRIMARY 维持上表。

### A9 `homological_visibility` — 新入列（APAL 拒稿后重建）

**拒稿性质要看清:不是内容被否,是没人读到内容。** `APAL-D-26-00107`,主编 Benno van den Berg 原话:"does not meet the standard requirements for a mathematical paper **in terms of style**"、"uses terminology **in a way that is not standard and is not explained**"、因此 "an evaluation of its content **is not possible** in its current state"。**没有审稿人评判过这篇的数学。**

**这意味着换刊无效** —— 同样的问题在任何期刊都会得到同样的 desk rejection。APAL 本就是最对口的去处(van den Berg 是范畴论/构造性数学专家),他给的是可修复的诊断。

**结构性成因(已量化)**:93 页、52 个定义、81 条定理/命题,核心词汇几乎全自造且与标准术语冲突:

| 词 | 次数 | 冲突 |
|---|--:|---|
| `visible` / `visibility` | 223 | 无标准含义,须自定义 |
| `realization` | 198 | **模型论中已有标准含义**(realizing a type),此处另作他用 |
| `slice` | 133 | **范畴论 slice category** 是标准术语 |
| `admitted reference` | 42 | 完全自造 |
| `bouquet` | 19 | 拓扑中指楔和 |

专家读到 `realization` 会自动套用模型论含义,越读越不对,最后判定无法评估。

**内容初判(待独立评估确认)**:摘要里能辨认出的是硬对象 —— 层化单位在终纤维上的满射性配合 $H^1$ 消没、带 band 的实现叠扩张给出落在 $H^2$ 的 **Giraud 类**、character-blind 情形恰为纯 $\operatorname{Ext}$ 贡献、以及一条**不可定义性分离定理**。最漂亮的是结尾那条充要刻画:**bouquet 好覆盖上,非零有限交换群 $G$ 出现为纯双分支消解核,当且仅当 $d(G)\le2eta$ 且 $G$ 不是循环 $p$-群**。这条被埋在 93 页末尾,**它应该是标题和引言第一句**。

**执行顺序(不可颠倒)**:① 独立评估定档(进行中)→ ② 术语审计 + 改名 + 术语对照表 → ③ 压缩至 35–45 页(用 A2/A4/A7 已验证的补充材料方案)→ ④ 引言用标准语言前置主定理 → ⑤ 再选刊。**先选刊没有意义。**

**候选去向**:重写后仍投 **APAL**(说明已按编辑意见重构),或 **JSL** / **Logic and Analysis** / **Theory and Applications of Categories**(TAC 对层论/gerbe 方向对口且开放获取)。

⚠️ **不可投 Nuclear Physics** —— Elsevier 只有 Nuclear Physics A/B,**无 D 刊**;且本文属层论与范畴逻辑,与核物理/高能物理无交集,投过去会当天 desk reject。

### 是否还有继续冲刺的必要与可能（2026-08-08 评估）

> ⚠️ **已失效(2026-08-16)**:本节的逐篇"继续/换向后再评"判断作于第三代提问之前。此后八篇均已产出领域对象定理、完成档位重估与结构估值。当前状态以顶部状态表为准。

判据用"最后一轮是否仍产出可整合的新内容"，而非轮数。

| 篇 | 已收轮 | 最后一轮 | 判断 |
|---|:--:|---|---|
| **A6** | 6 | r7 严格速度分离（区间证书）| **继续**——连续三轮 r5/r6/r7 均有实质产出，边际最高 |
| **A5** | 5 | r5 有效有理 Mahler 判定程序 | **继续**——r4 闭合 Nishioka 卡点、r5 升级为判定程序，方向明确 |
| **A8** | 6 | r7 尖锐交换点耦合边界 | **继续**——仍在产出，但拒收比例升高（minimax、尾格统计量、临界常数 $4e^c$ 均被驳回）|
| **A2** | 4 | r5 原始尾 Poisson 能量分解 | **继续**——但近两轮以"撤回/否定"为主，接近拐点 |
| **A3** | 2 | r3 无统一因果长度上界 | **继续**——探索最少的一篇，尚未触及边界 |
| **A7** | 4 | r4/r5 连续两轮诚实拒答 | **换向后再评**——原问题被 GRH、一致性范围、缺局部化三重阻断；r6 已改问本文有限结构可无条件处理的问题，一轮即可判定是否值得续跑 |
| **A4** | 3 | r4 诚实拒答（359 字节）| **换向后再评**——可判定性/$\Sigma^0_1$-困难性在给定有限输入模型下证不出；r5 已改问承诺问题的精确递归论分类 |

**结论**：没有一篇触发饱和（新一轮全判 `ALREADY-IN-PAPER`），所以**技术上都可以继续**；但边际价值已分层——A6/A5 最高，A3 最未开发，A7/A4 需先看换向后的一轮再决定。

**真正的瓶颈已不是深度，而是投稿就绪度**：A3 57 页、A8 55 页仍略超目标刊；A6 的 `sec_local_spectrum.tex` 1504 行超出 800 行规范且压缩尝试已回退（原因见下）。若要投递，这些比再加一条定理更关键。

**可能性上的现实约束**：Oracle 链路依赖 Cloudflare WARP 隧道，该服务停止后 `nyx-api.chrono-ai.fun` 完全不可达（WSL 内 github 可达、该主机返回 000），且启动服务需管理员提权。链路恢复前无法进行任何一轮。

### 冲刺产出（均经 codex 逐条检验 + 我方独立复跑 verifier 与编译后提交）

- **A5** `thm:determinant-boundary-lifting` 闭合了长期卡住的边界碰撞问题——绕开取不到的 Nishioka 1985，改用 1982 特殊值定理并显式核验全部参数（$p{=}2,N{=}0,n{=}1,m{=}2,M{=}2,U{=}1,L{=}1$，$M(p{+}N)n^2=4<2^{2+1/L}=8$），配合 Dieudonné–Dwork 整性给出 $F\in\mathbb Z[[z]]$；r5 再把存在性升级为**判定程序**（`thm:effective-rational-mahler-coboundary`：显式次数/高度界 + 有限 Padé 判定）。承重的平方归一化 $F(x)^2=\Pi_x(H)$ 已明写；不主张任意正有理 $H$ 的逆命题。
- **A6** r7 证得**严格速度分离** $v_2>v_c$，间隙 $\ge 0.001171960512764161$。截断证不了它（$\gamma_2$ 级数从下方慢收敛，部分和给的是 $v_2$ 的上界，方向相反），故改用区间证书 `verify_speed_separation.py`：$\gamma_{\text{upper}}=4435863088103/847288609443$、$v_2^{\text{lower}}=0.132397168$、$v_c^{\text{upper}}=0.131225208$。r6 另证**统一命题不成立**，并把 dyadic 词计数明确归为 Weinstein 已发表公式的系数推论。
- **A8** r7 整合固定交换点的**尖锐充要边界** `prop:helmert-growing-layer-bracket-main`；r4 补 Markov–Palm 交换点全切空间。
- **A2** r5 整合 `thm:raw-tail-poisson-energy-decomposition`（原始尾 Poisson 能量分解）。
- **A3** r3 证得三次 simple-Parry Pisot 数上 $\ell_{\mathrm{cau}}$ **无统一有限上界**，并收紧了 simple-Parry 系列结论的适用范围。

### 篇幅压缩（2026-08，本地执行，均经清理重建核验）

顶刊对篇幅有硬约束，故在 Oracle 链路中断期间就地压缩。**做法**：只迁移不删改，迁出的章节由独立编译的补充材料承载，正文留精确指针。

| 篇 | 原 | 现 | 补充材料 | 目标刊 |
|---|--:|--:|--:|---|
| A2 `cayley_chebyshev` | 90 | **55** | 31 | JFA ✓ |
| A4 `prime_languages` | 63 | **38** | 29 | Monatshefte ✓ |
| A7 `upper_fibers` | 50 | **25** | 27 | Fibonacci Quarterly ✓ |
| A6 `zeckendorf_fibers` | 62 | 62（已回退）| — | JNT |

**验收标准（三篇均通过）**：定理类环境总数不变；迁出章节的每个定理标签在 `supplement.pdf` 中解析；两文档**清空全部 `.aux` 后从零重建**，exit 0 且未定义引用/文献/重复标签/错误全为 0；verifier 与测试原样通过。A7 另外把 3805 行的单体 `main.tex` 拆到最大 544 行。

**教训（下次务必前置）**：
1. **增量编译会靠陈旧 `.aux` 报假成功** —— A2 曾自报"零未定义"，清理重建实测 60 处未定义引用、25 处未定义文献。只有 `latexmk -C` + `rm -f *.aux` 的完整序列算数。
2. **补充材料必须是能编译的真文档**，不能只是一串 `\input`；否则迁出的定理"源码里有、任何 PDF 里都没有"，正文指针悬空，而"零未定义引用"这项检查**发现不了**（指针是 `\path{}` 字面量）。
3. **补充材料只能包含正文不再 input 的章节** —— 重复 input 会把文章重排一遍。
4. **A6 回退原因**：正文与补充材料相互交叉引用，xr-hyper 需要往复多遍才收敛，单向"先正文后补充"的构建序列无法达到零未定义引用。若要重做，须先切断双向依赖（把被补充材料引用的结果留在正文，或改为文字指针）。

### 被拒绝写入的内容（同等重要）

深化的价值有一半来自拒收。已记录在案的有：A6 r4 的 **17 条 WRONG**；A8 的 minimax 主张（切线论证无效）、尾格统计量、临界常数 $4e^c$（精度不成立，反例已存）；A2 的跨壳层聚合主张（验伪）与"同一 Poisson 单元内不可抵消"断言（**整条撤回**，替代文字仅作经典背景、不申报新颖性）；A7 的 fibotomic 熵最优性主张（**正式撤回**，稿件确无该证明）并纠正 Granville 引用被误表述为 Fibonacci 奇重数定理；A5 的标量 Bernoulli 展开优先权归 Hasegawa–Saito（arXiv:1507.00498）。

**Oracle 两次诚实拒答**：A4 r4 在给定有限输入模型下无法建立几何同步方案的可判定性或 $\Sigma^0_1$-困难性，未向稿件加入任何定理；A7 r4/r5 连续两轮判 little-o 命题未决，障碍精确定位为 Sanna 的无条件定理只控制 $d\mid\alpha(p)$ 而非纤维 $\alpha(p)=d$、固定指标渐近式依赖 GRH 且仅在 $x>t^3$ 上一致（而 $\alpha(p)=d$ 迫使 $p=td\pm1$），r6 起已正式换向到本文有限结构理论可无条件处理的问题。

---

## 现状定稿 · 目标期刊（2026-08，深化 + Oracle 外审后，codex 选刊评估）

> ⚠️ **已被取代(2026-08-16)**:本节的目标刊定稿作于本轮重估之前。A2→JFA、A3→ETDS(若拆)、A4→Monatshefte、A5→ETDS、A6→TAMS/JNT(若拆)、A7→FQ、A8→EJS(若重构)、A9→Cahiers,均以顶部状态表为准。

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

> ⚠️ **已失效(2026-08-16)**:Wave 1–3 计划所列工作已完成或被后续路线取代。

- **Wave 1（最快见效，方法在手/Lean 背书）**：A1 tilt 深化 · A2 cayley 去水补全 · B4 Lucas-Hankel 提取。
- **Wave 2**：A3 three-window 族分类 · B1 Fibonacci-cube · B2 metallic-gap · C1 rank-$r$ 分类。
- **Wave 3（高难高回报）**：A5 finite_parts 紧群扩张 · C4 Lee–Yang 多元 · A4 prime-languages 全 Pisot。
- **随手先做**：修 A7 的 n=30 数据 bug（无论是否深化）。

## 对接清单（等待人工确认）

> ⚠️ **本清单已失效,请勿据此行动(2026-08-16)**。其中的降刊/弃稿建议已被推翻:A8 现有 Le Cam 局部等价定理、重构后 EJS 51%(非降为 note);A3/A5/A6 的降刊目标亦不再适用。**当前真正待确认的五项**:(1) A6 是否拆分(A 篇 TAMS 55–65% vs 合稿 35–45%);(2) A8 是否重构投 EJS(51% vs 现状最佳 39%);(3) A3 是否拆分(A 篇 ETDS 74% vs 合稿 58%);(4) 531 个已验证提交是否推送;(5) `tools/chatgpt-oracle/` 15 处 08-03 未提交改动的去留。
1. Wave 1 三项（tilt 深化 / cayley 去水 / Lucas-Hankel 提取）是否批准启动？（Codex 出初版 → Claude 审）
2. A3/A5/A6 的降刊目标（ERA·AIMS Math·CMP·JNT）是否认可？
3. B3 resonance-Galois 与已投 37a1 的区分度，是否需要先做一次撞车核查再动手？
4. A8 detector_shells：确认降为 note 或直接弃？
