# Open-Problem Research Board

**Purpose:** 跨来源已筛选的开放数学问题候选池, 用于 community-outreach 管线 (solve + broadcast + paper backflow). 每条 TODO 自包含, 设计为可由独立 worktree 中的 agent 并行深度推理。

**Strategy:** 优先无人触及 (untouched by other AI tools / no recent paper) + Omega 库强项 fit + 高话题度的子集. 不收硬碰不下来的 (Erdős #142 / #3 / 解析 NT)。

**Pipeline contract:**
- 每条 TODO 进入 worktree 后, 工作流: research.md 起草 → Codex+Claude 双审 → 解决 / 部分进展 / 报告卡点 → 用户审 → 提交 (issue comment / PR / forum post) → backflow paper appendix → X 宣发 (条件: 被外部接受)
- 当前 RESEARCH_BOARD 内容由 outreach-clean 分支 2026-04-29 离线调研产出 (未推送到外部任何仓库)
- 状态轨道: `Backlog` → `In Research` → `Draft Ready` → `Pending User Approval` → `Submitted`

**Hard rules (从 CLAUDE.md / memory 继承):**
- 任何对外提交前必须用户看过最终文本并明确同意
- 不发到 dev 分支, 走 outreach-clean
- 中文回流, 英文对外
- Lean 验证由 lean4-formalize 管线辅助, 不是 outreach 的产出本身

---

## Backlog (按优先级排序)

### T-01 · Erdős #475 · Graham/Alspach valid orderings (DECIDABLE)

| field | value |
|---|---|
| Status | **Stage A done · literature overtaken · narrow Stage C only** |
| Source | https://www.erdosproblems.com/475 |
| Type | DECIDABLE / additive combinatorics in $\mathbb{F}_p$ |
| Untouched | ⚠️ 不在 erdosproblems AI wiki, 但 2024-2026 三篇新论文已基本关闭"足够大素数"区间 |
| Omega fit | 9/10 (math) → **5/10 (formalization-only after Stage A)** |
| Topic value | 7/10 → **4/10 (no new research, only finite certificate)** |
| Effort est | 10-15 天 (broad) → 3-5 天 (narrow Stage C: emit certificates + verifier) |
| Risk | low-med |
| Stage A by | Codex 2026-04-30, score 6/10 |
| Lit staleness checked | 2026-04-30 — **OVERTAKEN** |

**Statement.** 设 $p$ 素数. 给定有限 $A \subseteq \mathbb{F}_p \setminus \{0\}$, 是否总存在 $A = \{a_1, \dots, a_t\}$ 的排列, 使所有部分和 $\sum_{1\le k \le m} a_k$ 在 $1\le m\le t$ 上互异?

**Prior (updated 2026-04-30 from Codex Stage A).**
- Graham: $t=p-1$ 时成立
- Costa-Pellegrini 2020: $t\le 12$ ([arxiv:2003.05939](https://arxiv.org/abs/2003.05939))
- Hicks-Ollis-Schmitt 2019: $p-3\le t\le p-1$
- Kravitz 2024 ([arxiv:2407.01835](https://arxiv.org/abs/2407.01835)): $t\le\frac{\log p}{\log\log p}$
- **Bedert-Kravitz 2024-25 ([arxiv:2409.07403](https://arxiv.org/abs/2409.07403))**: Graham conjecture beyond rectification barrier
- **Pham-Sauermann 2026 ([arxiv:2602.15797](https://arxiv.org/abs/2602.15797))**: Graham conjecture for sufficiently large primes
- **Costa-Della Fiore-Fontana-Vena 2026 ([arxiv:2603.20961](https://arxiv.org/abs/2603.20961))**: small-set sequenceability in abelian groups
- erdosproblems.com #475 page (2026-03-05 edit): "proved for all sufficiently large primes" — **the original middle-range gap that motivated this TODO is closed**

**Omega fit detail (path corrected 2026-04-30).** `lean4/Omega/FiniteFieldEquationalSaturation/*` (board originally cited `EquationalTheory/` which **does not exist**) + ZMod 加性结构 + `Folding/Window6.lean` / `Folding/FiberRing.lean` / CRT 装备. `FiberRing.lean` 提供 `X m ≃+* ZMod (Nat.fib (m + 2))` 同构, 素数 Fibonacci 情形升为域.

**Attack plan.**
1. 写 `tools/community-outreach/erdos/p475_valid_ordering.py`: 对小 $p$ ($\le 23$) 与中 $A$ 大小 (15-25), brute-force 验 (或反证) 在已发表区间外的猜想. 输出哪些 $(p, t)$ 被验证, 哪些 stay open.
2. 寻找结构性引理: 是否存在 $(p, t)$ 类型 (e.g. $A$ 含某 quadratic residue 子结构) 总有 valid ordering. 用 Codex 与 Claude 双轨推理.
3. 部分推进 = 论坛 post + erdosproblems.com PR 升级 status 字段 + 数据表回流 paper 附录 `theory/.../sections/appendix/erdos_475_*`.

**Worktree-ready inputs.** `lean4/Omega/FiniteFieldEquationalSaturation/`, `lean4/Omega/Folding/Window6.lean`, `lean4/Omega/Folding/FiberRing.lean` (静态读取, 不编辑).

**Deliverables.**
- ✅ `tools/community-outreach/targets/erdos_475/research.md` (Codex 2026-04-30, Stage A 6/10)
- ✅ `tools/community-outreach/targets/erdos_475/p475_valid_ordering.py` (1.1M 子集 → 50,642 轨道全 verified, $p\le 23$)
- 待: `--emit-certificates` 模式 + 独立 verifier 脚本
- 待: 论坛 post draft (formalization-only, 不再是新 research)
- 待: paper appendix (finite certificate 表)

**Stage A 总结 (Codex 2026-04-30).** $p\le 23$ 中段所有 size 全验证 (1,110,540 子集 → 50,642 multiplicative orbit reps); $p=29$ random sampling exploratory only. **Codex 自评 6/10, 推荐: 不要进 broad Stage C, 仅做窄路 finite-certificate / Lean formalization**. 鉴于 Pham-Sauermann 2026 已基本关闭"足够大素数",本 TODO 的研究上限已被外部占住, 剩余价值仅在 INTEGERS 短文 + erdosproblems wiki secondary formalization 条目.

---

### T-02 · Erdős #199 · Minimum Overlap (AI frontier gap)

| field | value |
|---|---|
| Status | **🔴 CLOSED · disproved (Lean) 2026-02-24 · drop or handoff lean4-formalize** |
| Source | https://www.erdosproblems.com/199 + Tao 2025-11 blog + AlphaEvolve PDF + TTT-Discover ([arxiv:2601.16175](https://arxiv.org/abs/2601.16175)) |
| Type | DISPROVED (Lean) — 不再是 open conjecture |
| Untouched | ❌ erdosproblems registry 2026-02-24 把 #199 标 `disproved (Lean)`, 即 Erdős 原 conjecture 在 Lean 里被反证 |
| Omega fit | 7/10 (math) → n/a (问题已闭) |
| Topic value | 9/10 → **2/10 (重复别人 2 个月前的 Lean 反证, 无 outreach 价值)** |
| Effort est | n/a |
| Risk | n/a |
| Lit staleness checked | 2026-04-30 — **CLOSED, registry 状态 `disproved (Lean)`** |

**Statement.** $A \sqcup B = \{1,\dots,2n\}$, $|A|=|B|=n$. 设 $M_k = |\{(a,b)\in A\times B: a-b=k\}|$, $M(n) = \min_{A,B}\max_k M_k$. 求 $\lim_{n\to\infty} M(n)/n$ 存在性 + 精确值.

**Prior (updated 2026-04-30).**
- White 2022: 下界 $0.379005$ (Fourier+凸优化, [arxiv:2201.05704](https://arxiv.org/abs/2201.05704))
- Haugland 2016: 上界 $0.380927$
- AlphaEvolve 2025: 上界 $0.380924$ (95 段 step function)
- Together AI 2025: 上界 $0.380871$
- **TTT-Discover 2026-01 ([arxiv:2601.16175](https://arxiv.org/abs/2601.16175)): 上界 $0.380876$, 600 段 ASYMMETRIC step function — 当前 SOTA**
- Gap $0.379005 \le \inf \le 0.380876$ 仍未闭, lower bound 自 2022 无进展

**Codex Stage B 数值发现 (2026-04-29).** Omega `SyncKernelWeighted/AdditionCollisionHoelderLowerBound` 在 minimum overlap 上的 collision-Hölder 路线给的渐近下界为 trivial $1/4$, 不能直接打到 $0.379$. 真攻 lower bound 需要 White 风格的 Fourier/convex dual certificate, **不是** 我们现有 collision-Hölder。

**Omega fit detail (refined 2026-04-30 from Codex).** $\mathbb{Z}/2n\mathbb{Z}$ 上指示符卷积极值. `SyncKernelWeighted/AdditionCollisionHoelderLowerBound` 是 ZMod collision-Hölder 框架但**仅给 1/4 渐近**. `GMajorArcRigidityAffineAutocorr` 是 affine autocorrelation rigidity, 离散→连续 step function 极值需要 Fourier 二阶矩 + dual certificate (Omega 暂无). 有限 exact search 在 $n\le 12$ 已验证, 拟合 White 路线则仍要新工具.

**Attack plan (refined 2026-04-30).**
1. 弃用 collision-Hölder 路线 (Codex 实测 trivial $1/4$, 无法逼近 White 下界).
2. 改建 White-style Fourier/convex dual certificate verifier — 这是 Omega 现在没有的工具.
3. 同时建独立 step-function upper-bound verifier, 把 TTT-Discover 的 600 段 asymmetric construction 当 reference.
4. 论文化路径: 即便不打过 SOTA, "我们形式化验证了 TTT-Discover 的 0.380876" 是 secondary contribution.

**Worktree-ready inputs.** `lean4/Omega/SyncKernelWeighted/AdditionCollisionHoelderLowerBound.lean`, `lean4/Omega/SyncKernelWeighted/GMajorArcRigidityAffineAutocorr.lean` (静态读取, 不编辑).

**Deliverables.** 同 T-01 模板 + 可能的 arXiv preprint.

---

### T-03 · Erdős #1026 · Monotone subsequence single-cell extension

| field | value |
|---|---|
| Status | **🔴 CLOSED · solved (Lean) · drop** |
| Source | Tao 2025-12-08 blog (https://terrytao.wordpress.com/2025/12/08/the-story-of-erdos-problem-126/) |
| Type | SOLVED (Lean) — Tao 12 月 blog 之后已被解 |
| Untouched | ❌ erdosproblems registry 把 #1026 标 `solved (Lean)`. Tao 那篇 blog 描述的是过程, 现在已经收尾 |
| Omega fit | n/a |
| Topic value | n/a — 重复已解题, 无 outreach 价值 |
| Effort est | n/a |
| Risk | n/a |
| Lit staleness checked | 2026-04-30 — **CLOSED, registry 状态 `solved (Lean)`** |

**Statement.** $c(n) = \inf_{x_1,\dots,x_n}\max_S \frac{\sum_{i\in S}x_i}{\sum_i x_i}$, $S$ 跑遍 monotone subsequences. 已证 $c(k^2+2a+1)=k/(k^2+a)$ for $-k\le a\le k$. **目标: 把 $|a|=k$ 边界外推一格 (e.g. $n=k^2+2k+2$)**.

**Prior.** Tao + 合作者 12 月 blog 给出 $|a|\le k$ 区段 closed form via Praton 嵌入. Aristotle 证 $c(k^2)=1/k$.

**Omega fit detail.** `Combinatorics/PathIndSet.lean`, `Combinatorics/FibonacciCubeGraph.lean`, `Folding/GaugeAnomalyTauIntClosed.lean` 处理离散单调链/路径独立集; `StableArithmetic/*` 提供 closed form 工具.

**Attack plan.**
1. 把 $c(n)$ 重写为 $n$-元 partition 的离散 LP 极值.
2. 在 Omega 里复现 Praton 嵌入 + 矩形 packing 论证, 推一格 $n=k^2+2k+2$.
3. 即便只补一格, "Tao 12 月 open 题被推一格" 是 clean 故事.

**Deliverables.** `targets/erdos_1026/research.md` + Tao blog 评论 draft + erdosproblems #1026 forum post + paper appendix.

---

### T-04 · Erdős #1191 · Sidon set $b\le 1.952$ ansatz extremality

| field | value |
|---|---|
| Status | Backlog |
| Source | Tao 2025-11 blog + AlphaEvolve PDF §3 |
| Type | OPEN / additive combinatorics extremal |
| Untouched | ✅ AE 给 ansatz 数值 1.952659, ImprovEvolve 1.95264, 没人证 ansatz 是充分的 |
| Omega fit | 9/10 |
| Topic value | 8/10 |
| Effort est | 18-21 天 |
| Risk | med |

**Statement.** Sidon 集 $S\subseteq[1,n]$ 直径 $n$ 的最大基数 $|S|\le n^{1/2}+cn^{1/4}+O(1)$. 求 $b = \limsup c$. 已知 $b\le 1.95264$ (AE).

**Prior.** Cilleruelo-Ruzsa 等给旧 1.96365. AE 改进到 1.952659 通过 piecewise-affine ansatz 优化. ImprovEvolve 1.95264.

**Omega fit detail.** `Combinatorics/GramDet`, `ChebyshevDworkCongruenceChain`, `Disc2Prim8SharedRamified37` 是 ZMod 加性结构. `SyncKernelWeighted/AdditionCollision*` 系列正是 Sidon 类下界证明的核心引理.

**Attack plan.**
1. Omega 内形式化 piecewise-affine ansatz 极值结构.
2. 证 $b$ 在该 ansatz 类中确为 $1.95264$ (ansatz extremality).
3. 证 ansatz 类外的下界改进至少需要某种 Fourier 二阶矩.
4. 即便不超过 AE 数值, "AE 数值是某 closed class 内极值" 已是结构性 contribution.

**Deliverables.** 同模板 + 可能的 arXiv preprint.

---

### T-05 · Erdős #7 · Odd distinct covering systems

| field | value |
|---|---|
| Status | Backlog |
| Source | https://www.erdosproblems.com/7 + OPG http://www.openproblemgarden.org/op/odd_incongruent_covering_systems |
| Type | OPEN / verifiable / falsifiable |
| Untouched | ✅ 不在 AI wiki, BBMST22 后 2024-2025 arxiv 仅零星进展 |
| Omega fit | 8/10 |
| Topic value | 9/10 (Erdős-Selfridge 60 年悬案, $25 prize) |
| Effort est | 7-10 天 (最差进度产出 entropy 改进) |
| Risk | med |

**Statement.** 是否存在 distinct covering system $\{(a_i\bmod m_i)\}_{i=1}^k$ 满足所有 $m_i$ 奇数 $>1$, $m_i$ 两两不同, $\bigcup\{n: n\equiv a_i\pmod{m_i}\}=\mathbb{Z}$?

**Prior.** Hough-Nielsen 2019: 最小模必含 2 或 3. BBMST22: lcm 必 $\mid 9$ 或 $15$, squarefree 时 lcm 至少 22 素因子. arxiv:2507.16135, 2508.18062 (2025) 偶尔小推进.

**Omega fit detail.** ZMod + CRT + idempotent + fiber ring (`Folding/FiberRing.lean`) + `Walsh balance` 为 entropy potential.

**Attack plan.**
1. 写 `coverage_density.py` 实现 Hough entropy potential, 复现 BBMST22 lcm 下界.
2. 在 squarefree 假设下 sweep lcm 至 22-prime 下界以下, SAT-solver 切.
3. 失败时 fallback: "改进 entropy potential 在某区间下界" 一篇 INTEGERS.

**Deliverables.** 同模板 + 论坛 post (Erdős #7).

---

### T-06 · Erdős #699 · Binomial coefficient gcd counterexample search

| field | value |
|---|---|
| Status | Backlog |
| Source | https://www.erdosproblems.com/699 |
| Type | FALSIFIABLE / number theory |
| Untouched | ✅ 不在 AI wiki |
| Omega fit | 7/10 |
| Topic value | 5/10 |
| Effort est | 5-7 天 |
| Risk | low |

**Statement.** $\forall 1\le i<j\le n/2$, 是否存在素数 $p\ge i$ 使 $p\mid \gcd\binom{n}{i},\binom{n}{j}$? 已知 $i\ge 4$ 仅一个反例 $\gcd\binom{28}{5},\binom{28}{14}=2^3\cdot 3^3\cdot 5$.

**Omega fit detail.** 二项系数 + 素数整除 = 我们 prime/factor 机器原生覆盖.

**Attack plan.**
1. Sweep $i\ge 4, n\le 200$, 寻新反例.
2. 找到 = 直接 falsify (头条).
3. 没找到 = "verified to $n\le 200$" 仍可 partial-claim.

**Deliverables.** 同模板.

---

### T-07 · OPG · Pierce expansion polylog upper bound

| field | value |
|---|---|
| Status | Backlog |
| Source | http://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions |
| Type | OPEN / decidable |
| Untouched | ✅ 2024-2025 arxiv 没人攻 polylog; 最新 arxiv:2405.02174 (2025) 做 Hausdorff 维数侧 |
| Omega fit | 9/10 |
| Topic value | 7/10 |
| Effort est | 7-10 天 |
| Risk | low |

**Statement.** $a>b>0$ 整数, $b_1=b$, $b_{i+1}=a\bmod b_i$. 终止 $b_{n+1}=0$, 设 $P(a,b)=n$. 证或反 $P(a,b)=O((\log a)^2)$.

**Prior.** Erdős-Shallit 1991: $P=O(a^{1/3+\epsilon})$. arxiv:2211.08374 (2022): $O(a^{1/3-2/177+\epsilon})$. 从 $a^{1/3}$ 到 $(\log a)^2$ 巨大 gap.

**Omega fit detail.** $\mathbb{Z}/a\mathbb{Z}$ 上数值动力轨道长度 = `halting frontier / prime-slice / S₂ counts` 装备核心.

**Attack plan.**
1. 数值 sweep $a\le 10^7$, 每个 $a$ 取 worst-case $b$, 拟合增长率.
2. 找最坏 $b$ 结构 (Stern-Brocot? continued fraction?).
3. 任何 sub-$a^{1/4}$ 结果即可发 INTEGERS.

**Deliverables.** 同模板.

---

### T-08 · OPG · Lucas mod $m$ complete residue characterization

| field | value |
|---|---|
| Status | **Literature closed · handoff to lean4-formalize · NOT outreach** |
| Source | http://www.openproblemgarden.org/op/lucas_numbers_modulo_m |
| Type | THEOREM (Avila-Chen 2013, proved) — OPG page hadn't been updated |
| Untouched | ❌ **猜想已被证明 13 年, 不是 open** |
| Omega fit | 10/10 (但只剩 formalization 价值, 没新研究) |
| Topic value | 2/10 (无 community visibility — 重复别人 13 年前的证明) |
| Effort est | n/a (handoff) |
| Risk | n/a |
| Stage A by | Codex 2026-04-29, score 7/10 (但分析未顾及 Avila-Chen 已证) |
| Lit staleness checked | 2026-04-30 — **CLOSED, do not pursue in outreach** |

**Statement.** Lucas $L_n$ 模 $m$ 含完全剩余系当且仅当 $m\in\{2,4,6,7,14\}\cup\{3^k: k\ge 0\}$.

**Prior (corrected 2026-04-30 from Codex Stage A).**
- Burr 1971: Fibonacci 版本完全分类
- **Avila-Chen 2013 (Fibonacci Quarterly 51.2): PROVED Lucas 版本** ([PDF](https://www.fq.math.ca/Papers1/51-2/AvilaChen.pdf)). 板子原写"验证 $m\le 10^9$"是错的——Codex 读 PDF 后确认: "The PDF gives a short proof of the full theorem", 不是计算验证.
- Lang-Lang 2013 (arXiv:1304.2892) 独立给出 Lucas 分类

**Omega fit detail.** **Omega 装备的 textbook 案例**: Pisano 周期 / `golden mean shift` / Fibonacci-Lucas in $\mathbb{Z}[\sqrt 5]/m$ / `S₂ S₃ counts`.

**Codex Stage A 数值 (2026-04-29).** $m=2..10000$ 全验证, mismatch_count=0, complete_moduli=`{2,3,4,6,7,9,14,27,81,243,729,2187,6561}` (= $\{2,4,6,7,14\}\cup\{3^k:0\le k\le 8\}$, 完全匹配 Avila-Chen 分类). 但: **Avila-Chen 已有完整证明**, 这个数值验证只是 sanity check, 不是新研究.

**Decision.** Outreach 不再追这条. 把已有 Codex 产出 (`research.md` + `lucas_complete_residue.py` + 验证数据) 转给 **lean4-formalize 管线**: 它的产出是一份 `lean4/Omega/...` 的 Avila-Chen 形式化, 这有价值, 但不属于 community-outreach 的 solve+broadcast 契约.

**Attack plan (deprecated for outreach).** ~~ZMod $m$ 中 $L_n\bmod m$ 轨道分析~~ — 已不再适用.

**Deliverables.**
- ✅ `tools/community-outreach/targets/opg_lucas_mod_m/research.md` (Codex Stage A, 转交 lean4-formalize)
- ✅ `lucas_complete_residue.py` + 数据 (转交 lean4-formalize 作为参考实现)
- 🔁 lean4-formalize 接力: `lean4/Omega/POM/LucasCompleteResidueClassification.lean` (新文件, 形式化 Avila-Chen 证明)

---

### T-09 · OPG · Singmaster Pascal repetition computational push

| field | value |
|---|---|
| Status | Backlog |
| Source | http://www.openproblemgarden.org/op/singmasters_conjecture |
| Type | weakly open / falsifiable |
| Untouched | ✅ 系统 sweep 远未做到 verified bound 极限 |
| Omega fit | 7/10 |
| Topic value | 9/10 (Pascal 三角形话题度高) |
| Effort est | 10-14 天 (大量算力) |
| Risk | low |

**Statement.** Pascal $\binom{n}{k}$ 非 1 元素重数有有限上界. 找 $\ge 9$ 重出现的具体 $n$ (反例) 或 push verified bound.

**Prior.** MRSTT 2021 证内部至多 4 解; 边界仍未证. Tao blog 明说"等机器算的题".

**Omega fit detail.** ZMod / fiber-ring / prime-slice / halting frontier 框架对 $\binom{n}{k}$ 友好.

**Attack plan.**
1. `pascal_repeats.py`: $n\le 10^9, 2\le k\le n/2$ sweep, hash 找重复.
2. 优先级: $\Omega(n)\le 4$ 限制 (大重数候选必特殊结构).
3. 找到 9 重 = 头条; 没找到 = "verified to $10^N$" 仍 publishable.

**Deliverables.** 同模板.

---

### T-10 · AimPL · Leth $g_t(n)$ Walsh-dyadic upper bound

| field | value |
|---|---|
| Status | Backlog |
| Source | http://aimpl.org/nscombinatorial/7/ (problem 7.1, Leth) |
| Type | OPEN / quantitative density |
| Untouched | ✅ Leth 2014 后无攻 |
| Omega fit | 9/10 |
| Topic value | 7/10 |
| Effort est | 12-15 天 |
| Risk | low |

**Statement.** $g_t(n)$ = 不"近似包含" $(t,d,w)$-progression ($d$ 为 $2$ 的幂, $w/d<d/n$) 的 $A\subseteq[1,n]$ 最大密度. 证 $g_t(n)<\frac{1}{(\log n)^{\log\log n}}$.

**Omega fit detail.** **Omega 甜蜜点**: $d=2^k$ + binary representation = Walsh balance / log identities / entropy estimates 直击.

**Attack plan.**
1. $n=2^N$ 上重写为 $\{0,1\}^N$ Walsh-uniform 子集密度问题.
2. Sweep $t=3,4,5, N\le 25$.
3. 数值数据本身可发 INTEGERS.

**Deliverables.** 同模板.

---

### T-11 · AimPL · $\{x,y,x+y,xy\}$ Ramsey family

| field | value |
|---|---|
| Status | Backlog |
| Source | http://aimpl.org/nscombinatorial/3/ (problem 3.3) |
| Type | OPEN / partition regular |
| Untouched | ✅ Moreira 2017 / Frantzikinakis 2024 没解决 family 版 |
| Omega fit | 7/10 |
| Topic value | 8/10 (Hindman 类 30 年低悬题) |
| Effort est | 10-14 天 |
| Risk | med |

**Statement.** $\forall$ 有限染色 $\mathbb{N}=C_1\cup\cdots\cup C_k$, $\exists a,b\in\mathbb{N}$ 使 $\{a,b,a+b,ab\}$ 同色?

**Prior.** Moreira 2017: monochromatic 单组. Frantzikinakis-Klurman-Moreira 2024: Pythagorean pairs PR. Family 版仍开放.

**Omega fit detail.** ZMod 上稳定加法子构造 + Lean4 有限染色可决性.

**Attack plan.**
1. SAT-solver $[1,N]$ 上 $k=2,3,4$ 染色找最小 $N(k)$ (反 Schur 数).
2. 搜 twisted Schur-Hindman 结构.
3. `xyabxy_ramsey.py` 输出 W-numbers 表.

**Deliverables.** 同模板.

---

### T-12 · FunSearch · Cap set dim 8 extremal uniqueness

| field | value |
|---|---|
| Status | Backlog |
| Source | FunSearch Nature 2024 + cap_set notebook |
| Type | OPEN / structural rigidity |
| Untouched | ✅ FS 给 size-512 没证唯一性 |
| Omega fit | 8/10 |
| Topic value | 8/10 (FunSearch 招牌结果) |
| Effort est | 18-21 天 |
| Risk | med |

**Statement.** $\mathbb{F}_3^8$ 中 cap set 极值 $r_3\ge 512$ (FunSearch). 证唯一性 (up to affine) 或给非 affine 等价类计数.

**Omega fit detail.** `FiniteFieldEquationalSaturation`, `RatioResultant`, `ChebyshevDworkCongruenceChain` 是有限域 equational 闭包/极值. `Combinatorics/FibonacciCubeGraph`, `PathIndSet` 处理离散极值.

**Attack plan.**
1. 不挑战 $\le 1480\to\le 512$ (太难).
2. 改证 size-512 的 affine 等价类数.
3. FF saturation 证 stabilizer 群必含某常子群.

**Deliverables.** 同模板.

---

### T-13 · Erdős #242 · Erdős-Straus computational push

| field | value |
|---|---|
| Status | Backlog |
| Source | https://www.erdosproblems.com/242 |
| Type | OPEN / falsifiable |
| Untouched | ✅ 不在 AI wiki |
| Omega fit | 5/10 |
| Topic value | 9/10 (教科书级) |
| Effort est | 7-10 天 (找一个反例 $n$) |
| Risk | low (不 break 也能 publish verified bound 推进) |

**Statement.** $\forall n>2$, $\frac{4}{n}=\frac{1}{x}+\frac{1}{y}+\frac{1}{z}$ distinct 整数?

**Prior.** 已验 $n\le 10^{14}$. 启发式概率"ridiculously small".

**Attack plan.**
1. `erdos_straus_sweep.py` push verified bound 至 $10^{16}$ 以上.
2. 找反例 = 头条; 没找到 = 推 bound.

**Deliverables.** 同模板.

---

### T-14 · AlphaEvolve · Autocorrelation inequality $C_2$ closed form

| field | value |
|---|---|
| Status | Backlog |
| Source | AlphaEvolve PDF + Boyer-Steinerberger arxiv:2506.16750 + arxiv:2508.02803 |
| Type | OPEN / extremal functional |
| Untouched | ✅ 全是 step-function 数值竞赛, 0 人攻 closed form |
| Omega fit | 7/10 |
| Topic value | 8/10 |
| Effort est | 21-30 天 |
| Risk | med |

**Statement.** 对非负 $f\in L^1(\mathbb{R})$ supp $\subset[-1/4,1/4]$, $C_2 = \sup_f\sup_{|t|\le 1}\int f(x)f(x+t)dx/\|f\|_1^2$. AE 数值 0.961, ImprovEvolve 0.96258. Closed form?

**Omega fit detail.** `GMajorArcRigidityAffineAutocorr` 是 ZMod 离散 affine autocorrelation rigidity, 可桥接连续版.

**Attack plan.**
1. Omega 内 $N$-段 step function $C_2(N)$ 闭式下界 (collision Hölder).
2. $C_2(N)\to C_2$ 极限化.
3. 论文化路径明确.

**Deliverables.** 同模板.

---

### T-15 · OPG · Erdős distinct covering big-modulus quantitative

| field | value |
|---|---|
| Status | Backlog |
| Source | http://www.openproblemgarden.org/op/covering_systems_with_big_moduli |
| Type | falsifiable / quantitative bound |
| Untouched | ✅ Hough 2015 + Balister 2022 后零星, 没人用 ML/SAT 大规模 sweep |
| Omega fit | 7/10 |
| Topic value | 6/10 |
| Effort est | 5-7 天 |
| Risk | low |

**Statement.** $\forall N$, 是否存在 distinct covering 所有模 $\ge N$? Hough 2015 NO. 找精确常数 $f(N)$.

**Prior.** Hough 2015 上界 $\sim 10^{16}$. Balister 2022 改进到 $\sim 6\cdot 10^8$.

**Attack plan.**
1. 复现 Hough entropy compression.
2. Walsh-balance 二阶矩估计.
3. Sweep $m_{\min}\le 10^4$ 找数值不可行界.

**Deliverables.** 同模板. 一定能产出 short paper.

---

### T-16 · AimPL · Fish product sumset contains subgroup

| field | value |
|---|---|
| Status | Backlog |
| Source | http://aimpl.org/nscombinatorial/6/ (problem 6.1, Fish) |
| Type | OPEN / structural sumset |
| Untouched | ✅ Fish 2017 1-D 后, 2-D 无显著进展 |
| Omega fit | 7/10 |
| Topic value | 6/10 |
| Effort est | 7-10 天 |
| Risk | med |

**Statement.** $A\subseteq\mathbb{N}\times\mathbb{N}$ 正 Banach 密度. $\Delta=\{xy:(x,y)\in A-A\}$ 含 $\mathbb{Z}$ 非平凡子群?

**Prior.** Fish 2017 1-D 版本; Björklund-Fish 2016 $\{xy-z^2\}$ 版本.

**Omega fit detail.** ZMod / fiber-ring / idempotent 对 product 友好.

**Attack plan.**
1. $(\mathbb{Z}/N\mathbb{Z})^2$ 上密度 0.05/0.1/0.2 实证 sweep $N\le 200$.
2. 失败 (有反例) 也是结果.

**Deliverables.** 同模板.

---

### T-17 · IMO 2025 P6 · AlphaEvolve tile arrangement optimality (题面待核)

| field | value |
|---|---|
| Status | Backlog (precondition: 核题面是否在 Omega 强项) |
| Source | Tao 2025-11 blog §"AI for IMO 2025" |
| Type | OPEN / extremal tiling |
| Untouched | ✅ AE 给 arrangement 没证最优, AlphaProof 没攻 |
| Omega fit | 6/10 (待核) |
| Topic value | 9/10 (IMO 题永远高热度) |
| Effort est | 14-21 天 |
| Risk | med |

**Statement.** 待从 IMO 2025 P6 原题 + AE 构造抽出.

**Attack plan (precondition).**
1. 找 IMO 2025 P6 原题 + AE 构造文档.
2. 评估是否落 Omega 强项 (有限组合 / equational / 有限域).
3. 若 fit≥7 推进, 否则降级.

**Deliverables.** 先 evaluate, 不直接进 worktree.

---

### T-18 · Tao Distillation Challenge · ETP cheat sheet (HOT, 6-week window)

| field | value |
|---|---|
| Status | Backlog (TIME-SENSITIVE) |
| Source | https://terrytao.wordpress.com/2026/03/13/mathematics-distillation-challenge-equational-theories/ |
| Type | OPEN competition (Tao + SAIR Foundation backed) |
| Untouched | ✅ 启动 6 周, ETP wiki 还没发布参赛者基线; 论坛 Formalisation thread 没人正式响应 |
| Omega fit | 9/10 |
| Topic value | 9/10 (Tao 加持 + 算力背书 + 早期参赛者会被官方 wiki 收录) |
| Effort est | 4-6 天 |
| Risk | med (需要小模型 evaluation 算力, 但提交本身只需 markdown) |

**Statement.** 给定 ETP (Equational Theories Project) 数据库中 22M 已形式化的 universal-algebra 蕴含 $E_i \implies E_j$ 真假对, 设计一份人类可读的 "cheat sheet" $C$ (短文本), 使得当 $C$ 作为 in-context prompt 喂给低成本开源 LLM $M_C$ 时, 在留出测试集上 $M_C(E_i, E_j)$ 二分类准确率显著超过 50%. 评分: $\mathrm{Acc}(M_C) - 0.5$ 最大化, 长度上界惩罚.

**Omega fit detail.** **直接对位**: 我们 lean4/Omega 的等式理论 + Fin n 魔群 + ZMod 加性结构正是 ETP 命题语言的目标域. 现成的 fiber rings, idempotents, 加性单子结构是 cheat sheet 的天然条目. 我们之前 #364 的工作就是 ETP-style 的 finite countermodel.

**Attack plan.**
1. 从 ETP 公开 Lean 数据库提取 50 条最高频 implication motifs (按频次分布)
2. 在我们的 ZMod / 魔群分类引理库中标注覆盖
3. 提交 ≤ 2 页 cheat sheet (markdown / PDF)

**Worktree-ready inputs.** ETP repo 公开数据 + `lean4/Omega/EquationalTheory/`.

**Deliverables.** `targets/tao_distillation/research.md` + `tools/community-outreach/tao_distillation/cheat_sheet.md` + ETP wiki / Tao blog comment draft.

---

### T-19 · Erdős #872 · Divisibility-free game, fan-capture lower bound (Bloom active)

| field | value |
|---|---|
| Status | Backlog (TIME-SENSITIVE: Bloom 论坛实时讨论中) |
| Source | https://www.erdosproblems.com/forum/thread/872 |
| Type | OPEN / combinatorial game |
| Untouched | ✅ 没有 follow-up arxiv paper, AlphaEvolve / Aristotle 没碰过 |
| Omega fit | 8/10 |
| Topic value | 8/10 |
| Effort est | 6-8 天 |
| Risk | med |

**Statement.** 在 $\{2,3,\dots,n\}$ 上两玩家轮流选数加入反链 $A$ (无 $a\mid b, a\ne b\in A$), 至无法移动. 设 $L(n)$ = Prolonger 先手保底游戏长度. Erdős 问 $L(n)\ge\varepsilon n$? $L(n)\ge(1-\varepsilon)n/2$?

**Discussion.** 2026-04-29 当天活跃, Bloom (registry 维护者本人) 与 natso26 反复讨论 dyadic refinement 的 fan-capture 下界. 当前下界仍远低于 $n/2$.

**Omega fit detail.** $\{2,\dots,n\}$ 上 divisibility 偏序的离散组合博弈 → 有限组合 + 素数 prime slices + game tree 熵估计.

**Attack plan.**
1. dyadic refinement 移植到 Lean, 形式化 $L(n)\ge c\cdot n/\log n$ 级下界
2. 数值搜索 $n\le 200$ 找紧界候选

**Deliverables.** 同模板 + erdosproblems #872 论坛 reply (与 Bloom 直接互动).

---

### T-20 · Size-4 Sidon non-extension · Niu arxiv:2604.25214 (yesterday)

| field | value |
|---|---|
| Status | Backlog (TIME-SENSITIVE: 论文 1 天前) |
| Source | https://arxiv.org/abs/2604.25214 (Tong Niu, 2026-04-28) |
| Type | OPEN / Sidon set extension |
| Untouched | ✅ 提交昨天, 单作者, 跟随 Alexeev-Mixon 2025-10 size-5 结果, 字段 wide open |
| Omega fit | 8/10 |
| Topic value | 9/10 |
| Effort est | 5-7 天 |
| Risk | med |

**Statement.** 论文留下中心 open problem: "A complete proof, in the spirit of Alexeev-Mixon's polarity argument or via a multiplier descent [showing the families $\{0,1,3,11\}$ and $\{0,1,4,11\}$ are complete in the relevant range], remains the central open problem."

**Omega fit detail.** Additive combinatorics + Sidon set + difference set = `Combinatorics.Additive` + ZMod perfect-difference-set 装备 (similar to T-12 cap set 思路).

**Attack plan.**
1. brute-force 验 size-4 family 完备性, 计算 $\mathbb{Z}_v$ 中所有扩展, $v\le 10^4$
2. 尝试 multiplier-descent 证: Sidon 集 $A\subseteq\mathbb{Z}_v$ 可扩 ⟺ multiplier-orbit condition. 编码为 LP
3. 与 polarity argument 结构对照

**Deliverables.** 同模板 + arXiv preprint 短文 + Niu 邮件 follow-up draft.

---

### T-21 · Sophie Germain × Fibonacci totient · Goel arxiv:2604.17847

| field | value |
|---|---|
| Status | Backlog |
| Source | https://arxiv.org/abs/2604.17847 (Aradhya Goel, IIT Kanpur, 2026-04-20) |
| Type | OPEN / Pisano-Sophie Germain bridge |
| Untouched | ✅ v3 刚发, 单作者, 没有 DeepMind/AlphaProof/Aristotle 关注 |
| Omega fit | 9/10 |
| Topic value | 8/10 |
| Effort est | 4-6 天 |
| Risk | low |

**Statement.** "We conjecture that $S(q)\ne\emptyset$ forces the existence of [a Sophie Germain prime] $p$; verified $q\le 50000$. Assuming that $z(2q+1)\mid\pi(q)$ holds for infinitely many Sophie Germain primes (verified ~23.9%) ... would imply infinitely many primes satisfying a purely Fibonacci-theoretic condition."

**Omega fit detail.** **直接命中** — Pisano periods $\pi(q)$ + Fibonacci entry-point $z(p)$ 活在 Omega 的 `ZMod.Cycle` / Lucas-sequence stack. 与 T-08 (Lucas mod m) 共享装备.

**Attack plan.**
1. 把 $q\le 50000$ 验证扩到 $q\le 10^7$ 用我们 Fibonacci.Pisano 表
2. 通过 CRT 分解 $\pi(q)=\mathrm{lcm}(\pi(p_i^{e_i}))$ 分类 $S(q)$ 的 AP 结构
3. 证 $|S(q)|$ 奇 ⟺ $q\equiv 8\pmod{15}$ via parity

**Deliverables.** 同模板 + Goel 邮件 follow-up.

---

### T-22 · Erdős #1163 · Subgroup orders of $S_n$ (today's brainstorm)

| field | value |
|---|---|
| Status | Backlog (TIME-SENSITIVE: 论坛今天活跃) |
| Source | https://www.erdosproblems.com/forum/thread/1163 (Przemek, 2026-04-29) |
| Type | OPEN / statistical group theory |
| Untouched | ✅ 论坛今天才头脑风暴, 0 partial result |
| Omega fit | 8/10 |
| Topic value | 7/10 |
| Effort est | 7-10 天 |
| Risk | med-high |

**Statement.** 描述 $\{|H|: H\le S_n\}$ 的算术结构 (统计意义). 子问题: $\mathrm{Sub}(S_n)$ 上均匀分布时 $\log|H|, v_p(|H|), \omega(|H|)$ 的极限律.

**Discussion.** Przemek 列了 3 种自然解读, 论坛求解读建议. **First-mover slot**: 任何形式化的"统计结构定理"都会被 Bloom 引用进官方 problem page.

**Omega fit detail.** 有限组合 / 魔群分类 / 离散概率测度极值. ZMod + idempotent 给出 $|H|$ 素因子分布工具.

**Attack plan.**
1. 选 uniform-subgroup 解读
2. 用 prime-slice + 加性组合工具证 $\log|H|/\log n!$ 弱大数 / 集中不等式 (粗糙的 $O(1)$ 量级即可)

**Deliverables.** 同模板 + 论坛 reply 抢早 slot.

---

### T-23 · Erdős #1196 · Von Mangoldt dual certificate (80-post thread)

| field | value |
|---|---|
| Status | **🔴 CLOSED · proved (Lean) · drop** |
| Source | https://www.erdosproblems.com/forum/thread/1196 (mbr63, 80 posts) |
| Type | PROVED (Lean) — thread 已经收尾, 形式化版本入库 |
| Untouched | ❌ registry 把 #1196 标 `proved (Lean)` + `formalized=yes`. 80-post 讨论是收尾过程 |
| Omega fit | n/a |
| Topic value | n/a |
| Effort est | n/a |
| Risk | n/a |
| Lit staleness checked | 2026-04-30 — **CLOSED, registry 状态 `proved (Lean)`** |

**Statement.** 配权有向图 $nq\to n$, $w(nq,n)=\Lambda(q)/(nq\log^2(nq))$, von Mangoldt 恒等 $\sum_{q\mid n}\Lambda(q)=\log n$ 给 outflow $\mathrm{Out}(n)=1/(n\log n)$. 求 $\nu$ 使整体可视为 stationary measure; 进一步 prime-only 子过程 $n\to n/p$ closed form.

**Omega fit detail.** Divisibility poset + von Mangoldt + idempotent 测度 → Omega fiber rings + 离散概率测度.

**Attack plan.**
1. 形式化 $\sum_{q\mid n}\Lambda(q)=\log n\Rightarrow\mathrm{Out}(n)=1/(n\log n)$ 基础引理
2. 把 mbr63 的 dual-certificate 框架 modularize
3. 挑 prime-only 跳跃 lemma 之一独立证

**Deliverables.** 同模板 + thread 内 Lean 形式化 note (高曝光).

---

### T-24 · WZ seeds · Hou-Mu arxiv:2604.22377 (Zeilberger resonance)

| field | value |
|---|---|
| Status | Backlog |
| Source | https://arxiv.org/abs/2604.22377 (Qing-Hu Hou, Yan-Ping Mu, 2026-04-24) |
| Type | OPEN / WZ enumeration |
| Untouched | ✅ 7 个新 WZ seeds, "are these all" 自然 follow-up 问题 |
| Omega fit | 6/10 |
| Topic value | 6/10 (Zeilberger 在 Twitter/blog 直接 engage WZ 进展) |
| Effort est | 5-7 天 |
| Risk | med |

**Statement.** 系统构造 WZ (Wilf-Zeilberger) seeds, 论文给 7 个新 seeds. 隐含开放问题: 分类所有 WZ seeds; 该方法只给有限多.

**Omega fit detail.** 超几何恒等式 + WZ 方法 ↔ Omega 的符号 `Combinatorics.WZ` glue. 与 T-07 Pierce / T-08 Lucas 共享 装备.

**Attack plan.**
1. 用 Gosper/Zeilberger 算法枚举 parameter complexity $\le N$ 的所有 WZ seeds
2. 测 7 个新 seeds + 经典 Apéry/Andrews seeds 是否构成有限 Gröbner 风格基
3. 寻 no-go 定理

**Deliverables.** 同模板 + Zeilberger 博客 / Twitter follow-up.

---

## In Research

(空 — 等用户挑选 + 派 worktree)

---

## Draft Ready

(空)

---

## Pending User Approval

(空)

---

## Submitted

(参见 `OUTREACH_LOG.md` 已完成区. 本看板只跟踪开放问题攻击, 不重复记录 OUTREACH_LOG 的 community comment 类提交.)

---

## Pipeline 并行架构 (worktree 派单契约)

每条 TODO 设计满足:
1. **Self-contained input**: research.md 产出所需的全部已知文献已在 TODO 中列出 + Omega 库相关模块路径已标注
2. **No write conflicts**: 不同 TODO 写不同 `targets/erdos_NNN/` 子目录 + 不同 `tools/community-outreach/erdos/p_NNN_*.py` 脚本 + 不同 `theory/.../sections/appendix/erdos_NNN_*` paper 子目录. 各 worktree merge 回主分支无冲突.
3. **State isolation**: 每个 worktree 跑独立 outreach_state JSON (`outreach_state/erdos_NNN.json`).
4. **Approval gate**: worktree 完成 Stage B (research.md) 后必须暂停, 用户从主仓库审, 通过后才能进 Stage C (draft) 和 Stage D (用户最终批准发布).

派单建议:
- 单 worker 同时跑 1 个 TODO (避免 Codex API 抢限流)
- 推荐先开 3 个 worktree 试: T-01 (低风险 + 高 fit) / T-02 (高话题 + 中风险) / T-08 (textbook 案例 + 极低风险). 三者完全独立, 可平行
- 跑通后扩展到 5-8 个 worktree 同时

---

## 调研记录

- **2026-04-29 #1**: 初版 board, 17 条 TODO, 来源 = erdosproblems registry (#475/#699/#7/#199/#1026/#1191/#242) + Open Problem Garden + AIM Problem Lists + AlphaEvolve/FunSearch/AlphaProof. arXiv 2026 Q1 sweep agent stream 超时未完成.
- **2026-04-29 #2**: 重派 arXiv (拆成两个窄范围 agent, 严格 tool budget). 完成 + 追加 7 条 TODO (T-18 至 T-24): Tao Distillation Challenge (6-周窗口), Erdős #872/#1163/#1196 (论坛今/昨日活跃), Niu Sidon size-4 (yesterday), Goel Sophie Germain × Fibonacci, Hou-Mu WZ seeds. 已剔除 5 条低 fit (132-avoiding, Bicirculant Hamiltonicity, Heffter $k\equiv 2$, Erdős #1190 大模 covering [overlap T-15], Erdős #1101 [GPT-5.5 已 partial 解]).
- 已确认硬碰不下来排除: Erdős #142 ($10k r_k$), #3 ($5k AP), #1/#28/#30/#39 高奖 Sidon (需 Kelley-Meka 级 NT), Polignac/Goldbach/Riemann 等超大问题, PDE/sieve/调和分析类 (Tao 12-01 prime factors, #1131 Lebesgue, #1138 prime gaps).
- **2026-04-30**: 建 Stage 0 工具 `tools/community-outreach/lit_staleness.py` 跨 24 条 TODO 跑 erdosproblems registry + AI wiki + arXiv API + 板子自陈 status. 全 board verdict 分布: 🔴 CLOSED × 4 (T-02/T-03/T-08/T-23), 🟠 OVERTAKEN × 2 (T-01/T-19), 🟡 PARTIAL × 8 (T-14/T-15/T-17/T-18/T-20/T-21/T-22/T-24), 🟢 FRESH × 10. **新发现 3 条 Erdős registry 已收尾的 (CLOSED)**: #199 disproved (Lean) 2026-02-24, #1026 solved (Lean), #1196 proved (Lean). T-19 是 false positive (registry 显示 #872 仍 open + Bloom 论坛今天活跃, 应以板子的 forum-active signal 为准, 不被工具的关键词噪声匹配误导).
- **当前 high-priority 重排 (2026-04-30 lit-staleness 后)**: T-04 Erdős #1191 ($1000 Sidon, 仍 open) 升至第一梯队; T-05 Erdős #7 ($25 odd covering, verifiable, 60-year fame); T-06 Erdős #699 (binomial gcd, falsifiable); T-13 Erdős #242 (Erdős-Straus, falsifiable); T-19 #872 (Bloom 论坛活跃, 工具误判但板子保留); T-22 #1163 (今天头脑风暴); T-21 Goel arxiv 1 周新.
