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
| Status | **🔴 DROP · profile judge DROP** — Misframed and too derivative for automated deep reasoning: the board entry itself records that the named Erdős #1191 infinite Sidon-set problem is being conflated with a finite Sidon diameter second-order constant / piec |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T05:45:51+00:00 · rc=0 · science_gate=CLOSE_TARGET |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T00:51:22+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-11T19:08:51+00:00 · science_gate=WRITEBACK_READY · impact=bounded_finite_certificate_claim |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T10:27:14+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T06:40:00+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **🔴 DISCARDED · misframed (Oracle Round 1, 2026-04-30)** |
| Source | FunSearch Nature 2024 + cap_set notebook |
| Type | OPEN / structural rigidity |
| Untouched | ✅ FS 给 size-512 没证唯一性 |
| Omega fit | 8/10 |
| Topic value | 8/10 (FunSearch 招牌结果) |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **DISCARDED**; Oracle: FunSearch 的 512 in $\mathbb{F}_3^8$ 是 best-known **构造**而非已证 extremal 值，"extremal uniqueness" 不是 well-defined 目标 |

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
| Status | **🟠 OVERTAKEN · board target obsolete (Oracle Round 1, 2026-04-30)** |
| Source | https://www.erdosproblems.com/242 |
| Type | OPEN / falsifiable |
| Untouched | ❌ board outdated |
| Omega fit | 5/10 |
| Topic value | 9/10 (教科书级) |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **OVERTAKEN**; Oracle: 已验证至 $10^{18}$（板子说 $10^{14}$），且有 2026 claimed proof 待审，不再是 computational push 题 |

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
| Status | **🔴 DROP · profile judge DROP** — Not viable as stated. The supremum over /t/<=1 includes t=0, so the objective contains ∫ f(x)^2 dx / //f//_1^2. For nonnegative L^1 functions supported in [-1/4,1/4], this ratio is unbounded by concentrating fixed L^1 ma |
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
| Status | **🟠 OVERTAKEN · board target stale (Oracle Round 1, 2026-04-30)** |
| Source | http://www.openproblemgarden.org/op/covering_systems_with_big_moduli |
| Type | falsifiable / quantitative bound |
| Untouched | ❌ board's stated target stale |
| Omega fit | 7/10 |
| Topic value | 6/10 |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **OVERTAKEN**; Oracle: 原"big-moduli 是否存在"已被 Hough negatively solved，later work 把 bound 降到 616,000，板子的"找精确常数"目标过时 |

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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T12:19:43+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **🔴 CLOSED · solution published (Oracle Round 1, 2026-04-30)** |
| Source | Tao 2025-11 blog §"AI for IMO 2025" |
| Type | OPEN / extremal tiling |
| Untouched | ❌ |
| Omega fit | — |
| Topic value | — |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **CLOSED**; Oracle: 已发表答案 $2112 = 2025 + 2 \cdot 45 - 3$，含 general formula。Evan Chen solution notes 等公开 |

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
| Status | **🟠 OVERTAKEN · stage 1 ended, stage 2 different problem (Oracle Round 1, 2026-04-30)** |
| Source | https://terrytao.wordpress.com/2026/03/13/mathematics-distillation-challenge-equational-theories/ |
| Type | OPEN competition (Tao + SAIR Foundation backed) |
| Untouched | ❌ |
| Omega fit | — |
| Topic value | — |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **OVERTAKEN**; Oracle: Stage 1 cheat-sheet 任务于 April 20 结束。Stage 2 是不同的 proof/counterexample 竞赛，不是 mathematical theorem target |

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
| Status | **🟠 OVERTAKEN · "untouched" claim FALSE (Oracle Round 1, 2026-04-30)** |
| Source | https://www.erdosproblems.com/forum/thread/872 |
| Type | OPEN / combinatorial game |
| Untouched | ❌ board 主张被 Oracle 推翻 |
| Omega fit | — |
| Topic value | — |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **OVERTAKEN**; Oracle: Erdős 页面已报告 AI-generated partial results；near-$n/2$ 问题已被负面回答，上界 $(23/48 + o(1))n$。原 board "untouched" 主张错。重新评估角度后再决定是否还可推 |

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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T11:50:32+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T09:58:10+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **Pending User Approval** — research_loop completed 2026-05-12T11:02:00+00:00 · rc=0 · science_gate=WRITEBACK_READY |
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
| Status | **🔴 DISCARDED · not a stated open problem (Oracle Round 1, 2026-04-30)** |
| Source | https://arxiv.org/abs/2604.22377 (Qing-Hu Hou, Yan-Ping Mu, 2026-04-24) |
| Type | OPEN / WZ enumeration |
| Untouched | ❌ |
| Omega fit | — |
| Topic value | — |
| Effort est | — |
| Risk | — |
| Lit staleness checked | 2026-04-30 — **DISCARDED**; Oracle: Hou-Mu 论文给的是构造方法 + 7 个 WZ seeds，"classify all seeds" 是我们 inferred 的项目，不是论文 stated open problem，缺 clear success criterion |

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
- **2026-04-30 (晚)**: 建 arxiv_watch.py + 接入 supervise/Round 1 freshness 注入 + 跑 Round 1 oracle discover (conv `bf5db0c917fe493f`, 13m35s ChatGPT 5.5 Pro 思考)。Oracle 比 lit_staleness 更激进，再清出 7 条 stale: 🔴 DISCARDED/CLOSED × 3 (T-12 misframed, T-17 IMO P6 已发表, T-24 not stated open), 🟠 OVERTAKEN × 4 (T-13 Erdős-Straus 已验 $10^{18}$, T-15 Hough negatively solved, T-18 Stage 1 ended Apr 20, T-19 "untouched" 主张被 Erdős 页面 AI partial+$(23/48+o(1))n$ 上界推翻)。**Oracle Round 1 TOP-3**: T-20 Sidon size-4 (best target), T-21 Sophie Germain × Fibonacci totient (strongest Omega fit), T-06 binomial gcd (pragmatic ship). **TOP-1 sub-goal**: T-20 lemma `SingerAffineNoEmbed_1024` ($A=\{0,1,3,11\}$, $B=\{0,1,4,11\}$ no affine embed in canonical Singer set $S_q\subset\mathbb{Z}/(q^2+q+1)\mathbb{Z}$ for $13\le q\le 1024$). 当晚启动 Round 2 deep on T-20.

### T-25 · Finite Sidon diameter b_inf verifier

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-12T01:37:16+00:00 · rc=0 · science_gate=WRITEBACK_READY |
| Source | https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/comment-page-1/ |
| Type | author question / arxiv followup |
| Untouched | Publicly inspectable as of source checks: Daniel Carter's 2025-11-07 Tao-blog comment proposes investigating the largest Sidon set in [n] / smallest Sidon diameter and says the Carter-Hunter-O'Bryant upper bound depends on unclear piecewise-affine parameters; Tao's 2025-11-09 and 2025-11-11 replies identify missing side-condition enumeration, an admissibility-checking verifier, and the 1.9526463099204112 b_inf tuple. Erdős Problems #14, last edited 2026-04-06, still marks the finite Sidon size problem OPEN and lists Carter-Hunter-O'Bryant as current record h(N) <= N^{1/2}+0.98183 N^{1/4}+O(1). Exact-string searches for 1.9526463099204112 and 1.952659676624688 found only the Tao discussion. Must rerun arXiv, MathSciNet/zbMATH if available, Google Scholar/Semantic Scholar, GitHub dcartermath/sidon, and Erdős Problems #14 checks immediately before RUN because the Tao constant is a post-paper blog-comment update. |
| Omega fit | 8/10 |
| Topic value | 8/10 |
| Effort est | 14-21 天 |
| Risk | med |
| Final display | source-audited research note plus private outreach draft for finite Sidon/Golomb-ruler researchers, centered on an independently checkable verifier/certificate for the finite Sidon diameter b_inf piecewise-affine ansatz |
| Success gate | Before operator approval or any send: research.md must explicitly separate Erdős #14 finite Sidon size/diameter from Erdős #1191 infinite Sidon liminf; coefficient normalization must be checked, with b_inf on the diameter side corresponding under inversion to half that constant in the N^{1/4} term for h(N); the Tao comments, Carter-Hunter-O'Bryant arXiv/Springer paper, dcartermath/sidon verifier code, Erdős Problems #14/#1191 pages, and newer literature after 2026-05-10 must be rechecked; any extremality claim must be only for a fully specified admissible parameter class and backed by a reproducible certificate or stated as failure analysis; independent oracle judge must confirm no claim of solving the global finite Sidon problem. |

**Statement.** Let A be a finite Sidon set of size k and diameter diam(A). The Carter-Hunter-O'Bryant method proves diam(A) >= k^2 - b k^{3/2} - O(k) for b <= 1.96365, equivalently h(N) <= N^{1/2}+0.98183 N^{1/4}+O(1). Tao's 2025-11-11 blog-comment update reports an AlphaEvolve/Daniel Carter parameter tuple giving b_inf <= 1.9526463099204112 after admissibility checks. The target is to reconstruct the admissible theorem/verifier for the piecewise-affine tau, alpha, cs framework and either produce a rigorous closed-class certificate for that tuple, or a precise failure report identifying missing hypotheses, numerical fragility, or non-extremality within the stated admissible class.

**Prior.** Baseline sources: Carter-Hunter-O'Bryant, arXiv:2310.20032 submitted 2023-10-30, later Acta Mathematica Hungarica 175 (2025), 108-126, proves b <= 1.96365 and h(N) <= N^{1/2}+0.98183 N^{1/4}+O(1) with computer assistance. GitHub https://github.com/dcartermath/sidon publicly hosts verify.py for the paper and says it verifies the Section 3 proof strategy and Theorem 3.3. Tao blog comments dated 2025-11-09 and 2025-11-11 identify the verifier side-condition problem and report b_inf <= 1.9526463099204112 with tau=1.1660611984972167, eight alpha values, and cs=(0.6338163952331487,). Erdős Problems #14, checked from a page last edited 2026-04-06, remains OPEN and lists CHO25 as the current record; Erdős #1191 is a different infinite Sidon liminf problem and must not be used as the target label. Freshness remains mandatory because the improved constant appears in a blog comment rather than a versioned paper.

**Omega fit detail.** Strong fit for Omega-style tooling if scoped as verifier/certificate work rather than solving the full Sidon conjecture: formalizable side-condition extraction, exact/interval linear-program checking, rational reconstruction of floating point parameters, dual certificate verification, additive-energy and collision-count lemmas, and reusable ZMod/Sidon abstractions. Exploratory bridge: even a negative result can become a useful benchmark for verifier hardening against AlphaEvolve-style exploit modes.

**Attack plan.**
1. Build a dated source table distinguishing Erdős #14 finite Sidon diameter/size, Erdős #1191 infinite Sidon liminf, Carter-Hunter-O'Bryant 2023/2025, dcartermath/sidon verify.py, and Tao's 2025-11 comments; record currentness queries and exact access dates.
2. Reconstruct the CHO piecewise-affine admissible parameter class from the paper and verifier code, then write a standalone mathematical theorem statement with all side conditions for tau, alpha, cs and the returned b_inf bound.
3. Convert the reported 1.9526463099204112 floating tuple into an independently auditable certificate: interval/rational bounds for admissibility, LP feasibility/duality or verified solver output, and a reproducible script producing results.json; if this fails, document the first unverifiable dependency precisely.

**Deliverables.**
- tools/community-outreach/targets/cand_finite_sidon_diameter_inf_verifier/research.md
- tools/community-outreach/targets/cand_finite_sidon_diameter_inf_verifier/results.json
- tools/community-outreach/targets/cand_finite_sidon_diameter_inf_verifier/submission_draft.md

_Inbox graduation rationale_: This should enter the board because it is publicly inspectable, current enough to warrant fast source-audited followup, and well matched to automated verification rather than open-ended conjecture hunting. The previous T-04 failure was a labeling and normalization error, not evidence that the finite Sidon diameter verifier target is stale. The viable contribution is a rigorous audit/certificate or a careful failure analysis of a specific post-paper bound, with explicit guardrails against claiming global optimality.

---

### T-26 · MRS 2026 Problem 1 · Fibonacci-Thue-Morse shift lower bound

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-11T18:24:18+00:00 · science_gate=WRITEBACK_READY · impact=author_email/short_note/operator_review |
| Source | https://arxiv.org/abs/2603.21645 |
| Type | open problem |
| Untouched | arXiv:2603.21645 is publicly inspectable, submitted 2026-03-23, v1 only as of the arXiv page checked 2026-05-10. The paper states Theorem 14 gives an O(c) upper bound for the minimal msd-first Fibonacci-DFAO generating (t(i+c))_{i>=0}, then leaves Problem 1: prove the state count is Θ(c). Freshness must be rechecked immediately before any RUN/outreach by searching the exact problem phrase, author pages, arXiv followups, and related arXiv:2603.18858; no public solution was found in the 2026-05-10 web check. |
| Omega fit | 9/10 |
| Topic value | 8/10 |
| Effort est | 10-20 天 |
| Risk | med |
| Final display | source-audited short research note or author email for automata/combinatorics-on-words audience |
| Success gate | Before operator approval or external send: confirm the exact Problem 1 statement in arXiv:2603.21645v1 and that no public solution/update exists; prove a uniform Ω(c) lower bound for the minimal msd-first Fibonacci-DFAO for u_c(i)=t(i+c), preferably via an explicit Myhill-Nerode family of linearly many distinguishable reachable residuals; include reproducible finite-state computations for small c; and separate proof, code, and outreach draft artifacts. |

**Statement.** Let t(n) be the parity of the number of 1s in the canonical Zeckendorf/Fibonacci representation of n, read by msd-first Fibonacci-DFAOs. For each c>=0 define u_c(i)=t(i+c). Prove that the number of states in the minimal msd-first Fibonacci-DFAO generating u_c is Θ(c).

**Prior.** Primary source: Moradi, Rampersad, and Shallit, 'Complexity of Linear Subsequences of Fibonacci-Automatic Sequences', arXiv:2603.21645, submitted 2026-03-23. The arXiv page checked 2026-05-10 lists v1 only; the PDF states Theorem 14 gives O(c) and Problem 1 asks for Θ(c). Related source arXiv:2603.18858, 'State Complexity of Shifts of the Fibonacci Word', submitted March 2026, resolves the shifted Fibonacci word case with O(log c), but that is a different sequence f(i+c), not the Fibonacci-Thue-Morse shift t(i+c). Web searches on 2026-05-10 for exact phrases including 'minimal automaton generating t(i+c)', 'Fibonacci-Thue-Morse Theta(c)', and '2603.21645 Problem 1' found the source paper and mirrors/summaries, not a solution. This is only a bounded freshness check, not a proof of untouchedness.

**Omega fit detail.** Strong fit for Automath/Omega because the target is finite-state and proof-auditable: construct Zeckendorf normal-form transducers, enumerate/minimize small-c DFAOs, extract reachable residuals, search for a linearly sized Myhill-Nerode separating family, and convert successful finite patterns into lemmas about synchronized Fibonacci carry/defect windows. The exploratory bridge is to relate MRS Theorem 14's length-(c+1) state window to canonical residue/carry layers whose future suffix probes distinguish Ω(c) residuals.

**Attack plan.**
1. Reproduce MRS definitions: build the msd-first Fibonacci-DFAO for t(n), implement the Theorem 13/14 shift construction for u_c, minimize for a range of c, and record exact state counts plus witness suffixes distinguishing states.
2. Audit the proposed bridge lemma C: identify a linear-size reachable canonical slab inside the Theorem 14 construction, formalize its residue/carry descriptors, and test whether short Fibonacci-valid suffix probes give pairwise different outputs.
3. Either prove a uniform Myhill-Nerode lower bound from the slab/probe structure or produce a precise failure analysis showing where the bridge collapses, with data and counterpatterns that are useful to the authors.

**Deliverables.**
- tools/community-outreach/targets/arxiv_2603_21645/research.md
- tools/community-outreach/targets/arxiv_2603_21645/results.json
- tools/community-outreach/targets/arxiv_2603_21645/submission_draft.md

_Inbox graduation rationale_: The candidate is a real, named, current open problem in an inspectable 2026 arXiv preprint. It has a sharply scoped missing lower bound, an existing matching O(c) upper bound, and a natural route through finite automata minimization, Zeckendorf normalization, and Myhill-Nerode witnesses. It is suitable for the outreach board because partial progress can still yield a reviewable research note or collaboration packet, while any claimed success has a clear mathematical verifier.

---

### T-27 · MRS 2026 Problem 2 · Tribonacci word shift state complexity

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-11T12:47:13+00:00 · rc=0 · science_gate=WRITEBACK_READY |
| Source | https://arxiv.org/abs/2603.21645 |
| Type | open problem |
| Untouched | arXiv:2603.21645v1 was submitted on 2026-03-23 and its conclusion explicitly states Problem 2: determine the state complexity of (r(i+c))_{i>=0} where r is the Tribonacci word. Web searches on 2026-05-10 for the exact problem phrase, Tribonacci word shift state complexity, and arXiv:2603.21645 Problem 2 surfaced the source paper and Fibonacci-shift companion material, not a public solution; this must still be rechecked before RUN/outreach. |
| Omega fit | 7/10 |
| Topic value | 9/10 |
| Effort est | 14-30 天 |
| Risk | high |
| Final display | source-audited research note with reproducible transition/certificate data for automata-on-words researchers; optional author email only after operator approval |
| Success gate | Before operator approval/send, verify the exact Problem 2 statement from arXiv:2603.21645, rerun a currentness search, fix the Tribonacci numeration and DFAO conventions, and produce either a proved asymptotic bound or an auditable finite transition/carry/partition certificate with reproducible data. |

**Statement.** Let r be the Tribonacci word, interpreted in its corresponding Tribonacci/Pisot numeration DFAO setting. Determine, or give sharp asymptotic upper and lower bounds for, the number of states in the minimal DFAO generating the shifted sequence (r(i+c))_{i>=0} as a function of the shift c.

**Prior.** Primary source: Moradi, Rampersad, and Shallit, arXiv:2603.21645v1, submitted 2026-03-23, conclusion Problem 2 asks this exact question and immediately frames it as a Pisot-degree generalization problem. Companion context: arXiv:2603.18858, submitted 2026-03-19, proves O(log c) state complexity for shifts of the Fibonacci word, not the Tribonacci word. Currentness check on 2026-05-10 found no public solution in broad web searches, but this is not proof of untouched status; operator should recheck arXiv/Google Scholar/Semantic Scholar/author pages immediately before RUN or outreach.

**Omega fit detail.** Strong exploratory fit if Omega can represent the problem as finite-state evidence: build Tribonacci numeration recognizers, bounded carry states for Y=X+c, minimization data for shifted DFAOs, and Rauzy-fractal or beta-expansion partition transitions. The bridge is not a direct reuse of existing Zeckendorf/Fibonacci modules; it is a degree-3 Pisot extension target where reproducible finite transition tables are the main Automath/Omega artifact.

**Attack plan.**
1. Source audit: extract the exact definitions of Tribonacci word, Tribonacci representation, input direction, state complexity convention, and any cited Pisot-generalized automatic framework from the paper and adjacent references.
2. Computational baseline: implement or reuse a Tribonacci numeration normalizer, DFAO for r, shift-by-c construction for small c, DFAO minimization, and record minimal state counts for a growing certified range of c.
3. Theory/certificate step: attempt to identify a finite carry-state or Rauzy-fractal partition invariant that proves an upper bound, and separately search for distinguishable-prefix witnesses giving lower bounds.

**Deliverables.**
- tools/community-outreach/targets/arxiv_2603_21645_2/research.md
- tools/community-outreach/targets/arxiv_2603_21645_2/results.json
- tools/community-outreach/targets/arxiv_2603_21645_2/submission_draft.md

_Inbox graduation rationale_: This is a real, recent, inspectable open problem stated in a 2026 arXiv paper by domain authors. It is close to Omega strengths because progress can be made through finite automata, minimization, transition certificates, and reproducible state-count data even if the full asymptotic classification remains out of reach. The risk is high because the degree-3 Pisot jump may require substantial new theory, but a well-audited computational/finite-partition packet would still be a useful outreach artifact.

---

### T-28 · Fibonacci Cube Edge General Position Conjecture

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-11T18:35:08+00:00 · science_gate=WRITEBACK_READY · impact=author_email/short_note/operator_review |
| Source | https://arxiv.org/abs/2304.10114 |
| Type | open problem |
| Untouched | Public source is arXiv:2304.10114, submitted 2023-04-20, with journal version published 2023-05-17; the paper states Conjecture 4.5 that gp_e(Γ_n)=2F_n for n≥2 after proving the Θ_1∪Θ_n lower bound. Freshness check on 2026-05-11 found later edge-general-position papers in 2024, 2025, and a 2026 Discrete Applied Mathematics article, but surfaced no inspectable paper closing the Fibonacci-cube conjecture; before any outreach, operator must re-check arXiv, Google Scholar/Semantic Scholar citations, MathSciNet/zbMATH if available, and the authors' pages for a post-2026-05-11 resolution. |
| Omega fit | 9/10 |
| Topic value | 8/10 |
| Effort est | 10-21 天 |
| Risk | med |
| Final display | Short research note plus reproducible ILP/certificate tables for Γ_n and an operator-approved author email to Klavžar and Tan. |
| Success gate | Before operator approval or external send, there must be either a human-readable proof of the upper bound gp_e(Γ_n)≤2F_n for all n≥2, or a clearly labeled partial contribution with reproducible verifier output matching gp_e(Γ_n)=2F_n for a nontrivial checked range and a fresh literature audit showing the conjecture remains open. |

**Statement.** Let Γ_n be the Fibonacci cube: the induced subgraph of the n-dimensional hypercube on binary strings with no consecutive 1s. Let F_0=0, F_1=1, and F_{k+2}=F_{k+1}+F_k. Prove that for every n≥2, the edge general position number of Γ_n is gp_e(Γ_n)=2F_n, where an edge set X⊆E(Γ_n) is edge-general-position if no three distinct edges of X lie on a common shortest path in Γ_n.

**Prior.** The source paper arXiv:2304.10114 was submitted on 2023-04-20 and the Springer open-access version was published on 2023-05-17. It proves that Θ_1(Γ_n)∪Θ_n(Γ_n) is a maximal edge general position set and gives gp_e(Γ_n)≥2F_n, then states Conjecture 4.5 asserting equality. Searches on 2026-05-11 for exact phrases including "edge general position" + "Fibonacci cube", "Conjecture 4.5" + "Fibonacci cube", and "gp_e" + "Fibonacci" found the source paper and later general edge-general-position work, including Tian-Klavžar-Tan 2024 on extremal edge general position sets, Cao-Ji-Wang 2025 on some graphs, Cao-Ji 2025 on cactus graphs, and a 2026 graph-products/ILP article, but no inspectable closure of this Fibonacci-cube equality. This is not a proof of openness; it is a bounded freshness baseline requiring citation-database and author-page review before outreach.

**Omega fit detail.** Strong automath fit: Γ_n can be represented by no-consecutive-1 binary words, already aligned with Fibonacci-word/count infrastructure and finite graph/path modules. The target separates into finite certificate generation for small n, Θ-class coordinate lemmas, shortest-path/geodesic predicates in induced hypercube subgraphs, and a possible recursive upper-bound proof using Γ_n = 0Γ_{n-1} ∪ 10Γ_{n-2}. Omega can contribute both executable certificates and formalizable lemmas about Fibonacci strings, Θ-classes, and geodesic edge triples.

**Attack plan.**
1. Implement a finite model of Γ_n with vertices as no-consecutive-1 bitstrings, edges labeled by flipped coordinate, and a checker for whether three selected edges lie on a common shortest path.
2. Run exact maximum edge-general-position searches for n up to the largest feasible range using ILP/SAT/branch-and-bound, record gp_e(Γ_n), extremal families, and dual upper-bound certificates where possible.
3. Use the 0Γ_{n-1} ∪ 10Γ_{n-2} decomposition and Θ-class structure to search for a recursive upper-bound proof that every edge-general-position set has size at most 2F_n.

**Deliverables.**
- tools/community-outreach/targets/arxiv_2304_10114/research.md
- tools/community-outreach/targets/arxiv_2304_10114/results.json
- tools/community-outreach/targets/arxiv_2304_10114/submission_draft.md

_Inbox graduation rationale_: This should enter the board because it is a named, public, inspectable conjecture in a peer-reviewed Fibonacci/Lucas-cube paper, the statement is crisp and certificate-friendly, the expected exact value is small enough to support meaningful finite verification, and the mathematical objects match Omega's graph and Fibonacci-combinatorics strengths. The main risk is freshness: later edge-general-position literature exists, so operator approval must include a final citation audit.

---

### T-29 · Perfect codes in the 111-free Fibonacci cube

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-12T02:41:42+00:00 · rc=0 · science_gate=WRITEBACK_READY |
| Source | https://arxiv.org/abs/1801.04106 |
| Type | arxiv followup |
| Untouched | Public source is Mollard arXiv:1801.04106, submitted 2018-01-12, which proves existence for Γ_n(1^s) when n=2^p-1 and s >= 3*2^(p-2) and explicitly leaves minimum-s/existence questions open. Freshness check on 2026-05-11: exact public searches for "Γ_n(1^3)"/"Gamma_n(1^3)" + "perfect code", "111" + "generalized Fibonacci cube" + "perfect code", and "minimum s" + "perfect code" + "Gamma_n(1^s)" found Mollard 2018, the 2022 generalized Lucas-cube followup, and related cube-recognition/Padovan material, but no public classification of the s=3 line. Before any external send, rerun arXiv, Google Scholar/Semantic Scholar, zbMATH/MathSciNet if available, and exact phrase web search for the same target. |
| Omega fit | 8/10 |
| Topic value | 8/10 |
| Effort est | 14-21 天 |
| Risk | med |
| Final display | Short research note plus reproducible exact-cover/SAT certificate package for graph theorists working on Fibonacci cubes and perfect codes |
| Success gate | Operator approval only after either a proved classification of all n for Γ_n(111), or a genuinely new infinite family/nonexistence theorem with reproducible code, certificates for the finite base cases, and an independently reviewable proof sketch. No author email or public post before this gate. |

**Statement.** Classify the integers n >= 0 for which Γ_n(111), the induced subgraph of the n-cube on binary strings with no substring 111 and edges between strings at Hamming distance 1, admits a 1-perfect code, equivalently an efficient dominating set whose closed neighborhoods partition V(Γ_n(111)).

**Prior.** Baseline sources: Ashrafi-Azarija-Babai-Fathalikhani-Klavzar proved ordinary Fibonacci cubes Γ_n(11) have perfect codes iff n <= 3 in Information Processing Letters 116(5), 2016. Mollard, arXiv:1801.04106 submitted 2018-01-12 and published as IPL 140, 2018, proves an infinite family for Γ_n(1^s) at n=2^p-1 and s >= 3*2^(p-2), while the public abstract and ScienceDirect page frame generalized Fibonacci cubes as the followup to the 2016 open problem. A 2022 Mollard Lucas-cube paper cites this as precedent and treats the analogous Lucas setting, not the Γ_n(111) classification. Search freshness on 2026-05-11 found no public paper closing the s=3 line; this is not a proof of untouchedness and must be rechecked before outreach.

**Omega fit detail.** Strong fit for Omega-style finite-state combinatorics: vertices are accepted words of a 3-state no-111 DFA, adjacency is one-bit Hamming flip preserving the regular language, and the perfect-code condition is an exact cover by closed neighborhoods. This can be attacked by certified finite search, transfer matrices over boundary states, and a Lean handoff formalizing Γ_n(111), closed neighborhoods, exact-cover certificates, and any recurrence/proof obligations.

**Attack plan.**
1. Implement the no-111 DFA and generate Γ_n(111) with closed neighborhoods; solve exact-cover/SAT/ILP instances for n through the largest feasible bound, storing solver logs and independently checkable certificates.
2. Extract structural data by boundary state: codeword prefix/suffix states, domination counts, residue constraints, and transfer-matrix obstructions; infer candidate periodic families or eventual nonexistence recurrences.
3. Prove the inferred classification by a finite-state dynamic program or recurrence whose local transitions are auditable, then formalize the graph definition and certificate checker enough for an operator to verify finite base cases and recurrence coverage.

**Deliverables.**
- tools/community-outreach/targets/arxiv_1801_04106/research.md
- tools/community-outreach/targets/arxiv_1801_04106/results.json
- tools/community-outreach/targets/arxiv_1801_04106/submission_draft.md

_Inbox graduation rationale_: The target is concrete, inspectable, and close to existing graph-code literature without duplicating an existing board item. It has a clean automath bridge: regular languages, induced hypercube subgraphs, exact covers, and certificate checking. The main risk is freshness, so the profile requires a bounded literature audit before outreach and no external send without operator approval.

---

### T-30 · Fibonacci-run fixed-degree spectrum

| field | value |
|---|---|
| Status | **Pending User Approval** — research_loop completed 2026-05-12T07:05:49+00:00 · rc=0 · science_gate=WRITEBACK_READY |
| Source | https://arxiv.org/abs/2010.05521 |
| Type | open problem / author question |
| Untouched | Inspectable source: arXiv:2010.05521 was submitted 2020-10-12 and the journal version 'Fibonacci-run graphs II: Degree sequences' lists Conjecture 6.7 and Question 10.1. Freshness bound from public search on 2026-05-12: visible later Fibonacci-run papers found address radius/center (2023), diameter conjecture barriers (2025), and cube polynomials (2025), not the fixed-degree count. Before any outreach, re-check MathSciNet, zbMATH, Google Scholar citing papers, and exact-title/web searches for 'Fibonacci-run graph degree k', 'Conjecture 6.7', and 'Question 10.1'. |
| Omega fit | 8/10 |
| Topic value | 7/10 |
| Effort est | 7-14 天 |
| Risk | med |
| Final display | Short research note and author email with a transfer-matrix derivation, reproducible code/certificate, p_k(t) table for small k, and a proof of the denominator and degree bound for fixed k. |
| Success gate | Operator approval/send only after the construction reproduces Examples 6.3-6.6 and Theorem 6.8 from the paper, a minimized or independently checkable automaton/transfer matrix is attached, and a second freshness pass finds no published solution to Conjecture 6.7 or Question 10.1. |

**Statement.** Let a_{n,k}=#{v in V(R_n): deg_{R_n}(v)=k} for the Fibonacci-run graph R_n. Prove, for every fixed k>=0, that A_k(t)=sum_{n>=0} a_{n,k} t^n has the form p_k(t)/(1-t^2)^{k+1}, where p_k(t) is an explicitly computable polynomial of degree (15k+8)/2 for even k and (15k+7)/2 for odd k, and give an algorithm or closed description for p_k(t), thereby answering Question 10.1 and proving Conjecture 6.7 of arXiv:2010.05521.

**Prior.** Primary source is arXiv:2010.05521, submitted 2020-10-12, with journal version in Discrete Applied Mathematics 300 (2021), 56-71, DOI 10.1016/j.dam.2021.05.018. The source explicitly states Conjecture 6.7 after Examples 6.3-6.6 and asks Question 10.1 in Section 10. Public search on 2026-05-12 found related later work on radius/center, diameter barriers, Lucas-run graphs, and cube polynomials, but no visible fixed-degree spectrum closure; this is a bounded public-web prior, not a substitute for MathSciNet/zbMATH/Google Scholar freshness before outreach.

**Omega fit detail.** Good automath/Omega fit because the target reduces to regular-language enumeration of binary words with local run constraints and flip-legality annotations. The exploratory bridge is to encode run-constrained words, up/down flip legality, and degree marking as a finite-state weighted automaton, then export a rational generating-function certificate plus independent enumeration checks. Formal proof integration can remain separate from outreach until the automaton invariant and coefficient extraction are stable.

**Attack plan.**
1. Extract the exact degree-enumerator generating function from Theorem 6.1 and reproduce the published small-k examples by symbolic differentiation or coefficient extraction.
2. Build an independent finite-state grammar for run-constrained words with boundary annotations for legal 0-to-1 and 1-to-0 flips, producing a weighted transfer matrix for F(t,x)=sum_{n,v} x^{deg(v)} t^n.
3. Prove that fixed-k coefficient extraction yields denominator (1-t^2)^{k+1}, derive the stated numerator degree bound, and generate p_k(t) tables plus brute-force checks for n,k in a reviewer-sized range.

**Deliverables.**
- tools/community-outreach/targets/arxiv_2010_05521/research.md
- tools/community-outreach/targets/arxiv_2010_05521/results.json
- tools/community-outreach/targets/arxiv_2010_05521/submission_draft.md

_Inbox graduation rationale_: This is a real, inspectable author question with an exact target, a natural finite-state/rational-generating-function route, and a clear verification loop. It is small enough for an outreach packet, but still mathematically substantive because it turns a conjectural fixed-degree spectrum into an explicit uniform algorithm and proof.

---
