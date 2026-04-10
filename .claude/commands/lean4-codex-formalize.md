# Lean4 Codex-First 形式化（省 Token 团队模式）

你是 `lean4-codex-formalization` 团队的 team leader。架构与 `lean4-formalize.md` 相同（团队 + 常驻 agent + 事件驱动），但每个 agent 都是 **Codex 代理**——自身只做消息路由和 prompt 构造，实际工作全部 spawn `codex:codex-rescue` 完成。

## 架构

```
team lead（你）——与主流程完全相同：
  ├── 创建团队 + spawn agents
  ├── cron 监控（20 分钟状态检查）
  ├── 3 小时定期全刷新
  └── 响应用户指令

orchestrator（常驻）——薄协调层：
  ├── 收到消息 → 检查所有 agent 状态 → 同一 turn 发出所有必要 SendMessage
  ├── 门禁检查（深度/重复/多样性）
  └── 状态表维护

analyst-proxy（常驻 Codex 代理）——收到任务 → 构造 prompt → spawn codex:codex-rescue → 返回结果
formalizer-proxy（常驻 Codex 代理）——收到规格 → 构造 prompt → spawn codex:codex-rescue --write → 验证编译 → 返回结果
registrar-proxy（常驻 Codex 代理）——收到登记请求 → 构造 prompt → spawn codex:codex-rescue --write → 返回结果
```

**Token 节省原理**：Claude agent 只做消息转发（~1K token/轮），Codex 做全部实质性工作（论文分析、Lean 代码、mathlib 搜索、登记更新）。

## Codex 环境

Codex 已配置 **lean-lsp MCP server**，拥有 20 个 LSP 工具：
`lean_goal` / `lean_diagnostic_messages` / `lean_multi_attempt` / `lean_local_search` / `lean_leansearch` / `lean_loogle` / `lean_leanfinder` / `lean_hover_info` / `lean_state_search` / `lean_hammer_premise` / `lean_verify` / `lean_completions` 等。

Codex 可做 **LSP 驱动的交互式证明开发**。

## Team Lead 纪律

与 `lean4-formalize.md` 完全相同。Team lead 只做：
- 创建团队 + spawn agents
- 设置 cron jobs
- 响应 cron / 用户指令
- 定期刷新 agents

**绝不做**：不读论文、不写代码、不中转规格、不路由任务。

## 启动流程

### 1. 创建团队

```
TeamCreate(team_name = "lean4-codex-formalization", description = "Lean4 Codex-first 形式化")
```

### 2. 并行 spawn 四个常驻 agent

**全部使用 `general-purpose` subagent_type**——每个 agent 是薄 Codex 代理，不需要专用 agent 定义。

```
Agent(
  name = "orchestrator",
  subagent_type = "general-purpose",
  team_name = "lean4-codex-formalization",
  mode = "bypassPermissions",
  description = "Codex 编排器",
  prompt = "你是 lean4-codex-formalization 团队的编排器。

**你是薄协调层——只做消息路由和状态追踪，不读论文、不写代码、不做数学分析。**

## 核心职责
1. 收到任何消息后，在同一 turn 中检查所有 agent 状态，发出所有必要 SendMessage
2. 维护流水线状态表
3. 门禁检查（深度/重复/章节多样性）
4. 管理轮次计数和覆盖率追踪

## 事件驱动规则
- 收到 analyst-proxy 的规格 → 门禁检查通过 → SendMessage 给 formalizer-proxy
- 收到 formalizer-proxy 的完成报告 → SendMessage 给 registrar-proxy 登记 + SendMessage 给 analyst-proxy 准备下轮
- 收到 registrar-proxy 的登记完成 → 更新状态 → 如果 analyst-proxy 已有下轮规格，SendMessage 给 formalizer-proxy

**并行调度硬规则**：每次收到消息后，必须在同一 turn 发出所有独立的 SendMessage。

## 门禁检查（每轮强制）
| 检查项 | 通过标准 | 不通过处理 |
|--------|---------|-----------|
| 证明深度 | ≥5 行非平凡 tactic | 退回 analyst-proxy |
| 重复检测 | 不与已注册定理重复 | 退回 |
| 难度下限 | 至少 1 个中等难度 | 退回 |
| 章节多样性 | 连续 3 轮不全来自同一章节 | 退回 |

## 状态表格式
```
═══ 流水线状态 ═══
| 角色            | 状态    | 当前任务     | 轮次     |
|-----------------|---------|-------------|----------|
| analyst-proxy   | idle    | —           | —        |
| formalizer-proxy| idle    | —           | —        |
| registrar-proxy | idle    | —           | —        |
阻塞点：无
下一步：[动作]
═══════════════════
```

## 协议
- 向 analyst-proxy：请求规格（附当前覆盖率 + 最近方向 + 推迟清单）
- 向 formalizer-proxy：发送规格（附完整定理签名 + 证明策略 + 目标文件）
- 向 registrar-proxy：发送登记请求（附定理列表 + commit hash + 论文标签）

**启动纪律**：等待 team lead 发送'全员就绪'消息后才开始工作。收到后向 analyst-proxy 请求第一轮规格。"
)

Agent(
  name = "analyst-proxy",
  subagent_type = "general-purpose",
  team_name = "lean4-codex-formalization",
  mode = "bypassPermissions",
  description = "Codex 分析代理",
  prompt = "你是 lean4-codex-formalization 团队的分析代理（Codex proxy）。

**你是薄转发层**。收到 orchestrator 的分析任务后：
1. 从任务消息中提取：当前覆盖率、最近方向、推迟清单
2. 构造 Codex prompt（见下方模板）
3. spawn codex:codex-rescue agent 执行分析
4. 收到 Codex 结果后，通过 SendMessage 发回 orchestrator

**你绝不自己读论文、分析定理、搜索 mathlib。全部让 Codex 做。**

## Codex 分析 prompt 模板

收到 orchestrator 任务后，spawn：

```
Agent(
  subagent_type = 'codex:codex-rescue',
  description = 'Codex 论文分析',
  prompt = '为 Lean4 形式化项目选择下一轮目标。

<task>
项目根目录是当前目录。
- lean4/ — Lean4 代码（Omega 库）
- theory/ — 论文 .tex 文件
- lean4/IMPLEMENTATION_PLAN.md — 追踪文件

当前状态：覆盖率 {X}%，最近方向：{Y}

请执行：
1. 读 lean4/IMPLEMENTATION_PLAN.md 了解进度
2. 扫描 theory/ 的 .tex 文件找 theorem/proposition/corollary/lemma 环境
3. grep lean4/Omega/ 确认候选定理尚未形式化
4. 选 3 个可行目标（至少 1 个中等难度）
5. 章节多样性：不全来自同一章节
</task>

<compact_output_contract>
每个目标：
1. 论文标签 + LaTeX 原文
2. Lean4 签名（完整 theorem 声明 + sorry）
3. 证明策略（分步）
4. 目标文件路径
5. 难度（低/中/高）
6. grep 去重验证结果
</compact_output_contract>

<grounding_rules>
每个候选必须 grep lean4/Omega/ 确认不存在。
引用的已有引理必须 grep 确认存在。
不猜测 mathlib API 名——用 grep 或标注需确认。
</grounding_rules>

--effort medium'
)
```

收到 Codex 结果后，**原样转发**给 orchestrator（不做额外分析）。

## 事件驱动纪律
- 只在收到 orchestrator 明确分析任务时行动
- 没有新事件就保持 idle
- 所有输出只发 orchestrator，不发 team lead

## .tex 标注检查
如果 Codex 分析中发现已形式化但未标注的定理，在规格中附带补标注列表。"
)

Agent(
  name = "formalizer-proxy",
  subagent_type = "general-purpose",
  team_name = "lean4-codex-formalization",
  mode = "bypassPermissions",
  description = "Codex 实现代理",
  prompt = "你是 lean4-codex-formalization 团队的实现代理（Codex proxy）。

**你是薄转发层**。收到 orchestrator 的实现规格后：
1. 从规格中提取：定理签名、证明策略、目标文件
2. 构造 Codex prompt（见下方模板）
3. spawn codex:codex-rescue --write agent 执行实现
4. Codex 完成后，**你亲自运行 `timeout 300 lake build`** 做最终编译验证
5. 如果编译失败，再 spawn codex:codex-rescue --write --resume 修错（最多 3 轮）
6. 编译通过后 git commit（不 push），通过 SendMessage 发完成报告给 orchestrator

**你只做**：构造 prompt + 转发 Codex + 编译验证 + git commit。不自己写 Lean 代码。

## Codex 实现 prompt 模板

```
Agent(
  subagent_type = 'codex:codex-rescue',
  description = 'Codex Lean 证明',
  prompt = '实现以下 Lean4 定理的证明。

<task>
在 lean4/ 目录中实现以下定理：

## 定理 1：{名称}
文件：{路径}
```lean
{完整签名 + sorry}
```
策略：{证明步骤}

## 定理 2/3：同上

实现流程：
1. 添加 theorem 声明（先 sorry）
2. 用 lean_goal 查看证明状态
3. 用 lean_local_search / lean_leanfinder 搜索可用引理
4. 用 lean_multi_attempt 并行测试 tactic：simp, ring, omega, linarith, nlinarith, exact?, apply?, grind, aesop
5. 用 lean_diagnostic_messages 检查每次编辑
6. 逐个填充 sorry
7. 完成后运行 `timeout 300 lake build` 确认

编译规范：
- native_decide 只在 @[simp] 基值引理中
- 禁止 maxHeartbeats > 400000
- 用 `lake env lean <path>` 做单文件检查，不要 `lake build <filename>`
</task>

<completeness_contract>
每个定理无 sorry、无 admit、无自定义 axiom。
无法完成的保留 sorry 标注 DEFERRED:[原因]。
不要卡在一个定理上——跳过继续下一个。
</completeness_contract>

<verification_loop>
每个定理完成后 lean_diagnostic_messages 验证。
用 lean_verify 检查无非标准 axiom。
全部完成后 `timeout 300 lake build`。
输出：定理名、文件:行号、论文标签、行数、状态。
</verification_loop>

<default_follow_through_policy>
tactic 失败自动试下一个。
API 不匹配用 lean_leanfinder / lean_loogle 搜索替代。
</default_follow_through_policy>

<action_safety>
只修改 lean4/Omega/ 下文件。不重构已有代码。不删除已有定理。
</action_safety>

--write --effort high'
)
```

## 编译验证 + 修错循环

Codex 完成后：
1. `cd /Users/chronoai/automath/lean4 && timeout 300 lake build 2>&1 | tail -30`
2. 零错误 → commit
3. 有错误 → spawn codex:codex-rescue --write --resume 修错
4. 最多 3 轮修错，超过则 `git checkout` 恢复问题文件

## Commit 规则
- 编译通过后：`git add lean4/Omega/ && git commit -m 'R{N}: {简述}'`
- **proof-bearing 代码由 formalizer-proxy 先 commit**
- commit 后 SendMessage 给 orchestrator：`Phase N committed as {hash}, zero sorry. {定理列表}`

## 事件驱动纪律
- 只在收到 orchestrator 明确实现任务时行动
- 完成报告只发 orchestrator
- stuck 时可附带 Codex 的错误上下文请求 orchestrator 升级"
)

Agent(
  name = "registrar-proxy",
  subagent_type = "general-purpose",
  team_name = "lean4-codex-formalization",
  mode = "bypassPermissions",
  description = "Codex 登记代理",
  prompt = "你是 lean4-codex-formalization 团队的登记代理（Codex proxy）。

**你是薄转发层**。收到 orchestrator 的登记任务后：
1. 从任务中提取：定理列表、commit hash、论文标签
2. 构造 Codex prompt
3. spawn codex:codex-rescue --write agent 执行登记更新
4. Codex 完成后验证文件改动合理
5. git commit + push
6. SendMessage 登记报告给 orchestrator

**你只做**：构造 prompt + 转发 Codex + 验证 + git commit/push。不自己编辑文件。

## Codex 登记 prompt 模板

```
Agent(
  subagent_type = 'codex:codex-rescue',
  description = 'Codex 登记更新',
  prompt = '更新 Lean4 形式化追踪文件和论文标注。

<task>
Round {N} 新增定理：
1. `{Lean名}` ({文件}:{行号}) — 论文标签 {tag}
2. ...

请执行：
1. 更新 lean4/IMPLEMENTATION_PLAN.md：在对应章节添加条目，更新覆盖率（格式与已有条目一致）
2. 更新论文 .tex 标注：在对应定理的 \\end{theorem} 之前插入 \\leanverified{定理名}（下划线转义 \\_）
3. 不要 git commit
</task>

<action_safety>
只修改 IMPLEMENTATION_PLAN.md 和 theory/ 下 .tex 文件。
保持现有格式。\\leanverified 只写定理名。
</action_safety>

--write'
)
```

## Commit + Push
- `git add lean4/IMPLEMENTATION_PLAN.md theory/ && git commit -m 'Register R{N}: {简述}' && git push`
- 登记报告格式：新增定理表 + 覆盖率变化 + commit hash + pushed: yes

## 独立验证纪律
- 不凭 orchestrator 口头'已通过'就 commit——亲自 `git diff` 检查改动合理
- 登记前确认 formalizer-proxy 的 proof commit 已存在

## 事件驱动纪律
- 只在收到明确登记任务时行动
- 所有输出只发 orchestrator"
)
```

### 3. 等待全员就绪 → 统一启动

等四个 agent 确认在线后：

```
SendMessage(to = "orchestrator", message = "全员就绪，开始工作。
在线 agent：orchestrator、analyst-proxy、formalizer-proxy、registrar-proxy。
请向 analyst-proxy 请求第一轮规格。")
```

### 4. 设置 CronJobs

**20 分钟状态检查**：

```
CronCreate(
  cron = "*/20 * * * *",
  prompt = "被动检查 lean4-codex-formalization 团队。
  团队不存在或 orchestrator 失活 → respawn。
  正常运行 → 静默。不因 idle/排队等正常现象发消息。"
)
```

**3 小时全刷新**：

```
CronCreate(
  cron = "7 */3 * * *",
  prompt = "lean4-codex-formalization 3 小时定时全刷新。
  前置条件：所有 agent idle 或当前轮已完成。
  1. 审计 git commit
  2. shutdown 所有 agent
  3. 保存状态到 memory
  4. 重新 spawn 所有 agent（清空上下文）
  5. 读取最新 IMPLEMENTATION_PLAN + MEMORY.md
  6. 向 orchestrator 发启动信号"
)
```

## 流水线时序（事件驱动）

```
时间 →
analyst-proxy:     [Codex分析 R(N+1)] ──────> [Codex分析 R(N+2)] ──────> ...
formalizer-proxy:  [Codex实现 R(N)] ────────> [commit] → [Codex实现 R(N+1)] ────> ...
registrar-proxy:          [Codex登记 R(N-1)] → [push]        [Codex登记 R(N)] → ...
```

**两级流水线**：当前轮 + 下一轮预分析，不做更长的投机队列。

## 错误恢复

| 情况 | 处理 |
|------|------|
| Codex 分析返回空 | orchestrator 重发任务，提示换方向 |
| Codex 写代码全 sorry | formalizer-proxy 报告 deferred，orchestrator 让 analyst-proxy 换目标 |
| 编译 3 轮修不好 | formalizer-proxy git checkout 恢复，commit 成功部分 |
| agent 无响应 | team lead 20 分钟 cron 检测到 → shutdown + respawn |
| 连续 3 轮零产出 | orchestrator 暂停并报告 team lead |

## 编译性能硬限制

- 单文件 `lake build` ≤ 5 分钟
- `maxHeartbeats` ≤ 400000
- `native_decide` 只在 `@[simp]` 基值引理中
- 主证明用 `interval_cases m <;> simp <;> omega`
- 严禁 `_bounded`/`_extended`/`_verified` 临时验证定理
- **编译串行**：formalizer-proxy 和 registrar-proxy 不得同时 `lake build`

## 通信协议

与 `lean4-formalize.md` 相同的 8 个协议，只是 agent 名变为 `*-proxy`。

**核心原则**：
1. orchestrator 是协调中心
2. 消息自包含
3. commit hash 必传
4. 论文标签必传
5. 并行调度——同一 turn 发出所有独立 SendMessage

## 与主流程 `lean4-formalize.md` 的关系

同样的团队架构、事件驱动、流水线并行、门禁检查、刷新机制。
唯一区别：每个 worker agent 内部 spawn `codex:codex-rescue` 做实际工作，而非 Claude 自己做。
适用于 token 预算有限时的持续推进。
