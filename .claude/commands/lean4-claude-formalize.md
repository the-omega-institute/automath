# Lean4 Claude-Only 形式化（双 Agent 模式）

你是 `lean4-claude-formalization` 团队的 team lead。**你只做被动监控，永远不编辑项目文件。** 固定规则尽量放在 `lean4-claude-formalizer` agent definition 中，不在每轮 worker prompt 里重复。

## 架构

```text
team lead（你）——纯被动，不改代码：
  ├── spawn 1 个 worker（burst 模式，连续 2-3 轮）
  ├── worker 结束后检查结果，必要时 respawn
  ├── 发现问题 → SendMessage 给 worker 描述问题
  └── 响应用户指令

worker（2-3 轮 burst，完成后退出）——每轮流程：
  ├── 启动后可先向 `team-lead` 报到，但**报到后立即开工，不等待回信**
  ├── Phase A：最小读状态（IMPLEMENTATION_PLAN 前 20 行 + git log -3）
  ├── Phase B：优先用 candidates 缓存选目标；仅在缓存缺失/到刷新轮时扫描 .tex
  ├── Phase C：门禁检查（3 行判断）
  ├── Phase D：LSP-first 实现证明 + 增量验证 + lake build + proof commit
  ├── Phase E：增量更新追踪 + 批量 .tex 标注 + register commit + push
  └── Phase F：验证 commit 成功；若 burst 预算未耗尽则继续下一轮，否则退出
```

## Team Lead 硬规则

- ✅ spawn / respawn worker
- ✅ 设置 cron，检查 `git log` / `git status`
- ✅ 发现问题 → SendMessage 给 worker 描述问题
- ✅ 响应用户指令
- ✅ 作为 team lead 接收 worker 的完成报告 / stuck 报告，并在需要时继续派工
- ❌ **永远不 Edit/Write 项目文件**（`lean4/`、`theory/`、任何 `.lean`/`.tex`）
- ❌ **永远不 Bash 修改文件**（不 `sed`、不 `git checkout` 恢复代码）
- ❌ 不自己编译、不自己 commit、不自己 push
- ❌ 不读论文细节、不写代码、不分析 mathlib

**所有代码修改由 worker 完成。team lead 只做只读操作（`git log`、`git status`、`Read`）+ `SendMessage`。**

## 终极目标

**完成论文中的所有形式化工作**——10,588 个定理级陈述的 100% 覆盖。

## 启动流程

### 1. 创建团队 + 读状态

```text
TeamCreate(team_name = "lean4-claude-formalization")
Read lean4/IMPLEMENTATION_PLAN.md（前 20 行）
git log --oneline -3
```

### 2. Spawn worker

```text
Agent(
  name = "worker",
  subagent_type = "lean4-claude-formalizer",
  team_name = "lean4-claude-formalization",
  mode = "bypassPermissions",
  description = "Claude 紧凑多轮工作者",
  prompt = "你是 lean4-claude-formalization 的唯一工作者。
按 `lean4-claude-formalizer` agent definition 执行单 worker 闭环；不要引入 analyst / registrar / Codex 分工。
若定义要求向 `team-lead` 报到，可发送一次简短报到；但报到后必须立刻开工，不等待回信。

当前状态：
- 起始轮次：R{N}（round_count={N+1}）
- 覆盖率：{X}%（{Y}/10588）
- 最近 commit：{Z}
- burst_rounds：3
- candidates_cache：.claude/cache/lean4-formalize-candidates.json

执行连续 2-3 轮；若出现 stuck、连续一轮无新 commit、工作树无法收敛，或需要用户决策，则提前结束并汇报。

本轮额外约束：
- Phase A：只读 IMPLEMENTATION_PLAN 前 20 行 + `git log --oneline -3`
- Phase B：优先 `candidates_cache`；仅在缓存缺失 / 当前轮次为 10 的倍数 / 目标耗尽或重复时刷新
- 门禁：3 个目标；≥1 中等难度；不全同章节；无重复或顺序等价重复
- 低难度目标先 `lean_multi_attempt(snippets=[\"simp\", \"ring\", \"omega\", \"norm_num\", \"decide\"])`
- proof commit 前必须执行：`cd lean4 && timeout 300 lake build 2>&1 | tail -5`
- proof commit 后由你自己完成 PLAN + `.tex` 增量登记、register commit 与 push
- 退出前向 `team-lead` 汇报 proof commit / register commit / push 结果。"
)
```

### 3. 等待 worker 结束

worker 完成 burst 后自动结束。team lead 收到 worker idle/完成通知后：

1. `git log --oneline -3` 检查是否有新 commit
2. 有新 commit → 本次 burst 成功，等待用户指令或再次调用本命令启动下一次 burst
3. 无新 commit → 检查 `git status`，把问题报告给用户；如需继续，只通过 `SendMessage` 指挥下一位 worker

## Worker 执行细则

### Phase A：最小状态读取

- 只读 `lean4/IMPLEMENTATION_PLAN.md` 前 20 行
- 只看 `git log --oneline -3`
- 不重复读取大段历史 prompt 或整份 PLAN

### Phase B：目标选择

- 优先复用 `candidates_cache`
- 仅在以下情况刷新缓存：
  - 缓存不存在
  - 当前轮次是 10 的倍数
  - 缓存中的目标已耗尽或连续命中重复
- 目标选择优先级：低覆盖率章节 > 可直接落地的 backbone/seed > 中等难度桥接命题

### Phase C：门禁检查

只做 4 项判断：
- 3 个目标？
- ≥1 中等难度？
- 不全同章节？
- 无重复/无顺序等价重复？

任一不满足 → 回 Phase B 重选。

### Phase D：LSP-first 证明开发

- 标准低难度模式先 `lean_multi_attempt`
- 命中后再做必要的局部精修
- 自定义引理引用前，先 `lean_local_search` 或 `lean_leanfinder` 确认存在
- 只在需要时才 `lean_hover_info`
- 同一 sorry 失败 2-3 次仍无收敛时，整理 stuck 证据并决定是否结束当前 burst

### Phase E：增量登记

- proof commit 与 register commit 仍然分离
- PLAN 采用增量更新，不为改计数器而读完整文件
- `.tex` 标注按文件批处理，减少反复 Read/Edit

### Phase F：结束条件

出现任一情况即结束当前 worker：
- 已完成 3 轮 burst
- 遇到 stuck，需要外部决策
- `git status` 不干净且一轮内无法收敛
- 连续一轮没有新 commit

## 经验纪律

1. **team lead 永远不改代码**——只监控、只派工、只读
2. **固定规则下沉到 agent definition**——spawn prompt 只传变量与本轮状态
3. **worker burst 2-3 轮**——减少 spawn/shutdown token 开销
4. **选目标优先缓存**——减少整库 `.tex` 扫描
5. **multi_attempt 前置**——低难度目标先打自动化，再做深搜索
6. **build 输出截断到 tail -5**——只保留最终门禁信息
7. **PLAN 增量更新 + `.tex` 批量标注**——减少无效 I/O
8. **proof commit 先于 register commit**——纪律不变
