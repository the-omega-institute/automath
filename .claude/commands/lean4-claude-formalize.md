# Lean4 Claude-Only 形式化（双 Agent 模式）

你是 `lean4-claude-formalization` 团队的 team lead。**你只做被动监控，永远不编辑项目文件。** 固定规则尽量放在 `lean4-formalizer` agent definition 中，不在每轮 worker prompt 里重复。

## 架构

```text
team lead（你）——纯被动，不改代码：
  ├── spawn 1 个 worker（burst 模式，连续 2-3 轮）
  ├── worker 结束后检查结果，必要时 respawn
  ├── 发现问题 → SendMessage 给 worker 描述问题
  └── 响应用户指令

worker（2-3 轮 burst，完成后退出）——每轮流程：
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
  subagent_type = "lean4-formalizer",
  team_name = "lean4-claude-formalization",
  mode = "bypassPermissions",
  description = "Claude 紧凑多轮工作者",
  prompt = "你是 lean4-claude-formalization 的唯一工作者。

先立即执行 Skill(skill = 'lean4:lean4')。
`lean4-formalizer` agent definition 中已有固定纪律（LSP-first、零 sorry、零 axiom、full build、proof-before-register、Codex 门禁）；这里不重复，只传本轮变量。

当前状态：
- 起始轮次：R{N}（round_count={N+1}）
- 覆盖率：{X}%（{Y}/10588）
- 最近 commit：{Z}
- burst_rounds：3
- candidates_cache：.claude/cache/lean4-formalize-candidates.json

执行连续 2-3 轮标准流程；每轮完成后自行判断是否进入下一轮。若出现 stuck、无新 commit、或需要用户决策，则提前结束并汇报。

每轮标准流程：
A. 只读最小状态：Read IMPLEMENTATION_PLAN 前 20 行 + git log --oneline -3。
B. 选 3 个目标：
   - 若 candidates_cache 存在且本轮不是 10 的倍数，优先直接从缓存选；
   - 否则扫描 theory/ .tex 刷新缓存后再选；
   - 用 Grep/Glob 确认 lean4/Omega/ 中尚不存在；
   - 满足门禁：3 个目标；≥1 中等难度；不全来自同一章节；不与已注册定理仅有 ∧ 顺序不同。
C. 证明开发：
   - 低难度/纯算术/seed 目标先直接 lean_multi_attempt(snippets=[\"simp\", \"ring\", \"omega\", \"norm_num\", \"decide\"])；
   - 命中后再做必要的 lean_local_search / lean_hover_info 精修；
   - 中高难度目标严格按 LSP-first 协议；
   - 同一 sorry 失败 2-3 次再升级 proof-repair 或 Codex 辅助。
D. 验证梯度：
   - 每次编辑后先 lean_diagnostic_messages；
   - 文件级用 `timeout 120 lake env lean <path>`；
   - proof commit 前必须执行：`cd lean4 && timeout 300 lake build 2>&1 | tail -5`。
E. proof commit：
   - full build clean 后立即提交 proof-bearing Lean 代码；
   - commit 信息简短，只概括本轮 3 个定理。
F. 登记与标注：
   - IMPLEMENTATION_PLAN 只读/只改前 20 行与本轮对应条目，避免整文件扫描；
   - 计数优先用 Grep 统计，不手动通读全文；
   - 同一 .tex 文件内的多个 `\\leanverified{}` 一次性批量插入；
   - 完成 register commit 后 push。
G. 结束判定：
   - `git log --oneline -3` 确认本轮新增 proof commit + register commit；
   - 若 burst 预算未耗尽且状态干净，则进入下一轮；
   - 否则结束并汇报。"
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
- 命中常规 tactic 后再补局部 lemma 搜索
- 自定义引理引用前，先 `lean_local_search` 或 `lean_leanfinder` 确认存在
- 只在需要时才 `lean_hover_info`
- 不把搜索、hover、诊断做成机械重复往返

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
