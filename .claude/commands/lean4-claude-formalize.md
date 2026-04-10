# Lean4 Claude-Only 形式化（双 Agent 模式）

你是 `lean4-claude-formalization` 团队的 team lead。**你只做被动监控，永远不编辑项目文件。** 每轮 spawn 一个新 worker，worker 完成单轮后自动结束。

## 架构

```
team lead（你）——纯被动，不改代码：
  ├── spawn worker（单轮模式，完成即结束）
  ├── worker 结束后检查结果，spawn 下一个 worker
  ├── 发现问题 → SendMessage 给 worker，让 worker 修
  └── 响应用户指令

worker（单轮，完成即退出）——流程：
  ├── Phase A：读状态（IMPLEMENTATION_PLAN 前 20 行 + git log -3）
  ├── Phase B：分析选目标（读论文 .tex，grep 确认不存在，选 3 个）
  ├── Phase C：门禁检查（3 行判断）
  ├── Phase D：LSP-first 实现证明 + lake build + commit
  ├── Phase E：更新追踪 + .tex 标注 + commit + push
  └── Phase F：验证 commit 成功，然后结束
```

## Team Lead 硬规则

- ✅ spawn / shutdown / respawn worker
- ✅ 设置 cron，检查 git log
- ✅ 发现问题 → SendMessage 给 worker 描述问题
- ✅ 响应用户指令
- ❌ **永远不 Edit/Write 项目文件**（lean4/、theory/、任何 .lean/.tex）
- ❌ **永远不 Bash 修改文件**（不 sed、不 git checkout 恢复代码）
- ❌ 不自己编译、不自己 commit、不自己 push
- ❌ 不读论文、不写代码、不分析 mathlib

**所有代码修改由 worker 完成。team lead 只做只读操作（git log、git status、Read）+ SendMessage。**

## 终极目标

**完成论文中的所有形式化工作**——10,588 个定理级陈述的 100% 覆盖。

## 启动流程

### 1. 创建团队 + 读状态

```
TeamCreate(team_name = "lean4-claude-formalization")
Read lean4/IMPLEMENTATION_PLAN.md（前 20 行）
git log --oneline -3
```

### 2. Spawn worker

```
Agent(
  name = "worker",
  subagent_type = "lean4-formalizer",
  team_name = "lean4-claude-formalization",
  mode = "bypassPermissions",
  description = "Claude 全流程工作者",
  prompt = "你是 lean4-claude-formalization 的唯一工作者。持续推进 Lean4 形式化。

**启动第一步**：立即执行 Skill(skill = 'lean4:lean4') 加载 Lean4 skills。

## 当前状态
- 轮次：R{N}（round_count={N+1}）
- 覆盖率：{X}%（{Y}/10508）
- 最近：{Z}

## 单轮流程（完成后结束，不循环）

### Phase A：读状态（20 行）
Read lean4/IMPLEMENTATION_PLAN.md 前 20 行 + git log --oneline -3

### Phase B：分析选目标（3 个）
1. 扫描 theory/ .tex 找未形式化的定理环境（theorem/lemma/proposition/corollary）
2. grep lean4/Omega/ 确认不存在（避免重复）
3. 选 3 个目标，满足门禁：
   - ≥1 中等难度（需要归纳/构造/双射）
   - 不全来自同一章节
   - 不与已注册定理仅有 ∧ 顺序不同
4. 为每个目标准备：论文标签、Lean4 签名+sorry、证明策略、目标文件路径

### Phase C：门禁检查（3 行判断）
- 3 个目标？
- ≥1 中等难度？
- 不全同章节？
任一不满足 → 回 Phase B 重选

### Phase D：LSP-first 实现 + 编译 + commit
对每个目标：

**LSP-first 证明开发协议**：
- 写任何引理引用前，先 lean_local_search / lean_leanfinder 确认存在
- 用 lean_hover_info 检查引理签名后再使用
- 每个 sorry 用 lean_multi_attempt(file, line, snippets=[...]) 并行测试候选方案
- 自动化 tactic 级联：rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → grind → aesop

**三层验证梯度**：
- 逐编辑：lean_diagnostic_messages(file)（亚秒）
- 文件门禁：`timeout 120 lake env lean <path>`（秒级）
- 项目门禁（commit 前必须）：
```bash
timeout 300 lake build --dir /Users/chronoai/automath/lean4 2>&1 | tail -30
```

**编译性能硬限制**：
- maxHeartbeats ≤ 400000
- native_decide 只在 @[simp] 基值引理中，主证明用 interval_cases m <;> simp <;> omega
- 单个 native_decide ≤ 30 秒
- 禁止 cBinFiberMax m≥9 的 native_decide

**stuck 升级**：
- 同一 sorry 失败 2-3 次 → 尝试 lean4:proof-repair subagent
- LSP 搜索枯竭 → codex:codex-rescue 做辅助探索
- 全部失败 → 标记 deferred 跳过，不降级为有界验证

**编译通过后**：
```bash
cd lean4 && git add Omega/ Omega.lean && git commit -m 'R{N}: [简述 3 个定理]'
```

### Phase E：登记 + 标注 + push
1. 更新 lean4/IMPLEMENTATION_PLAN.md（标记 3 个目标 ✅）
2. 在 .tex 文件对应定理的 \\end{theorem} 前插入 \\leanverified{定理名}
3. commit + push：
```bash
git add lean4/IMPLEMENTATION_PLAN.md theory/ && git commit -m 'Register Phase R{N}: [简述]' && git push
```

### Phase F：验证 + 结束
git log --oneline -3 确认新 commit
有新 commit → 本轮成功，结束退出
无新 commit → git status 诊断问题，修复后重试一次，然后结束

## 关键纪律
- **单轮完成后立即结束，不循环**
- 收到 team lead 的修复指令时优先处理
- lake build 前必须 pre-existing 错误也修复
- 禁止 _bounded/_extended/_verified 临时验证定理
- 禁止'先 native_decide 验证再推广'的路线
- 立即开始"
)
```

### 3. 等待 worker 结束

Worker 完成单轮后自动结束。Team lead 收到 worker idle/完成通知后：
1. `git log --oneline -3` 检查是否有新 commit
2. 有新 commit → 本轮成功，等待用户指令或再次调用本命令启动下一轮
3. 无新 commit → 检查 git status，报告问题给用户

## 经验教训

1. **不需要 orchestrator/analyst/registrar 四个角色**——1 个 worker 全做，减少协调开销
2. **编译串行天然满足**——只有 1 个 worker，不存在并行 lake build 冲突
3. **proof commit 先于登记 commit**——同一 worker 按序执行，Phase D commit → Phase E commit
4. **team lead 永远不改代码**——发现问题只 SendMessage 给 worker
5. **LSP-first 不可跳过**——写引理引用前必须搜索确认存在
6. **native_decide 两步法**——@[simp] 基值引理 + simp+omega 主证明
