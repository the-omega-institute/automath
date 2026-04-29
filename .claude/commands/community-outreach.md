# Community Outreach — 社区定点贡献管线

event-driven 管线：Codex 检索 → 深度研究 → 起草 → Claude review → 用户审核 → 提交。

## 快速启动

```bash
# 全自动检索+研究（停在用户审核）:
python3 tools/community-outreach/outreach_pipeline.py --discover --parallel 2

# 指定库:
python3 tools/community-outreach/outreach_pipeline.py --repo teorth/equational_theories

# 查看状态:
python3 tools/community-outreach/outreach_pipeline.py --status

# 从 Stage C 恢复:
python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --skip-to C
```

## 管线架构（v23）

### Stage A: 检索候选库 (batch)

1. **A1 — Codex 检索** GitHub 搜索（Lean 4 + 关键词，stars<500，近 3 月活跃）
2. **A2 — Codex 初筛** 评估关联度 (1-10)
3. **A3 — Claude review** 确认候选列表
4. 输出: `outreach_state/candidates.json`

### Stage B: 深度数学研究 (per repo, score-gated ≥8, max 5 rounds)

每轮 5 步:
1. **B0 — Claude 规划** content plan + scope 判断
2. **B1 — Codex 读库** 代码 + README + 论文 PDF
3. **B2 — Codex 交叉分析** 深度研究 + 结论链条
4. **B2.5 — Codex 自验证** 用 Python 检查自己的代数
5. **B3 — Claude review** 评分 + action items

Gate: final_score ≥ 8 → Stage C; < 3 连续 3 轮 → SKIP
升级: 2 轮低于 8 → 切换坏例子结构定理驱动模式

### Stage B → 回流 (backflow)

通过研究门禁后自动回流到主论文:
1. Codex 提议章节定位 (body/appendix)
2. Claude 审查定位
3. Codex 生成中文 .tex（执行 BACKFLOW_LANGUAGE_POLICY）
4. **语言门禁**: `verify_backflow_language()` 检测中/英文比例、术语一致性、`\text{且}`
5. Wire 进 main.tex

### Stage C: 起草 issue/PR (per repo, max 2 rounds)

1. **C1 — Codex 起草** issue body（Tolmeton 风格）
2. **C2 — Claude review** 格式 + 准确性 + tone

### Stage D: 用户审核 + 提交

1. 展示草稿给用户
2. 用户 approve / revise / skip
3. `gh issue create` 或 `gh issue comment`

### Future Queue: 深化任务管理

超出当前 scope 的内容进入 future_queue.jsonl:
- 每个 task 必须声明 route: `proof` / `computation` / `hybrid`
- Codex 执行研究 → 生成 Claude review packet
- Claude 终审: `approve_backflow` / `approve_partial` / `needs_revision` / `reject`
- 通过后回流到论文附录

## 安全策略

- **NO_LEAN_EXECUTION_POLICY**: 不运行 lake/lean/elan，不编辑 Lean 文件，只读静态证据
- **Artifact hygiene**: outreach_state/, logs/, drafts/, targets/ 不进入 git
- **BACKFLOW_LANGUAGE_POLICY**: 回流 .tex 必须中文，术语自动修正
- **Outreach tracking**: OUTREACH_LOG.md 追踪所有提交状态（不在 .tex 中标注）

## Codex 日志持久化

所有 Codex 调用可通过 `log_tag` 参数将 prompt 和 output 持久化到 `logs/codex/`:
```
logs/codex/{tag}_{timestamp}.prompt.txt
logs/codex/{tag}_{timestamp}.out.txt
```

## 状态持久化

- 每个 target: `outreach_state/{owner}_{repo}.json`（schema v2）
- Future queue: `outreach_state/future_queue.jsonl`（schema v1）
- 已处理列表: `outreach_state/processed.json`
- Outreach 日志: `OUTREACH_LOG.md`

## 与其他管线的关系

- **形式化管线** (`lean4/scripts/codex_formalize.py`): 并行运行，通过 `\leanverified` 标签在 .tex 中汇合
- **Oracle 管线** (`tools/chatgpt-oracle/oracle_pipeline.py`): 共享 `codex_exec()` 基础设施
- **killo-golden** (`.claude/skills/killo-golden/`): 论文编写规范，outreach 回流内容需遵守

## User Input

$ARGUMENTS
