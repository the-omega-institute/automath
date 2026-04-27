# Community Outreach — 社区定点贡献管线

event-driven 管线：Codex 检索 → 深度研究 → 起草 → Claude review → 用户审核 → 提交。

## 快速启动

```bash
# 全自动检索+研究（停在用户审核）:
python3 tools/community-outreach/outreach_pipeline.py --discover --parallel 2

# 指定库:
python3 tools/community-outreach/outreach_pipeline.py --repo mysticflounder/equational-magma-theorems

# 查看状态:
python3 tools/community-outreach/outreach_pipeline.py --status

# 从 Stage C 恢复:
python3 tools/community-outreach/outreach_pipeline.py --repo owner/name --skip-to C
```

## 五阶段架构

### Stage A: 检索候选库 (batch, 不循环)

1. **A1 — Codex 检索** GitHub 搜索
   - 关键词: Lean 4 + (fibonacci|golden ratio|symbolic dynamics|zeckendorf|equational|formal verification|AI theorem proving)
   - 过滤: language=Lean, stars<500, 近 3 月有活跃 commit
   - 排除: Mathlib (太大), 已处理过的库
2. **A2 — Codex 初筛** 评估每个库与 Automath 的关联度 (1-10)
3. **A3 — Claude review** 确认候选列表
4. 输出: `outreach_state/candidates.json`

Gate: 至少 1 个候选 → 每个候选进入 Stage B

### Stage B: 深度数学研究 (per repo, score-gated ≥8)

每轮 4 步:
1. **B1 — Codex 读库** 代码 + README + 论文 PDF（如有）
2. **B2 — Codex 交叉分析**
   - 继续深入研究, 结合 Automath 论文分析
   - 找有发表价值的惊艳结论链条 (禁止同义表述)
   - 发现定理、推论、猜想、命题及证明
   - 可以使用他人结论, 不要中间过程
   - 顶级数学期刊学术化语言, 禁止口语
   - 不重复已公开发表内容
3. **B3 — Codex 自评** 1-10 分 (JSON)
4. **B4 — Claude review** 评价数学正确性 + 新颖性, 取 min(codex, claude)

Gate: final_score ≥ 8 → Stage C; 否则循环 (最多 3 轮)
Gate: final_score < 5 连续 2 轮 → 跳过此库

### Stage C: 起草 issue/PR (per repo)

每轮 2 步:
1. **C1 — Codex 起草** issue body
   - Tolmeton 风格: 精确对应表, 诚实标注 proved/conjectured/untested
   - 包含: Lean 4 定理引用 (file:line), 证明草图, 数学联系
   - 末尾附 `**Repo:** https://github.com/the-omega-institute/automath`
2. **C2 — Claude review** 格式 + 准确性 + tone
   - 不能是自我推销, 必须是技术贡献
   - 数学必须正确
   - 引用的 Lean 4 定理必须存在且 statement 正确

Gate: approved → Stage D; 否则循环 (最多 2 轮)

### Stage D: 用户审核 + 提交 (per repo)

2 步, 不循环:
1. **D1 — 展示给用户**
   - 目标库, issue 标题, issue body 全文
   - 用户选择: approve / revise / skip
2. **D2 — 提交**
   - `gh issue create --repo owner/name --title "..." --body "..."`
   - 记录提交结果到 state

### Stage E: 跟踪回复 (定期, 可选)

1. **E1 — 检查回复** `gh api repos/owner/name/issues/N/comments`
2. **E2 — 如果有回复, 通知用户**
3. **E3 — 如果对方邀请 PR, 进入 PR 起草流程**

## 状态持久化

每个候选库的状态存在 `outreach_state/{owner}_{repo}.json`:
- stage, round, scores, findings, draft, submission URL
- action history (最近 30 条)

已处理库列表: `outreach_state/processed.json`

## 事件驱动流转

```
Stage A (batch)              Stage B (score loop, per repo)
  A1: codex search             B1: codex read repo
  A2: codex filter             B2: codex cross-analysis
  A3: claude review            B3: codex self-score
  → candidates.json            B4: claude review
                                Gate: ≥8? ──yes──→ Stage C
                                     └──no──→ B1

Stage C (draft loop)         Stage D (user gate)
  C1: codex draft issue         D1: present to user
  C2: claude review             D2: gh issue create
  Gate: approved? ──yes──→           → DONE
  └──no──→ C1
```

## 与 Oracle 管线的关系

- 共享 `codex_exec()` 基础设施
- 共享 `parse_json_from_output()`, `git_commit()` 工具函数
- 独立状态目录 (`outreach_state/` vs `pipeline_state/`)
- 不依赖 Oracle server (无需 ChatGPT Pro)

## User Input
