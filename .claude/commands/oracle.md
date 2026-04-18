# ChatGPT Oracle — 四阶段自动论文审稿管线

四阶段条件循环管线：Codex 研究优化 → Oracle 审稿 → Claude 终审 → 回流主论文。

## 前置条件

1. `oracle_server.py` 运行中: `python tools/chatgpt-oracle/oracle_server.py &`
2. Tampermonkey 脚本 `chatgpt_oracle.user.js` 已安装
3. ChatGPT Pro 标签页已打开

## 快速启动

```bash
# 单篇论文:
python3 tools/chatgpt-oracle/oracle_pipeline.py \
  --paper theory/2026_xxx/ \
  --target-journal "Advances in Mathematics" \
  --main-paper theory/2026_golden_ratio.../

# 所有论文, 2 路并发:
python3 tools/chatgpt-oracle/oracle_pipeline.py --all --parallel 2

# 查看状态:
python3 tools/chatgpt-oracle/oracle_pipeline.py --status

# 从 Stage B 恢复:
python3 tools/chatgpt-oracle/oracle_pipeline.py --paper theory/2026_xxx/ --skip-to B

# 预览模式:
python3 tools/chatgpt-oracle/oracle_pipeline.py --dry-run --all
```

## 四阶段架构

### Stage A: Codex 深度研究 + 期刊风格（score-gated, ≥8 pass）

每轮 4 步:
1. **A1 — Codex 深度研究** → commit
   - 深入研究补全论文到编辑可接收水准
   - 找有发表价值的惊艳结论, 不挤牙膏
   - 不重复已发表推理, 可引用他人结论
2. **A2 — Codex 期刊风格优化** → commit
   - 按目标期刊最近收录论文学习语言风格
   - 全面优化行文/用语/逻辑递进/appendix比例
   - 追求"人话感", 去 AI 味
3. **A3 — Codex 自评** 1-10 分 (JSON 输出)
4. **A4 — Claude review** 评价, 取 min(codex, claude) 分

Gate: final_score ≥ 8 → Stage B; 否则循环 (最多 5 轮)

### Stage B: Oracle 审稿（accept-gated）

每轮 5 步:
1. **B1 — 编译 PDF** → commit
2. **B2 — Oracle editorial review** → EVENT WAIT (ChatGPT Pro)
3. **B3 — 解析 verdict** + issues
4. **B4 — Codex fix** issues → commit
5. **B5 — Claude review** fixes → commit

Gate: verdict = Accept → Stage C; 否则循环 (最多 4 轮)

### Stage C: Claude 独立审阅（approval-gated）

每轮 2 步:
1. **C1 — Claude 独立审阅** → 返回 submit/revise
2. **C2 — Codex fix** issues → commit

Gate: verdict = submit → Stage D; 否则循环 (最多 4 轮)

### Stage D: 回流主论文

4 步, 不循环:
1. **D1 — Codex 检查回流候选** (JSON 输出)
2. **D2 — Claude review** 回流方案 (approve/reject)
3. **D3 — 修改主论文** → commit
4. **D4 — Claude 验证** → commit

## 轮次追踪

每篇论文的状态持久化在 `pipeline_state/{name}.json`:
- 每个 Stage 的轮数、评分历史、verdict 历史
- 全部 action history (最近 50 条)
- 可通过 `--status` 查看汇总

## 事件驱动流转

```
Stage A (score loop)          Stage B (accept loop)
  A1: codex research            B1: compile PDF
  A2: codex style               B2: oracle review ← EVENT WAIT
  A3: codex score               B3: parse verdict
  A4: claude review             B4: codex fix
  Gate: ≥8? ──yes──→            B5: claude review
       └──no──→ A1              Gate: accept? ──yes──→
                                     └──no──→ B1

Stage C (submit loop)         Stage D (backflow)
  C1: claude review              D1: codex check
  Gate: submit? ──yes──→         D2: claude review
  C2: codex fix                  D3: apply changes
  └──→ C1                        D4: claude verify
                                      → DONE
```

## 手动单次任务

```bash
# 直接提问:
python tools/chatgpt-oracle/oracle_ask.py "Review this paper" --pdf paper.pdf

# 指定任务类型:
python tools/chatgpt-oracle/oracle_dispatch.py --paper theory/2026_xxx/ --task editorial_review --wait
```

任务类型: `editorial_review` | `deep_research` | `literature_search` | `proof_verification` | `journal_fit`

## User Input
