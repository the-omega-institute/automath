# Lean4 形式化流水线 Token 优化报告

> 基于 R625-R636 连续 12 轮实测数据（2026-04-11）

## 1. 当前消耗概况

| 指标 | 数值 |
|---|---|
| 会话轮次 | R625-R636（12 轮） |
| 平均轮次耗时 | ~10 分钟 |
| 每轮产出 | 3 个论文定理（含子定理 5-17 个） |
| 每轮标注增量 | 3-14 个 \leanverified |
| lake build jobs | 3511→3537（递增） |

### Token 消耗分布（估算）

| 阶段 | 占比 | 说明 |
|---|---|---|
| Worker prompt（含指令+状态） | ~15% | 每轮 spawn 新 worker，重复发送完整指令 |
| Phase B 论文扫描 | ~20% | 读 .tex 文件、grep 确认、选目标 |
| Phase D 证明开发 | ~35% | LSP 调用、multi_attempt、编辑、诊断 |
| Phase E 登记标注 | ~15% | 更新 IMPLEMENTATION_PLAN、编辑 .tex |
| Team lead 开销 | ~10% | spawn/shutdown 消息、状态跟踪 |
| Skill 加载 + Phase A | ~5% | lean4:lean4 skill + 读 PLAN 前 20 行 |

## 2. 高 ROI 优化策略

### 2.1 压缩 Worker Prompt（预计节省 10-15%）

**问题**：每轮 spawn 新 worker 时，完整 prompt 包含 ~2000 token 的指令模板，其中大部分是固定不变的。

**方案**：
- 将固定指令写入 `.claude/agents/lean4-formalizer-compact.md`，仅在 prompt 中传递变量（轮次、标注数、最近 commit）
- 精简 prompt 到 ~500 token：只传 `R637, 2820 annotations, last: R636 commit hash`
- 固定部分由 agent definition 承载，不在每轮 prompt 中重复

**示例精简 prompt**：
```
轮次 R637 (round_count=638)。标注 2820/49。
最近: R636 POM centralizer/pressure, Folding gauge anomaly。
执行标准单轮流程，完成后退出。
```

### 2.2 减少 .tex 扫描范围（预计节省 10-20%）

**问题**：Phase B 每轮扫描整个 theory/ 目录寻找未形式化定理，读取大量 .tex 内容。

**方案**：
- 维护一个 `candidates.json` 缓存文件，列出所有未形式化定理（标签、章节、难度估计）
- 每 10 轮刷新一次缓存，非刷新轮次直接从 JSON 中选目标
- 按章节覆盖率排序，优先选低覆盖率章节，避免反复扫描高覆盖章节
- 预估节省：每轮减少 3-5 次 Read 大文件操作

### 2.3 LSP 调用优化（预计节省 5-10%）

**问题**：Phase D 中 lean_local_search、lean_leanfinder、lean_hover_info 多次往返。

**方案**：
- **批量查询**：一次 lean_local_search 查多个候选名，而非逐个查
- **缓存常用引理签名**：在 worker prompt 中附带本项目 top-50 常用引理列表（如 `Nat.add_comm`、`Finset.sum_le_sum` 等），减少 hover_info 查询
- **lean_multi_attempt 前置**：对标准 sorry，直接用 multi_attempt 测试 `["simp", "ring", "omega", "norm_num", "decide"]`，而非先搜索再尝试
- **跳过已知低难度模式**：如果目标签名是纯算术/Fibonacci 恒等式，直接用 `norm_num`/`omega` 而不走搜索流程

### 2.4 Team Lead 开销消除（预计节省 5-8%）

**问题**：team lead 每轮执行 spawn → 等待 → shutdown → spawn 循环，每次 shutdown 消息 + 响应消耗 token。

**方案**：
- **Worker 内循环模式**：允许 worker 在单个 agent 内完成 2-3 轮，而非每轮 spawn/shutdown
- 风险：agent context 膨胀。缓解：每轮结束后清理 context（不读回已 commit 的文件）
- 预估节省：每 3 轮减少 2 次 spawn+shutdown 开销

### 2.5 IMPLEMENTATION_PLAN 增量更新（预计节省 3-5%）

**问题**：Phase E 每轮读取完整 IMPLEMENTATION_PLAN.md（可能 >500 行），只为更新前 20 行的计数器。

**方案**：
- 只 Read 前 20 行 + Edit 前 20 行，不读取全文
- 标注数等计数器用 `grep -c` 实时统计，不在 PLAN 中手动维护

### 2.6 .tex 标注批量化（预计节省 2-3%）

**问题**：每个定理的 \leanverified 标注需要分别 Read + Edit 对应 .tex 文件。

**方案**：
- 使用单个 Bash 脚本一次性插入所有标注：
```bash
sed -i '' '/\\end{theorem}.*thm:label/i\
\\leanverified{theorem_name}' file.tex
```
- 或维护一个标注脚本 `scripts/annotate.py`，输入定理列表，批量更新

## 3. 中等 ROI 优化

### 3.1 Codex 混合模式（预计节省 20-30% Claude token）

**问题**：当前 Claude-only 模式下所有工作（扫描、编码、证明、标注）都消耗 Claude token。

**方案**：
- 低难度定理（seed/algebraic backbone）委托给 Codex（GPT 系列）
- Claude 只处理中高难度定理（归纳、构造、需要 mathlib 深度搜索的）
- 本次 12 轮中 100% 目标被标记为"低难度，Codex 豁免"——说明 Codex 可以承担大部分当前工作负载
- **关键发现**：当前选目标策略偏向低难度 seed 定理，如果改用 Codex 处理这些，Claude token 可大幅节省

### 3.2 lake build 增量化（预计节省编译时间，间接省 token）

**问题**：每轮 `lake build` 全量编译（3500+ jobs），虽然增量编译只重建新文件，但输出处理仍消耗 token。

**方案**：
- `lake build 2>&1 | tail -5` 代替 `tail -30`，只看最后结果
- 编译无警告时不输出完整日志

## 4. 低 ROI / 高风险优化（谨慎考虑）

| 优化 | 节省 | 风险 |
|---|---|---|
| 跳过 lake build 全量检查 | ~2 min/轮 | 可能漏掉跨文件错误 |
| 减少 lean_diagnostic_messages 调用 | 少量 | 可能遗漏编译错误 |
| 合并 proof+register 为单 commit | 少量 | 违反现有 "proof before registration" 纪律 |

## 5. 量化总结

| 优化类别 | 预计节省 | 实施难度 |
|---|---|---|
| 压缩 Worker Prompt | 10-15% | 低（修改 prompt 模板） |
| 减少 .tex 扫描 | 10-20% | 中（需维护 candidates 缓存） |
| LSP 调用优化 | 5-10% | 低（调整调用顺序） |
| Team Lead 开销消除 | 5-8% | 低（改 worker 为多轮） |
| PLAN 增量更新 | 3-5% | 低 |
| .tex 标注批量化 | 2-3% | 低 |
| Codex 混合模式 | 20-30% | 中（需要 Codex runtime） |
| **综合** | **40-60%** | — |

## 6. 推荐实施顺序

1. **立即**：压缩 Worker Prompt + PLAN 增量更新 + build 输出截断（改 tail -30 → tail -5）
2. **短期**：candidates.json 缓存 + LSP multi_attempt 前置
3. **中期**：Codex 混合模式（低难度定理分流）+ Worker 多轮模式
4. **长期**：全自动难度评估 → 动态路由 Claude vs Codex

## 7. 关键观察

本次 12 轮运行的最重要发现：

1. **100% 低难度**：所有 36 个目标都被标记为"低难度，Codex 豁免"。这意味着当前目标选择策略倾向于 seed/algebraic 级别定理，Claude 的高级推理能力在大部分时间未被充分利用。
2. **标注增量波动大**：每轮 +3 到 +14 标注不等，取决于子定理数量。高标注轮次（如 R630 +14）比低标注轮次（如 R627 +3）效率高 4-5 倍，但 token 消耗相似。
3. **Team lead 几乎无实质工作**：team lead 只做 spawn/shutdown/等待，其 context 中积累的轮次记录是纯开销。
4. **编译递增成本**：3511→3537 jobs，每轮 +3 个文件。长期需关注编译时间增长。

---

*报告生成时间：2026-04-11，基于 lean4-claude-formalization 会话 R625-R636 实测数据*
