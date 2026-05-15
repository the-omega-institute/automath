# bedc-deep → community-outreach 整合分析

**Source**: `the-omega-institute/newmath@bedc-claim-packet-pipeline:tools/bedc-deep/`
**Target**: `automath@openproblem-target:tools/community-outreach/`
**Date**: 2026-05-05

## 1. 已经 parity 的部分（不重做）

两个 supervisor 都已实现：

| 功能 | bedc-deep | community-outreach |
|---|---|---|
| 启动/退出 + STOP_FILE | ✅ `.stop` | ✅ `.outreach_stop` |
| 周期性日志 + supervisor.log | ✅ | ✅ |
| oracle_server 健康探测 | ✅ port 8767 | ✅ port 8766（advisory only）|
| auto-commit + push | ✅ `papers/bedc/parts/` + BOARD.md | ✅ OUTREACH_LOG.md + RESEARCH_BOARD.md |
| macOS osascript 通知 | ✅ | ✅ |
| PI agent review（周期）| ✅ pi_agent_v1 | ✅ outreach_pi_agent |
| PI 回调：adjust_cooldown | ✅ probe/curator/pi/oracle_refill | ✅ pi_review/arxiv_watch/lit_staleness/inbox_watcher |
| signal handler | ✅ | ✅ |

## 2. bedc-deep 有、我们没有 的关键能力（按整合优先级排）

### 🟢 P0 — 现在就值得搬

#### 2.1 服务自动拉起（`ensure_server`）

bedc-deep `supervisor.py:105-121`：oracle_server 如果死了，supervisor 自己 spawn 它，等 3s 再 check。

我们这边 outreach_supervisor.py 是**纯 advisory** —— 服务死了只 log 不重启，要人手干预。这个差距在你跑 long-running outreach loop 的时候是真的痛点（半夜服务挂了，pipeline 第二天才发现）。

**整合**：把 `ensure_server` 直接照搬，把 `bedc_oracle_server.py` 替成 `outreach_oracle_server.py`，端口 8767 → 8766。

#### 2.2 浏览器 tab 卡死告警（`queue_stuck_too_long` + macOS notify）

bedc-deep `supervisor.py:152-157, 887-894`：当 oracle_server 报 `diagnosis = queue_waiting_for_browser_agent` 且队列里有 task `age_seconds > 300`，触发 macOS 桌面通知 + 写日志。

outreach 这边 oracle_consultant 也是浏览器 tab 路由的，**同样会卡 tab**。我们当前没告警，只能靠人巡检。

**整合**：复用 `queue_stuck_too_long` 逻辑，把通知文案改成 outreach 项目对应的 ChatGPT URL。

#### 2.3 inner-restart 退避机制（`spawn_inner` + backoff）

bedc-deep 有 `--inner-restart-backoff` 30s 默认值，inner 异常退出时 sleep 后重启。我们 outreach 没有 managed inner（per docstring "no managed inner loop"），但**应该有**：当 inbox watcher / arxiv watcher / oracle_consultant 这种长跑子任务挂了，你现在没有自动重启。

**整合**（中等改造）：把 outreach pipeline 里"长跑型"子任务（`outreach_pipeline.py` 的 deep mode、`outreach_inbox_watcher --watch`）也按 inner-loop 管理，加 backoff + auto-respawn。

### 🟡 P1 — 值得搬但需要先确认形态

#### 2.4 板低水位自动补题（`oracle_board_refill.py` + prompts）

bedc-deep 当 BOARD unfinished 数 < `--low-water` 时，自动让 ChatGPT Project（attached PDF）出 5-10 个新候选，跑 maker/checker judge，atomically 追加到 BOARD.md。`prompts/oracle_board_refill.txt` 写得很有讲究 —— 已有 BOARD 候选 + paper_labels coverage summary 都注入，明确"不要重复 / 不要参数搬运 / 不要 marker-only / quality > quantity"。

我们这边 RESEARCH_BOARD 是**人工策划**的（你 2026-04-29 离线一次性产出 24 项 T-NN）。等 backlog 跑完后没人补题，pipeline 就空转。

**整合方案**（建议讨论）：写一个 `outreach_board_refill.py`，让 ChatGPT 给我们出新 outreach target —— 但这里 prompt 要重新设计，因为 outreach 的"题"是 _open problem registry 候选_（erdosproblems / OPG / AimPL），不是论文 theorem。可能更适合做成 **arxiv 周扫描 + erdosproblems wiki diff** 联合喂给 oracle 让它判断有没有"这周新出现的、未被 AI 触及的、和我们工具栈对得上的题"。

**ROI 评估**：取决于你打算让 outreach 跑多久。如果是连续运行的 service（你现在的方向），这个补题机制是必备，不然 board 跑完就停。

#### 2.5 paper_review / curriculum probe（多路径补题）

bedc-deep `auto_discovery.py` 有三个互补的补题路径：
- `probe`：codex 静态扫描，找内部对称缺失（A→B 但缺 B→A 等）
- `curriculum`：textbook-classical 缺漏（"标准教材会 cover 但我们没有"）
- `paper_review`：editorial-referee 风格审稿，loning-style REVIEW gated by board_judge

每个有独立 cooldown（默认 6h / 6h / 3h）。这是**多源补题**思路。

**整合方案**：等 P1.4 决定后再说，具体路径要看 outreach 这边什么"补题源"对得上 —— 也许是 `arxiv_watch`（已有）、`erdos_registry_diff`（待写）、`oracle_consultant_referee`（待写）。

#### 2.6 dev_sync_resolver — claude 自动解 git 冲突

bedc-deep `supervisor.py:392-482` + `dev_sync_resolver.py`：每个 supervisor tick 之前 fetch + merge upstream，**冲突时自动 spawn claude 解冲突、跑 lake build / check-axioms / bedc_ci 验证、失败硬 reset**，protected files (lean4/, papers/main.tex) 直接 abort 进 human_inbox。

我们这边 outreach 是 outreach-clean 单分支，目前不需要跨人合并 —— 但**如果 Haobo Ma 也要 push 到这个分支**（你刚才提到 chrono ai ceo 是合作者），冲突自动解很快就有用。

**整合 verdict**：等到第二个人开始 push 同分支再谈。现在 ROI 低。

### 🔴 P2 — 不要搬

#### 2.7 stage2 reject cluster analytics

bedc-deep `supervisor.py:179-229`：扫所有 `targets/*/stage2_result.json`，分类 rejection reasons（item_N / build_invariant / content_duplication / line_cap / undefined_macro 等），给 advice。

这是**论文 LaTeX 写回 pipeline** 特有的失败模式分析（800 行 cap、undefined macro），跟 outreach 的"草稿被审被拒"完全不同语义，硬搬过来用不上。

#### 2.8 board_archive / lifecycle / closure_candidate 等

那一套是 BEDC 专门的 BOARD 状态机（`.in_progress` 标记、retriable 重置、closure 跟踪），跟我们 outreach 的 OUTREACH_LOG（按行人工维护）模型不同。重构成本 > 收益。

## 3. 推荐整合路径（先后顺序）

| 步 | 内容 | 估时 | 风险 |
|---|---|---|---|
| 1 | P0.1 ensure_server 自动拉起 | 30 min | 低 |
| 2 | P0.2 tab 卡死告警 + macOS notify | 30 min | 低 |
| 3 | 验证两条新逻辑在 dry-run 下不误触 | 30 min | — |
| 4 | P0.3 inner-restart 退避（针对 outreach_inbox_watcher 长跑模式）| 1-2h | 中（要重构 watcher 为 daemon 形态）|
| 5 | （决策点）P1.4 outreach_board_refill — 设计 prompt + 信号源 | 半天 | 中 |
| 6 | P1.5 多路径补题（如果第 5 步落地）| 半天 | 中 |
| 7 | P1.6 dev_sync_resolver — 等 Haobo 加入 outreach 分支再做 | — | — |

## 4. 需要你决策的问题

1. **outreach pipeline 的目标形态**是什么？
   - (a) 一次性把 board 跑完然后停？→ 只做 P0.1/P0.2/P0.3 就够
   - (b) 持续运行，定期发现新 target？→ 必须做 P1.4 补题机制，否则 board 跑完就空转
2. **outreach_oracle_server 是否要做成"必有"**？现在是 advisory（服务死了不影响主流程，但 oracle_consultant 不能用）。如果要给它装 ensure_server 自动拉起，需要确认它是否**总应该**在跑 —— 还是只在某些子命令时才用？
3. **Haobo Ma 加入 outreach 分支的时间表**？这决定了 dev_sync_resolver 的 ROI。
