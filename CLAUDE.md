# 工作规范

## 环境与工具链

- Python: `python3`, 程序内纯英文(含图片生成), 长时间运行每 20s 输出一次进度
- LaTeX: 中文 `.tex` 用 `xelatex` 编译, `sections/generated/` 下的 `.tex` 由 Python 脚本生成
- 单个 `.tex` 文件不超过 800 行, 超过须拆分
- 非明确指定时不自动编译 PDF
- 二进制运算使用原生实现, 不用二进制字符串
- Lean 4: 使用 `lake` 构建

## 语言与格式

- 工作语言默认中文, 英文版文档以 `_en.md` / `_en.tex` 结尾
- 公式只用 `$` 与 `$$`(不支持 ` ```math `), `$$` 必须独立成行
- GitHub Markdown 数学公式注意事项:
  - `$$` 块必须顶格(列 0), 不可缩进, 否则 GitHub 不渲染
  - 中文全角标点(`：`、`，`、`、`等)与 `$` 之间必须加空格, 否则 GitHub 不识别为公式定界符(如 `：$` → `： $`)
- Mermaid: Material Design 配色, 标签用引号(`""`)包裹, 标签内禁用 LaTeX 公式

## 写作纪律

- 禁止任何修订痕迹: 不出现"新增""修订""修复了上一版本...""本版本为严格修订版"等字样
- 不生成修改记录、日志、变更原因、报告、总结
- 不添加文件内备注(如"这样修改是因为...")
- 有问题直接改, 无需备份

## 项目结构

- `lean4/` — Lean 4 形式化证明(Omega 库, 依赖 mathlib)
- `theory/` — 中文核心数学论文, 含可复现的 Python 脚本管线(`scripts/` → `sections/generated/`)
- `papers/publication/` — 英文投稿论文(从 theory/ 提取, 面向各期刊)
- `tools/chatgpt-oracle/` — 管线主控脚本和 Oracle 桥接

## 出版管线架构（必读）

**主控脚本**: `tools/chatgpt-oracle/oracle_pipeline.py`（全部流程编排在此）
**辅助工具**: `papers/publication/backflow.py`（scan/review/diff/mark）
**辅助工具**: `papers/publication/pipeline_auto.py`（状态查询, 不控制流程）

### Stage 定义（F→A→B→C→D→DONE）

定义在 `oracle_pipeline.py` 顶部注释, 不要自行发明新命名:

| Stage | 谁做 | 做什么 | 轮次上限 |
|-------|------|--------|:--------:|
| F | Codex 评估 + Claude 审 | 期刊方向适配(fit ≥ 6 通过) | 1 |
| A | Codex 写 + Claude 审计 | 内容补全、去重、修证明、拆文件 | 8 |
| B | Oracle 审 + Codex 改 | ChatGPT referee 循环 | 无上限(须 accept/minor) |
| C | Oracle + Claude 联合终审 | 最终确认 | 无上限(须双方通过) |
| D | Codex 做 + Claude 审 + /killo-golden | 回流到 theory/ 中文核心论文 | — |

### 角色分工（铁律）

- **Codex 做, Claude 审**: Claude 不直接写论文内容或回流内容, Codex 出初版, Claude 审阅和打磨
- **Oracle 是 ChatGPT Pro**: 通过 `oracle_dispatch.py` + Tampermonkey 浏览器桥接调用
- 三者不可混淆: Codex 编辑, Claude 验证(独立), ChatGPT 是外部 Oracle

### 状态持久化

- 每篇论文的 pipeline state: `tools/chatgpt-oracle/pipeline_state/<paper>.json`
- 包含: 当前 stage、轮次、所有 verdicts/scores 历史、累积 issues
- Agent 记忆通过 prompt 注入, 不通过对话历史:
  - `fresh_review`: 无记忆, 干净审阅
  - `contextual_execution`: 有记忆, 看 issues + scope + 前序上下文

---

# The Omega 科研宪章

## I. 第一性原理优先

- 每个结论须有可追溯的推导链: 定义/公理/已证引理 → 命题/定理 → 推论
- 直觉/物理解释不得替代证明; 若仅为启发须标注为解释性叙述, 不得作为后续推理前提
- 引用外部结果须明确精确形式(定理陈述、条件、常数/界)并给出可复核的引用位置

## II. 最小输入原则

- 新增公理/假设/外部输入前须给出必要性说明: 移除后哪一步无法完成, 指出最小失败点
- 优先选择输入更少、依赖链更短的表述; 禁止为叙事完整引入不可检验的额外结构
- 经验性参数须区分: 定义参数、可拟合参数、可预测参数

## III. 显式依赖链

- 每条基础陈述须归类为: 定义、约定、公理、假设、猜想、推导结果、经验事实
- 跨层跳跃(如数学对象→物理指称)须单独列出桥接假设及其可检验/可反驳路径
- 禁止隐含公理: 推理所需额外条件须显式写出并进入依赖链

## IV. 可证伪与量化约束

- 经验性/数值性主张须配套: 观测量定义、数据来源、误差指标与预算
- 纯理论结果须给出至少一种一致性检查: 边界情形、极限行为、已知特例复现、维度一致性
- 负面结果与适用边界须记录; 禁止以"未来工作"替代已知限制

## V. 可复现、可审计

- 所有表格/图像/数值结果须由脚本生成并可一键再现; 禁止手工修改生成的 `.tex`
- 生成脚本须记录: 输入参数、随机种子(如有)、版本信息; 输出须可追溯到源脚本
- 依赖外部服务时须提供可复现的导出/快照策略

## 论文结构要求

每篇论文须包含(可合并但功能不得缺失):
1. 摘要与贡献点(最小主张清单)
2. 引言(问题、动机、与现有工作差异)
3. 预备知识/定义/公理与假设(依赖链)
4. 主要结果与证明/推导
5. 验证路径与误差说明
6. 讨论、局限与可证伪点
7. 可复现性声明(代码/脚本/数据路径)

写作纪律: 不用权威背书替代论证, 不扩大叙事范围, 禁止"口径化"(须带明确引理/定理与引用定位)

## 质量门禁(提交前)

- [ ] 新增公理/假设是否必要且显式?
- [ ] 关键结论是否可追溯到基础层?
- [ ] 结果是否可一键再生成且参数/版本齐备?
- [ ] 适用范围与失败模式是否记录?

## Skill routing

When the user's request matches an available skill, ALWAYS invoke it using the Skill
tool as your FIRST action. Do NOT answer directly, do NOT use other tools first.
The skill has specialized workflows that produce better results than ad-hoc answers.

Key routing rules:
- Product ideas, "is this worth building", brainstorming → invoke office-hours
- Bugs, errors, "why is this broken", 500 errors → invoke investigate
- Ship, deploy, push, create PR → invoke ship
- QA, test the site, find bugs → invoke qa
- Code review, check my diff → invoke review
- Update docs after shipping → invoke document-release
- Weekly retro → invoke retro
- Design system, brand → invoke design-consultation
- Visual audit, design polish → invoke design-review
- Architecture review → invoke plan-eng-review
