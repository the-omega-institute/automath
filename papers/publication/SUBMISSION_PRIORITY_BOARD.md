# Next-Step Plan — Submission & Deepening

纯**前向建设计划**：深化已有真结果 + 提取全新内容。核心资产是 `lean4/Omega`（9,786 文件、**zero `sorry`**）。方法：两套独立 scout（Claude 3-agent 深挖 + codex）+ 5-agent 评审。

**规划原则（铁律）：每篇都先深入挖掘，不丢不降档。** 每篇统一流程：**① 深入挖掘（补一条新定理）→ ② 机器验证（`lake build` + 数值反例）→ ③ 打磨（referee 循环）→ ④ 选刊（凭强化后的结果争对应档次，不预降档）→ ⑤ 投递。** 选刊在深化之后。运行载体 = **fkst + 本地大脑**（fkst 编排、本地 F→A→B→C→D 计算）。下表"候选刊"是深化前的方向参考，最终档次以强化后的结果为准。

> ⚠️ **关键可信度校正（codex）**：`zero sorry` 只是"能编译"，**不等于定理名所声称的数学**。库中相当一部分"paper theorem"要么把关键递推当作**假设**、要么在已含结论的结构上量化、要么结论就是 `True`。**因此每个 Lean 种子在投入前必须逐条核验:陈述是 object-level 且无条件的**（下面 B/C 的种子已标注哪些需先验无条件性）。

---

## 冲刺状态 · 停跑论文的最终目标期刊（滚动更新）

深化冲刺（ChatGPT 5.6 sol pro chat 模式多轮追问 + codex 逐条检验 + 独立复核）。**一篇论文在 Oracle 开始复述已整合内容（即新一轮全判 `ALREADY-IN-PAPER`）时判定饱和、停跑**，此表随即记录其最终目标期刊。

### 冲刺后目标期刊（codex 依"实际通过验证并入稿"的内容重评，2026-08）

| 篇 | 目录 | 页 | 最新裁决 | **去向** |
|---|---|--:|---|---|
| **A2** | `cayley_chebyshev_..._jfa` | **32+0** | **重组已执行并核实**：87+33 → 32；stable 脊柱为唯一主线，正文不再指向任何补充证明 | **JFA**（待重新评）|
| **A3-A** | `linear_overlap_transients_bounded_zero_pisot_etds` | **18+0** | **ETDS 小修已执行并核实**：第 5 节删除、防御层清除、引言立 Theorem A/B/C、四页补充不再提交 | **ETDS 75–77%** |
| **A3-B** | `cyclic_rank_thresholds_quadratic_simple_parry_etds` | **30+0** | **ETDS 大修已执行并核实**：36+15 → 30；16 条孤儿文献清理中 | **ETDS** |
| **A4** | `prime_languages_..._monatshefte` | **31** + 伴随 43 | **Monatshefte 大修已执行并核实**；原 43 页补充**分立为独立论文**；书目需按文档拆分 | **Monatshefte** |
| **A5** | `finite_parts_..._etds` | **52+19** | **四条新定理已验证：三条无条件、两条条件于未核实的 (KN85)**；主定理经查也依赖 (KN85) 且未标明，修复中 | ETDS |
| **A6-A** | `brocot_condensation_critical_fibonacci_renewal_tams` | **27+0** | **TAMS 审稿人裁决：Major revisions** | **TAMS** |
| **A6-B** | `finite_window_zeckendorf_thermodynamics_jnt` | **32+7** | **JNT 大修已执行并核实**：52+19 → 32+7；四个被取代的定理族直接删除 | **JNT** |
| **A7** | `upper_fibers_..._fq` | 33+36 | **Fibonacci Quarterly 审稿人裁决：REJECT AND RESUBMIT**，12 项重构中 | **Fibonacci Quarterly**（重构后）|
| **A8-A** | `renewal_experiment_equivalence_singular_lan_ejs` | **32+22** | **EJS 小修已执行并核实**：第 4 节重排、三条补充结果陈述入主文、防御层清除 | **EJS 51%** |
| **A8-B** | `detector_shells_..._jphyscomm` | 72+19 | 原装配版原样保留,作为被删材料的存放处 | **SPA 39%**(未改动)|
| **A9** | `homological_visibility_..._apal` | 39+6 | **Cahiers 审稿人裁决：Major revisions**；含该刊版式要求（法文 Résumé）| **Cahiers** |







**八篇外审全部走完、全部修复入库、投稿包七项齐备。A2 是唯一从拒稿走到 tier-2 的一篇。**


**八篇外审全部走完并修复入库;A2 是唯一拿到"不因数学正确性拒稿"的一篇。**


**八篇全部完成外审并修复入库。**


**七篇外审全部走完;六篇已修复入库,余 A7、A9 在改。**


**七篇全部走完外审。六篇存在优先权遗漏，三篇因补充材料未随投而被扣分。**
















> **TICK 205b — A4 书目拆分入库（f457d3796）；并查出一个比原缺陷更严重的问题：修好的是工作副本，要投出去的是旧的。** 拆分按"按文档拆"而非"删 30 条"执行：正文 27 条、伴随论文 30 条、共享 5 条、两者都不引的 30 条丢弃；**保留条目逐字节与原文相同**，且源码改动只有两行 \input——因此**不可能**存在为保条目而往正文塞引用的情形，这比任何口头保证都硬。我按文档分别核：27/27、30/30，双向差集均空；两文档 29 与 41 页、undefined 全 0；Mignotte 缺口未动（literature_check.md 零删除行）且该条目在正文仍被引用并打印，故缺口记录仍附着于一条活引用。**新问题：submission_bundle/ 是 git 跟踪的手工装配产物，且已陈旧**——它仍带着拆分前的 82 条 references.tex、main.tex 仍 \input{references}、main.pdf 仍为 31 页，source.zip 与 reproducibility.zip 也是修订前构建的。**即我们刚修好的缺陷，在真正会寄给 Monatshefte 的那份里原封不动。**执行方发现后未擅自处理而交回来，这是对的。**而且这是系统性的**：我扫了全部论文，两篇有 git 跟踪的 submission_bundle（A4 24 文件、**A5 44 文件**），两份的 bundle main.tex 与根目录都 **DIFFERS**。A5 正在修订中，其 bundle 修完后也必须重生。已派 A4 bundle 重生任务，任务书重点写了两条：**PDF 必须用 bundle 自己的副本重建**（从根目录拷一份 PDF 过去并不能证明随附的源码能生成它），以及**仅存于 bundle 、根目录无对应物的文件不得静默删除**（手工 bundle 常带投稿信或期刊表单，弄丢比陈旧更糟）。**核验清单增至九条：跟踪的投稿包须与已修订的正文同步。**

> **TICK 205 — 三个 agent 均健在；Oracle 通道已断，但当下不阻塞任何工作。** 无可收割：A4 书目拆分（1.13 MB）、A5 r2（0.34 MB）、A7 重构（0.64 MB）转录 mtime 均在 20 秒内，均无 tokens used。**Oracle：WARP 中继已断**——172.18.32.1:40002 不可达，Test-NetConnection 返回 False；根因是流水线所在的 WSL 发行版 **NyxIDUbuntu2404Cli 处于 Stopped**（三个发行版全停），而 wrapper 自述"从不启动或重连 WARP"，需显式启动（start-shared.ps1 内有显式启动路径）。**判断：现在不重启。** 理由两条：（a）**当下没有任何待办的 Oracle 任务**——九篇 house-style 报告与 A5 深研究均已取回，在跑的三件全是本地 codex；（b）刚发生过 0xC0000142 进程创建失败（资源耗尽），在三个 agent 跑着时再拉起一个 WSL 发行版是往相反方向使力。待三件落地、且确实需要下一轮 Oracle 时再启。已记录以免下次调用时把它误诊为协议问题。内存 2.09 GB、缺页 0、无孤儿——降并发后环境明显转好。

> **TICK 204e — A7 双派已解除，A4 拆分进行中，两条基线更正。** 我重派的 A7 agent 已停手，且**从未启动 codex、从未执行任何 taskkill**；另一会话的 A7 运行保留为唯一所有者。它在停手前做过一次 baseline 构建，删重建了辅助文件（均已 gitignore，无跟踪文件变动），**但那次抹除落在对方运行的活窗口内**——若对方转录在 00:16-00:17 出现一次假的 undefined 引用，那是辅助文件被抽走所致、非其编辑造成，重建即自愈，评分时不计入。其遗留的两个抽取转储文件已由我删除，A7 目录现干净。**基线更正一**：对方给的 A7@HEAD 基线称"零 	ag"，我实测为 **2 处**（sec_support_entropy_arithmetic_interface.tex 的 	ag{H1}、	ag{H2}）。但这两处是**助记式假设标号**，与 A8-A 的 LE/SL 系列同类，属正当用法，不是硬编码方程编号。故"修订后出现 	ag 即为新引入"这条判据需改为"除 H1/H2 外新增的 	ag 才是新引入"。其余基线属实且有用：HEAD 下 main 与 supplement **均为 36 页**（目录里那份 5 页的 supplement.pdf 是不完整构建的陈旧产物，引用它作"改前 5 页"会得出错误结论），iffalse/endinput/begin{comment} 均为 0。**基线更正二：抑制机制清单需加一项 egin{comment}**（comment 宏包环境），我原来只查 \iffalse 与 \endinput。**A4 书目拆分正在正确执行**：references.tex 已删，main_references.tex（27 条）与 finite_state_references.tex（30 条）已生成，agent 仍在跑（转录 40 秒内 +140 KB）。注：我中途一次 grep 报 0 bibitem 是模式错误，实为正常内容；在 agent 活跃期间不得据中途快照下结论。并发维持在 A4、A5 r2、A7 三个，不再新增。

> **TICK 204d — 对 204c 的死因归因更正，并因此下调并发。** 我在 204c 里把三个 agent 的死亡全归于镜像级 taskkill，**这个归因对一半**。A5 死于 00:04:30，而扫射发生在约 00:13——时间上就对不上。A5 的真实死因是 Windows 进程创建失败 **0xC0000142 STATUS_DLL_INIT_FAILED**，发生在最后一步重跑 Python 测试器时，并在一个健康探针上循环约 19 次后死掉；它实际上已跑完编辑、清洁重建与抽取检查（主文 45 标题 / 补充 22 标题、排序失败 0）。**因此只有 A7 与 A6-A 是扫射的牺牲品。****这个区分有运行上的意义**：0xC0000142 在进程创建处报出，典型地是资源耗尽（桌面堆、句柄、会话进程限），而非任务缺陷。当时同时在跑 5-6 个 codex 加 latexmk 与 pdftotext。故**下调并发：仅保留已在飞的 A4、A5 r2、A7 三个，在它们落地前不再派新工**（A6-A 继续暂缓）。另：另一会话在我重派 A7 之后也重派了 A7，其运行已先行且正在写盘；我已让自己那个 A7 agent 停手，以守住"同时只跑一个 agent 改同一篇"，并在停手指令里明写只得杀自己启动的进程树。

> **TICK 204c — 三个 agent 被误杀，已回滚并重派。** 一个并行会话为停掉 A4 清理而执行了**镇级的 taskkill /F /IM node.exe**（未限定到自身进程树），连带杀掉了其他论文的 agent。已核实：A5（转录 00:04:30 停止）、A7（00:11:29）、A6-A（00:13:12）三个均无 tokens used 且 45 秒内零增长，均属中途被杀；仅重新派出的 A4 存活。**三篇的遗留状态均不一致**：finite_parts 与 upper_fibers 的 latexmk 直接 exit=12（根本编不过），brocot 虽能编但只剩 20 页（HEAD 为 27，即删除已做、其余未做）。**处置：三篇全部 git checkout HEAD + git clean 回滚**，而非尝试抢救——提交一个半应用的编辑修订比丢失工作更危险，何况其中两篇连编译都不过。回滚后三篇均重建成功：52 / 36 / 27 页，工作区干净。已重派 A5（阻断级）与 A7（最重的重构），A6-A 暂缓。两份新任务书均加写了进程卫生要求：**停止 codex 只能杀自己启动的进程树，不得对 node.exe/codex.exe 做镜像级 taskkill**。并记一条方法教训：并发 agent 共享一个进程镜像名时，"杀掉我启动的那个"必须按 PID 树而非按名称。另：A4 清理 agent 确认未造成损害（杀时尚未写盘，工作区与 literature_check.md 校验和均未变），并另查出我原任务书两处路径错误（指向不存在的 sections/bibliography.tex 与不存在的 references.bib），实际为顶层 references.tex；已按正确路径与按文档拆分的操作重派。

> **TICK 204b — 对上一条的两处更正，均源于我自己的测量。** **更正一：43 页补充不是被删除，而是被分立为独立论文** finite_state_article.tex（自带标题、摘要、引言、MSC 与作者栏，仍能构建，材料全在）。投 Monatshefte 的数学上传从 80 页降为 31 页。标签集 diff 显示编号结果**零丢失、零新增**，唯一消失的是一个被删先前工作目录的小节锚点；25 个结果对应 25 个证明、无一例外。**更正二：孤儿文献的数字和修法都错了。** references.tex 是**两份文档共享**的手写 thebibliography，两者都把 82 条全印。故存在三个不同的计数：正文自身引用约 21-27 条；两份文档**都不引**的约 30 条；**在 main.pdf 印出但正文从未引用的达 55-61 条**。我上一条报的"30 条"是用目录级 grep 得出的，把伴随论文的引用也算进了被引集。若按我原任务书只删那 30 条，正文仍会印着二三十条属于伴随论文的条目——只修了一半不到。**正确操作是按文档拆书目**：每份文档各持一份只含其自身引用键的参考文献表，条目逐字搬运不得重拟，两份都不引的丢弃，两份都引的各自保留，然后**对每份文档分别验证双向差集为空**。已将此更正发给在跑的清理 agent，并告知若已按错误指令删除则重置到 d59ac1e9a 重做。另记：Mignotte 在本次修订后**承重更重**（摘要第二分支依赖它，正文五处使用），而其全文仍未读到——该缺口记录（literature_check.md 848-862 行）未被动、未被二次转述封口，但其重要性上升了，值得在投稿前单独衡量。

> **TICK 204 — A4 大修完工并核实入库（d59ac1e9a）；同时暴露了我自己的一个派工时序缺口。** 37+43 → **31 页**，43 页独立数学补充材料已不属投稿件。第 10 项被评估者直接命名为"remove revision-response vocabulary throughout"，已执行；Mignotte 旧来源缺口未被重开、未被二次转述封口。独立核实：重建 exit 0、undefined 全 0、31 页、PDF 正文无泄漏且无补充指针、无抑制块、Pisot pumping verifier 通过、21 测试 + 9 子测试通过、SHA 8/8、artifacts/oracle_*.md 与 HEAD 一致。（一处需更正的自述：我首次在 artifacts/ 目录内跑测试报 ModuleNotFoundError，那是我的调用路径错了，不是测试坏了；从论文根目录跑为 21 passed + 9 subtests。）**但发现 30 条孤儿文献**（打印 82 / 被引 52）——与 A3-B 同一类。**这是我的时序缺口，不是执行方的失误**：孤儿文献检查是 tick 202 生成 A7/A6-A 任务书时才加的，而 A4 在 tick 199 就已派出；我已核实 a4 任务书中该检查计数为 0、a7 为 1。教训：新增的核验项必须回填到**已在飞**的任务，而不只是写进下一份模板。已派 A4 孤儿文献清理（要求自行推导名单）。A5、A7、A6-A 仍在跑。内存 0.75 GB、缺页 148、无孤儿进程。

> **TICK 203 — A9 裁决到齐，九篇录用评估全部完成；四个修订 agent 在飞，A9 暂不派。** A9：Major revisions，七项必需。**其中第 3 项是不问就永远不会知道的东西：该刊近期论文几乎无一例外地以**法文 Résumé** 开头，随后才是英文摘要、关键词与 MSC**——他明言这不是偶尔偏好而是该刊可见的版式惯例，并将"未使用该刊前部惯例，尤其是法文 Résumé"列为不合该刊语域的痕迹之一，并指出本稿命中其中六项。这类期刊形式要求不会出现在任何估值问题的答案里。其余六项与其他八篇同病：引言立显式结果层次、删除贯穿全文的编辑性与伴随稿审计、删除重复的范围免责、保留中心证明而压缩标准基础设施、重建第 5-6 节的应用链、第 7 节缩为真正的边界节。他还给了一条可操作的证明风格规则："承载区分本文的那部分论证；专家视为标准的基础设施可引用或简验。"**九篇最终分布：两篇小修、五篇大修、两篇退修重投（A2、A7）。** 无一篇直接可投。**A9 暂不派**：已有四个修订 agent（A5、A4、A7、A6-A）在跑，codex 进程 5、内存 0.93 GB；A9 是九篇里价值最低的（35% Cahiers），先等一个落地再派是正确的次序。本 tick 无可收割。

> **TICK 202 — A3-B 收尾；A7 裁决回来且是第二篇退修重投；两篇大修已派。** 孤儿文献清理提交 fdbe644f0：十六条全删、**零条被“救活”**，bibliography.tex 为纯删除（0 插入/61 删除），无任何正文文件被打开，因此不存在编造依赖的句子。我独立复核：打印 25 / 被引 25 / 双向差集空；literature_check.md 零删除行（纯追加），Frougny DOI 修复与四处 429 速率限制记录均在。**A7：REJECT AND INVITE RESUBMISSION**，12 项。这是第二篇退修重投，而且 A7 正是板上记为"天花板已论证"的那一篇——天花板是对**定理**而言的（新颖性 75-80%、不进 JNT 档），但作为**稿件包**它是退稿。这正是对天花板论文也跑一遍录用问法的理由。项目包括：删去独立定理块以"定义一篇论文"、摘要整段重写、新颖性免责声明至少砍三分之二、第 7 节整节移出投稿件、重新平衡 36 页补充材料。已派 A7 重构与 A6-A（TAMS 大修）两个 agent。**两份任务书均携带全部八道核验**，包括本轮新增的三道：源码无抑制块、可复现包须与投稿一致、打印书目与被引键集双向一致（后者并明令不得往正文塞引用）。A6-A 的任务书另写明：不得把发育轮写入的假设逐条验证退回引用、Omey-Van Gulck 与 Panov-Liehl 作为外部黑箱是诚实的不得粉饰、且 r>=j 的平衡尾修正须存活。A9 第三次重发后仍 waiting_response。内存 1.17 GB、缺页 3.9、无孤儿。

> **TICK 201 — A3-B 入库，A6-A 裁决到齐：九篇全部受检完毕。** A3-B 提交 39ec099e4（36+15 → 30 页，源码 -3061/+493，编号结果 64 → 29）。第一项的二选一取手艺路线且**未编造**：Theorem 4.8 对 m>=4 仍只给界、数学内容与改前逐字节相同。**本 tick 查出第八类缺陷**：删掉补充材料与七个节后，**16 条文献成为孤儿仍在打印**（打印 41、正文引 25）。因为书目是字面的 thebibliography 环境而非 BibTeX——BibTeX 会静默略去未引用条目，而 thebibliography 里每个 ibitem 无论是否被引都会印出来，所以 LaTeX 不给任何警告、日志全绿、逐页读也会滑过。**我头两次核查返回 0，是我的工具问题**（Python 递归 glob 未匹配到文件、首版 grep 模式也不对），换用 main.aux 的 bibcite 与源码 \cite 键集对比后与对方完全一致。清理已派，并明写**不得为"救活"条目而往正文塞引用**。**核验清单增至八条**：打印书目与被引键集须双向一致。**A6-A（TAMS）裁决：Major revisions**，已存 artifacts。至此九篇全部过了录用问法，分布：**两篇小修、六篇大修、一篇退修重投**，无一篇是"直接可投"。A9 第三次 extraction_failure 后已再次重发（f893974c-3ecf-4a85-802a-0ea39b3cf8c3）；A7 waiting_response。内存 1.44 GB、缺页 938、四 agent 在飞、无孤儿。

> **TICK 200 — 空转：四个 agent 均在飞，两发 Oracle 因 extraction_failure 已重发。** A3-B 修订、A5 主定理依赖标注、A4 大修三份转录均无 tokens used；不收割。A6-A 的 house-style（fb5ac1c9）仍 waiting_response；A7 与 A9 返回 extraction_failure（worker 端抓取失配，非协议问题），已取消并按原协议间隔 30 秒重发：A7 → 60b10b45-850c-45ed-b10a-a677cc747784、A9 → a37af77c-95ca-4f30-9172-25a8d91abaac。内存：首采缺页 3399/s，复采 143.7/32.6/50.4、内存 1.80→1.98 GB，仍属成批读入而非频繁换页（自由内存同时上升），四个 agent 均处中途，不减。无孤儿。本 tick 无实质产出，属正常等待状态。

> **TICK 199 — A6-B 大修完工并核实入库（c6f1238d3）；两件需记录的判断。** 52+19 → **32+7** 页，源码 4741 → 2653 行。脊柱现为本文自有的六条定理；拆分时的约束守住了——回收的 Bernoulli 卷积压力与转移的极值分类仍为从属，摘要写明"转移已知极值"与"使用已知 L^q 谱"，二者均未声称为自己的。遇到可走"新数学"路径的条目时选了纯手艺路线，**将联合代价-重数 LDP 直接省去而非编造一个有限窗版本**，并在附录中一次性写明尚需什么（在多元指数条件下一致的格点稳定/半稳定局部更新定理）且明言"本文未使用任何此类定理"。**判断一：四个被取代的定理族是直接删除而非移存**（条目 3 授权如此），这是本次最大的内容决定；材料仍在 git 历史中，但与 A2 不同，这里**没有伴随论文承接它们**。**判断二：成品 32 页低于评估的 40-45 页区间**，执行方自行标出并拒绝填充（"填充会与要求的主操作相矛盾"），我同意这个取舍。六道核验全过：重建 exit 0、undefined 全 0、32+7 页、PDF 正文无泄漏且无悬空补充指针、编号按首次定义递增且无手写编号、**无抑制块**、20/20 测试 + 三个 verifier 通过 + SHA 15/15、**artifacts/oracle_*.md 与 HEAD 逐字节一致**。**发现一处可复现性不一致（新目定的第七道检查）**：REPRODUCE.md 仍指示读者运行 verify_speed_separation.py，而"speed separation"与"dyadic"在两份文档中均出现 **0 次**——它认证的二进制乘子律属于被删的那四族。审稿人按 REPRODUCE.md 跑一遍会拿到论文里没有的东西，这会直接引出"还删了什么"的追问。**已将这两条（源码无抑制块、可复现包须与投稿一致）追加进 A4 任务书**并派出 A4 大修；A4 另有 Mignotte 全文的旧来源缺口，任务书已明令不得重开、不得用二次转述封口（A5 上周就是这么掉的）。A6-B 的 verifier 包对齐待单独处理。内存 1.42 GB。

> **TICK 198 — 三 agent 在跑，空闲 Oracle 池投向最后三篇未受该问法检验的稳定论文。** 无可收割：A3-B（8.7 MB）、A6-B（10.3 MB）、A5 主定理依赖标注（0.7 MB）三份转录均在增长且无 tokens used；该目录现有 54 项未提交变更，属在飞状态。**新派三发**：A6-A（TAMS）fb5ac1c9-7dfd-4d3e-a7fd-62871291607a、A7（Fibonacci Quarterly）2d2cf71c-39b1-4c0d-97b6-02ae43097bda、A9（Cahiers）270416ab-a20d-48c5-a6eb-21b31ab717f2。至此 house-style/审稿人/编辑门槛三合一问法将覆盖全部九篇可问稿件。选 A7 与 A9 的理由值得记：二者都在**已论证过的天花板**上（A7 不进 JNT 档、A9 35% Cahiers 带优先权异议），而那些天花板是**估值**问出来的；本轮已反复证明**录用**问法会查出估值问法看不见的东西——A2 就是估值说"最强、可投 JFA"而录用说"退修重投，稿中含三篇论文"。天花板未必不真，但值得用另一种问法复核。A6-A 则是发育完成后首次受检。内存 1.28 GB、缺页 876、无孤儿。

> **TICK 197 — A5 验证收尾，并查出一件比原问题更重的事：主定理本身就是条件的。** 提交 6d8125674。纠正轮已把标题与 O(V log V) 主结果恢复，线性结果改为携带具名假设 (KN85) 的条件定理，literature_check.md 改记为"书目记录已核实；陈述未核实"并将 zbMATH 评论登记为二次转述、明言其**不能**封闭代数到有理的那一步；且逐字引出了该 1985 页必须提供的确切陈述，以便日后取得原页即可机械地封闭。裁定：锐无平方因子 Mahler 界、碰撞-射流不等式、奇素数多重碰撞定理（经执行方自查出并修正一处分式线丢失）均无外部输入，确认；素-初刚性定理与采样阶推论条件于 (KN85)，后者下界无条件、仅上界继承缺口。**但随后查出：被恢复的 O(V log V) 主定理同样依赖 (KN85)，而它没有说。** 我逐行核过依赖链：主定理证明（sec_refocused_odd_adams_sampling.tex:174）调用 p=2 的提升定理；提升定理的证明（sec_refocused_boundary_collisions_part1.tex:548）结尾调用 prop:algebraic-mahler-coboundary；而该命题正是归于 Keiji Nishioka 1985 的代数-有理接口。已查无奇偶性旁路。**这推翻了我自己的前提**：我当时告诉执行方"不能拿已证的 O(V log V) 去换带未核实前提的线性结果"——而那个 O(V log V) **从来就不是无条件已证的**。现状是论文把一个新定理的依赖诚实标出，而主定理静默地继承同一前提——这比最初的错误更坏，因为现在已知。已派修复（sprint/a5_headline_dependency_task.txt）：**按证明链而非 grep** 列出所有抵达该命题的结果，逐个在定理假设处标明 (KN85)，在摘要与引言各说一次而不埋也不滥重复，保持"哪些部分自立"可见，并重新衡量标题是否超声称；明令不得用评论/摘要/转述/OCR 封口，不得再试突破付费墙。**核验清单新增第四道：源码无抑制块**（\iffalse / \endinput）——A2 那边曾以此方式遗留 1103 行已删文本而日志全绿，该残留已以 fa3e39d54 清理。A3-B、A6-B 修订仍在跑。内存 1.45 GB。

> **TICK 196 — 三篇大修落成任务，已派两篇；并把反复出现的约束固化为可复用模板。** 模板存 sprint/_template_editor_revision.txt，三份包装任务为 a3b/a6b/a4_editor_revision_task.txt。**设计要点**：不再由我转述条目（转述会失真），而是直指该论文 artifacts 里的归档报告为规格书，要求逐条实现 PART THREE；并把本轮反复付出代价学到的四条写死在模板里：（1）**主操作是删不是改**，页数不降就是读错了题；（2）**artifacts/oracle_*.md 只读**——曾有 agent 为让自己的审计通过而改写评估者原文，模板明写"若审计与归档文本冲突，错的是审计而非归档"；（3）**开工前先 grep 本论文 artifacts 里的旧 blocker 与来源缺口**，已关闭的否定性结论不得用更弱的证据重开（付费墙后的原文不会因为评论数据库转述了它就变成已核实）；（4）**编译干净不等于印出来干净**——必须 pdftotext 抽正文核：无印出的控制序列、无 .tex/.pdf、无 ??、无悬空的"见补充材料"指针、且编号按首次定义递增；若发现硬编码 	ag/\setcounter 则移除机制。**A4 的第 10 项直接写作 "Remove revision-response vocabulary throughout"**——这是同一种防御性散文病的**第四次**独立诊断，且这次是被直接命名的。A4 第 1 项另要求移除那份 43 页的独立数学补充材料。已派 A3-B、A6-B 两个 agent；A4 暂缓，需等内存与并发降下来再派（同时只跑一个 agent 改同一篇，但总并发也要管）。A5 纠正轮仍在跑。内存：首采缺页 2592/s，复采 0/907/0/0、内存稳在 1.58-1.60 GB，不属持续，不减。

> **TICK 195 — A2 重组完工并核实入库（8f23634c2）；A4 house-style 回来，三篇均为大修。** JFA 正文 **87+33 → 32 页**，补充材料整体取消；构成 stable 脊柱（相对熵耗散与端点表示、临界 stable 平移估计、最优首个未匹配矩渐近、逐律正尾部射流分解与抽象核定理、锐性构造、一个应用），Cayley-Haar 预备不再横在引言与 stable 定理之间。**证明安置的病这次是从实质上治的**：tick 186 只改了重定向宏的印刷方式，真正的问题是主文充当自己证明的索引；现在正文**零处**指向补充材料（pdftotext 核实 "Supplementary Material" 出现 0 次）。被移出的 Cauchy 系数层级、Gauss 求积、高阶系数缺陷、RKHS 完化与格采样另成一篇 `2026_cauchy_poisson_entropy_coefficients_quadrature_rkhs_lattice`（108 页），其 metadata 如实记录分离来源且**未编造目标期刊与录用概率**（尚未评估）。独立核实：两目录清洁重建 exit 0、undefined 全 0、32 与 108 页、PDF 正文零泄漏、方程号首次出现顺序递增、三个 verifier 全 PASS、14/14 单元、SHA 29/29；并按新定的证据完整性检查确认 artifacts/oracle_*.md 与 HEAD 逐字节一致。**三篇新 house-style 裁决均为大修**：A3-B（ETDS）MAJOR REVISIONS、A6-B（JNT）Major revisions、A4（Monatshefte）Major revisions。三份报告已存各自 artifacts，待详读后落成改稿任务。至此该问法已覆盖六篇：两篇小修、三篇大修、一篇退修重投。A5 纠正轮仍在跑。内存 1.16 GB、缺页 96。

> **TICK 194 — A5 验证第一轮落地，结果印证了那条约束的必要性；又两篇 house-style 回来，均为大修。** **A5：掉入了我担心的那个坑。** codex 自己的假设审计确认 Theorem 5.1 "导入了两条 Nishioka 结果"，却仍将其记为 CONFIRMED，并用**第三方评论性转述**封口："因出版社正文仅限订阅，该特例改对照 John H. Loxton 的 zbMATH 评论 Zbl 0568.12014 核对"——而这正是前一轮明确拒绝的证据类别。在此基础上它**替换了主结果**：标题由 "Finite radial determination ... odd-Adams-invariant abelian two-group extensions" 改为 "Linear radial determination ... prime-primary abelian extensions"，M(V)=V，并自述"旧的 O(V log V) 径向主结果已移除"。纠正轮已按显式会话 ID 续接启动：按"无外部输入 / Kumiko 1982 / Keiji 1985"重排五条裁定，凡需 Keiji 1985 者降为 CONFIRMED MODULO THE UNVERIFIED KEIJI NISHIOKA 1985 STATEMENT 并写明缺哪一句、该句须说什么；恢复 O(V log V) 标题与主结果；线性定理改为**把依赖写进假设**的条件定理；Corollary 5.3 不得再呈现为无条件封死；literature_check.md 改记为**未核实**并将 zbMATH 评论登记为二次转述。Theorems 2.1、3.1、6.1 不用外部定理，裁定应完整存活。**教训已写入长期记忆**：前一轮的否定性结论必须被**逐字引入**后续任务书，否则新 agent 会用更弱的证据重开已关闭的问题；那份 blocker 就在该论文自己的 artifacts/ 里，错在任务书没指向它。**新到两篇 house-style**：A3-B（ETDS）MAJOR REVISIONS、A6-B（JNT）Major revisions，已存 artifacts，待详读后落成改稿任务。A4 仍 waiting_response。A2 重组转录已 17 MB、仍在跑。内存：缺页再现 60471 与 24434/s 尖峰，但可用内存稳定在 1.44-1.54 GB、间隔采样为 16 与 54/s，仍属成批读入而非频繁换页（后者会压低自由内存），不减并发。

> **TICK 193 — 空转一拍：三 agent 三 Oracle 均在飞，无可收割。** 三份转录均无 tokens used（A5 验证 9.9 MB、A2 重组 8.1 MB，均大幅增长）；A3-B、A6-B、A4 三发 house-style 均 waiting_response。**内存：缺页出现 14318 与 38373/s 的尖峰，但判为不需减并发，理由需记下**：尖峰同时可用内存从 0.86 **升到** 1.62-1.72 GB。页调入率高而自由内存同时上升，是进程在成批读入文件（三个 codex agent 加 latexmk），而非内存不足导致的频繁换页——后者的特征是缺页高且自由内存**被压低**。再采 6 次为 0/178.7/25.7/213.2/31.7/0，内存 1.51→2.51 GB，已完全回落，故非"持续 >1000/s"。三个 agent 均在中途，不减。**A8-A 编号修复：根因确实被动了**——main.tex 中 \setcounter{estimator} 已为 0 处，sections/collision_theorem.tex 中硬编码 	ag{} 也已为 0 处，即手写标号已整体移除、交回 LaTeX 自动编号，而非把写死的值改成另一串递增数字。该目录工作区现有 175 项变更，待其收尾后按六道核验复核并更正 eb7048fd9 的记录。

> **TICK 192 — 三个 agent 均在飞，空闲的 Oracle 池用于将 house-style 问法推广到其余稳定论文。** 无可收割：A5 验证、A8-A 编号修复、A2 重组的转录均在增长且无 tokens used。**内存触线且已处置**：首采 0.57 GB（低于 0.6 阈值），但硬缺页仅 52/s——阈值的目的是避免频繁换页，故先复采再决定。复采 5 次为 1.27/1.24/1.33/0.97/1.27 GB、缺页 16.9-390.5，均在限内；占用前五为 claude 664 MB、vmmemWSL 607 MB、Cursor 366+285 MB、MsMpEng 345 MB——**都不是冲刺 agent**，即使减并发也释不出这些内存，而三个 agent 均处中途、杀任一个都会丢失已做工作。判为瞬时回落，不减。**新派三发 Oracle**：house-style/审稿人/编辑门槛三合一问法推广到 A3-B（ETDS）6df68e07-d72d-4c6e-8ab8-81b7eb834dcb、A6-B（JNT）127319c8-ce56-49fd-b4ff-7f65de5296b1、A4（Monatshefte）e0829e4f-4c82-477c-8f42-fb516950976b。选这三篇的理由是它们当下稳定：A5 正在验证中内容可能变、A6-A 刚改、A2 正在重组，对正在变动的稿子问行文风格是浪费。该问法的已知产出：三篇中两篇得 ACCEPT WITH MINOR REVISIONS、一篇得 REJECT AND RESUBMIT，且三篇均被独立诊断出同一种防御性散文病——对剩余论文先问再改比盲改便宜得多。

> **TICK 191 — A2 重组已派（本轮最大一块）；并更正一条我自己提交过早的记录。** **更正：提交 eb7048fd9（A8-A）里带有编号错位缺陷。** 第 4 节重排后，旧的印刷编号被冻结在原处：方程标号按阅读顺序印成 (3.17)(3.18)(3.13)(3.19)(3.20)(3.21)，而 (3.10)-(3.12) 排在其后；"Estimator 7" 于第 18 页出现而 "Theorem 4" 在第 20 页。我已独立在构建后的 PDF 中复现。我当时核实了引用能解析、被移出定理陈述的机制仍存，**但没检查印出的编号是否递增**，所以缺陷进了库。根因不是计数器值错，而是方程用**硬编码 	ag{} 加 \setcounter 写死**——手写标号意味着 LaTeX 根本没在编号，因此**今后任何一次重排都会再次静默错位且永远不会有日志警告**（手写标号总是"解析成功"）。已要求修根因而非改数字：去掉硬编码标号、交回 LaTeX 自动编号、用 \label/\eqref 承载引用，并先确认补充材料的跨文档引用是否依赖这些具体数字。**我方固定核验因此再加一道**：现为——清洁重建、undefined 三项归零、**PDF 正文抽取**、**编号顺序**、verifier 与单元测试、SHA。前两道都是被实际缺陷逼出来的，不是预设的。**新派：A2 JFA 重组**（sprint/a2_jfa_reconstitution_task.txt）。围绕 stable 脊柱重建现目录：保留 Thm 4.2、5.17、5.23、5.27 与 Cor 5.30、锐性构造、至多一个简明应用；移出第 3 节大部、Cor 4.5-4.8、5.1、5.3 的 Gauss 求积、第 6 节首个 proxy 缺陷定理之后大部、第 7 与 8 节全部，另组成一篇新论文（新建同级目录）。Cayley-Haar 预备不得再横在引言与 stable 定理之间；摘要整段重写为 200-250 词且禁列文献审计与非声称清单。**其中唯一触及数学的一项**：七条点名结果必须在正文或随文附录中有完整证明，且凡保留结果其证明仅为"见补充材料中某处"者必须补上证明或删除——tick 186 只改了该宏的**印刷方式**，它暴露的实质问题（主文充当自己证明的索引）本次才真正修。另明令新论文**不得编造目标期刊与录用概率**（尚未评估）。A5 验证与 A8-A 编号修复仍在跑。内存 0.85 GB、缺页 204。

> **TICK 190 — A8-A 修订入库；A5 深研究返回四条声称新定理，已派独立验证。** A8-A 提交 eb7048fd9：33→32 页；第 4 节重排使 Estimator 与残差化统计量先于定理定义，score-chart/奇异块/Schur 补/回退门/默认不拒绝移出定理陈述但**经核实仍全部存于构造与证明**（Schur 5 处、回退 2 处、奇异块与 score-chart 各 1 处）；三条补充结果的精确陈述已印入主文；防御性重复降到每项一次（fixed serial order / known sampling interval / phase-type 均为 1），而诚实限定未丢失——改以"两点阈值下界证明的是**阶**最优"的形式保留。独立核实：清洁重建 exit 0、三文档 undefined 全 0、32/22/1 页、PDF 正文抽取零泄漏、12/12 + 16/16 + SHA 5/5。**A5：深研究问法返回了实质内容**——Theorem 2.1 锐无平方因子 Mahler 界、Theorem 3.1 碰撞-射流不等式、Theorem 5.1 素-初碰撞-射流刚性、Theorem 6.1 奇素数多重碰撞，加 Corollary 5.3；自评正确性 0.96、新颖性 0.84，并自行点名最不确定的一步（仅将相对比 H_chi 降到 Q(z) 后应用本文 Theorem 3.8）。他声称这些结果应**把现有 O(V log V) 主结果换成线性定理**，并由 Corollary 5.3 精确封死采样复杂度阶。这是对我方中心结果的重大外部声称，**不得凭一份自信的写作采纳**。已派 codex 任务（sprint/a5_deep_verify_task.txt），结构为**先验证后集成**：验证阶段禁止编辑稿件，逐条给出 CONFIRMED / CONFIRMED WITH CORRECTION / UNVERIFIABLE AS STATED / REFUTED，需打开被引的本文内部定理核对其假设是否真被满足，对有限/数值声称需写脚本实测（并明言**反例是可接受且更有价值的结果**），且两条 Nishioka 文献分属不同作者（Kumiko 1982 / Keiji 1985）须分别核实。若无一存活，则不集成、如实上报。A2 重组任务仍待派。内存 1.11 GB、缺页 117。

> **TICK 189 — A3-A 九项修订完成并核实入库（d7c8a317a）。** 页数 20+4 降为 **18+0**，.tex 源码 1020 行降为 793 行——本次操作确实是删而非增。第 5 节与 S01 技术审计、supplementary_material.tex 均已删除；固定-变动系统对比移入引言，simple-Parry 依赖与阶锐性限定各成 Theorem 4.1 后的一条注记，伴随论文压到一句。引言现立 Theorem A/B/C，层次在第二页可见；第 3 节开头加了五句概念桥；标题改为 "Linear overlap transients and cyclic rank recodings in Pisot numeration"。**第 5 项（可能触及数学的那项）的处置**：四页补充判为编辑规则的第三类（扩展有限记录、复现命令、输出与哈希），不作为数学补充材料提交；其 24 项声称/计算逐条定位：19 项已在正文，5 项为例示或实现回归、无任何证明依赖之，精确根隔离则移入立方定理的证明。随后逐条核验了"任何定理不得依赖仅以机器输出存在的论证"，结果为无。**我方独立核实**：清洁重建 exit 0、undefined 全 0、18 页、PDF 正文抽取零泄漏、固定三次 28/28、任意 D 13/13（七边回归通过）、SHA 8/8。**一处需人工回补**：submission_metadata.md 被一并精简，丢失了长度区间、ETDS/TAMS 概率与伴随论文目录指针；这属流水线记账而非稿件内容，已按最新数字重写并记入"审计材料保留于 artifacts/、不属投稿件、无结果依赖之"。A8-A 四项修订仍在跑；A2 重组任务待派；A5 深研究 2bb0d4b1 仍 waiting_response。内存 1.05 GB、缺页 104。

> **TICK 188 — 三篇 house-style 裁决到齐,结论分化,且三篇被独立诊断出同一种病。** A8-A(f00cdaba)与 A2(c3109c16)取回。**A8-A：ACCEPT WITH MINOR REVISIONS**——"不建议再来一轮数学,也不认为这是退修重投的案子"。他特别肯定第 2 节的 record-to-sample 耦合与反向续延核,以及 Proposition 3 的极点阶论证(它讲清了碰撞坐标上的正信息是模型特有事实而非一般锥形 LAN 的推论),二者须原样留在主文。四项必需：第 4 节重排(Estimator 7 移到 Theorem 4 之前、先定义残差化统计量与经验信息、把 score-chart/奇异块/Schur 补/回退门/默认不拒绝等机制**移出定理陈述但全部保留在构造与证明中**)；在主文印出被 Theorem 4 证明所用三条补充结果的**精确陈述**(DQM/包络、停止得分 CLT 与信息 LLN、插入等度连续),证明仍留补充；删除重复的防御性限定；大幅缩短讨论。**A2：REJECT AND RESUBMIT**——本组此前认定最强的一篇。他明言问题不在数学："若作者愿意拆分重组,我看不出需要新的旗舰定理。"病因是**稿中至少含三篇独立论文**(一维 Cauchy/Cayley 全阶熵系数篇、stable 半群耗散与最优矩指数篇、RKHS 与整数格采样篇),题名承诺 stable 而前 27 页几乎全是 Cauchy 与径向 Poisson 机器,一般 stable 定理到第 28 页才开始；第 7、8 节作者自述为次要却仍留在正文。要求围绕 stable 脊柱重组(Thm 4.2、5.17、5.23、5.27 与 Cor 5.30、锐性构造、至多一个简明应用),移出第 3 节大部、Cor 4.5-4.8、5.1、5.3 的 Gauss 求积、第 6 节首个 proxy 缺陷定理之后的大部、以及第 7、8 节全部,另成一到两篇。另一条直指我们刚"修好"的那个宏：**凡保留结果其证明仅为"见补充材料中某处"者,必须补上证明或删除**——tick 186 修的是文件名泄漏这一表层,真正的病是主文把证明外包。**三篇独立得出同一诊断**：A3-A"散文表现得像历次审计的记录"、A8-A"过度防御,同一组限制被反复陈述"、A2"每一段都像是为预先堵住某个假想异议而写"。这是我方流水线自身的指纹——每轮审稿追加的澄清逐层沉积,从环内看不见。已写入长期记忆(feedback_referee_round_scar_tissue),并在任务书里把本次操作明确定义为**删而非改**。已派 A8-A 修订(sprint/a8a_ejs_revision_task.txt)。A2 重组任务待派。A5 深研究 2bb0d4b1 仍 waiting_response。A3-A 九项修订仍在跑。内存 0.98 GB、缺页 276。

> **TICK 187 — A3-A 拿到本次冲刺最强裁决:ACCEPT WITH MINOR REVISIONS,且明言不需要任何新数学。** Oracle 88ce0241 取回(572 行),存 sprint/result_A3A_style_r1.md 与 artifacts/oracle_sprint_A3A_style_r1.md。他以 ETDS 审稿人身份给出接收+小修,并以编辑身份列出 9 项必需、2 项可选,同时写明"就这二十页的证据而言,不需要额外的定理、推广或应用;剩下的差距压倒性地是写作、层次与包装"。**house style 那一问确实拿到了可操作的答案**:他点名了 2023-2025 年 ETDS 实际录用的六篇(Akiyama-Hichri、Mercat、Moss-Perrone、Damanik-Lenz、Gorodetski-Kleptsyn、Wormell)作为语域基准,并判定我方"在长度、证明密度、定理规模与附录比例上已在 ETDS 正常区间内";他还确认短证明只要被引定理真正承担了数学工作且归约透明就完全可接受,ETDS 不要求为凑长度复述标准论证——这直接否掉了"证明短=有问题"的顾虑。**核心诊断值得单独记下,因为它是我方流水线自身的指纹**:"部分散文仍表现得像该稿历次审计的记录:它保留了每一处边界、区分、限定与材料归属。"即历轮审稿每次追加一条防御性澄清,这些澄清累积下来,如今读起来像是在回应旧异议而非推进数学叙事。他指出最可能沉掉这篇的不是数学,而是**反复的边界管理与伴随论文讨论使其看起来像一个更大分类项目的技术切片,而非有自身概念弧的独立 ETDS 文章**——并判定可修。必需项要点:摘要重建为单一主结果并删去 {E_m,-E_m} 与后继集为空这类证明级细节;引言加 Theorem A/B/C 显式层次使逻辑在第 2-3 页可见;删除审计与反驳语域(点名 Remark 2.1、"not the definitional center"、"not a disguised standard-initial-value convention"等);第 5 节整节取消并把有用材料分派回引言与 Theorem 4.1 后的注记;伴随论文压到一句;第 3 节开头补概念桥;第 2 节不再重复 G_m(U,D) 的完整定义、整体链二分法改为带标号推论;代码可得性声明改回普通数学语域。**第 5 项可能触及数学**:须判定四页补充材料是否含证明必需的推理(是则并为 Appendix A),并显式核验"任何定理都不得依赖仅以机器输出或验证断言形式存在的论证"。已派 codex(sprint/a3a_etds_revision_task.txt),并提醒执行方本次修订的核心是**删**而非增。Oracle:A5 deep 2bb0d4b1、A8A style f00cdaba 仍 waiting_response;A2 style 二次 extraction_failure 后已第三次重发为 c3109c16-cc8e-4ad0-8304-8c913fee1428。内存 1.59 GB、缺页 15.9。

> **TICK 186 — 渲染缺陷清理完工入库,且实际比我查到的更广;两发 Oracle 因 extraction_failure 已重发。** 提交 de3064199。**缺陷范围比 tick 184 我自己扫出的更大**:EJS 主文不是 10 处而是 11 处,补充材料另有 6 处反向的 main.pdf 泄漏,字面量 qquad 除 (2.1) 外在补充的 (M4)、(M5) 两式中另有两处;JFA 除 \relocatedproof 宏外,正文散文里还有成批的裸 \path{...} 源文件名引用(形如"sec_strip_30_cardinal_observation.tex, Corollary ..., collected by supplement_relocated_support.tex"),另有 3 处宏外的 supplement.pdf 提及、补充材料印出 main.tex 一次。根因两条:EJS 是 xr-hyper 的外部文档未给空的可选 URL 字段,故把伴随文件名附到每个导入标签上,补上 \externaldocument{...}[] 即止;JFA 是宏本身把内部记账印了出来,**宏已单独修好,17 个调用点逐字节未动**,位置参数仍照传、只是不再印出。独立核实:两目录清洁重建,五份文档全 exit 0、undefined ref/cite/multiply-defined 全 0,页数 33/22/2/87/33 无一移动一页;PDF 正文抽取五份全部为 .pdf=0、.tex=0、qquad=0、??=0;EJS 12/12 检查 + 16/16 单元 + SHA 5/5,JFA 三个 verifier 全 PASS + 17/17 单元 + SHA 13/13。**方法记录:这一整类缺陷对基于日志的核验完全不可见**,必须编译后用 pdftotext 抽取正文再读;此项已并入我方每篇的固定核验步骤。Oracle:A8A 与 A2 的 house-style 问题返回 extraction_failure(worker 端抓取失配,非协议问题),已取消并按原协议重发,新 id 分别为 f00cdaba-05de-40ab-b737-a3950eacaf89 与 c763026a-8b59-4d7b-b7df-22555c4c645f;A3A style 88ce0241 与 A5 deep 2bb0d4b1 仍 waiting_response。内存 1.01 GB、缺页 4.9、无 agent 在跑、无孤儿。

> **TICK 185 — off-by-one 已修并入库;开出四种全新问法,四发在飞。** A6-A 提交 5aa99b2b5:两处下限均改为 r>=j,并补一句说明保留项为 O(j^{-alpha}) 对 j^{1-alpha} 属低阶故常数不变;修正顺带恢复了一项旧式通不过的自洽检验——j=0 时该恒等式现给出总质量 1。相邻十二处指标边界(更新递推与 Omey-Van Gulck 对应、Fibonacci 层恒等式、余项幂和、奇指标对应)经扫查均正确。独立核实:旧下限零残留、清洁重建 exit 0、undefined 全 0、27 页不变、PDF 正文抽取无印出的控制序列/文件名/未解析引用、verifier exit 0、单元 3/3。**本轮的方法进展是四种此前未用过的问法**,均非估值问题而是录用问题:(1) **house style 迁移**——不问期刊的宗旨与范围(那我们自己会读),而是要他回忆该刊近三到五年**实际录用论文的写法**:主定理出现在哪一页、引言占比、解释性散文与形式陈述的配比、证明是自带论证还是可交给引用、**正文与附录的惯常比例及何种材料按惯例下放**、人称与语域、以及"不合该刊语域的论文有哪些痕迹";然后逐节指出我方的偏离。同一问里要求他找机器写作的特征——段落长度均匀、该取舍处穷举、每句陈述前清嗓、无信息的对冲、对称句式、宣告结构而非推进论证的过渡、以及**重点分布的平坦(人类作者是故意不均的,有的三句有的三十页)**——并明言宁可被直言也不要恭维。(2) **审稿人角色**:以该刊审稿人身份写给编辑的推荐信,先给结论(接收/小修/大修/退修/退稿)后给理由,指明最可能沉掉这篇的那一条异议及其是否可修。(3) **编辑门槛**:换成编辑角色,给出可使其达到"我会接收"状态的具体条目清单,按重要性排序,分必需与可选,并**把需要新数学的条目与纯属写作组织的条目分开**——我们需要知道差距里哪部分是活、哪部分是手艺。(4) **深研究**:要求直接做数学而非评估,只要终局结论不要中间过程,不得复述本文已有内容,不得重走他人已发表的推理(可引用他人结论但须给出精确形式与假设),并明令"不要挤牙膏——能给三条就给三条";同时要求分别给出证明正确性与新颖性两个数,并区分"未找到先例"与"不存在先例"。在飞:A3A style 88ce0241-0ef2-4d5f-838f-05e62e353942、A8A style 21d34d75-dda4-48e1-97f2-321745795e5c、A2 style 1605672f-3d87-4616-b75b-11debc8648a2、A5 deep 2bb0d4b1-6640-4213-a812-152376a777d0。模板存 sprint/ask/_template_house_style_referee.txt,可复用于其余各篇。PDF 渲染缺陷修补 agent 仍在跑。

> **TICK 184b — 对上一条的两处更正,以及 A6-A 提交后查出的一个真缺陷。** (1) 我在 tick 184 把 A6-A 的发育描述为"假设逐条验证而非断言",这话只对了一半,须更正:被拆开的黑箱是 Feller 的吸引域判据(尾平衡、归一化、截断二阶矩与大跳跃界、补偿特征指数收敛、中心化展开现均在文内证明);**Omey-Van Gulck 的二阶更新定理仍是黑箱**,新证的只是其三条假设的核验(质量一、整数支撑、span 1、有限均值、2<sigma_0<3 故 1<alpha<2)与从 F(j)~Kj^{-alpha} 到平衡尾的换算。八条新编号结果中约两条是真新增(Lemma 4.5 的单侧稳定引理、Remark 4.7 的数值数据),其余六条是重组。执行方在自述里略微高估了这一点,独立审计指出后予以更正。(2) **已提交的 940ec7ba3 里有一处印错的恒等式**:平衡质量定义为 p^e_j = F(j-1)/mu,而正文印出 F^e(j) = sum_{k>j} p^e_k = (1/mu) sum_{r>j} F(r);以 r=k-1 代入时 k>=j+1 对应 r>=j,故精确恒等式的下限应为 **r>=j**。漏掉的一项为 F(j)/mu,量级 O(j^{-alpha}),而和的量级为 j^{1-alpha}/(alpha-1),确属低阶,Karamata 渐近与最终常数不受影响——但它是用等号印出的,所以照字面是假的,与 A3 那条未锚定的 "Equivalently" 属同一类。同一表达式在 Karamata 步处再次出现,两处都要改。已派 codex(sprint/a6a_equilibrium_offbyone_task.txt)修正并顺带扫查相邻的指标边界(同类错误常成对出现),另轻度收紧审计指出的三段重复。任务书明令不得把等号弱化为渐近了事——精确恒等式在 r>=j 下确实成立,应照此陈述。(3) 我在 d240d5dfd 里提交了伴随论文 `cyclic_rank_thresholds` 的互引条目却没有重建该篇,属核验疏漏;现已补做:清洁重建 exit 0、两文档 undefined 全 0、36+15 页、PDF 正文抽取零 .pdf/.tex 泄漏、互引在渲染书目中正常解析。
> **TICK 184 — 两个 agent 收割入库,A8-A 复评守住,并查出一类此前所有检查都看不见的缺陷。** A6-A 提交 940ec7ba3:发育完成,19→27 页、tex 1229→1686 行;二阶格更新输入与单侧吸引域判据的假设现按本文记号逐条验证而非断言,span-1 由插入语升格为证明,经典 Fibonacci 配分函数的非整数有限尺度推论单列;并补上此前完全缺失的可复现校验——数值确认尾常数 b_C=8,截断和随截断增大依次为 7.6324、7.8769、7.9590、7.9864。独立核实:清洁重建 exit 0、undefined 全 0、27 页、verifier exit 0、单元 3/3、SHA 5/5。A3-A 提交 d240d5dfd:伴随论文入参考文献表并在两处引用,**按未投稿事实登记为 companion manuscript,无 DOI、无 arXiv 号、无 URL**(已逐项复查确认);参考文献 [6] 补上 arXiv:2606.30496v2。独立核实:三文档清洁重建 exit 0、undefined 全 0、20/4/1 页、固定三次 28/28、任意 D 13/13、SHA 8/8。**A8-A 复评(502daf2f)回来:EJS 51% 守住**,他确认改写没削弱 Theorem 4,反而"更可信,因为读者现在能看出哪条定理消除哪个障碍";明确不要压到 25 页去投 Bernoulli(33 页时仍是 11-13%,即便压缩成功拿到 21% 也不及 EJS 51% 的一半,且压缩会让中心奇异定理重新显得依赖台下的串行代数);AoS、EJP、Bernoulli 与更窄的专业刊均判为更差,Statistical Inference for Stochastic Processes 虽字面最贴切但已停止接收新投稿。**但他指出了成品 PDF 的生产缺陷,而这类缺陷此前每一轮检查都看不见**:我方的核验一直是基于日志的(exit code、undefined ref/cite、multiply-defined),而这些缺陷的 LaTeX 完全合法,只在渲染结果里现形。经我方用 pdftotext 抽取正文复核:A8-A 主文 10 处交叉文档引用把文件名印了出来(如 "Lemma S2supplementary.pdf"),显示式 (2.1) 里印着字面量 qquad。**随后我把这类检查扫了全部十一篇,查出更严重的一处**:A2 `cayley_chebyshev`(本组最强、投 JFA)的 \relocatedproof 宏在正文里印出我方的源文件名,形如"See Supplementary Material, ..., in supplement.pdf (source: sec_entropy_core_main.tex)",全文约十七处——把我方的 LaTeX 文件布局直接印给审稿人看。其余九篇该项为零。已派 codex(sprint/pdf_defect_cleanup_task.txt)修这两篇,并要求用 pdftotext 抽取正文验证而非只读源码,同时把整类缺陷(正文里的 .tex/.pdf、印出的控制序列、?? 引用、TODO 占位)在两篇里扫一遍。内存 1.96 GB。**核验方法已改进:此后每篇都加一道 PDF 正文抽取检查。**





























































































































































































> **Oracle 协议已变更(2026-08-14 实测)**：worker 升级到 `cdp-2.5-chat-work-media-gate` 后加了 `submission-gate` 前置校验。**新会话必须在 `--tag` 里显式写 `mode:chat` 或 `mode:work`**（v1 通过 tag 传模式，`--mode` 参数不再被接受）；**续接会话必须省略模式控制与附件**，原 worker/账号与控制项自动保留；首轮只能带 `--pdf` 或 `--attach-file` 其一。不合规的任务会一直排队且**永不派发**——症状是 worker 全空闲、Queued 不降。


**目标期刊在整轮冲刺后没有变化。** 深化显著增厚了内容（见下），但没有哪一篇因此跨过档次线；PRIMARY 维持上表。

### A9 `homological_visibility` — 新入列（APAL 拒稿后重建）

**拒稿性质要看清:不是内容被否,是没人读到内容。** `APAL-D-26-00107`,主编 Benno van den Berg 原话:"does not meet the standard requirements for a mathematical paper **in terms of style**"、"uses terminology **in a way that is not standard and is not explained**"、因此 "an evaluation of its content **is not possible** in its current state"。**没有审稿人评判过这篇的数学。**

**这意味着换刊无效** —— 同样的问题在任何期刊都会得到同样的 desk rejection。APAL 本就是最对口的去处(van den Berg 是范畴论/构造性数学专家),他给的是可修复的诊断。

**结构性成因(已量化)**:93 页、52 个定义、81 条定理/命题,核心词汇几乎全自造且与标准术语冲突:

| 词 | 次数 | 冲突 |
|---|--:|---|
| `visible` / `visibility` | 223 | 无标准含义,须自定义 |
| `realization` | 198 | **模型论中已有标准含义**(realizing a type),此处另作他用 |
| `slice` | 133 | **范畴论 slice category** 是标准术语 |
| `admitted reference` | 42 | 完全自造 |
| `bouquet` | 19 | 拓扑中指楔和 |

专家读到 `realization` 会自动套用模型论含义,越读越不对,最后判定无法评估。

**内容初判(待独立评估确认)**:摘要里能辨认出的是硬对象 —— 层化单位在终纤维上的满射性配合 $H^1$ 消没、带 band 的实现叠扩张给出落在 $H^2$ 的 **Giraud 类**、character-blind 情形恰为纯 $\operatorname{Ext}$ 贡献、以及一条**不可定义性分离定理**。最漂亮的是结尾那条充要刻画:**bouquet 好覆盖上,非零有限交换群 $G$ 出现为纯双分支消解核,当且仅当 $d(G)\le2eta$ 且 $G$ 不是循环 $p$-群**。这条被埋在 93 页末尾,**它应该是标题和引言第一句**。

**执行顺序(不可颠倒)**:① 独立评估定档(进行中)→ ② 术语审计 + 改名 + 术语对照表 → ③ 压缩至 35–45 页(用 A2/A4/A7 已验证的补充材料方案)→ ④ 引言用标准语言前置主定理 → ⑤ 再选刊。**先选刊没有意义。**

**候选去向**:重写后仍投 **APAL**(说明已按编辑意见重构),或 **JSL** / **Logic and Analysis** / **Theory and Applications of Categories**(TAC 对层论/gerbe 方向对口且开放获取)。

⚠️ **不可投 Nuclear Physics** —— Elsevier 只有 Nuclear Physics A/B,**无 D 刊**;且本文属层论与范畴逻辑,与核物理/高能物理无交集,投过去会当天 desk reject。

### 是否还有继续冲刺的必要与可能（2026-08-08 评估）

> ⚠️ **已失效(2026-08-16)**:本节的逐篇"继续/换向后再评"判断作于第三代提问之前。此后八篇均已产出领域对象定理、完成档位重估与结构估值。当前状态以顶部状态表为准。

判据用"最后一轮是否仍产出可整合的新内容"，而非轮数。

| 篇 | 已收轮 | 最后一轮 | 判断 |
|---|:--:|---|---|
| **A6** | 6 | r7 严格速度分离（区间证书）| **继续**——连续三轮 r5/r6/r7 均有实质产出，边际最高 |
| **A5** | 5 | r5 有效有理 Mahler 判定程序 | **继续**——r4 闭合 Nishioka 卡点、r5 升级为判定程序，方向明确 |
| **A8** | 6 | r7 尖锐交换点耦合边界 | **继续**——仍在产出，但拒收比例升高（minimax、尾格统计量、临界常数 $4e^c$ 均被驳回）|
| **A2** | 4 | r5 原始尾 Poisson 能量分解 | **继续**——但近两轮以"撤回/否定"为主，接近拐点 |
| **A3** | 2 | r3 无统一因果长度上界 | **继续**——探索最少的一篇，尚未触及边界 |
| **A7** | 4 | r4/r5 连续两轮诚实拒答 | **换向后再评**——原问题被 GRH、一致性范围、缺局部化三重阻断；r6 已改问本文有限结构可无条件处理的问题，一轮即可判定是否值得续跑 |
| **A4** | 3 | r4 诚实拒答（359 字节）| **换向后再评**——可判定性/$\Sigma^0_1$-困难性在给定有限输入模型下证不出；r5 已改问承诺问题的精确递归论分类 |

**结论**：没有一篇触发饱和（新一轮全判 `ALREADY-IN-PAPER`），所以**技术上都可以继续**；但边际价值已分层——A6/A5 最高，A3 最未开发，A7/A4 需先看换向后的一轮再决定。

**真正的瓶颈已不是深度，而是投稿就绪度**：A3 57 页、A8 55 页仍略超目标刊；A6 的 `sec_local_spectrum.tex` 1504 行超出 800 行规范且压缩尝试已回退（原因见下）。若要投递，这些比再加一条定理更关键。

**可能性上的现实约束**：Oracle 链路依赖 Cloudflare WARP 隧道，该服务停止后 `nyx-api.chrono-ai.fun` 完全不可达（WSL 内 github 可达、该主机返回 000），且启动服务需管理员提权。链路恢复前无法进行任何一轮。

### 冲刺产出（均经 codex 逐条检验 + 我方独立复跑 verifier 与编译后提交）

- **A5** `thm:determinant-boundary-lifting` 闭合了长期卡住的边界碰撞问题——绕开取不到的 Nishioka 1985，改用 1982 特殊值定理并显式核验全部参数（$p{=}2,N{=}0,n{=}1,m{=}2,M{=}2,U{=}1,L{=}1$，$M(p{+}N)n^2=4<2^{2+1/L}=8$），配合 Dieudonné–Dwork 整性给出 $F\in\mathbb Z[[z]]$；r5 再把存在性升级为**判定程序**（`thm:effective-rational-mahler-coboundary`：显式次数/高度界 + 有限 Padé 判定）。承重的平方归一化 $F(x)^2=\Pi_x(H)$ 已明写；不主张任意正有理 $H$ 的逆命题。
- **A6** r7 证得**严格速度分离** $v_2>v_c$，间隙 $\ge 0.001171960512764161$。截断证不了它（$\gamma_2$ 级数从下方慢收敛，部分和给的是 $v_2$ 的上界，方向相反），故改用区间证书 `verify_speed_separation.py`：$\gamma_{\text{upper}}=4435863088103/847288609443$、$v_2^{\text{lower}}=0.132397168$、$v_c^{\text{upper}}=0.131225208$。r6 另证**统一命题不成立**，并把 dyadic 词计数明确归为 Weinstein 已发表公式的系数推论。
- **A8** r7 整合固定交换点的**尖锐充要边界** `prop:helmert-growing-layer-bracket-main`；r4 补 Markov–Palm 交换点全切空间。
- **A2** r5 整合 `thm:raw-tail-poisson-energy-decomposition`（原始尾 Poisson 能量分解）。
- **A3** r3 证得三次 simple-Parry Pisot 数上 $\ell_{\mathrm{cau}}$ **无统一有限上界**，并收紧了 simple-Parry 系列结论的适用范围。

### 篇幅压缩（2026-08，本地执行，均经清理重建核验）

顶刊对篇幅有硬约束，故在 Oracle 链路中断期间就地压缩。**做法**：只迁移不删改，迁出的章节由独立编译的补充材料承载，正文留精确指针。

| 篇 | 原 | 现 | 补充材料 | 目标刊 |
|---|--:|--:|--:|---|
| A2 `cayley_chebyshev` | 90 | **55** | 31 | JFA ✓ |
| A4 `prime_languages` | 63 | **38** | 29 | Monatshefte ✓ |
| A7 `upper_fibers` | 50 | **25** | 27 | Fibonacci Quarterly ✓ |
| A6 `zeckendorf_fibers` | 62 | 62（已回退）| — | JNT |

**验收标准（三篇均通过）**：定理类环境总数不变；迁出章节的每个定理标签在 `supplement.pdf` 中解析；两文档**清空全部 `.aux` 后从零重建**，exit 0 且未定义引用/文献/重复标签/错误全为 0；verifier 与测试原样通过。A7 另外把 3805 行的单体 `main.tex` 拆到最大 544 行。

**教训（下次务必前置）**：
1. **增量编译会靠陈旧 `.aux` 报假成功** —— A2 曾自报"零未定义"，清理重建实测 60 处未定义引用、25 处未定义文献。只有 `latexmk -C` + `rm -f *.aux` 的完整序列算数。
2. **补充材料必须是能编译的真文档**，不能只是一串 `\input`；否则迁出的定理"源码里有、任何 PDF 里都没有"，正文指针悬空，而"零未定义引用"这项检查**发现不了**（指针是 `\path{}` 字面量）。
3. **补充材料只能包含正文不再 input 的章节** —— 重复 input 会把文章重排一遍。
4. **A6 回退原因**：正文与补充材料相互交叉引用，xr-hyper 需要往复多遍才收敛，单向"先正文后补充"的构建序列无法达到零未定义引用。若要重做，须先切断双向依赖（把被补充材料引用的结果留在正文，或改为文字指针）。

### 被拒绝写入的内容（同等重要）

深化的价值有一半来自拒收。已记录在案的有：A6 r4 的 **17 条 WRONG**；A8 的 minimax 主张（切线论证无效）、尾格统计量、临界常数 $4e^c$（精度不成立，反例已存）；A2 的跨壳层聚合主张（验伪）与"同一 Poisson 单元内不可抵消"断言（**整条撤回**，替代文字仅作经典背景、不申报新颖性）；A7 的 fibotomic 熵最优性主张（**正式撤回**，稿件确无该证明）并纠正 Granville 引用被误表述为 Fibonacci 奇重数定理；A5 的标量 Bernoulli 展开优先权归 Hasegawa–Saito（arXiv:1507.00498）。

**Oracle 两次诚实拒答**：A4 r4 在给定有限输入模型下无法建立几何同步方案的可判定性或 $\Sigma^0_1$-困难性，未向稿件加入任何定理；A7 r4/r5 连续两轮判 little-o 命题未决，障碍精确定位为 Sanna 的无条件定理只控制 $d\mid\alpha(p)$ 而非纤维 $\alpha(p)=d$、固定指标渐近式依赖 GRH 且仅在 $x>t^3$ 上一致（而 $\alpha(p)=d$ 迫使 $p=td\pm1$），r6 起已正式换向到本文有限结构理论可无条件处理的问题。

---

## 现状定稿 · 目标期刊（2026-08，深化 + Oracle 外审后，codex 选刊评估）

> ⚠️ **已被取代(2026-08-16)**:本节的目标刊定稿作于本轮重估之前。A2→JFA、A3→ETDS(若拆)、A4→Monatshefte、A5→ETDS、A6→TAMS/JNT(若拆)、A7→FQ、A8→EJS(若重构)、A9→Cahiers,均以顶部状态表为准。

6 篇核心 Track A 均已完成：**深化新定理（verifier 验证）→ 前沿门 → Oracle referee 外审 → 修订**（A2/A3/A7/A8 首轮已提交；A5/A6 二轮已提交）。目标期刊依**修订后实际内容 + 外审新颖性天花板**定稿（以本表为准，下方各表"候选刊"列为深化前参考）：

| 篇 | 目标 PRIMARY | BACKUP | 状态 / 备注 |
|---|---|---|---|
| A2 `cayley_chebyshev` | **JFA** | Bernoulli · EJP | 两项 HIGH-rated 尖锐熵阈值结果达 JFA 级；71→40–45 页待压缩 |
| A3 `sharp_three_window` | **DCDS-A** | JNT · Dynamical Systems | ⚠️ **DCDS 曾拒旧版**——重投前须确认可行或转 backup（JNT）|
| A5 `finite_parts` | **Dynamical Systems** | QTDS · DCDS | 聚焦 20 页修正 note（Frobenius 积常数修正 $F_\rho$/$L_\rho$）；逆刚性留背景 |
| A6 `finite_window_zeckendorf` | **JNT** | Adv. Appl. Math · EJC | TAMS 原过高；冻结定理 + affine 对应属 JNT 专业层级 |
| A7 `upper_fibers` | **Fibonacci Quarterly** | J. Integer Seq. · INTEGERS | 37→20–25 页 + 计算附录 |
| A8 `detector_shells` | **Stochastic Models** | MCAP · JPhysComm | 由物理框架转对口应用概率（D-MAP/更新理论）|
| A1 `tilt`（banked）| JTP（在审，不动）| — | 深化以 `_deepening_notes/tilt_interior_nongibbs/` 归档，待 JTP 结果后再定 |

**选刊原则**：凭修订后实际达到的层级对口投递——A2 凭 HIGH 结果守住 JFA；A5/A6 回落至其真实专业层级（外审判为 medium novelty），非武断降档。**投前共性动作**：多数篇需按外审压缩页数（A2/A7 尤甚）并把 certificate/comparator 材料移入 supplement。

---

# Track A — 深化已有真结果（最高 ROI，方法已在手）

对已有的 modest 结果，不原样重投，而是补一条**新定理**把它抬成强论文，深化+验证后再选刊。按"深化后成强稿的把握"排序。

> **深化阶段状态（2026-08-01，manual codex + 独立复核 + commit）**：✅ **A2/A5/A7/A3/A6/A8 已完成并提交**（每篇都独立重跑 verifier + 一手核验，非采信 codex 自报）。⏸ **A1 未应用**（深化目标已在 JTP 在审稿中，仅得一条小增量=k-态端点律，已另存 `_deepening_notes/tilt_general_sft/` 待 revision，不动 live 投稿）。下一步：这批进入 **polish（F→A→B→C→D referee）+ Lean 有限阶恒等式 + fresh-Oracle + 选刊 → 投递**。

| # | 起点论文 | 下一步要证的定理（深化） | 难度 | 候选刊（深化+验证后再定）|
|---|---|---|---|---|
| A1 ⭐ | `tilt_dynamics` | zero asymptotic variance of cylinder-information ⟺ 测度为最大熵测度（**任意 mixing SFT**，脱离黄金壳）——**是他们自己提的 open problem**，cohomology 判据 alphabet-agnostic | 可行 | ETDS / Nonlinearity |
| A2 ⭐ | `cayley_chebyshev` | **去水后**补全全阶矩-系数等价：$A_{2m}(\nu)<\infty \iff \mathbb{E}|X_c|^{2m-2}<\infty$（每阶带 converse）——把一个阈值升成熵-Laurent 矩层级 | 可行（多为重整）| JFA / Bernoulli / EJP |
| A3 | `sharp_three_window` | 阈值函数 $m^*(\beta)$ 跨 metallic/β 族分类，证黄金基是唯一达 $m^*=3$ 的极值 + 熵/zeta 不变量解释 | 可行（同方法）| ETDS / Nonlinearity |
| A4 | `prime_languages` | REG-immunity ⟹ **CF-immunity**（Ogden 升级）+ 从 Zeckendorf 推广到**所有 Pisot 数系**——base-independent"素数在任何 Pisot 数系不可识别" | 可行 | Monatshefte / TCS / RAIRO-ITA |
| A5 | `finite_parts` ζ | **inverse-rigidity 框架（codex 更优）**：刻画 cocycles-mod-gauge $\to\{\det(I-zB_\rho)\}_{\rho\in\hat G}$ 的核——给出行列式相等 ⟹ Livšic 上同调的精确图假设 + 最小反例。（现结果只重建周期数据，这才是真反问题定理）。可选再推紧群扩张 | 中–高 | ETDS / J. Modern Dynamics |
| A6 | `finite_window_zeckendorf_fibers` | 完整**大偏差原理** + 可微 rate function（Gärtner–Ellis），解析化 $q\to\infty$ 零温极限 | 中 | JNT / Monatshefte / Trans. AMS |
| A7 | `upper_fibers` | **先修 n=30 数据 bug**（8 型只实现 5 型）；再证 $\#\mathcal{M}_n$ / 平均阶的渐近（Sperner/Wigert 界）| 投机 | Fibonacci Q. / JNT |
| A8 | `detector_shells` | 深化路径最难：目标是**n-态 killed-leakage D-MAP 的可辨识性/quotient 结构定理**（把 2×2 quotient-inverse 升成一般 n 态的结构刻画）。先做可行性探查再定；最低优先，但不丢 | 高/待定 | 强化后定（应用概率刊）|

# Track B — 提取全新、未被任何论文覆盖的 Lean 验证种子（可信度最高）

这些在 `lean4/Omega` 已验证、且 grep 全部 paper body 零命中——纯新，直接可写。

| # | 种子（Lean dir/files）| 已验证主结果 | Lean | 目标刊 |
|---|---|---|---|---|
| B1 ⭐ | Fibonacci-cube / 独立集枚举 `Omega/Combinatorics`（`PathIndSet.lean`, `FibonacciCube*.lean`）| 路径图 $P_n$ 独立集数 $=F_{n+2}$（container 双射）；Fibonacci cube $\Gamma_m$ 结构。深化：独立多项式/谱、自同构群 | ✅ | Fibonacci Q. / Discrete Math. / Australas. J. Comb. |
| B2 ⭐ | Metallic-gap `Omega/Kronecker`（`MetallicGap.lean`, `W1DenominatorClosedForm.lean`）| $\kappa(A)=A/\log\lambda_A$（$\lambda_A$ 金属 Perron 根）在 $A\ge1$ **严格递增**（隐式代数族上的超越单调性）+ 有理 α 的 $W_1$ 传输精确闭式 | ✅ | Nonlinearity / ETDS / JNT |
| B3 | Resonance-window Galois 证书 `Omega/POM`, `Omega/RootUnitCharacterPressureTensor` | 两个共振窗数域 Gal$=S_{13}$（Jordan 判据，分歧素 59/62927）；显式 $S_4$；$S_4\times S_7$ 线性无关 | ✅ | Math. Comp. / LMS JCM / JNT ⚠️须对 37a1 说清区分 |
| B4 ⭐ | Lucas 幂 Hankel char-p `conclusion`（`thm:conclusion-lucas-charp-shifted-hankel-geometric-ratio` 等）| $a_n=L_n^q$、char $p>q$ 下 Hankel 秩塌缩到 $m=\mathrm{ord}(\beta/\alpha)$，平移 Hankel 几何比 | ✅ | JNT / Integers / Fibonacci Q. |
| B5 | 单次 Stokes 探针读 Minkowski 维 `spg`（`thm:spg-dyadic-outer-approx-stokes-gain-minkowski-readout`）| $|\int_{\partial U_m}\omega|\le C\,2^{-m(n-d)}\|d\omega\|_\infty$（比朴素界好一个余维）| ✗ | J. Fractal Geom. / Real Anal. Exchange / JGA |

# Track C — 把理论核的 vein 推到新定理（需真推理，部分 Lean 背书）

起点已在库中，但强定理需要投入更多本地推理。

| # | 起点（file）| 深化目标定理 | 难度 | 目标刊 |
|---|---|---|---|---|
| C1 ⭐ | rank-1 fusion defect `body/pom/parts/lem__pom-shifted-fib-fusion-defect-positive.tex`（$F_{a+2}F_{b+2}=F_{a+b+2}+F_aF_b$ + 刚性已证）| **rank-$r$ 对称 defect 分类**：$G(a)G(b)=G(a+b)+\sum_{i\le r}u_i(a)u_i(b)$ 的次指数解是否塌缩到有限 Fibonacci/Lucas 族 | 中 | JNT / Aequationes Math. |
| C2 | Cartwright 零点间隙 `appendix/fold_multiplicity/...cartwright_gaps.tex`（$\delta(R)\le\varphi^4/(4R)$ i.o.）| 闭合两侧到 **sharp constant** $\delta(R)=\frac{\varphi^4}{4R}(1+o(1))$（证 Lucas 对为极值）| 中 | J. Approx. Theory / CMFT |
| C3 | Dyadic 病态 `body/spg/thm__spg-dyadic-...ill-conditioning.tex`（只有上界 $\sigma_{\min}\le\sqrt{2n}2^{-m/2}$）| 匹配下界 → 两侧 $\kappa(\partial_n)\asymp 2^{m/2}$，再扩到非均匀 cell 几何 | 中 | SIAM J. Matrix Anal. / Numer. Math. |
| C4 | Lee–Yang double-resultant `body/group_unification/cor__group-jg-leyang-holography-double-resultant.tex` | 多元提升：环面上 Lee–Yang $P(x_1,\dots,x_k)$ 的传输可逆性 + Newton 多胞形有效恢复度 | 高 | Math. Ann. / Res. Math. Sci. |
| C5 ⭐ | **Fold-tower 算子代数（codex 新增）** `Omega/OperatorAlgebra/FoldConditionalExpectation.lean`, `FiniteCondexpVarianceDecomposition.lean`, `Omega/Folding/InverseLimit.lean`（已真证有限条件期望 + $L^2$-Pythagoras）| 证有限 **Pimsner–Popa 指数 = 最大纤维重数**；把各分辨率的期望拼成 Bratteli/AF 塔，算其有序 $K_0$ 与指数增长率——把组合纤维增长变成算子代数不变量 | 中–高 | J. Operator Theory / IEOT |

---

## 排除（纯灌水/条件包装，不投）
- `Omega/Zeta`、`Omega/Conclusion`（合计 ~5000 文件）绝大部分是**条件 RH 重述**（`*ImpliesRh*`/`*Certificate*`）——非定理。
- `Omega/OperatorAlgebra/*NPHard*`——假设"存在具目标 index gap 的 SAT 电路"，是包装非归约。
- `Omega/Frontier`（`Conjectures.lean`/`Assumptions.lean` 是假设，`Conditional.lean` 全部条件依赖）。
- `typed_address_biaxial_completion`、`fold-gauge-anomaly-*` boilerplate、pom 280 文件的大多数（Pisano/矩有限验证）。
- **库约 88–92% 是脚手架/定义/有限值证书**；真定理集中在 `Combinatorics`、`Kronecker`、`RootUnitCharacterPressureTensor`、`SyncKernelRealInput`、`EA`、`SPG` 的高信噪小目录。
- ⚠️ **两 scout 分歧待裁**：`RatioResultant` 被 Claude-scout 判 ~60% 真、被 codex 判**死胡同**（dummy splitting data、平凡子群、假设的非平凡特征）——**投入前先核验**；`Frontier` 含 `True` 占位；B2/B3 的 Kronecker/POM 种子须先确认 Lean 陈述**无条件**（codex 指出部分 parity/extremal 结果把递推当假设）。

> **codex 补充的统一视角**：A3（three-window 族）+ A6（Zeckendorf 热力学）其实是**同一个更大纲领**——"**Real Ostrowski thermodynamics beyond the golden mean**"：对每个纯周期二次无理数 $[0;\overline{a_1,\dots,a_r}]$ 建真正的有限归一化 transducer，证 $S_q(n)\sim C_{n\bmod r,q}\lambda_q^n$（$\lambda_q$ 代数）+ 解析压力 + CLT/LDP + 零温极限。把强黄金理论迁移到一整个结构分类的无限数系族。目标 **ETDS / Acta Arithmetica / TCS**。可作为 Wave 2–3 的合并大目标。另 codex 强调 A6 的真正缺口是**把极值纤维公式做成无条件**（现假设 two-step/forbidden 递推）：证 $D_m=D_{m-2}+D_{m-4}$（$m\ge6$）+ 最大化子分类 → **Adv. Appl. Math / EJC**。

## 建议执行波次

> ⚠️ **已失效(2026-08-16)**:Wave 1–3 计划所列工作已完成或被后续路线取代。

- **Wave 1（最快见效，方法在手/Lean 背书）**：A1 tilt 深化 · A2 cayley 去水补全 · B4 Lucas-Hankel 提取。
- **Wave 2**：A3 three-window 族分类 · B1 Fibonacci-cube · B2 metallic-gap · C1 rank-$r$ 分类。
- **Wave 3（高难高回报）**：A5 finite_parts 紧群扩张 · C4 Lee–Yang 多元 · A4 prime-languages 全 Pisot。
- **随手先做**：修 A7 的 n=30 数据 bug（无论是否深化）。

## 对接清单（等待人工确认）

> ⚠️ **本清单已失效,请勿据此行动(2026-08-16)**。其中的降刊/弃稿建议已被推翻:A8 现有 Le Cam 局部等价定理、重构后 EJS 51%(非降为 note);A3/A5/A6 的降刊目标亦不再适用。**当前真正待确认的五项**:(1) A6 是否拆分(A 篇 TAMS 55–65% vs 合稿 35–45%);(2) A8 是否重构投 EJS(51% vs 现状最佳 39%);(3) A3 是否拆分(A 篇 ETDS 74% vs 合稿 58%);(4) 531 个已验证提交是否推送;(5) `tools/chatgpt-oracle/` 15 处 08-03 未提交改动的去留。
1. Wave 1 三项（tilt 深化 / cayley 去水 / Lucas-Hankel 提取）是否批准启动？（Codex 出初版 → Claude 审）
2. A3/A5/A6 的降刊目标（ERA·AIMS Math·CMP·JNT）是否认可？
3. B3 resonance-Galois 与已投 37a1 的区分度，是否需要先做一次撞车核查再动手？
4. A8 detector_shells：确认降为 note 或直接弃？
