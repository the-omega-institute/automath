# NyxID ChatGPT 共享 Worker 设计

## 目标

将已停用的本地 Oracle 管线替换为 3 个固定的 company 共享 worker，并使它们稳定驱动当前 ChatGPT 5.6 页面。三个 worker 必须支持 Chat/Work 模式、PDF 上传、图片与文件产物回传、模型参数选择和同一会话追问。

共享 worker 身份固定为：

- `company_win_work_1`
- `company_win_work_2`
- `company_win_work_3`

旧 `tab_1..3` 本地池不再由默认启动路径创建或恢复，也不再使用本地 worker token。

## 当前问题

现有运行目录同时保留本地 worker、company worker、多个历史 label 和两套 token。启动单个 worker 时还会主动执行 `warp-cli connect`，把网络生命周期与任务 worker 生命周期耦合在一起。

当前 WARP daemon 已停止。本地 HTTP relay 仍尝试绑定旧地址 `172.18.32.1:40002`，并产生 `EADDRNOTAVAIL`。旧 worker 因此每 5 秒持续产生 `fetch failed`，但不能自行恢复有效网络。

仓库内 `tools/chatgpt-oracle/cdp-worker/worker.mjs` 是旧本地 Oracle 协议实现；实际 NyxID company worker 位于 `.nyxid-oracle/company-slot2-worker/worker-slot2.mjs`。必须明确唯一可维护真源，并由部署步骤生成或同步运行副本。

## ChatGPT 5.6 DOM 基线

以下结构来自 2026-07-12 对登录态 ChatGPT Pro 页面的实际 CDP 检查。

### Chat 与 Work

首页使用两个 `button[role="radio"]` 表示 `Chat` 和 `Work`，实际选择由 `data-state="on"` 表示。

Chat 首页提示为 `What's on the agenda today?`，并直接提供：

- Add photos & files
- Create image
- Web search
- Deep research
- Write or edit
- Look something up
- Visualize

Work 首页提示为 `What should we work on?`，并直接提供：

- Choose project
- Connect plugins
- Sites
- Visualize

Work 会话还显示 `Progress`、`Outputs`、`Create file or site` 和 `Subagents`。Work 会话标题和侧栏会话链接的可访问名称带 `Work` 标记。

### Composer 与消息

- 输入框：`#prompt-textarea`，同时匹配 `[contenteditable="true"][role="textbox"]`
- 发送按钮：`button[data-testid="send-button"]`，当前可访问名称为 `Send prompt`
- 附件按钮：`button[data-testid="composer-plus-btn"]`，当前可访问名称为 `Add files and more`
- 文件输入：页面存在多个 `input[type="file"]`
- 消息角色：`[data-message-author-role="user"]` 和 `[data-message-author-role="assistant"]`
- 消息 turn：`section[data-testid^="conversation-turn"]`
- 最终正文：assistant role 节点内的 `.markdown`

代码不得依赖 turn 的 `article` 或 `section` 标签，应使用 `[data-testid^="conversation-turn"]`。

### 模型控制

Chat/Work 与模型选择相互独立。当前 composer 模型菜单包含：

- Power：5 档 slider
- Model：当前为 `GPT-5.6 Sol`
- Effort：当前可为 `Ultra`
- Speed：当前可为 `Standard`

worker 必须读取实际菜单项并验证最终状态，不能依赖旧版 `GPT-5.5`、`Pro 扩展`、`极速` 或 `均衡` 等写死名称。

## 模式路由

三个固定 tab 运行相同 worker，不做静态 Chat/Work 分工。新任务支持 `chat`、`work` 和 `auto` 三种 mode。

推荐映射：

| 任务 | 模式 |
|---|---|
| contextual execution | Work |
| 完整论文、多 PDF、回复信联合审查 | Work |
| 模型架构、代码、实验交叉审计 | Work |
| 证明链和引用完整性审计 | Work |
| fresh review | Chat |
| 单点证明或短文本核验 | Chat |
| 外部文献系统检索 | Chat + Deep research |
| follow-up | 原会话原模式 |

`auto` 由任务语义映射到上述模式。未知旧任务保持向后兼容，默认使用 Work 处理完整审阅，使用 Chat 处理 fresh/targeted review。

## 任务配置

worker 接受以下逻辑字段；服务端尚未提供的字段必须使用兼容默认值：

```json
{
  "mode": "auto",
  "review_kind": "contextual_execution",
  "model": "GPT-5.6 Sol",
  "effort": "Ultra",
  "speed": "Standard",
  "power": 5,
  "prompt": "...",
  "files": [
    {
      "name": "paper.pdf",
      "mime_type": "application/pdf",
      "content_base64": "..."
    }
  ],
  "is_followup": false,
  "conversation_url": null
}
```

对 fresh task，执行顺序为：打开固定 tab 的空白首页、选择并验证 Chat/Work、选择并验证模型参数、上传并验证附件、填写 prompt、记录发送前 assistant turn 数量、发送、等待完成、提取新回答和产物。

## PDF 与输入文件

优先使用 Playwright `setInputFiles` 操作实际文件输入。若输入尚未挂载，则先打开 `composer-plus-btn`，选择 `Upload from computer`，再定位可接受目标 MIME 类型的 input。

worker 将 base64 内容写入任务专属临时目录。文件名必须清理路径字符，临时文件在任务结束后删除。

发送前必须同时满足：

- 附件 chip 或等价上传成功状态已经出现；
- 上传 progress 已消失；
- 发送按钮已启用。

失败必须返回具体阶段，例如 `file_input_missing`、`upload_timeout` 或 `attachment_rejected`，不能在没有附件的情况下继续发送科研审阅任务。

## 图片和 Work 产物回传

结果收集范围包括：

- 最终回答中的生成图片；
- 最终回答中的图表和可下载图片；
- Work `Outputs` 中的图片；
- Work 创建的其他可下载文件。

每个产物包含：

```json
{
  "name": "figure-1.png",
  "mime_type": "image/png",
  "source": "work_output",
  "source_url": "...",
  "content_base64": "...",
  "width": 1536,
  "height": 1024
}
```

下载应复用登录态 Chrome context 的 cookie 和请求上下文。对于 blob URL 或页面内资源，可通过页面 context 转换。每个文件和整个结果设置大小及超时限制。单个产物失败应记录 artifact error，但不能丢弃已经成功提取的文本回答和其他产物。

如果 NyxID 当前 `/result` 端点不接受 artifact 字段，worker 必须探测并使用现有上传端点；若服务端完全没有附件回传契约，则本地实现保留结构化 artifact spool，并明确报告服务端协议缺口，不得假装已经回传。

## 追问

首次任务发送后，worker 等待 URL 稳定为 `/c/<conversation-id>`，并随结果回传：

- `conversation_url`
- 实际 Chat/Work mode
- 实际 Model/Effort/Speed/Power

追问任务要求 `is_followup=true` 和原 `conversation_url`。worker 必须：

1. 导航到原 URL；
2. 验证 conversation ID；
3. 从 Work header、侧栏可访问名称及 Work 专属面板检测原 mode；
4. 禁止在追问期间重新切换 Chat/Work；
5. 允许本轮继续上传新文件；
6. 记录发送前 assistant turn 数量，只提取新 turn；
7. 若原会话不可用、登录失效或 mode 无法确认，返回明确错误，禁止静默创建新会话。

追问不依赖原浏览器 tab。任一空闲固定 worker 可通过 conversation URL 接管，但同一 conversation 必须由服务端任务租约串行执行。

## WARP 生命周期

WARP、relay 和 worker 分成三个独立职责：

- 显式启动共享栈时，启动一次 WARP 和 relay；
- 单个 worker 启动脚本不调用 `warp-cli connect`；
- worker 网络失败只退避轮询，不启动或重启 WARP/relay；
- 用户手动 disconnect 或关闭 WARP 后，现有 worker 保持离线，不自动恢复 WARP；
- 只有再次显式执行共享栈启动命令才恢复网络；
- relay 不使用写死的 `172.18.32.1`，而使用当前实际可监听地址；
- 轮询采用有上限的指数退避，避免断网时每 5 秒永久刷日志。

默认启动器只启动 `company_win_work_1..3` 和 company token。旧本地 labels、旧本地 token 和本地 Oracle worker 不进入默认路径。

## 真源与配置边界

NyxID worker 的可维护源文件必须进入仓库受控目录。`.nyxid-oracle` 仅作为本机运行状态目录，保存 token、PID、日志、临时 relay 状态和部署副本。

启动时应验证运行副本版本或从仓库真源启动，避免仓库 worker 与运行 worker 再次独立演化。token 不进入 Git，日志中不得输出 token 或完整认证 header。

## 错误处理

错误至少区分：

- WARP/relay 不可达；
- NyxID API 认证失败；
- Chrome CDP 不可达；
- 固定 tab 缺失或被关闭；
- Chat/Work 切换失败；
- 模型参数找不到或验证失败；
- PDF/文件上传失败；
- 回答生成超时；
- 回答为空或误取旧 turn；
- artifact 下载或回传失败；
- follow-up conversation 不存在或不匹配。

认证失败使用长退避。普通网络失败使用有上限指数退避。任务阶段错误应回传给 NyxID，使任务终止或可重试，而不是等待租约自然过期。

## 测试与验收

自动测试覆盖：

- 默认 labels 和 company token；
- 旧 `tab_1..3` 不进入默认启动路径；
- worker 启动不会执行 WARP connect；
- 显式共享栈启动可启动一次 WARP；
- 手动关闭后 worker 不尝试恢复 WARP；
- Chat/Work radio 的选择及 `data-state` 验证；
- mode 自动路由；
- 当前 Model/Effort/Speed/Power 菜单结构；
- PDF 上传成功、超时及拒绝；
- 当前无标签依赖的 conversation turn 选择器；
- reasoning 与最终答案分离；
- 图片及 Work Outputs 收集；
- artifact 大小、超时和部分失败；
- follow-up URL、conversation ID、mode 保持及新 turn 提取；
- 旧任务字段的向后兼容。

实时验收使用登录态 Chrome CDP，验证：

1. WARP 和 relay 显式启动成功；
2. 3 个固定 ChatGPT tab 存在并分别绑定唯一 marker；
3. NyxID 显示 3 个固定 company worker 在线；
4. Chat 与 Work fresh task 都可完成；
5. PDF 可上传并参与回答；
6. Work 任务可产生并回传图片或文件 artifact；
7. 同一 conversation 可连续追问并只返回新回答；
8. 手动 disconnect WARP 后，没有进程自动执行 reconnect；
9. 再次显式启动共享栈后可恢复。
