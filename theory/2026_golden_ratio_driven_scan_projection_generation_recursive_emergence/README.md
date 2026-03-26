# 2026 Golden ratio driven scan–projection generation (recursive emergence)

本目录包含论文 `main.tex` 及其可复现实验流水线。

## 项目结构（多级目录）

- **根入口**
  - `main.tex`：主文档入口（全量编译）。
  - `main_fast.tex`：快速编译入口（定义 `\FASTBUILD` 后复用 `main.tex`）。
  - `references.bib`：参考文献数据库。
- **sections/**
  - `sections/frontmatter/main.tex`：前置材料入口（可独立编译）。
  - `sections/body/main.tex`：正文入口（可独立编译）。
  - `sections/appendix/main.tex`：附录入口（可独立编译，内部负责 `\appendix`）。
  - `sections/backmatter/main.tex`：后置材料入口（可独立编译，含 bibliography）。
  - `sections/generated/`：脚本生成的 LaTeX 片段（只写，不手改；路径保持稳定）。
- **scripts/**：可复现实验脚本（统一由 `scripts/run_all.py` 编排）。
- **artifacts/**：导出与审计产物（CSV/PNG/JSON 等）。

## 编译

先 run_all.py 然后 build；若新增实验脚本，必须加入 `scripts/run_all.py` 的 steps 列表。

```bash
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main_fast.tex
```

正式全量编译（用于最终导出）使用 `main.tex`：

```bash
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

目录级单独编译（用于局部测试）：任意进入一个目录，只要该目录存在 `main.tex`，即可直接编译：

```bash
cd sections/body
latexmk -pdfxe -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

说明：
- 目录级编译面向“语法/排版/局部推导链”快速核验；跨目录引用（`\ref`/`\cite`）可能需要先编译根 `main.tex` 以生成完整 aux 信息。

## 复现实验

安装依赖：

```bash
python3 -m pip install -r requirements.txt
```

运行一键流水线：

```bash
python3 scripts/run_all.py
```

脚本将生成：

- `sections/generated/*.tex`：可直接 `\input{}` 的图/表 LaTeX 片段
- `artifacts/export/*`：CSV/PNG 等导出（用于审计与复核）

## 写作与拆分规范（label 地址化）

### label 唯一与文件命名

- **主 label（primary label）**：每个“内容文件”应在其第一个主锚点处提供 `\label{...}`，该 label 作为该文件的唯一地址标识（全工程唯一）。
- **文件名映射**：文件基名由主 label 进行确定性映射得到：
  - 将 `:` 替换为 `__`；
  - 其余字符保持（允许 `-`）；
  - 扩展名固定为 `.tex`。
- **示例**
  - `sec:folding` → `sec__folding.tex`
  - `app:unit-circle-phase-gate` → `app__unit-circle-phase-gate.tex`

### 原子化与层级控制

- **单文件尺度**：单个 `.tex` 文件不得超过 800 行；超过必须按子节/主题拆分为多个文件，并以目录内 `main.tex` 聚合。
- **每级文件数量**：人工维护目录建议控制在 **≤ 30 个 `.tex`**（不含 `sections/generated/`）；超过则按主题拆分子目录，并为子目录提供可独立编译的 `main.tex`。
- **聚合入口**：每个目录的 `main.tex` 作为编译入口与聚合器，可使用 `\subfile{...}` 纳入子目录入口，使用 `\input{...}` 纳入同目录内容文件。

### 路径与可复现性约定

- **generated 目录**：`sections/generated/` 由脚本生成，禁止手工编辑；正文引用保持 `\input{sections/generated/...}` 形式不变。
- **\input 的基准**：TeX 的 `\input{...}` 路径解析以“编译入口 `main.tex` 所在目录”及 `subfiles` 注入的搜索路径为基准，而非“当前被包含文件所在目录”。因此要保证目录级可编译：子目录中的文件若需再 `\input{}` 其他子目录文件，应使用从其编译入口目录出发的相对路径；或为该子目录提供 `main.tex` 并通过 `\subfile{.../main}` 引入，以获得自动路径修正。
- **subfiles 路径修正**：若在目录级编译时遇到外部程序（如 bibtex）报 “file not found”，对相应文件名使用 `\subfix{...}` 或改用从当前目录到根目录的相对路径（本工程后置材料入口已使用 `\bibliography{../../references}` 保证可独立编译）。

## 脚本添加

添加实验脚本需要同时添加到run_all.py