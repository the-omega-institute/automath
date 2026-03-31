# E1. Conservative Extension Chain and State Forcing

## 当前定位

- 当前稿件路径：
  `docs/papers/auric-golden-phi/publication/2026_conservative_extension_chain_state_forcing_apal`
- 主论文源材料路径（本轮只读取，不改动）：
  `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence`
- 目标期刊：Annals of Pure and Applied Logic (APAL)
- 目标定位：
  把主论文里已经出现但尚未被独立抽象成"逻辑/语义元定理"的内容，整理成可向数理逻辑期刊提交的独立论文。

## 本轮修订要点

### 1. 修复逻辑缺口

- Theorem 4.26（component gerbe decomposition）：无条件整栈分解降级为带 branch constancy 假设的 corollary；无假设版本只保留"每个 visible branch 的 full substack 是 banded gerbe"。
- Theorem 4.28（gerbe-null-semantics）：显式引入 global conservativity at the terminal fibre（stackification morphism 在终纤维上本质满），作为 $\mathfrak L_r(a)\neq\varnothing \Leftrightarrow \Sec_s(r)$ 的必要条件。

### 2. Forcing 必要性定理

- 新增 Theorem（pointwise irreducibility of gluing predicates）：构造两个 admitted references，在 $\mathbb{L}_1$ 上不可区分，但在 $\mathbb{L}_2$ 上一个可 glue、另一个不可 glue。由此证明 $\CompSec_s$ 和 $\Sec_s$ 不是 information-state forcing 语言可定义的。

### 3. Abramsky--Brandenburger 联系

- 新增 subsection（Connection to sheaf-theoretic contextuality）：在 unique-branch case 下，将本文的 branched gerbe semantics 退化为标准 no-global-section picture，并用 $\operatorname{Ext}$-residual 精确解释 Caru 所发现的 incomplete cohomological detection。

### 4. 清除 "larger architecture ghost"

- 引言、预备知识、结论中的 "broader research program"、"eleven-layer architecture"、"larger conservative-extension architecture" 等措辞全部替换为自足四层链的表述。

### 5. 复杂性上界移至附录

- Section 5 中的 Finite-state complexity subsection 提取为独立附录。
- 主文只保留 refinement monotonicity 与 visibility monotonicity。

### 6. 文件拆分

- `sec_null_decomposition.tex` 拆为三个文件（均 < 800 行）：
  - `sec_null_decomposition.tex`：局部对象、层化、realization prestacks、typed readouts、structural absence、forcing necessity
  - `sec_gerbe_obstruction.tex`：component gerbes、visible quotients、worked example
  - `sec_homological_visibility.tex`：homological evaluation、intrinsic visibility、branch aggregation、contextuality

## 已从主论文抽出的深层定理

### 1. 信息状态层

- 显式补出 `lifted soundness of pointwise reasoning`。
- 显式补出 `canonical Kripke reduct`。
- 显式补出 `Kripke recovery after atomization`。

### 2. 局部对象层

- 显式补出 `sheafification characterizes compatible local sectionability`。
- 显式补出 `sheafification removes gluing failure`。
- 抽象化写出 `typed readout`、`address before value`、`typed-readout persistence`。
- 新增 `pointwise irreducibility of gluing predicates`。

### 3. NULL 分解层

- 显式补出 `classification after refinement`。
- 显式补出 `finite model for the three absence modes`。
- 保留并对齐 `gerbe semantics of gluing-level absence`（含 branch constancy 与 global conservativity 修补）。
- 新增 `connection to sheaf-theoretic contextuality`。

### 4. 多轴动态层

- 保留 `non-retrocausal delayed classification`。
- 保留 `explicit lifting principle`。
- 保留 `value-preserving rewrites do not create facts`。
- `finite-state complexity upper bounds` 移至附录。

## 当前编译状态

- 已执行：
  `pdflatex -> bibtex -> pdflatex -> pdflatex`
- 当前 `main.tex` 可成功编译出 PDF。
