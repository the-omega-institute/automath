# G. Circle Dimension and Haar Pullback

## 工作定位

- 目标题目：`Circle Dimension, Haar Pullback, and Poisson--Cauchy Gram Kernels`
- 目标期刊：
  - 首选：`Journal of Functional Analysis`
  - 次选：`Annales de l'Institut Fourier`
- 本稿定位：
  - 只保留一条主线：`Cayley 紧化 -> Haar 回拉唯一性 -> circle dimension -> Poisson--Cauchy / Gram kernel`
  - 不引入与本线无直接关系的 Prym / Hurwitz / Nielsen / Langlands 分支

## 本稿当前应保留的核心定理包

### 代数主线

- Haar 回拉唯一性与规范重参数刚性
- circle dimension 的公理刚性
- 短正合列加法、rank-nullity、`Hom / Ext / tensor` 算律
- phase spectrum
  - 极限刻画 `\cdim`
  - 从 `N -> |\Hom(G,\mu_N)|` 完整重构 `G`
  - 相位谱像的内禀刻画
- half-circle dimension 的 dyadic prefix 操作型解释
- 二阶异常律与最小 injectivization 成本

### 分析主线

- precision potential 与 entropy ledger
- Poisson 半群与 relative-entropy contraction
- 高阶 Fisher 能量闭式
- 二阶正规形、锐 `L^p` 渐近、KL 主项
- KL 六阶校正与归一化 KL 的最终单调性
- phase Fourier 有限模态与 `(\sigma^2,\mu_3,\mu_4)` 反演
- central slice 的 Stieltjes 可识别性
- central two-channel 对全分布的唯一重构
- Cauchy 导数 Gram 闭式与差核 `2 / (4 + (a-b)^2)`
- 差核 RKHS 的仿射复合、条带延拓、整数采样稳定性

## 本次从主论文抽取到的“更深定理”

源材料：

- `..\2026_golden_ratio_driven_scan_projection_generation_recursive_emergence`
- 重点来源：
  - `sections/body/circle_dimension_phase_gate/subsubsec__circle-dimension-phase-gate-cdim-fg-abelian-calculus.tex`
  - `sections/body/circle_dimension_phase_gate/subsec__circle-dimension-phase-gate-operational-half-circle-dimension.tex`
  - `sections/body/circle_dimension_phase_gate/subsec__circle-dimension-phase-gate-poisson-cauchy-constants.tex`
  - `sections/body/circle_dimension_phase_gate/para__circle-dimension-phase-gate-poisson-cauchy-phase-fourierization.tex`
  - `sections/body/circle_dimension_phase_gate/subsec__circle-dimension-phase-gate-poisson-cauchy-gram-kernel.tex`
  - `sections/body/circle_dimension_phase_gate/subsec__circle-dimension-phase-gate-cauchy-kernel-rkhs-affine-translate.tex`

本稿已优先吸收以下高价值结果：

- `circle dimension` 的公理刚性、phase spectrum 重构与可实现性判据
- `\NN^d` 在 dyadic prefix 下的操作型 half-circle law
- 高阶 Fisher 能量
- moment-matching 下的 KL 主项思想
- phase-mode 矩反演
- central slice / two-channel reconstruction
- Gram closed form 与差核 RKHS

## 对主论文的补全/修正建议

按你的要求，这些建议只记录在本稿 README，不直接改主论文。

### 数学结构层面

- 主论文里的 `circle_dimension_phase_gate` 已经包含一组足以独立成文的 JFA 级主结果，但目前分散在多个子文件里，主线不够显式。
- 建议主论文后续把下面几条结论提到更前面的位置，并作为一个可单独引用的 theorem package：
  - `cdim` 公理刚性
  - phase spectrum reconstruction
  - phase spectrum characterization
  - higher-order Fisher energies
  - phase-mode inversion
  - central two-channel reconstruction
  - Gram kernel / RKHS package
- KL 六阶校正、最终单调性、two-divergence moment tomography 这些结果在主论文里是“高价值但埋得过深”的结论，后续应当明确标成一组 asymptotic package，而不是只作为长节中的局部命题存在。

### 写作组织层面

- 主论文把“基础接口定理”和“大量旁支应用”混在一个 section 中，导致可移植性差。
- 建议把主论文后续整理成：
  - interface theorems
  - asymptotic theorems
  - reconstruction theorems
  - RKHS / operator-theoretic consequences
  - side branches / arithmetic applications

### 工程层面

- 本稿编译时暴露出一个重要问题：`sec_precision_potential.tex` 曾经以隐式方式被 TeX 搜索路径解析，而不是作为本目录中的显式源文件存在。
- 这说明相关分析结果在工程组织上缺少“可移植的局部封装”。
- 对主论文的建议是：任何准备外拆成 publication 版本的 section，都必须先保证：
  - 本地显式文件存在
  - 不依赖未声明的 TeX 搜索路径命中
  - theorem label 与 bibliography key 可独立解析

## 当前本稿的编辑原则

- 不再从主论文机械复制长段文本
- 只抽取可直接服务于 JFA 主线的定理
- 所有迁入结果都要重写成更紧凑的英文论文表达
- 优先保证：
  - theorem chain 清晰
  - proofs 可读
  - bibliography 可编译
  - section 之间没有隐式依赖
