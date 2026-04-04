# Projection Ontological Mathematics Core

## 目标定位

- 目标稿件：`publication/2026_projection_ontological_mathematics_core_tams`
- 目标风格：`Transactions of the American Mathematical Society`
- 当前策略：只保留已经能由有限状态、Hankel 证书、模素因子型证书闭合的主定理链

## 本稿实际吸收的主源材料

主源目录：

- `docs/papers/auric-golden-phi/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence`

本次重点挖掘并转写到投稿稿的源文件：

- `sections/body/pom/parts/subsec__pom-projection-entropy.tex`
- `sections/body/pom/parts/subsec__pom-state-evolution.tex`
- `sections/body/pom/parts/thm__pom-hankel-nf-shift-invariance-and-propagation.tex`
- `sections/body/pom/parts/thm__pom-hankel-inverse-propagation-minor-dynamics.tex`
- `sections/body/pom/parts/thm__pom-hankel-finite-pole-spectral-gap.tex`
- `sections/body/pom/parts/thm__pom-oracle-capacity-stieltjes-inversion-mellin.tex`
- `sections/body/pom/parts/resonance/subsubsec__pom-resonance-hankel-null-integral-principalization.tex`
- `sections/body/pom/parts/resonance/prop__pom-observable-minpoly-galois-chebotarev.tex`
- `sections/generated/tab_fold_collision_observable_minpoly_galois_certificate_q9_13.tex`
- `sections/generated/tab_fold_collision_moment_charpoly_galois_certificate_q12_15.tex`
- `sections/generated/tab_fold_collision_moment_charpoly_disc_squareclass_independence_q12_15.tex`
- `sections/generated/tab_fold_collision_resonance_aitken_certificate_q9_17.tex`

## 本稿已经提升进来的深层结果

- 信息账本主定理：熵分解、fiber-uniform lift 的 KL 刚性、side-information 下界。
- 重写主定理：projection-word 片段终止且合流，reverse-rewrite 计数满足 root-of-unity filter 与模 \(q\) 指数均匀化。
- 碰撞矩主定理：有限状态 realization、对称压缩、capacity/Stieltjes 反演、有限 Hankel 谱隙恢复 Perron 根。
- 共振算术主定理：
  - `q=9..17` 上 Hankel null-module 被最小递推多项式整系数主理想化；
  - `q=9..17` 上最小多项式全部不可约；
  - `q=9..17` 上 Galois 群全部闭合到满对称群；
  - `q=12,13,14,15` 上 splitting fields 线性无交；
  - `q=12,13,14,15` 上 Perron 根具强乘法独立性；
  - 同时不可约的 Chebotarev 密度精确为 `1/20449`；
  - 定义了投稿版可接受的 synchronized Chebotarev capacity（以 `-log density` 记同步算术代价）；
  - `q=9..17` 上次主根全部呈现“唯一负实主导”，从而给出最终交替二阶律。

## 对主论文的补全/修正建议

注意：以下内容只记录在本 `README.md`，不直接改动主论文源。

### 结构建议

- 把 `thm__pom-oracle-capacity-stieltjes-inversion-mellin.tex` 前移，紧跟 collision-kernel 主定理与 Hankel 三联定理，避免 capacity 在主稿里出现得过晚。
- 把 Hankel shift-invariance / inverse-propagation / finite-pole spectral-gap 三个定理打包成明确的“有限 Hankel 可恢复性”子链。
- 把 principalization（Hankel null = short multiples）从备注级/侧枝级结果提升为共振算术节的主定理。
- 把 squareclass independence 与 product Chebotarev 紧挨着放，形成一个完整的“线性无交 -> 直积 Galois 群 -> 乘法密度”闭环。
- 把 secondary spectral fingerprint 提升为正文主结果，而不是停留在数值备注层：至少应显式写出负实次主根主导导致的最终交替二阶律。
- 把 `q=12,13,14,15` 的 Perron 强乘法独立性提升为主定理级结论，因为它把“分裂域线性无交”直接转化成“主指数尺度无算术共振”。
- 把探索性材料与审计完成材料分层：已闭合定理与 RH/超越性/更远端猜想不要混写在同一主叙事层。

### 需要明确修正的数学点

- 主源里的 `q=12,14,15` 满对称群证明，若只依赖“素数次数 + `d`-cycle + `(d-1)`-cycle”这一路径，群论上是不够的；`AGL_1(\mathbf F_p)` 是反例。
- 投稿稿已改为严格的 Jordan 证书路线：
  - `q=12` 额外使用 `p=97` 的 `(7,6)` 因子型；
  - `q=14` 额外使用 `p=71` 的 `(7,6)` 因子型；
  - `q=15` 额外使用 `p=37` 的 `(7,4)` 因子型；
  - `q=16` 额外使用 `p=19` 的 `(7,2,2,2)` 因子型；
  - `q=17` 额外使用 `p=23` 的 `(7,6)` 因子型。
- 建议主论文相应位置也改成 “不可约 -> 传递；素数次数或 `(d-1)`-cycle -> primitive；显式 3/5/7-cycle + Jordan -> \(A_d\)；再用奇置换排除 \(A_d\)” 这一条完整证法。

## 当前投稿稿的修改原则

- 不再声称未在正文闭合的结果。
- 删除投稿版里不必要的 transcendence / discriminant-thickness 主叙事负担。
- 把摘要、引言、结论全部收敛到正文真正证明的定理。
- 算术节从“零散审计”改成“principalization -> irreducibility -> full symmetric groups -> linear disjointness -> product density -> capacity”。

## 编译说明

- 本目录当前使用手写 `sec_references.tex`，不是 BibTeX 驱动。
- `latexmk` 在当前环境不可用，原因是 MiKTeX 缺少 `perl` 脚本引擎。
- `microtype` 已从投稿稿移除，避免当前 MiKTeX 字体配置下的扩展报错。
- 建议编译命令：
  - `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
  - 再运行一次同命令以稳定交叉引用

## 后续检查清单

- 检查摘要与引言是否仍有超纲承诺。
- 检查 `sec_chebotarev.tex` 中所有群论结论是否都对应到显式模素证书。
- 检查所有 `\cite{...}` 是否在 `sec_references.tex` 中有条目。
- 检查表格宽度与分页是否符合 TAMS 风格。
