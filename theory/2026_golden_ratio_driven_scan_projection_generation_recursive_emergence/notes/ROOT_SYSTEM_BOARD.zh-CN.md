# 根系 Board: window-6 B3/C3/BC3 线索

- 日期: 2026-05-18
- 所属主线: `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence`
- 当前定位: 主论文内部的 window-6 根系/权模型/可见几何工作板
- 核心对象: `X_6 = X_6^{cyc} \sqcup X_6^{bdry}`, `|X_6^{cyc}| = 18`, `|X_6^{bdry}| = 3`
- 当前判断: 这条线已经有足够多 Lean-certified 锚点支撑一段论文级叙述，但要严格避免把 B3/C3 两种径向规范误写成全局线性等价。

## 一句话结论

window-6 的 cyclic 可见层携带一个刚性的 `6 + 12` 根向量骨架。它可以按 B3 或 C3 规范读成完整的秩 3 根系，并与 boundary 三词合成 `18 + 3 = 21` 的伴随权多重集；但 B3/C3 之间只共享组合壳层和 Weyl 轨道结构，不存在一个同时统一所有字典点的全局线性变换，四阶矩层也阻止把二者当作单纯 Euclidean rescaling。

## Claim Boundary

- 可以说: `X_6^{cyc}` 的 18 个稳定词有确定性 B3/C3 根字典；B3/C3 规范下分别给出完整根系。
- 可以说: Hamming 权阈值切出两条 Weyl 轨道，大小为 6 和 12；在 B3 与 C3 中长短根角色互换。
- 可以说: 加上 boundary 三重零权后，window-6 给出 B3/C3 伴随权多重集的显式模型。
- 可以说: 二阶矩是各向同性 tight frame，B3 常数为 10，C3 常数为 16；C3 long/short blocks 各贡献 `8 |u|^2`。
- 可以说: B3/C3 的四阶矩公式不同，并且没有统一正缩放能把 C3 的四阶矩全方向写成 B3 的四阶矩缩放。
- 不要说: 已证明 B3 与 C3 是同一个线性模型。
- 不要说: 根字典来自 `R_6` 商环内部算术。已有外在性结论说明它依赖外部组合入射数据。
- 不要说: `Window6CyclicWeightThresholdRootLength.lean` 这种包装型 theorem 本身已经穷尽证明了字典表的全部组合内容；表格/生成脚本和正文证明仍是解释层锚点。

## 已证核心锚点

| 层级 | 结论 | Lean 锚点 | 论文用途 |
| --- | --- | --- | --- |
| visible support | B3/C3 非零支撑落在三张 Levi 平面上；每个可见权至少一个坐标为零 | `lean4/Omega/GU/Window6B3C3VisibleSupportThreeLeviPlanes.lean` | 支撑“局域 rank-2 Levi plane”叙述 |
| adjoint multiset | 18 个非零权加 3 个零权，形成 21 个伴随权槽位 | `lean4/Omega/GU/Window6AdjointWeightMultiset.lean` | 支撑 `21 = 18 + 3` 伴随权模型 |
| second moment | B3/C3 二阶矩各向同性，常数分别为 10 和 16 | `lean4/Omega/GU/Window6B3C3AdjointSecondMomentIsotropy.lean` | tight frame / quadratic invariant |
| C3 equipartition | C3 六个长根和十二个短根各贡献 `8(x^2+y^2+z^2)` | `lean4/Omega/Zeta/XiWindow6C3QuadraticEnergyEquipartition.lean` | C3 长短根二阶能量平分 |
| rootcloud design | B3/C3 root clouds 一阶矩为 0，并接入二阶 isotropy/equipartition | `lean4/Omega/DerivedConsequences/DerivedWindow6B3C3RootcloudIsotropicDesign.lean` | 作为 derived isotropic-design wrapper |
| Weyl orbit split | B3/C3 root clouds 按平方范数分成 `6 + 12` 两块 | `lean4/Omega/Zeta/XiWindow6B3C3WeylInvariantImageQuadratic.lean` | 说明两条 Weyl 轨道 |
| no linear unifier | 四个字典点已经推出不存在全局线性统一器 | `lean4/Omega/Zeta/XiWindow6B3C3NoGlobalLinearUnifier.lean` | 防止过度统一 B3/C3 |
| fourth moment nonsimilarity | 二阶均各向同性，但四阶矩阻止单一 Euclidean rescaling | `lean4/Omega/Zeta/XiWindow6B3C3TightFrameFourthMomentNonsimilarity.lean` | 正面说明 B3/C3 差异层 |
| quartic defect | 四阶缺陷只沿一个 octahedral harmonic 方向存活 | `lean4/Omega/GU/Window6B3C3QuarticDefectOnedim.lean` | quartic detector / axis-diagonal reversal |
| even moment gap | B/C 差异全部来自六个轴向权，给出偶矩 gap 和 Laplace domination | `lean4/Omega/GU/Window6B3C3EvenMomentGapLaplaceDomination.lean` | 高阶偶矩层级比较 |
| degree-5 cubature | 21 labeled spherical support 上有三参数 boundary-transfer family | `lean4/Omega/GU/Window6B3C3SphericalCubatureStrength5.lean` | cubature / boundary mass transfer |
| multiplicity collapse | multiplicity-decorated B3 root cloud 的 signed Weyl 对称压缩到 Klein-four | `lean4/Omega/DerivedConsequences/DerivedWindow6MultiplicityRootcloudSignedWeylCollapse.lean` | multiplicity tomography 的群作用约束 |

## 主论文入口

| 文件 | 内容 |
| --- | --- |
| `sections/generated/tab_fold6_b3c3_root_dictionary_B3.tex` | `X_6^{cyc}` 到 B3 根系的确定性字典 |
| `sections/generated/tab_fold6_b3c3_root_dictionary_C3.tex` | `X_6^{cyc}` 到 C3 根系的确定性字典；轴向根径向放大 |
| `sections/body/group_unification/subsubsec__window6_rootcartan_boundarytower_adjoint_weight_model.tex` | Hamming 阈值、`21 = 18 + 3` 伴随权模型、二阶/四阶不变量 |
| `sections/body/group_unification/subsubsec__window6_rootcartan_boundarytower_uniqueness.tex` | 根-Cartan 字典与 boundary tower 维数接口 |
| `sections/body/group_unification/subsubsec__window6_b3c3_levi_quartic_laplace_gff.tex` | 三 Levi 平面、triaxial selection、quartic defect、Laplace domination |
| `sections/body/conclusion/subsec__conclusion-window6-cyclic-b3-rootcloud-multiplicity-tomography.tex` | B3 rootcloud multiplicity tomography、二阶反演和 isotropy 温点 |
| `sections/body/zeta_finite_part/xi/subsubsec__xi-time-protocol-conclusions-part48-fiber-algebra-collision-zero-temp-primitive-flat.tex` | BC3 root datum、C3 Hamming root-length split、根字典外在性 |

## 结构图

1. `X_6` 分解层:
   `X_6^{cyc}` 提供 18 个根标签，`X_6^{bdry}` 提供 3 个零权标签。

2. 根字典层:
   B3 规范把六个 Hamming weight-one 词送到 `±e_i`，十二个其余 cyclic 词送到 `±e_i ± e_j`。
   C3 规范把六个轴向词送到 `±2e_i`，十二个非轴向词保持为 `±e_i ± e_j`。

3. 不变量层:
   二阶矩给出 tight frame；四阶矩检测 B/C 规范差；偶矩和 Laplace gap 进一步显示差异完全来自轴向六根。

4. 对称层:
   未加 multiplicity 时有共同 signed-permutation Weyl 轨道结构；加 window-6 multiplicity 后，全 signed Weyl 对称坍缩到保留三层 `R2/R3/R4` 的 Klein-four 子群。

5. 外在性层:
   B3/C3 根字典是可见固定点商上的组合入射几何，不应被写成 `R_6` 商环内部自然产生的结构。

## 当前风险

- `paper_window6_cyclic_weight_threshold_root_length` 是包装型 theorem，参数化接收 `weightOneShortRootOrbit` 等 Prop；正文如果声称“Lean 直接枚举了 Hamming 字典”，需要同时引用生成表格或更具体的枚举 theorem。
- `paper_window6_b3c3_degree4_relation_space_saturation` 是依赖输入 Prop 的包装器，不应当单独当成 degree-4 relation-space 已完全审计的证书。
- BC3 口径应该表述为“共同的 `6 + 12` 组合壳层/根数据”，而不是新的完整非约化 BC3 根系已经在 Lean 中全量形式化。
- `Window6RootDictionaryPullbackBracket.lean` 给出的是沿已有 inverse pair 拉回 bracket 的一般结构性引理；它不单独证明物理/几何连续 Lie bracket 的自然性。
- multiplicity tomography 目前主要在 B3 字典下组织；不要自动把所有 multiplicity 结论转写到 C3 规范，除非逐项检查归一化。

## 可立即写进论文的版本

> The window-6 visible cyclic sector carries a rigid `6 + 12` root datum. In the B3 normalization the six Hamming-weight-one words are the axial roots `±e_i`, while the remaining twelve cyclic words are `±e_i ± e_j`; in the C3 normalization the same twelve off-axis roots are unchanged and the six axial roots are rescaled to `±2e_i`. Thus the intrinsic finite object is not a choice between B3 and C3, but a visible `6 + 12` shell whose two standard radial normalizations are B3 and C3. Adding the three boundary words as zero weights gives the `18 + 3` adjoint-weight multiset. The quadratic layer is isotropic in both normalizations, with constants 10 and 16, whereas the quartic and higher even-moment layers record the normalization difference and rule out a single global linear identification.

## 下一批任务

| 优先级 | 任务 | 产物 |
| --- | --- | --- |
| P0 | 给 B3/C3 字典表补一个可读 proof note，明确哪些行来自生成脚本、哪些行由 Lean wrapper 覆盖 | `notes/window6_b3c3_dictionary_proof_note.md` |
| P0 | 检查正文所有 “BC3 root datum” 表述，替换掉可能暗示完整 BC3 root system formalization 的句子 | patch to group_unification / xi sections |
| P1 | 把 `NoGlobalLinearUnifier` 和 `TightFrameFourthMomentNonsimilarity` 放进主论文根系段的 claim boundary | one paragraph + theorem refs |
| P1 | 给 multiplicity tomography 加一个 B3-only scope warning，避免被误读成 C3 invariant statement | local paragraph in conclusion subsection |
| P2 | 若需要更强 Lean 证书，新增直接枚举 theorem：B3/C3 字典全 18 行与 generated tables 一致 | new Lean file or extension of existing dictionary file |
| P2 | 审计 `degree4 relation-space saturation` 的真实依赖，把包装 Prop 替换或标注为 paper-external assumptions | Lean/doc sync |

## 邮件/对外口径

给合作者或审稿人时，不要发送“路径清单式”解释。推荐只说：

- finite window-6 has a certified visible `6 + 12` root shell;
- B3 and C3 are two radial normalizations of that shell;
- the adjoint-weight package is `18 roots + 3 zero weights`;
- quadratic invariants agree in form but not constant;
- quartic/fourth-moment data shows the two normalizations are not globally linearly unified.

如果对方要求复核，再给 branch/commit 和 Lean anchors。
