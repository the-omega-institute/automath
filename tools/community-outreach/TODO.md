# Community Outreach TODO

管线从这里认领任务。每个 item 有状态：`TODO` / `CLAIMED` / `DONE` / `SKIP`。
管线跑 `--todo` 模式时按优先级从上到下认领第一个 `TODO` 项。

---

## Tier 1: 最高价值目标

### google-deepmind/formal-conjectures (926★, 872 issues)

- [ ] **FC-01**: ams-40 (序列/级数) = 0 issues。提交 Fibonacci 增长、S₂ 递推、Hankel 行列式序列的猜想声明。搜索 `lean4/Omega/Folding/MomentSum.lean` `MomentRecurrence.lean` `HankelSpectrum.lean`。目标：3-5 个 Lean 4 conjecture statements PR。
- [ ] **FC-02**: ams-37 (动力系统) = 2 issues。提交 golden-mean shift 熵、Sturmian 刚性、逃逸率猜想。搜索 `lean4/Omega/Folding/Entropy.lean` `ShiftDynamics.lean`。现有 issues #2153 (Sofic) #2152 (Gottschalk) 我们的 sofic shift 直接相关。
- [ ] **FC-03**: ams-28 (测度/积分) = 1 issue。提交 Parry 测度、遍历猜想。搜索主论文 `theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence/` 的 ergodic 部分。
- [ ] **FC-04**: ams-11 (数论) = 1 issue。提交 Zeckendorf 唯一性推广猜想、Fibonacci 素数模猜想。搜索 `lean4/Omega/Folding/FiberRing.lean` `Zeckendorf.lean`。
- [ ] **FC-05**: ams-47 (算子理论) = 1 issue。提交碰撞核谱猜想、转移算子猜想。搜索 `lean4/Omega/Folding/CollisionKernel.lean` `CollisionZeta.lean`。

### teorth/equational_theories (512★, 30 issues)

- [ ] **EQ-01**: Issue #1236 (extra countermodels)。用 `FiberRing.lean` 的 ring-operation magmas 构造新的 separating magma 族。直接 PR 回应明确需求。
- [ ] **EQ-02**: Issue #364 (linear magma x◇y=ax+by)。Z/F_{m+2}Z 是 linear magma 特例。跑 Fibonacci 模数上的线性蕴含计算，提供数据集。
- [ ] **EQ-03**: Issue #184 (counting lemmas 1.11/1.12, Catalan/Bell)。检查 Automath 有无 Fibonacci counting 的 Lean 4 证明可以贡献。搜索 `lean4/Omega/Combinatorics/`。
- [ ] **EQ-04**: Issue #2153 在 formal-conjectures 中 (Sofic Group Conjecture)。Automath 的 golden-mean shift 是 sofic shift 的典型例子。可以在 teorth 里补充 sofic shift 的 magma 构造。

## Tier 2: 值得参与

### mo271/FormalBook (82★, 5 issues)

- [ ] **FB-01**: Issue #118 Ch8 misformalisations。检查 Automath 的 Lean 4 证明技术能否修复。
- [ ] **FB-02**: Issue #131 Ch20 Inequalities。检查 Automath 的 moment bounds (`MomentBounds.lean`) 是否有相关不等式。

### math-inc/OpenGauss (1176★) + RiemannHypothesisCurves (50★)

- [ ] **MI-01**: OpenGauss (1176★) 是 Math Inc 的自动形式化 agent，"beating Aristotle"。方法论互补：他们做自动形式化（LaTeX→Lean），我们做自动发现（seed→theorems）。在 OpenGauss issue 里提出合作方向：用 Automath 的 discovery_report.json 作为 OpenGauss 的 benchmark corpus。
- [ ] **RH-01**: RiemannHypothesisCurves (50★) 方法论交流。他们用 Gauss agent 做自动形式化，我们用 Oracle pipeline。在 issue 里分享 pipeline 经验。

### Zulip 社区

- [ ] **ZU-01**: Lean Zulip #Formal-conjectures 发帖介绍 Automath 的猜想贡献计划（在 FC-01 完成后）。
- [ ] **ZU-02**: Lean Zulip #Equational 回复相关讨论（在 EQ-01 完成后）。
- [ ] **ZU-03**: SAIR Zulip 回复 McKenna Spine Isolation 帖子（已有 issue #1，等回复后跟进）。

## 已完成

- [x] **EQ-00**: mysticflounder/equational-magma-theorems issue #1 已提交 (2026-04-15)
