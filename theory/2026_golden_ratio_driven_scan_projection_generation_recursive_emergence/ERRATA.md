# 论文勘误记录

形式化过程中发现的论文错误、条件不精确或表述问题。

## 勘误列表

### E-001: lem:pom-fib-fusion-submultiplicativity 严格次乘性条件不精确

**位置**: sections/body/pom/parts/def__pom-ind-lyapunov-fingerprint.tex

**论文原文**: 当 $(a,b) \neq (1,1)$ 时，$F_a F_b < F_{a+b-1}$

**问题**: 条件 $(a,b) \neq (1,1)$ 不够强。反例：$(a,b) = (1,2)$ 时 $F_1 \cdot F_2 = 1 \cdot 1 = 1 = F_2 = F_{1+2-1}$，等号成立，严格不等式不满足。类似地，$(a,b) = (k, 1)$ 或 $(1, k)$ 时 $F_{a-1}F_{b-1} = 0$，融合恒等式退化为 $F_{a+b-1} = F_a F_b$，等号成立。

**修正建议**: 条件应改为 $a \geq 2 \wedge b \geq 2$（即 $\min(a,b) \geq 2$）。在论文实际应用场景（component fusion, $\ell \geq 1$ 即 $a = \ell + 2 \geq 3$）中此条件总是满足的，不影响下游推导。

**Lean4 处理**: `fib_prod_lt_fib_fusion` 使用 `ha : 2 ≤ a, hb : 2 ≤ b` 作为前提条件。

**发现于**: 形式化第1轮，Codex审核确认

---

### E-002: thm:pom-max-fiber 闭式有效范围未明确标注

**位置**: sections/body/pom/parts/def__pom-ind-lyapunov-fingerprint.tex（推测）

**论文原文**: $D_{2k+1} = 2F_{k+1}$

**问题**: 当 $m = 1$（即 $k = 0$）时，$D_1 = 1$（$X_1$ 有2个元素，$2^1 = 2$ 个词，各纤维大小 = 1），但 $2F_1 = 2 \neq 1$。闭式从 $m \geq 2$ 开始成立，但论文中该有效范围限制不够显眼。

**修正建议**: 在定理陈述中明确标注"对 $k \geq 1$"或"对 $m \geq 2$"。

**Lean4 处理**: `maxFiberMultiplicity_odd_le` 和 `maxFiberMultiplicity_odd_ge` 将添加 `hk : 1 ≤ k` 前提条件。

**发现于**: 形式化第2轮，analyst 分析阶段
