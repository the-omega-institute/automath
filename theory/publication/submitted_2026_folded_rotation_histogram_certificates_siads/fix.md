基于你现在这版稿子，我先给一个明确判断。

**你已经把四条主要意见中的三条，推进到了 theorem-level。**
具体来说：

* “prototype 太窄”已经不再只是叙述层回应，而是被 Theorem 5.16 与 Theorem 5.19 提升成了 **lossless coarse-graining / injective placement barrier** 的结构性结论。
* “为何是 Fibonacci weighting”已经被 Appendix C 的唯一性定理与 residue-fold 唯一性补成了严格结论。
* “I-projection 关系过弱”已经被 Appendix A 的 dual characterization 补成了完整的 maximum-entropy / I-projection 对偶。
* “应用过薄”则已经通过 Section 6.7 的非线性 circle-map realization 大幅缓解，但我仍然认为它还可以再往前推进半步。

所以这一次我不给你重复之前那些已经写进稿子的证明。我只做两件事：

1. 先指出，**你这版稿子中哪些 theorem 已经足够直接对冲审稿意见**。
2. 再补两条我认为还值得加进去的新结论，并给出**完整证明**。这两条不是对现有内容的重复，而是把你稿子里还略显“说明性”的部分，继续提升成可以压审稿意见的硬结果。

---

## 一、你当前版本中，已经足以正面对冲审稿意见的部分

### 1. 关于“范围刻意狭窄”

你现在已经不是在说“我们故意只做一个 prototype”，而是在说：

* canonical slice 上的精确 injective optimum，是 **所有 realized-source lossless coarse-grainings** 的统一基准；
* primitive SFT 中的一般情形保留的是 asymptotic barrier；
* golden-mean benchmark 的特殊性，不在于“它是唯一例子”，而在于“它把一般 barrier finite-(m) exact 化，并给出显式优化器与 bounded-gap canonical realization”。

这件事现在主要由 Theorem 5.16 与 Theorem 5.19 共同完成。前者把 canonical slice 提升为 **universal lossless coarse-graining envelope**。后者把这种 envelope 提升到一般 primitive SFT 的 injective placement barrier。

### 2. 关于“fold 的自然性和唯一性”

这部分也已经不是解释，而是定理：

* Theorem C.1 证明，只要要求合法语言 (X_m) 被一个 contiguous numeration 精确枚举为 ({0,\dots,F_{m+2}-1})，权重就只能是 Fibonacci。
* Corollary C.2 再证明，在同一个 residue-selection 公理类中，deterministic fold 也只能是 canonical residue fold。

这已经足以压住“为何不是 Ostrowski 或别的编码”这一类质疑。因为在你的模型类中，golden branch 上的 Ostrowski 其实并不是一个 genuinely different competitor。你的 axiom class 已经把它收束回 Zeckendorf/Fibonacci 了。

### 3. 关于“Appendix A 与 I-projection 的关系太轻”

现在已经不轻了。Theorem A.4 和 Proposition A.5 联合起来，已经给出：

* (Q_m\pi) 是 fiber-uniform family 上的唯一 I-projection；
* 同时又是线性族 (L_\pi) 上的唯一 maximum-entropy lift；
* 两者通过 folded observable (Fold_m) 这个 sufficient statistic 汇合。

这个补强是有效的，而且是信息论审稿人会真正在意的那种补强。

---

## 二、我认为还可以继续补上的两条新结论

下面这两条，是我觉得你再加进去，会把剩余风险进一步压下去的地方。

---

# 结果 A. 将 Section 6.7 从“说明性 transfer”提升为正式 transfer theorem

你现在的 Section 6.7 已经说明：对与 irrational rotation 共轭的 circle diffeomorphism，整个 audit verbatim transfer。
但目前正文还是偏叙述。最稳妥的做法，是把它升级成一个 theorem。

---

## Theorem 6.8. Full audit invariance under topological conjugacy

设 (f:S^1\to S^1) 是 orientation-preserving circle homeomorphism，且与 irrational rotation
[
R_\alpha(x)=x+\alpha \pmod 1
]
topologically conjugate。即存在 orientation-preserving homeomorphism (h:S^1\to S^1) 使得
[
h\circ f = R_\alpha \circ h.
]
取任意锚点 (a\in S^1)，并归一化 (h(a)=0)。定义 coding window
[
I_a := [a,f(a))
]
为从 (a) 到 (f(a)) 的正向半开弧。对任意 (x\in S^1)，定义符号轨道
[
s_t^{(f)}(x):=\mathbf 1_{I_a}(f^t(x)), \qquad t\ge 0.
]
再定义 rotation side 的符号轨道
[
s_t^{(\alpha)}(y):=\mathbf 1_{[0,\alpha)}(y+t\alpha \bmod 1), \qquad y\in S^1.
]
则对每个 (x\in S^1)，令 (y=h(x))，有逐时刻恒等式
[
s_t^{(f)}(x)=s_t^{(\alpha)}(y)\qquad (t\ge 0).
]
因此，对任意 (m,N\ge 1)，由 (f) 产生的 length-(m) microstate law、folded law、empirical histogram、discrepancy certificate、Parry comparison、higher-block conjugacy、injective optimum、以及 Section 5 中全部 Rényi / KL 结论，都与 rotation 模型逐字一致。

特别地，若 (f) 为 (C^2) orientation-preserving circle diffeomorphism 且 rotation number 为 irrational (\alpha)，则整个两阶段 audit 完整成立。

---

## Proof

因为 (h) 是保向圆同胚，弧 (I_a=[a,f(a))) 在 (h) 下的像，恰是从 (h(a)=0) 到
[
h(f(a)) = R_\alpha(h(a)) = \alpha
]
的正向半开弧。因此
[
h(I_a)=[0,\alpha).
]

对任意 (x\in S^1)，令 (y=h(x))。则由共轭关系，
[
h(f^t(x)) = R_\alpha^t(h(x)) = y+t\alpha \pmod 1.
]
于是
[
s_t^{(f)}(x)
============

# \mathbf 1_{I_a}(f^t(x))

# \mathbf 1_{h(I_a)}(h(f^t(x)))

# \mathbf 1_{[0,\alpha)}(y+t\alpha \bmod 1)

s_t^{(\alpha)}(y).
]
逐时刻恒等式得证。

既然两个符号序列在每个时刻都完全相同，则任意长度 (m) 的滑动窗口词
[
\omega_m^{(f)}(t;x)
===================

s_t^{(f)}(x)s_{t+1}^{(f)}(x)\cdots s_{t+m-1}^{(f)}(x)
]
与
[
\omega_m^{(\alpha)}(t;y)
========================

s_t^{(\alpha)}(y)s_{t+1}^{(\alpha)}(y)\cdots s_{t+m-1}^{(\alpha)}(y)
]
逐项相同。于是：

1. 任意 fixed (x) 与 (y=h(x)) 的 empirical microstate counts 完全一致。
2. 应用同一个 deterministic fold (Fold_m) 后，folded histogram 完全一致。
3. 因为 histogram 本身一致，Section 3 的 TV discrepancy bounds 与 Section 4 的 KL bounds 逐字 transfer。
4. canonical slice (\beta=\alpha) 下，Section 4 的 no-collision rigidity 与 higher-block conjugacy 全部 transfer。
5. Section 5 中关于 (\pi_m) 的全部比较，只依赖 folded law 本身，因此也逐字 transfer。

最后，若 (f) 是 (C^2) orientation-preserving circle diffeomorphism 且 rotation number 为 irrational，则 Denjoy 定理给出它与相应 rigid rotation 的 topological conjugacy，因此上面的结论自动成立。证毕。

---

## 这条结果的作用

它比现有 Section 6.7 更强。因为它不是“我们举了一个 nonlinear example”，而是：

**你整个 benchmark 不是 rigid rotation 专属，而是一个完整的 circle-diffeomorphism 共轭类不变量。**

这样一来，“应用示例太单薄”的问题会从“只有一个数值例”变成“我们给了一个 family-level transfer theorem，再用标准 circle map 做了一个 concrete numerical witness”。这就足以把 Section 6.7 从 illustration 提升为 theorem-backed application bridge。现有稿子已经有这个思路和数值例。上面这条 theorem 只是把它正式化。

---

# 结果 B. 将 universal barrier 再推进成“低复杂度源的一般不兼容定理”

你现在的 Theorem 5.19 已经给了 primitive SFT 中的 injective placement barrier。
但它还是以“给定一个有限集合 (S_m) 与概率向量 (\mu_m)”来写。对 SIADS 审稿人来说，再往前一步，把它改写成“任意低复杂度 deterministic source 的普适 incompatibility theorem”，会更有力。

下面这条结论是直接从你现在的 Theorem 5.19 推出来的，但正文中还没有明确写出。

---

## Theorem 5.21. Universal primitive-SFT barrier for low-complexity deterministic sources

设 (\Sigma_A) 是 primitive one-step SFT，拓扑熵为
[
h=\log\lambda,
]
其 Parry (m)-block law 为 (\pi_m^A)。设 ((S_m,\mu_m)_{m\ge 1}) 是一族有限概率空间，满足：

1. (|S_m| = e^{o(m)}).
2. 对每个 (q\in[0,\infty])，有
   [
   H_q(\mu_m)=\log |S_m| + O(1),
   ]
   其中 (O(1)) 可取对 (q) 一致。

则对于充分大的 (m)，任意 injection
[
\iota_m:S_m\hookrightarrow X_m^A
]
都满足
[
D_q(\iota_{m*}\mu_m ,|, \pi_m^A)
================================

mh-\log |S_m|+O_A(1)+O(1),
\qquad q\in[0,\infty],
]
其中常数对 (q) 一致。

特别地，若 (|S_m|=m+O(1))，则
[
D_q(\iota_{m*}\mu_m ,|, \pi_m^A)
================================

mh-\log m+O(1),
\qquad q\in[0,\infty].
]

---

## Proof

由 Theorem 5.19，存在常数 (c_*>0)、(\kappa_A>0)、以及 (m_0)，使得最大 endpoint class
[
C_m(i_*,j_*)
]
满足
[
|C_m(i_*,j_*)|\ge \kappa_A e^{mh}
\qquad (m\ge m_0),
]
并且对任意 injection (\iota_m:S_m\hookrightarrow X_m^A)，有
[
D_q(\iota_{m*}\mu_m|\pi_m^A)
\ge
(m-1)h-\log c_* - H_q(\mu_m).
\tag{1}
]
另一方面，因为 (|S_m|=e^{o(m)})，故
[
\log |S_m| = o(m).
]
于是对于充分大的 (m)，有
[
|S_m| \le \kappa_A e^{mh} \le |C_m(i_*,j_*)|.
]
因此 Theorem 5.19 的 attainability 部分适用，得到存在 injection (\iota_m) 将 (S_m) 映入该 endpoint class，并且此时
[
\inf_{\iota_m:S_m\hookrightarrow X_m^A}
D_q(\iota_{m*}\mu_m|\pi_m^A)
============================

(m-1)h-\log c_* - H_q(\mu_m).
\tag{2}
]

由假设 2，
[
H_q(\mu_m)=\log |S_m| + O(1)
\qquad (q\in[0,\infty]),
]
且该 (O(1)) 对 (q) 一致。代入 (2)，得到
[
\inf_{\iota_m}
D_q(\iota_{m*}\mu_m|\pi_m^A)
============================

(m-1)h-\log c_*-\log |S_m|+O(1).
]
把 ((m-1)h-\log c_*) 吸收为 (mh+O_A(1))，便得
[
\inf_{\iota_m}
D_q(\iota_{m*}\mu_m|\pi_m^A)
============================

mh-\log |S_m|+O_A(1)+O(1).
]
由于任意 injection 的 divergence 都不小于该 infimum，而可达 injection 存在，所以实际上该数量就是低复杂度 deterministic source 的 sharp placement scale。

若进一步 (|S_m|=m+O(1))，则
[
\log |S_m| = \log m + O(1),
]
代回即得
[
D_q(\iota_{m*}\mu_m|\pi_m^A)
============================

mh-\log m+O(1).
]
证毕。

---

## 这条结果的作用

这条定理把你文章的“prototype value”再往上抬了一层。

它说明，**只要源的 block-complexity 是 subexponential，且 block law 在 realized support 上不是极端尖锐，而是近似 quasi-uniform，那么 injective placement into any primitive SFT 都不可避免地承受**
[
mh-\log |S_m|
]
**量级的 Parry penalty。**

golden-mean benchmark 的真正特殊性，不是“只有它有 barrier”，而是：

* 一般 primitive SFT 只能得到这个 universal placement scale；
* 你的 benchmark 把它 exact 化；
* 并且 canonical fold 本身仍与最优 injection 只差一个 bounded additive error。

这会让审稿人更难把文章看成“单一 golden-mean 技巧”。

---

## 三、如果你要继续补一处最值得补的正文段落，应该写在哪里

我建议只再加一段，不要大改结构。

### 在 Section 5.4 末尾紧接 Theorem 5.19 后面加一个 corollary

就是我上面写的 Theorem 5.21 的简化版。正文里不必写得过长。可以只保留下面这个版本：

> **Corollary 5.xx (Low-complexity source barrier).**
> Let ((S_m,\mu_m)) be a family with (|S_m|=e^{o(m)}) and (H_q(\mu_m)=\log |S_m|+O(1)) uniformly in (q). Then any injective placement into a primitive one-step SFT of entropy (h) satisfies
> [
> D_q^{\mathrm{opt}}(m)=mh-\log |S_m|+O(1),
> \qquad q\in[0,\infty].
> ]
> In particular, linear-complexity sources satisfy
> [
> D_q^{\mathrm{opt}}(m)=mh-\log m+O(1).
> ]

这样你结论部分那句
[
D_q^{\mathrm{opt}}=mh-H_q(\mu_m)+O(1)
]
就不再只是 summary，而是已经在正文里被一个更适合读者消化的 corollary 重新表达过了。

### 在 Section 6.7 前面加一个 theorem 环境

直接把我上面的 Theorem 6.8 写进去。然后数值例子保留在 theorem 后面。这样 Section 6.7 就从“一个 nice example”变成“一个 theorem-backed application section”。

---

## 四、最关键的结论

以现在的稿子为基础，再加上我上面这两条，你整篇文章的逻辑形态会变成：

1. canonical slice 上，fold 对 realized source 是无损的 higher-block conjugacy。
2. 对 Parry baseline 的 mismatch 不是 fold 造成的信息损失，而是 source/reference pairing 的结构性不相容。
3. 这种不相容并非 golden-mean 特例，而是 low-complexity lossless placements into primitive SFTs 的普适 barrier。
4. golden-mean benchmark 的价值，在于它把这个普适 barrier finite-(m) exact 化，并给出显式 optimizer、bounded-gap canonical realization、以及唯一的 contiguous numeration axiom。
5. 整个 audit 不是 rigid rotation 专属，而是对整类 irrational circle diffeomorphisms 共轭不变。

这五步一旦连起来，编辑和审稿人看到的就不再是“一个非常漂亮但略窄的 symbolic dynamics 例子”，而会更接近：

**一篇用一个 fully solvable benchmark 精确标定 low-complexity coarse-graining barrier 的 applied symbolic-dynamics paper。**
