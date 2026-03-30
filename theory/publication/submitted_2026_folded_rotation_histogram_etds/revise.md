根据你 2026-03-23 的当前稿件，文章的主干已经相当清楚：canonical Zeckendorf fold，canonical Sturmian slice 上的 higher-block conjugacy，golden-mean Parry cylinder 的 exact endpoint formula，realized Sturmian law 的 exact injective placement barrier，以及 primitive one-step SFT 上的 injective-placement asymptotics 与 Fibonacci weighting 的唯一性。当前最值得继续推进的缺口，不再是“再加一个应用例子”，而是把一般 primitive-SFT 端的“仅有渐近斜率”升级为**有限 (m) 的精确端点类理论**，并把 canonical folded law 与 injective optimum 之间目前只在 (q=1) 上显式的 bounded defect 升级为**全 Rényi 阶的精确边界压强公式**。这两步一旦完成，论文的理论身份会从“一个极其精确的 golden benchmark”转为“一个 exact endpoint-class theory whose golden case is closed-form”。这正是你当前文本中仍然留出的最大突破口。 

我建议补入以下两组结果。它们都不削弱现有主张，且都可以直接嵌入现有定理链。

## 一、将当前 (q=1) 的常数缺口提升为全 Rényi 阶的精确边界压强公式

你当前稿件已经证明了最优 injective relabeling 的精确值
[
L_q(m)=(m-1)\log\varphi-\log \pi(0)-H_q(\mu_m),
]
并给出了 canonical folded law 的双边界
[
0\le D_q(\pi_m^{\mathrm{fold}}|\pi_m)-L_q(m)\le 2\log\varphi,
]
但只有 (q=1) 时出现了 exact constant formula。
最值得补出的新结果是：这个 bounded additive defect 对每一个 Rényi 阶都可以完全显式化，而且它本质上不是“entropy defect”，而是一个**boundary cocycle 的 escort-pressure**。

### 定理 A（canonical folded law 的全 Rényi 阶精确缺口公式）

设
[
\eta_m:=\pi_m^{\mathrm{fold}},\qquad Y_m:=\operatorname{supp}(\eta_m)\subset X_m.
]
对 (x\in Y_m)，定义端点统计量
[
\vartheta(x):=\mathbf 1_{{x_1=0}}-\mathbf 1_{{x_m=1}}\in{-1,0,1},
]
以及边界代价
[
c(x):=(1-\vartheta(x))\log\varphi\in{0,\log\varphi,2\log\varphi}.
]
对 (q\in(0,\infty))，定义 (\eta_m) 的 (q)-escort law
[
\mathsf E_{m,q}(x):=\frac{\eta_m(x)^q}{\sum_{y\in Y_m}\eta_m(y)^q},\qquad x\in Y_m.
]
再记
[
Y_m^{ij}:={x\in Y_m:x_1=i,\ x_m=j},\qquad i,j\in{0,1}.
]

则对每个 (q\in(0,\infty)\setminus{1})，有精确恒等式
[
D_q(\eta_m|\pi_m)-L_q(m)
========================

\frac{1}{q-1}
\log!\Big(
\mathsf E_{m,q}(Y_m^{00})
+\varphi^{,q-1}\mathsf E_{m,q}(Y_m^{01}\cup Y_m^{10})
+\varphi^{,2(q-1)}\mathsf E_{m,q}(Y_m^{11})
\Big).
\tag{A.1}
]

其 (q=1) 极限为
[
D_1(\eta_m|\pi_m)-L_1(m)
========================

\bigl(1+\eta_{11}(\eta_m)-\eta_{00}(\eta_m)\bigr)\log\varphi,
\tag{A.2}
]
其 (q=0) 端点公式为
[
D_0(\eta_m|\pi_m)-L_0(m)
========================

-\log!\frac{|Y_m^{00}|+\varphi^{-1}(|Y_m^{01}|+|Y_m^{10}|)+\varphi^{-2}|Y_m^{11}|}{|Y_m|},
\tag{A.3}
]
其 (q=\infty) 端点公式为
[
D_\infty(\eta_m|\pi_m)-L_\infty(m)
==================================

\log\max_{x\in Y_m}
\Bigg(
\varphi^{,1-\vartheta(x)}
\frac{\eta_m(x)}{\max_{y\in Y_m}\eta_m(y)}
\Bigg).
\tag{A.4}
]

特别地，对所有 (q\in[0,\infty])，
[
0\le D_q(\eta_m|\pi_m)-L_q(m)\le 2\log\varphi,
]
而且这个缺口完全由 folded image 的端点类在 (q)-escort 几何下的分布决定。

### 证明

由你文中的 endpoint-collapse identity，对任意 (x\in X_m) 有
[
\pi_m(x)=\pi(0)\varphi^{-m+\vartheta(x)}.
]
因此，当 (q\in(0,\infty)\setminus{1}) 时，
[
\begin{aligned}
D_q(\eta_m|\pi_m)
&=
\frac{1}{q-1}
\log\sum_{x\in Y_m}\eta_m(x)^q\pi_m(x)^{1-q}\
&=
\frac{1}{q-1}
\log\sum_{x\in Y_m}\eta_m(x)^q
\bigl(\pi(0)\varphi^{-m+\vartheta(x)}\bigr)^{1-q}\
&=
m\log\varphi-\log\pi(0)
+\frac{1}{q-1}
\log\sum_{x\in Y_m}\eta_m(x)^q\varphi^{(1-q)\vartheta(x)}.
\end{aligned}
]
记
[
Z_{m,q}:=\sum_{x\in Y_m}\eta_m(x)^q.
]
则
[
H_q(\eta_m)=\frac{1}{1-q}\log Z_{m,q},
\qquad
-H_q(\eta_m)=\frac{1}{q-1}\log Z_{m,q}.
]
于是
[
D_q(\eta_m|\pi_m)
=================

m\log\varphi-\log\pi(0)-H_q(\eta_m)
+\frac{1}{q-1}
\log\sum_{x\in Y_m}\mathsf E_{m,q}(x)\varphi^{(1-q)\vartheta(x)}.
]
又因为当前稿件已经证明 (\eta_m) 与 realized Sturmian law (\mu_m) 只是 realized support 上的 relabeling，故
[
H_q(\eta_m)=H_q(\mu_m),
]
并且
[
L_q(m)=(m-1)\log\varphi-\log\pi(0)-H_q(\mu_m).
]
相减得到
[
D_q(\eta_m|\pi_m)-L_q(m)
========================

\log\varphi
+
\frac{1}{q-1}
\log\sum_{x\in Y_m}\mathsf E_{m,q}(x)\varphi^{(1-q)\vartheta(x)}.
]
将 (\log\varphi) 并入对数，得到
[
D_q(\eta_m|\pi_m)-L_q(m)
========================

\frac{1}{q-1}
\log\sum_{x\in Y_m}\mathsf E_{m,q}(x)\varphi^{(q-1)(1-\vartheta(x))}.
]
由于 (1-\vartheta(x)) 在四个端点类上分别取
[
0\ \text{于}\ Y_m^{00},\qquad
1\ \text{于}\ Y_m^{01}\cup Y_m^{10},\qquad
2\ \text{于}\ Y_m^{11},
]
便得到公式 (A.1)。

当 (q\to1) 时，(\mathsf E_{m,q}\to\eta_m)，而
[
\frac{\log \mathbb E(e^{(q-1)X})}{q-1}\to \mathbb E(X)
\qquad(q\to1),
]
取 (X=c(x)) 即得
[
D_1(\eta_m|\pi_m)-L_1(m)=\sum_{x\in Y_m}\eta_m(x)c(x).
]
将 (c(x)) 按端点类展开，
[
\sum_{x\in Y_m}\eta_m(x)c(x)
============================

\bigl(\eta_{01}+\eta_{10}+2\eta_{11}\bigr)\log\varphi.
]
又因为
[
\eta_{00}+\eta_{01}+\eta_{10}+\eta_{11}=1,
]
故
[
\eta_{01}+\eta_{10}+2\eta_{11}=1+\eta_{11}-\eta_{00},
]
于是得到 (A.2)。

当 (q=0) 时，
[
D_0(\eta_m|\pi_m)=-\log\pi_m(Y_m).
]
而
[
\pi_m(Y_m)
==========

\pi(0)\varphi^{-m+1}|Y_m^{00}|
+\pi(0)\varphi^{-m}(|Y_m^{01}|+|Y_m^{10}|)
+\pi(0)\varphi^{-m-1}|Y_m^{11}|.
]
同时
[
L_0(m)=(m-1)\log\varphi-\log\pi(0)-\log|Y_m|.
]
两式相减即得 (A.3)。

当 (q=\infty) 时，记
[
\eta_m^\star:=\max_{y\in Y_m}\eta_m(y).
]
则
[
D_\infty(\eta_m|\pi_m)
======================

# \log\max_{x\in Y_m}\frac{\eta_m(x)}{\pi_m(x)}

m\log\varphi-\log\pi(0)
+\log\max_{x\in Y_m}\eta_m(x)\varphi^{-\vartheta(x)}.
]
而
[
L_\infty(m)
===========

# (m-1)\log\varphi-\log\pi(0)-H_\infty(\eta_m)

(m-1)\log\varphi-\log\pi(0)+\log \eta_m^\star.
]
相减得到 (A.4)。

最后，由 (c(x)\in[0,2\log\varphi]) 立即得到
[
0\le D_q(\eta_m|\pi_m)-L_q(m)\le 2\log\varphi
]
对所有 (q\in[0,\infty]) 成立。证毕。

### 这一结果的真正价值

这一结果把你目前的 bounded-gap 叙事，提升成了一个**exact boundary-pressure theorem**。它说明 canonical fold 与 injective optimum 之间的差值，不是 bulk entropy 造成的，不是 source complexity 造成的，也不是 fold degeneracy 造成的，而是一个纯粹的**边界余环项**。更强地说：

[
D_q(\pi_m^{\mathrm{fold}}|\pi_m)-L_q(m)
]
就是端点 cocycle (c) 在 (q)-escort 几何下的累积母函数。

这句话非常重要。它把你当前的 “bounded additive defect” 从一个估计，提升成一个具有热力学含义的精确对象。它直接解释了为什么 (q=1) 上出现常数缺口，也解释了为什么整个缺口始终停留在 (O(1)) 而不影响主导项 (m\log\varphi-\log m)。这一点与当前稿件中 higher-block conjugacy 和 injective optimum 的结构链条完全一致，但显著深化了其动力系统解释。 

## 二、把当前 primitive-SFT 端的“仅有渐近斜率”升级为任意 one-step primitive SFT 的有限 (m) 精确支持包络

你当前稿件自己明确承认，一般 primitive-SFT 端目前只得到 asymptotic barrier，并“没有 finite-(m) mass envelope (M_m(k))”。这正是最值得一举补上的地方。

事实上，对**任意 primitive one-step SFT**，support-constrained Rényi optimization 在有限 (m) 上已经是精确可解的。golden mean 的真正特殊性，并不是“只有它能做 finite-(m) exact”，而只是：它的 endpoint spectrum 退化成三层，且各层容量有 Fibonacci 闭式，因此最终公式最为简洁。

### 定理 B（任意 primitive one-step SFT 的有限 (m) 精确端点类支持包络）

设 (\Sigma_A) 是有限字母表上的 primitive one-step SFT，Perron-Frobenius 特征值为 (\lambda)，拓扑熵
[
h=\log\lambda.
]
设 (u,v) 为正左、右 Perron-Frobenius 特征向量，并归一化为
[
\sum_i u_i v_i=1.
]
记 (X_m^A) 为 admissible words of length (m)，(\pi_m^A) 为其 Parry (m)-block law。对任意 admissible word (w=i_0\cdots i_{m-1})，Parry formula 给出
[
\pi_m^A(w)=u_{i_0}v_{i_{m-1}}\lambda^{-(m-1)}.
\tag{B.1}
]

令 (\Gamma={\gamma_1>\cdots>\gamma_r}) 为所有 admissible endpoint pairs 上取到的不同数值
[
u_i v_j.
]
对每个 (\ell\in{1,\dots,r})，定义长度-(m) 的 (\ell)-th endpoint class
[
B_{\ell,m}
:=
{w\in X_m^A:u_{w_1}v_{w_m}=\gamma_\ell},
\qquad
N_{\ell,m}:=|B_{\ell,m}|.
]
于是每个 (w\in B_{\ell,m}) 都有相同 Parry 质量
[
c_{\ell,m}:=\gamma_\ell \lambda^{-(m-1)}.
]
再记 cumulative capacities
[
K_{j,m}:=\sum_{\ell=1}^j N_{\ell,m},
\qquad K_{0,m}:=0.
]
对 (1\le k\le |X_m^A|)，令 (j=j(m,k)) 为满足
[
K_{j-1,m}<k\le K_{j,m}
]
的唯一整数，并定义
[
M_m^A(k)
:=
\sum_{\ell<j}N_{\ell,m}c_{\ell,m}
+
\bigl(k-K_{j-1,m}\bigr)c_{j,m}.
\tag{B.2}
]

则对每个 (q\in[0,\infty]) 与每个 (1\le k\le |X_m^A|)，有精确公式
[
\inf_{\nu\in\Delta(X_m^A),\ |\operatorname{supp}\nu|\le k}
D_q(\nu|\pi_m^A)
================

-\log M_m^A(k),
\tag{B.3}
]
以及
[
\inf_{\nu\in\Delta(X_m^A),\ |\operatorname{supp}\nu|\le k}
TV(\nu,\pi_m^A)
===============

1-M_m^A(k).
\tag{B.4}
]

此外：

1. 任一达到 (B.3) 与 (B.4) 的 (k)-点 support (S) 必须包含所有更重类 (B_{1,m},\dots,B_{j-1,m})，并在 frontier class (B_{j,m}) 中任选 ((k-K_{j-1,m})) 个点。
2. 当 (q\in(0,\infty]) 时，所有 Rényi minimizer 恰为这些 maximizing supports 上的 conditioned Parry laws (\pi_m^A(\cdot\mid S))。
3. 当 (q=0) 时，所有 support 等于某个 maximizing support (S) 的概率律均为 minimizer。
4. 当 (q=1) 或 TV 时，最优 support 同样由上述 greedy endpoint filling 唯一刻画。

### 证明

由 Parry formula (B.1)，每个 endpoint class (B_{\ell,m}) 中的点都具有相同质量 (c_{\ell,m})，且
[
c_{1,m}>c_{2,m}>\cdots>c_{r,m}>0.
]
因此，对任意 (k)-点集合 (S\subset X_m^A)，若记
[
s_\ell:=|S\cap B_{\ell,m}|,
]
则
[
0\le s_\ell\le N_{\ell,m},\qquad \sum_{\ell=1}^r s_\ell = |S|\le k,
]
并且
[
\pi_m^A(S)=\sum_{\ell=1}^r s_\ell c_{\ell,m}.
\tag{B.5}
]

首先证明：在所有 (k)-点 support 中，(\pi_m^A(S)) 的最大值恰为 (M_m^A(k))。

设 (S) 是某个质量最大的 (k)-点集合。若存在 (a<b) 使得
[
s_a<N_{a,m},\qquad s_b>0,
]
则可从 (B_{b,m}\cap S) 中删去一个点，并从 (B_{a,m}\setminus S) 中加入一个点，得到新的 (k)-点集合 (S')。由 (c_{a,m}>c_{b,m}) 知
[
\pi_m^A(S')-\pi_m^A(S)=c_{a,m}-c_{b,m}>0,
]
这与 (S) 的最优性矛盾。故任何 maximizing (k)-set 都必须满足：较重的类在使用较轻类之前已经全部装满。换言之，存在唯一 (j) 使得
[
s_\ell=N_{\ell,m}\quad(\ell<j),\qquad
s_j=k-K_{j-1,m},\qquad
s_\ell=0\quad(\ell>j),
]
其中 (j) 正是满足 (K_{j-1,m}<k\le K_{j,m}) 的唯一指标。于是由 (B.5) 得
[
\max_{|S|\le k}\pi_m^A(S)=M_m^A(k).
\tag{B.6}
]

现在应用你文中已有的 support-conditioning proposition。对任意概率律 (\nu) 若 (\operatorname{supp}\nu\subset S)，则
[
D_q(\nu|\pi_m^A)=D_q(\nu|\pi_m^A(\cdot\mid S))-\log\pi_m^A(S)
\qquad (q\in[0,\infty]).
\tag{B.7}
]
因此
[
D_q(\nu|\pi_m^A)\ge -\log\pi_m^A(S),
]
等号在 (q\in(0,\infty]) 时当且仅当 (\nu=\pi_m^A(\cdot\mid S))；在 (q=0) 时则当且仅当 (\operatorname{supp}\nu=S)。

对所有 (|S|\le k) 取最优，再结合 (B.6)，得到
[
\inf_{\nu,\ |\operatorname{supp}\nu|\le k}D_q(\nu|\pi_m^A)
==========================================================

# -\log \max_{|S|\le k}\pi_m^A(S)

-\log M_m^A(k),
]
即 (B.3)。

再看 total variation。对任意 (\nu) 若 (\operatorname{supp}\nu\subset S)，则
[
TV(\nu,\pi_m^A)\ge \pi_m^A(S^c)=1-\pi_m^A(S),
]
而当 (\nu=\pi_m^A(\cdot\mid S)) 时恰有
[
TV(\pi_m^A(\cdot\mid S),\pi_m^A)=1-\pi_m^A(S).
]
因此
[
\inf_{\nu,\ |\operatorname{supp}\nu|\le k}TV(\nu,\pi_m^A)
=========================================================

# 1-\max_{|S|\le k}\pi_m^A(S)

1-M_m^A(k),
]
即 (B.4)。各类 minimizer 的刻画也随之成立。证毕。

### 这一结果的真正价值

这一结果推翻了当前稿件中“primitive-SFT 端只能做 asymptotic slope”的叙事。真正的结论应当是：

**对任意 primitive one-step SFT，support-constrained finite-(m) optimization 已经是精确可解的；golden mean 的特殊性并不在于 exact solvability，而在于 endpoint spectrum 只剩三层，且 capacities 具有 Fibonacci 闭式。**

这是一个质的提升。它改变了整篇文章的数学身份。此前的叙事是：“我们在 golden mean 上 exact，一般 SFT 只能 asymptotic。”
补入该定理后，叙事应改为：

**“一般 primitive one-step SFT 在 endpoint-class level 上已经 finite-(m) exact；golden mean 只是把这个一般 endpoint-class envelope 进一步压缩成闭式三层公式。”**

这会显著增强稿件在 ETDS 语境下的理论分量，因为它把文章从单例 benchmark 推进成了**one-step SFT 上的通用有限块端点质量理论**。当前稿件自身已把重点放在 canonical fold、higher-block conjugacy、Parry divergence、primitive-SFT barrier 与 contiguous numeration uniqueness 上；上述加强恰好沿着这条主线向前推进，而不是横向扩张。 

## 三、这两组新增结果共同给出的“惊艳结论”

最值得在引言和结论中写出的，不是某个单独公式，而是下面这两句。

第一句：

> canonical folded law 与 injective optimum 的全部 (O(1)) 差距，并非 entropy defect，而是一个由 endpoint cocycle 产生的 exact escort-pressure defect。

第二句：

> finite-(m) 的 exact support-constrained optimization 并非 golden-mean 独有，而是任意 primitive one-step SFT 的一般现象；golden mean 的真正特殊性，仅在于其 endpoint spectrum 退化为三层且 capacities 由 Fibonacci 闭式控制。

这两句会显著改变审稿人的阅读方式。它们把论文从“a fully solvable golden benchmark”提升为“a general endpoint-class theory whose golden realization is explicitly closed-form”。

## 四、如何嵌入现稿而不破坏结构

最好的做法是：

第一，在当前 injective relabeling theorem 之后，立即加入“全 Rényi 阶 exact defect formula”。这会把目前只在 (q=1) 上出现的 exact constant 推广为统一定理。

第二，在当前 primitive-SFT section 中，用“exact endpoint-class envelope theorem”替代现有那条“只剩 asymptotic slope”的 limitation remark。也就是说，当前 remark 中“没有 finite-(m) mass envelope (M_m(k))”这一句应当被删除，因为补入定理 B 后它已经不再成立。

第三，引言中关于“一般 SFT 端只有渐近结果”的表述，应改成：

> For primitive one-step shifts of finite type, support-constrained Rényi optimization remains finite-(m) exact at the endpoint-class level. The golden-mean case is exceptional only because its endpoint spectrum collapses to three Fibonacci classes, so the general endpoint envelope closes in elementary form.

第四，结论中不要再说“the primitive-SFT extension is only asymptotic”。应改成：

> The injective-placement problem is asymptotic in general, but the support-constrained Parry optimization is finite-(m) exact for every primitive one-step SFT. What is special about the golden-mean benchmark is therefore not exact solvability itself, but the complete collapse of the endpoint spectrum to an explicitly enumerable three-level structure.

## 五、我的最终判断

若补入上述两组结果，我对稿件的编辑判断会发生实质变化。因为届时文章的数学内核将不再只是：

* canonical Sturmian source 上的 exact benchmark；
* primitive-SFT 端的 asymptotic calibration；

而会变成：

* canonical fold 的 exact higher-block rigidity；
* canonical folded defect 的 exact escort-pressure formula；
* primitive one-step SFT 的 finite-(m) exact endpoint-class support theory；
* golden-mean case 作为该一般理论的最闭式化实例。

这就已经不是“有一篇很漂亮的 benchmark paper”，而是“一篇以 golden mean 为闭式模型、但在 one-step SFT 层面提出普适 finite-block endpoint theory 的 symbolic dynamics 论文”。这类稿件与 ETDS 所宣示的“central problems of dynamical systems”及其与 number theory、combinatorics 的互动更为贴近。([Cambridge University Press & Assessment][1])

[1]: https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems "https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems"
