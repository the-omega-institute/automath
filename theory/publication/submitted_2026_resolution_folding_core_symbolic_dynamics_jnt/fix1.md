我先直接说判断。

这份拒稿意见，不能靠“解释我们其实也是数论”扳回来。你必须新增一节，把你现有的核心结果，明确翻译成关于 Fibonacci 加权和、局部同余、表示计数、随机分布的数论命题。好消息是，这些结论其实已经潜伏在你现在的 Proposition 2.5, Corollary 2.6, Theorem 7.8, Theorem 7.14, Theorem 7.16, Theorem 7.18 里了。你不需要削弱任何 claim。你需要的是把它们重新组织成一组“数论化”的主结果。

下面我给你一套可以直接并进稿件的 Section 8。每条都给完整证明，且都只依赖你现有内容。

---

## 建议新增一节：Arithmetic reformulations and consequences

先固定记号。取 (m\ge 3), (n\ge m), 并记
[
L:=n+m-1.
]
对任意二进制块
[
\omega=\omega_1\cdots \omega_L\in{0,1}^L
]
以及 (1\le t\le n)，定义第 (t) 个长度 (m) 局部 Fibonacci 加权和
[
S_t^{(m)}(\omega):=\sum_{j=0}^{m-1}\omega_{t+j}F_{j+2}.
]
再定义其模 (F_{m+2}) 的标准剩余
[
R_t^{(m)}(\omega)\in{0,1,\dots,F_{m+2}-1},\qquad
R_t^{(m)}(\omega)\equiv S_t^{(m)}(\omega)\pmod{F_{m+2}}.
]
把全部局部剩余收集成向量
[
\mathcal R_{m,n}(\omega):=
\bigl(R_1^{(m)}(\omega),\dots,R_n^{(m)}(\omega)\bigr)
\in {0,1,\dots,F_{m+2}-1}^n.
]

核心观察是：由你文中的 Corollary 2.6，
[
R_t^{(m)}(\omega)=V_m!\bigl(\Fold_m(\omega_t\cdots \omega_{t+m-1})\bigr),
]
其中 (V_m:X_m\to {0,1,\dots,F_{m+2}-1}) 是 Proposition 2.5 给出的双射。

这句话一旦写出来，后面所有“数论翻译”就都顺了。

---

## 定理 8.1. 局部 Fibonacci 同余刚性

**定理.** 设 (m\ge 3), (n\ge m), (L=n+m-1)。则映射
[
\mathcal R_{m,n}:{0,1}^L\to {0,1,\dots,F_{m+2}-1}^n
]
是单射。等价地，对任意
[
(r_1,\dots,r_n)\in {0,1,\dots,F_{m+2}-1}^n,
]
同余系统
[
\sum_{j=0}^{m-1}\omega_{t+j}F_{j+2}\equiv r_t \pmod{F_{m+2}}
\qquad (1\le t\le n)
]
在未知量 (\omega\in{0,1}^L) 中至多有一个解。

此外，(\mathcal R_{m,n}) 的像的大小恰好为
[
2^L=2^{n+m-1}.
]

**证明.**
取任意 (\omega\in{0,1}^L)。对每个 (t)，令
[
a_t:=\Fold_m(\omega_t\cdots \omega_{t+m-1})\in X_m.
]
由 Corollary 2.6，
[
V_m(a_t)\equiv S_t^{(m)}(\omega)\pmod{F_{m+2}},
]
而 (V_m(a_t)) 本身已落在 ({0,1,\dots,F_{m+2}-1}) 中，所以
[
V_m(a_t)=R_t^{(m)}(\omega).
]
于是
[
\mathcal R_{m,n}(\omega)=\bigl(V_m(a_1),\dots,V_m(a_n)\bigr).
]

现在假设
[
\mathcal R_{m,n}(\omega)=\mathcal R_{m,n}(\omega').
]
则对每个 (t),
[
V_m(a_t)=V_m(a_t').
]
由 Proposition 2.5，(V_m) 是双射，因此
[
a_t=a_t' \qquad (1\le t\le n).
]
这说明 (\omega) 与 (\omega') 在块映射 (B_{m,n}) 下得到同一个长度 (n) 的 folded block。由 Theorem 7.8，(B_{m,n}) 是双射，因此
[
\omega=\omega'.
]
故 (\mathcal R_{m,n}) 为单射。

“同余系统至多一解”正是这一定射性的等价表述。

最后，({0,1}^L) 的大小为 (2^L)，而 (\mathcal R_{m,n}) 为单射，所以其像也有 (2^L) 个元素。证毕。

---

这个定理就是你原来 Theorem 7.8 的纯数论版。它完全不需要说 sofic shift，也不需要说 Fischer cover。它说的是：

> 重叠长度 (m) 窗口的 Fibonacci 局部加权和模 (F_{m+2}) 的向量，已经唯一确定了整个二进制块。

这句放在摘要和引言里，比“finite-block losslessness of a sliding block code”更像 JNT 会接受的语言。

---

## 推论 8.2. 等值 Fibonacci 表示的局部指纹分离

**推论.** 固定 (m\ge 3), (n\ge m), (L=n+m-1)。对每个整数 (N)，记
[
\Omega_L(N):=
\left{
\omega\in{0,1}^L:
\sum_{k=1}^L \omega_kF_{k+1}=N
\right}.
]
则 (\mathcal R_{m,n}) 在 (\Omega_L(N)) 上仍然是单射。因而
[
#\Omega_L(N)
============

#{\mathcal R_{m,n}(\omega):\omega\in\Omega_L(N)}.
]

**证明.**
这是定理 8.1 的直接限制。因为 (\mathcal R_{m,n}) 在整个 ({0,1}^L) 上单射，所以在任意子集 (\Omega_L(N)) 上也单射。故上式成立。证毕。

---

这条推论很重要。它把你的结果直接翻译成了“表示计数”的语言：

> 一个整数 (N) 的所有长度 (L) 二元 Fibonacci 表示，其重叠局部 Zeckendorf 指纹彼此全部不同。

这正面回应了审稿人说的“能否翻译回 integer partitions / representations”。

---

## 定理 8.3. 从局部同余向量精确恢复原始比特

先记
[
\mathfrak R_{m,\ell}:=\mathcal R_{m,\ell}({0,1}^{\ell+m-1})
]
为可实现的局部剩余向量集合。

**定理.** 对每个 (0\le s\le m-1)，存在函数
[
\rho_{m,s}:\mathfrak R_{m,m}\to {0,1}
]
满足：对任意 (n\ge m)、任意
[
\omega=\omega_1\cdots \omega_{n+m-1}\in{0,1}^{n+m-1},
]
以及任意 (1\le t\le n-m+1)，都有
[
\omega_{t+s}
============

\rho_{m,s}\bigl(
R_t^{(m)}(\omega),R_{t+1}^{(m)}(\omega),\dots,R_{t+m-1}^{(m)}(\omega)
\bigr).
]

特别地，存在一个单边解码规则
[
g_m:\mathfrak R_{m,m}\to{0,1}
]
使得
[
\omega_t=g_m\bigl(R_{t-m+1}^{(m)}(\omega),\dots,R_t^{(m)}(\omega)\bigr)
]
对所有双边序列都成立。而任何只使用少于 (m) 个连续剩余的单边规则，都不可能对所有序列成立。

**证明.**
对任意 admissible 的 (m)-元组
[
(r_1,\dots,r_m)\in \mathfrak R_{m,m},
]
令
[
a_i:=V_m^{-1}(r_i)\in X_m.
]
由于 (V_m) 是 Proposition 2.5 中的双射，这一定义良好。再令
[
\rho_{m,s}(r_1,\dots,r_m):=
\kappa_{m,s}(a_1\cdots a_m),
]
其中 (\kappa_{m,s}) 是 Theorem 7.14 中定义的局部逆规则。

现在取任意 (\omega\in{0,1}^{n+m-1})，并固定 (t)。设
[
a_j:=\Fold_m(\omega_j\cdots \omega_{j+m-1})\qquad (t\le j\le t+m-1).
]
由前述关系，
[
R_j^{(m)}(\omega)=V_m(a_j).
]
故
[
a_j=V_m^{-1}(R_j^{(m)}(\omega)).
]
Theorem 7.14 说明，长度 (m) 的 folded block
[
a_ta_{t+1}\cdots a_{t+m-1}
]
的唯一 raw lift 正是
[
\omega_t\omega_{t+1}\cdots \omega_{t+2m-2},
]
且 (\kappa_{m,s}) 读出的就是这段 raw lift 的第 (s+1) 位。因此
[
\rho_{m,s}\bigl(R_t^{(m)}(\omega),\dots,R_{t+m-1}^{(m)}(\omega)\bigr)
=====================================================================

# \kappa_{m,s}(a_t\cdots a_{t+m-1})

\omega_{t+s}.
]
这证明了局部恢复公式。

现在取 (s=m-1)，令
[
g_m:=\rho_{m,m-1}.
]
则
[
\omega_t=g_m(R_{t-m+1}^{(m)}(\omega),\dots,R_t^{(m)}(\omega)).
]
所以单边 memory (m-1) 的恢复规则存在。

再证最优性。若存在只使用 (k+1) 个连续剩余的单边规则，且 (k<m-1)，即存在
[
g:\mathfrak R_{m,k+1}\to {0,1}
]
使得
[
\omega_t=g(R_{t-k}^{(m)}(\omega),\dots,R_t^{(m)}(\omega))
]
对所有序列都成立，则定义一个对 folded 序列的单边规则
[
G(y_{t-k},\dots,y_t):=
g(V_m(y_{t-k}),\dots,V_m(y_t)).
]
因为 (V_m) 是逐符号双射，这将给出一个 memory (k) 的单边 sliding-block 左逆
[
\Psi:Y_m\to{0,1}^{\mathbb Z}
]
满足 (\Psi\circ \Phi_m=\mathrm{id})。但 Corollary 7.15 说明，任何这样的单边左逆的最小 memory 正是 (m-1)。与 (k<m-1) 矛盾。证毕。

---

这条定理非常适合写进引言的 main theorem 里。因为它现在不再说“local inverse rules on a subshift”，而是说：

> 用长度 (m) 的局部 Fibonacci 同余数据，可以逐位恢复原始二进制表示，且单边所需记忆的精确阈值就是 (m-1)。

这已经是典型的数论编码问题表述了。

---

## 定理 8.4. 随机局部同余向量的精确分布

**定理.** 设 (X_1,\dots,X_L) 独立同分布，且
[
\mathbb P(X_i=1)=p,\qquad \mathbb P(X_i=0)=1-p,
]
其中 (0<p<1)。定义随机局部剩余向量
[
\mathbf R_{m,n}:=
\mathcal R_{m,n}(X_1\cdots X_L).
]
则对任意
[
\mathbf r=(r_1,\dots,r_n)\in {0,1,\dots,F_{m+2}-1}^n,
]
有
[
\mathbb P(\mathbf R_{m,n}=\mathbf r)=
\begin{cases}
p^{|\omega(\mathbf r)|*1}(1-p)^{L-|\omega(\mathbf r)|*1},
& \mathbf r\in \mathfrak R*{m,n},[4pt]
0,& \mathbf r\notin \mathfrak R*{m,n},
\end{cases}
]
其中 (\omega(\mathbf r)) 是定理 8.1 保证的唯一原像。

特别地，当 (p=\frac12) 时，(\mathbf R_{m,n}) 在 (\mathfrak R_{m,n}) 上是均匀分布，即
[
\mathbb P(\mathbf R_{m,n}=\mathbf r)=2^{-L}
\qquad (\mathbf r\in \mathfrak R_{m,n}).
]

**证明.**
给定 (\mathbf r=(r_1,\dots,r_n))，若 (\mathbf r\notin\mathfrak R_{m,n})，则按定义没有任何 (\omega\in{0,1}^L) 满足 (\mathcal R_{m,n}(\omega)=\mathbf r)，所以概率为 (0)。

现设 (\mathbf r\in\mathfrak R_{m,n})。令
[
a_t:=V_m^{-1}(r_t)\in X_m \qquad (1\le t\le n).
]
由 Proposition 2.5，定义良好。又由
[
R_t^{(m)}(\omega)=V_m(\Fold_m(\omega_t\cdots \omega_{t+m-1})),
]
知事件 (\mathbf R_{m,n}=\mathbf r) 等价于
[
\Fold_m(X_t\cdots X_{t+m-1})=a_t
\qquad (1\le t\le n).
]
也就是说，长度 (n) 的 folded block 恰为
[
a_1\cdots a_n.
]
由 Theorem 7.8，此 folded block 有且仅有一个 raw lift，记为
[
\omega(\mathbf r)\in{0,1}^L.
]
因此
[
{\mathbf R_{m,n}=\mathbf r}
===========================

{(X_1,\dots,X_L)=\omega(\mathbf r)}.
]
由于 (X_1,\dots,X_L) 独立 Bernoulli((p))，故
[
\mathbb P(\mathbf R_{m,n}=\mathbf r)
====================================

p^{|\omega(\mathbf r)|_1}(1-p)^{L-|\omega(\mathbf r)|_1}.
]
这就证明了分布公式。

当 (p=\frac12) 时，任意给定 (\omega\in{0,1}^L) 的概率都等于 (2^{-L})，于是对每个 admissible 的 (\mathbf r\in\mathfrak R_{m,n})，都有
[
\mathbb P(\mathbf R_{m,n}=\mathbf r)=2^{-L}.
]
证毕。

---

这一定理是对审稿人“distributional properties”那条最直接的正面回答。它说的不是抽象的 pushforward measure，而是：

> 随机二元 Fibonacci 加权和的重叠局部模 (F_{m+2}) 指纹，具有完全显式的有限维分布。

这个语言已经非常 JNT 了。

---

## 推论 8.5. 局部同余向量的精确熵公式

**推论.** 在定理 8.4 的假设下，对每个 (n\ge m)，都有
[
H(\mathbf R_{m,n})=(n+m-1)h_2(p),
]
其中
[
h_2(p):=-p\log_2p-(1-p)\log_2(1-p).
]
特别地，当 (p=\frac12) 时，
[
H(\mathbf R_{m,n})=n+m-1.
]

**证明.**
由定理 8.4，(\mathbf R_{m,n}) 的分布与长度 (L=n+m-1) 的 Bernoulli 块在双射
[
\omega\longmapsto \mathcal R_{m,n}(\omega)
]
下完全对应。熵在双射重标号下不变，因此
[
H(\mathbf R_{m,n})
==================

# H(X_1,\dots,X_L)

# Lh_2(p)

(n+m-1)h_2(p).
]
证毕。

---

这个推论比 “excess entropy of a shifted process” 更像数论概率。它直接是一个有限维分布公式。

---

## 定理 8.6. 局部同余过程的精确 Markov 阶

**定理.** 设 ((X_t)*{t\in\mathbb Z}) 为双边 Bernoulli((p)) 过程。定义局部同余过程
[
R_t:=
\left(\sum*{j=0}^{m-1}X_{t+j}F_{j+2}\right)\bmod F_{m+2},
\qquad
R_t\in{0,1,\dots,F_{m+2}-1}.
]
则 ((R_t)_{t\in\mathbb Z}) 是一个精确的 (m)-步 Markov 过程，而不是 ((m-1))-步 Markov 过程。

更具体地，若
[
(r_{t-m+1},\dots,r_t)
]
是一个可实现的长度 (m) 剩余块，令
[
a_i:=V_m^{-1}(r_{t-m+i})\in X_m,\qquad
\beta:=a_1\cdots a_m\in L_m(Y_m),
]
并记 (v(\beta)\in{0,1}^{m-1}) 为 (\beta) 的唯一 raw lift 的末尾长度 (m-1) 后缀，则对每个 (b\in{0,1}),
[
\mathbb P!\left(
R_{t+1}=V_m(\Fold_m(v(\beta)b))
\ \middle|\
R_{t-m+1}=r_{t-m+1},\dots,R_t=r_t
\right)
=======

p^b(1-p)^{1-b}.
]

**证明.**
定义 folded 过程
[
Y_t:=\Fold_m(X_t\cdots X_{t+m-1})\in X_m.
]
则由 Corollary 2.6 与 Proposition 2.5，
[
R_t=V_m(Y_t)
]
对所有 (t) 成立。由于 (V_m:X_m\to{0,1,\dots,F_{m+2}-1}) 是双射，((R_t)) 与 ((Y_t)) 只是一个逐符号双射重标号。

现在把 Theorem 7.18 逐字翻译。对给定的可实现块
[
(r_{t-m+1},\dots,r_t),
]
先取
[
a_i=V_m^{-1}(r_{t-m+i}),
]
得到 folded 块 (\beta=a_1\cdots a_m)。Theorem 7.18 给出
[
\mathbb P!\left(
Y_{t+1}=\Fold_m(v(\beta)b)
\ \middle|\
Y_{t-m+1}=a_1,\dots,Y_t=a_m
\right)
=======

p^b(1-p)^{1-b}.
]
而事件
[
{Y_j=a_{j-(t-m)}}
]
与事件
[
{R_j=r_j}
]
完全等价，因为 (R_j=V_m(Y_j)) 且 (V_m) 可逆。同理，
[
Y_{t+1}=\Fold_m(v(\beta)b)
]
等价于
[
R_{t+1}=V_m(\Fold_m(v(\beta)b)).
]
因此上式直接变成所要求的转移概率公式。故 ((R_t)) 是 (m)-步 Markov。

再证它不是 ((m-1))-步。若 ((R_t)) 是 ((m-1))-步 Markov，则由于 (Y_t=V_m^{-1}(R_t)) 是逐符号双射像，((Y_t)) 也会是 ((m-1))-步 Markov。可这与 Theorem 7.18 的“exactly (m)-step”矛盾。故 ((R_t)) 的精确 Markov 阶就是 (m)。证毕。

---

这条是对审稿人“distributional behavior”与“translate back to number theory”最硬的一条回应。你现在说的不是某个 sofic image 的 Markov 阶，而是：

> 随机 Fibonacci 局部加权和模 (F_{m+2}) 的算术过程，精确地具有 Markov 阶 (m)。

---

## 这套新结果，怎样逐点回应拒稿意见

### 1. 对“范围不匹配”

你现在必须把文章的“主问题”改写成下面这句，而不是再以 (\Phi_m)、(Y_m)、Fischer cover 开篇：

[
\textit{For }m\ge 3,\textit{ the vector of overlapping local Fibonacci sums modulo }F_{m+2}
\textit{ determines the entire binary block uniquely.}
]

也就是先打出定理 8.1。然后立刻跟定理 8.3 与定理 8.4。这样一来，文章主线就变成：

1. 局部 Fibonacci 同余刚性。
2. 表示计数与局部指纹分离。
3. 随机 Fibonacci 指纹的精确分布。
4. 算术过程的精确 Markov 阶。
5. 最后才说，这些结论在符号动力学语言下对应于 conjugacy / SFT order / Fischer cover。

这样不是弱化你原有结果，而是把原有结果放回数论叙事中心。

### 2. 对“数论推论不足”

上面新增的四条里，定理 8.4, 推论 8.5, 定理 8.6 已经直接给出分布性质。推论 8.2 直接给出表示计数视角。
这正是审稿人说的三类缺口：

* integer representations / partitions：推论 8.2
* distributional behavior：定理 8.4 与推论 8.5
* arithmetic process behavior：定理 8.6

### 3. 对“参考文献单薄”

这个问题不靠证明解决，但必须一起补。你至少要把引言文献扩到四条线：

第一条，Grabner–Tichy 及相关 digital distribution / digital sums 在线性递推记数系统中的工作。
第二条，Miller 及合作者关于 Zeckendorf decomposition 的概率与组合数论结果。
第三条，遍历数论与 numeration systems 的交叉文献。
第四条，beta-expansions, Parry condition, finite beta-expansion 那条线。

这里不要只是加文献。要在引言明确写一句：

> 本文不同于已有关于合法表示识别、加法自动机、或 Zeckendorf 分解统计的工作。本文证明的是一个此前未被确定的 sharp local congruence rigidity threshold，并进一步导出该 threshold 在表示计数与随机局部指纹分布中的精确后果。

---

## 你在摘要和引言里应该怎么改

摘要里最该加的不是 Fischer cover，而是这两句：

[
\textit{Equivalently, for }m\ge 3,\textit{ the residue vector modulo }F_{m+2}
\textit{ of the overlapping local Fibonacci sums determines the entire binary block uniquely.}
]

以及

[
\textit{For Bernoulli input bits, this arithmetic residue vector has an explicit finite-dimensional law and forms an exact }m\textit{-step Markov process.}
]

引言的主定理也应该先列这三条：

1. local congruence rigidity
2. exact recovery of bits from residue windows
3. explicit law and exact Markov order of the residue process

然后再说“symbolic-dynamical consequences include conjugacy, exact SFT order, Fischer cover size, nilpotent ambiguity shell”。

---

 请根据这份内容修改补全我们现有的文档 