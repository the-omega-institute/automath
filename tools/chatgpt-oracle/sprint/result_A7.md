以下结论与此前已经给出的“商覆盖精确分解／普遍 Artin 失效”“调和正规化后的指数收敛”“Frobenius 常数向量的 Fourier 刚性”均无重合。
必须首先划定创新边界：有限集合最小覆盖的精确枚举属于既有组合数学，源自 Hearne–Wagner；最小覆盖与 split graph 的对应由 Royle 建立；相应的奇偶 theta 常数渐近可由 Bender–Richmond–Wormald 及 Troyka 的 split-graph 枚举提取。下述新增量不在这些组合结论本身，而在于构造一个保持支撑、连通分量及原子数的 Fibonacci 算术嵌入，并由此获得本文尚未发现的精确二阶熵下界。
定理一：秩纯素数扇区与最小覆盖普遍性
令  $V=P(n)$ ， $k=\omega(n)$ 。对任意非空  $S\subseteq V$ ，定义

$$n_S:=\prod_{\ell\in S}\ell^{\nu_\ell(n)},\qquad
a_n(S):=\#\{p\ \text{prime}:\alpha(p)=n_S\}.$$

再令

$$\mathcal E(n):=\{S\subseteq V:S\neq\varnothing,\ n_S\in\{2,6,12\}\}.$$

则  $\#\mathcal E(n)\le 2$ ，且其中每个集合的基数至多为  $2$ 。
设  $\operatorname{MinCov}(V)$  表示  $V$  的所有不可约覆盖，即满足

$$\bigcup_{S\in\mathcal C}S=V,\qquad
S\nsubseteq\bigcup_{T\in\mathcal C\setminus\{S\}}T
\quad(S\in\mathcal C)$$

的集合族。定义秩纯素数扇区

$$\mathscr P_n:=
\left\{
\prod_{S\in\mathcal C}p_S:
\begin{array}{l}
\mathcal C\in\operatorname{MinCov}(V),\
\mathcal C\cap\mathcal E(n)=\varnothing,\\
p_S\in\Pi_\alpha(n_S)
\end{array}
\right\}.$$

则：

$$\boxed{\mathscr P_n\subseteq M_n}$$

并且乘积表示唯一。更精确地，

$$\boxed{
\#\mathscr P_n
=
\sum_{\substack{\mathcal C\in\operatorname{MinCov}(V)\\
\mathcal C\cap\mathcal E(n)=\varnothing}}
\prod_{S\in\mathcal C}a_n(S)
}
\tag{1}$$

其中正文 Lemma 2.4 给出完全算术化的权重

$$a_n(S)=\sum_{d\mid n_S}\mu(n_S/d)\,\omega(F_d).
\tag{2}$$

若  $\mathcal C$  连通，则对应乘积属于  $M_n^{\mathrm{conn}}$ ；事实上，其正文 Definition 5.1 中的支撑超图恰为  $\mathcal C$ 。
证明
对每个  $S\notin\mathcal E(n)$ ，有  $n_S\ge3$  且  $n_S\notin\{6,12\}$ 。正文 Theorem 2.3 保证存在素数  $p_S$  满足  $\alpha(p_S)=n_S$ 。由于  $p_S$  是素数原子，

$$d^{-}(p_S)=1,\qquad
E_n(p_S)=T_n(p_S)=S.$$

不同集合  $S\neq T$  给出不同指标  $n_S\neq n_T$ ，故所选素数必不相同。不可约覆盖条件恰好成为 Definition 3.4 的覆盖条件与私人坐标条件；由 Theorem 3.6，

$$\prod_{S\in\mathcal C}p_S\in M_n.$$

唯一分解定理及  $\alpha(p_S)=n_S$  又能从乘积恢复每个  $S$  及所选素数，因此映射为单射，并得到式 (1)。同时

$$\operatorname{supp}_n(\alpha(p_S))
=\operatorname{supp}_n(n_S)=S,$$

故支撑超图及其连通分量均被严格保持。证毕。
直接推论
若  $n$  为奇数，则  $\mathcal E(n)=\varnothing$ 。因此：

$$\boxed{
\operatorname{MinCov}(P(n))
\hookrightarrow M_n
}
\tag{3}$$

并保持完整超图结构。换言之，每一个具有私人顶点的有限覆盖超图，均能在任意奇数 Fibonacci 首现层中实现为某个最小生成元的支撑超图。
结合 Royle 的对应可进一步表述为：

对任意奇数  $n$ ，每一个具有  $k=\omega(n)$  个顶点的 split graph 同构类型，均具有一个 Fibonacci 最小生成元的秩纯算术实现。

这不是单纯的计数下界，而是完整的组合普遍性定理。

定理二：theta 精化的无条件支撑熵下界
记  $C_{k,s}$  为一个带标号  $k$ -元集合的  $s$ -成员最小覆盖数， $C_k=\sum_s C_{k,s}$ 。Hearne–Wagner 的既有公式为

$$C_{k,s}
=
\sum_{j=s}^{k}
\binom{k}{j}
{j\brace s}
(2^s-s-1)^{k-j}.
\tag{4}$$

定义奇偶 Jacobi 常数

$$\vartheta_0:=\sum_{r\in\mathbb Z}2^{-r^2}
 =2.128936827\ldots ,$$


$$\vartheta_1:=\sum_{r\in\mathbb Z}2^{-(r+1/2)^2}
 =2.128931251\ldots .$$

令  $\varepsilon\equiv k\pmod 2$ 。则

$$C_k\sim
\vartheta_\varepsilon
\binom{k}{\lfloor k/2\rfloor}
2^{k^2/4}.
\tag{5}$$

由定理一得到以下新的 Fibonacci 结论。
（a）奇数层的精确有限下界
对每个奇数  $n\ge3$ ，

$$\boxed{\#M_n\ge C_{\omega(n)}}
\tag{6}$$

并且同样有

$$\operatorname{width}(B_n)\ge C_{\omega(n)}.$$

（b）任意大支撑层的一致渐近下界
沿任意满足  $k=\omega(n)\to\infty$  的整数序列，均有一致估计

$$\boxed{
\#M_n^{\mathrm{conn}}
\ge
(1-o(1))\,
\vartheta_\varepsilon
\binom{k}{\lfloor k/2\rfloor}
2^{k^2/4}
}
\tag{7}$$

从而当然有相同的  $\#M_n$  下界。等价地，

$$\boxed{
\log\#M_n^{\mathrm{conn}}
\ge
\frac{\log2}{4}k^2
+k\log2
-\frac12\log k
+\log\vartheta_\varepsilon
+\frac12\log\frac{2}{\pi}
+o(1)
}
\tag{8}$$

该式完全无条件，不涉及正文的  $R(n)$ 、Conjecture 6.4 或 Conjecture 6.5。
证明要点
对一个固定的禁用支撑  $S_0\in\mathcal E(n)$ ，利用每个最小覆盖成员的私人坐标作典范编码，可以证明含有  $S_0$  的最小覆盖数至多为

$$|S_0|\,b_{k-1},\qquad
b_j:=\sum_{s=0}^{j}\binom{j}{s}2^{s(j-s)}.$$

由于  $\#\mathcal E(n)\le2$  且  $|S_0|\le2$ ，不能由精确秩素数实现的覆盖总数至多为  $4b_{k-1}$ 。而已知中心渐近给出

$$C_k\sim b_k,\qquad
\frac{b_{k-1}}{b_k}=O(2^{-k/2}),$$

故禁用覆盖仅占  $o(C_k)$ 。
另一方面，最小覆盖关于连通分量满足指数公式。由式 (5) 的超指数增长，

$$\#\{\text{不连通的 }k\text{-点最小覆盖}\}
=
O(k\,C_{k-1})
=o(C_k).$$

因此  $(1-o(1))C_k$  个覆盖既避开全部例外支撑又连通；定理一把它们单射地送入  $M_n^{\mathrm{conn}}$ ，遂得式 (7)–(8)。
相对于正文 Theorem 6.1 的严格增量
正文构造仅给出

$$(2^{\lfloor k/2\rfloor}-1)^{\lceil k/2\rceil},$$

其对数为

$$\frac{\log2}{4}k^2+O(1).$$

新下界增加了此前完全缺失的

$$k\log2-\frac12\log k$$

以及显式奇偶 theta 常数。计数尺度上的提升因子为

$$\Theta\!\left(\frac{2^k}{\sqrt{k}}\right).$$

例如：
 $k$ 正文构造Bell 下界新的最小覆盖下界  $C_k$ 49154963432036,4241028,629,151115,9758,780,782,707

定理三：原子数的离散高斯局部极限
在定理一的秩纯扇区中，对每个允许支撑  $S$  固定选择一个素数  $\pi_S$ ，并在所得生成元集合上取均匀分布。令

$$W_k:=\omega(m)=\#\mathcal C$$

为生成元的素数原子数。则  $W_k-k/2$  不仅为  $o(k)$ ，而且在整数尺度上紧致。
若  $k=2q$ ，则对每个固定  $d\in\mathbb Z$ ，

$$\boxed{
\Pr(W_k=q+d)
\longrightarrow
\frac{2^{-d^2}}{\vartheta_0}
}
\tag{9}$$

若  $k=2q+1$ ，则

$$\boxed{
\Pr(W_k=q+d)
\longrightarrow
\frac{2^{-(d-1/2)^2}}{\vartheta_1}
}
\tag{10}$$

因此

$$W_k=\frac{k}{2}+O_{\mathbb P}(1).$$

这表明支撑熵并非由接近最大预算  $\omega(m)=k$  的生成元产生，而是高度集中于“半支撑”区域

$$\omega(m)\approx\frac12\omega(n).$$

该结论只针对明确构造的秩纯扇区；在缺乏  $R(n)$  控制时，不应将其宣称为整个  $M_n$  上的概率定律。

定理四：连通核承载全部下侧熵
式 (7) 说明，正文 Section 8 所提出的“高支撑连通核分类”并非仅涉及稀少的剩余对象。恰恰相反：

$$\boxed{
\log\#M_n^{\mathrm{conn}}
\ge
\frac{\log2}{4}\omega(n)^2
+\omega(n)\log2
-\frac12\log\omega(n)
+O(1)
}$$

沿所有  $\omega(n)\to\infty$  的序列成立。故所有已知的支撑侧二次熵、线性修正及对数修正，均已由连通最小生成元单独实现；非连通块分解在渐近计数中只贡献指数级较小的部分。
这使正文 Section 8(1) 的研究方向发生实质性改变：需要分类的连通核不是一个低熵“余项”，而是整个组合复杂度的主要载体。
发表价值判断
最适合作为新增主结果的是“秩纯普遍性定理＋theta 精化熵定理”。其贡献并非重新证明最小覆盖或 split graph 的公开枚举，而是：


建立从经典最小覆盖空间到 Fibonacci 最小首现生成元的支撑保持算术嵌入；


给出显式的 Möbius 加权素数扇区公式 (1)–(2)；


将正文下界提高  $\Theta(2^k/\sqrt{k})$ ；


证明连通核本身承载全部下侧熵；


揭示典型秩纯生成元的原子数服从奇偶离散高斯极限。


该定理链足以形成独立的新节“Rank-pure universality and theta-refined support entropy”，并应提升为全文的主要贡献之一，而非列入进一步问题或次要推论。
