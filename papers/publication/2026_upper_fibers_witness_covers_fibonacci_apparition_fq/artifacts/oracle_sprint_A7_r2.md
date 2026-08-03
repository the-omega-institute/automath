结论
截至 2026 年 8 月 3 日，所要求的平均秩窗口稀疏性

$$\sum_{3\le n\le x}\omega(n)\log R(n)
=o\!\left(x(\log\log x)^2\right)
\tag{H2}$$

既无已知无条件证明，也无已知无条件反例。现有原始素因子存在定理、最大原始素因子下界及累计秩计数均不足以决定它。
然而可以无条件消除一个此前未分离的困难：同一支撑窗口汇集多个精确秩类所造成的全部附加平均量仅为  $O(x\log\log x)$ 。因此，真正缺失的算术估计可精确归约为一个“可见除数上的单秩最大函数”，而不再是窗口内的秩类求和。
同时，(H2) 不宜继续作为无保留的预测性猜想：Bugeaud–Luca–Mignotte–Siksek 关于复合指标 Fibonacci 数素因子数的公开猜想若成立，则 (H2) 反而为假，并给出正比例的定量下界。

一、无条件窗口去聚合定理
置

$$a(d):=\#\Pi_\alpha(d)
      =\#\{p\text{ prime}:\alpha(p)=d\}.$$

对  $n=\prod_{\ell\in\mathcal P(n)}\ell^{e_\ell}$ ，定义

$$W_J(n):=
\{d\mid n:T_n(d)=J\}
=
\left\{
\prod_{\ell}\ell^{f_\ell}:
\begin{array}{ll}
f_\ell=e_\ell,&\ell\in J,\\
0\le f_\ell<e_\ell,&\ell\notin J
\end{array}
\right\},$$

故

$$\#W_J(n)=\prod_{\ell\notin J}e_\ell.
\tag{1}$$

再定义可见除数集合及其单秩最大重数

$$\mathscr D^{+}(n):=
\{d\mid n:T_n(d)\ne\varnothing\},$$


$$A^{*}(n):=
\max\left\{1,\max_{d\in\mathscr D^{+}(n)}a(d)\right\}.
\tag{2}$$

定理 1（平均窗口去聚合）
当  $x\to\infty$  时，

$$\boxed{
\sum_{3\le n\le x}\omega(n)\log R(n)
=
\sum_{3\le n\le x}\omega(n)\log A^{*}(n)
+O(x\log\log x).
}
\tag{3}$$

特别地，(H2) 等价于

$$\boxed{
\sum_{3\le n\le x}\omega(n)
\log
\max\left\{
1,
\max_{\substack{d\mid n\\
\exists \ell\mid n:\,\nu_\ell(d)=\nu_\ell(n)}}
\#\Pi_\alpha(d)
\right\}
=o\!\left(x(\log\log x)^2\right).
}
\tag{4}$$

证明
对非空  $J\subseteq\mathcal P(n)$ ，所有精确秩素数原子的并为

$$P_J(n)=\coprod_{d\in W_J(n)}\Pi_\alpha(d),
\qquad
\#P_J(n)=\sum_{d\in W_J(n)}a(d).
\tag{5}$$

秩类两两不交，因为素数只有一个首次出现秩。
由素数–阶梯二分，非单元素族只能来自  $P_J(n)$ 。固定一个本质坐标  $\ell$  后，秩提升公式中的满指数方程唯一决定可能的阶梯指数；这对  $\ell=2,5$  及一般素数均成立。因此，固定支撑对至多比相应素数窗口多一个阶梯原子。于是

$$\max_{\varnothing\ne J}\sum_{d\in W_J(n)}a(d)
\le R(n)
\le
1+\max_{\varnothing\ne J}\sum_{d\in W_J(n)}a(d).
\tag{6}$$

由 (1)–(2)，

$$A^{*}(n)\le R(n)
\le
1+A^{*}(n)\max_J\#W_J(n)
\le
1+A^{*}(n)\prod_{\ell^{e_\ell}\parallel n}e_\ell.$$

置

$$h(n):=\sum_{\ell^{e_\ell}\parallel n}\log e_\ell.$$

由于  $A^{*}(n)\ge1$ ，

$$0\le\log R(n)-\log A^{*}(n)\le \log 2+h(n).
\tag{7}$$

另一方面，

$$h(n)
\le
\sum_{\substack{p^j\mid n\\j\ge2}}\log j.$$

故

$$\begin{aligned}
\sum_{n\le x}\omega(n)h(n)
&\le
\sum_{\substack{p^j\le x\\j\ge2}}
\log j
\sum_{m\le x/p^j}\omega(p^jm)\\
&\le
\sum_{\substack{p^j\le x\\j\ge2}}
\log j
\sum_{m\le x/p^j}\bigl(1+\omega(m)\bigr)\\
&\ll
x\log\log x
\sum_p\sum_{j\ge2}\frac{\log j}{p^j}\\
&\ll x\log\log x,
\end{aligned}$$

因为最后的双重级数绝对收敛。再用

$$\sum_{n\le x}\omega(n)\ll x\log\log x$$

对 (7) 求和，即得 (3)，而 (4) 为其直接等价形式。证毕。
算术意义
定理 1 已无条件处理：


一个固定支撑  $J$  中的全部除数秩  $d$ ；


同一支撑汇集的所有精确秩类；


非平方自由指标带来的指数窗口；


全部阶梯原子。


因此唯一未解决的量不是窗口宽度，而是

$$d\longmapsto \#\Pi_\alpha(d)$$

在整数除数图上的可见最大函数 (4)。
一个较强但可直接检验的充分条件是

$$\sum_{d\le x}
\frac{\bigl(\omega(d)+\log\log x\bigr)\log\max\{1,a(d)\}}{d}
=o\!\left((\log\log x)^2\right),
\tag{8}$$

因为

$$\log A^{*}(n)
\le\sum_{d\mid n}\log\max\{1,a(d)\}$$

并可对倍数  $n=dm$  求和。另一方面，(H2) 必然蕴含其对角必要条件

$$\sum_{n\le x}\omega(n)\log\max\{1,a(n)\}
=o\!\left(x(\log\log x)^2\right).
\tag{9}$$

目前甚至 (9) 亦无公开证明。

二、为什么现有算术结果不能推出 (H2)
Stroiński 的 Theorem 7 只给出

$$\sum_{d\le y}a(d)
=
\#\{p:\alpha(p)\le y\}
\ll \frac{y^2}{\log y},$$

并给出明确的上极限常数；它控制累计秩计数，而不控制 (4) 中的除数最大函数。Stroiński, On Dirichlet Products Evaluated at Fibonacci Numbers
这种逻辑缺口是严格的。形式重数序列

$$a_0(d)=
\max\left\{1,\left\lfloor \frac{c\,d}{\log(2d)}\right\rfloor\right\}$$

同时满足

$$\sum_{d\le y}a_0(d)\ll \frac{y^2}{\log y},
\qquad
a_0(d)\ll\frac d{\log d},
\qquad
\sum_{d\le y}a_0(d)\log d\ll y^2,$$

即与现有累计计数、点态乘积约束及对数质量尺度相容；但

$$\sum_{n\le x}\omega(n)\log a_0(n)
\asymp x\log x\log\log x,$$

远大于 (H2) 的尺度。此构造不是 Fibonacci 反例，而是证明现有不等式在逻辑上不足。
Carmichael 与 Bilu–Hanrot–Voutier 给出存在性，不给出  $a(d)$  的上重数分布。Bilu–Hanrot–Voutier Granville 给出具有指定奇偶重数性质的原始素因子，Granville；Hong 给出任意固定线性倍数以上的大原始素因子，Hong；二者均不控制同一精确秩中的素数个数。故这些结果不能补足 (4)。

三、一个与 (H2) 相反的公开算术预测
Bugeaud–Luca–Mignotte–Siksek 证明了

$$\omega(F_n)\ge(\log n)^{\log 2+o(1)}
\quad\text{对几乎所有 }n,$$

并猜想对复合  $n$  有

$$\omega(F_n)\gg\log n.
\tag{BLMS}$$

参见其论文 On Fibonacci numbers with few prime divisors。
命题 2（BLMS 猜想条件下的定量否定）
若 (BLMS) 成立，则

$$\liminf_{x\to\infty}
\frac{1}{x(\log\log x)^2}
\sum_{3\le n\le x}\omega(n)\log R(n)
\ge
\frac6{\pi^2}(1-\log 2)>0.
\tag{10}$$

因而 (H2) 为假。
证明
设  $n$  平方自由， $k=\omega(n)$ 。此时每个非空支撑  $J\subseteq\mathcal P(n)$  对应唯一除数

$$n_J=\prod_{\ell\in J}\ell,$$

且

$$W_J(n)=\{n_J\}.$$

精确秩分拆给出

$$\omega(F_n)
=
\sum_{d\mid n}a(d)
=
\sum_{\varnothing\ne J\subseteq\mathcal P(n)}a(n_J).$$

故由抽屉原理，

$$R(n)\ge
\max_Ja(n_J)
\ge
\frac{\omega(F_n)}{2^k-1}.
\tag{11}$$

假定 (BLMS)。对几乎所有平方自由复合  $n$ ，

$$\omega(F_n)\ge c\log n,
\qquad
k=(1+o(1))\log\log n.$$

这里 Hardy–Ramanujan 型结论只用于  $k=\omega(n)$ ，并未被用作秩窗口估计。由 (11)，

$$\begin{aligned}
\log R(n)
&\ge
\log\log n-k\log2+O(1)\\
&=
(1-\log2+o(1))\log\log n.
\end{aligned}$$

于是

$$\omega(n)\log R(n)
\ge
(1-\log2+o(1))(\log\log n)^2.$$

平方自由整数的密度为  $6/\pi^2$ ，平方自由素数指标的密度为零。对该密度一集合求和即得 (10)。证毕。
因此，现稿的 Conjecture 6.11 不宜继续称为“预期的正常稀疏性”；更准确的名称应为“平均稀疏情形”或“条件性稀疏假设”，并应明确指出它与 (BLMS) 的冲突。

四、非连通部分的正确条件定理
对  $V=\mathcal P(n)$  及非空  $C\subseteq V$ ，仍记

$$n_C=\prod_{\ell\in C}\ell^{\nu_\ell(n)}.$$

对非平凡集合分拆  $\Pi\in\operatorname{Part}(V)$ ，定义跨块面积

$$\Delta(\Pi)
:=
\sum_{\substack{C,D\in\Pi\\C<D}}|C||D|
=
\frac{k^2-\sum_{C\in\Pi}|C|^2}{2}.
\tag{12}$$

定理 3（跨块秩窗口条件下的非连通指数稀疏性）
令  $n=n_j$  且  $k=\omega(n_j)\to\infty$ 。假设

$$\varepsilon_k:=
\max_{\substack{\Pi\in\operatorname{Part}(V)\\|\Pi|\ge2}}
\frac{\displaystyle
\sum_{C\in\Pi}|C|\log R(n_C)}
{\Delta(\Pi)}
\longrightarrow0.
\tag{BW}$$

则

$$\boxed{
\frac{\#(\mathcal M_n\setminus\mathcal M_n^{\rm conn})}
{\#\mathcal M_n^{\rm conn}}
\le
\exp\!\left[
-\left(\frac{\log2}{2}-o(1)\right)k
\right]
=o(1).
}
\tag{13}$$

一个较易核验的充分条件是

$$\max_{\varnothing\ne C\subsetneq V}
\frac{\log R(n_C)}{k-|C|}
\longrightarrow0.
\tag{BW'}$$

特别地，若所有非空真块  $C\subsetneq V$  最终均满足  $R(n_C)=1$ ，则 (13) 成立。
证明
首先改进现稿的私有坐标上界。若一个  $s$ -坐标层的见证覆盖有  $t$  个原子，选取其  $t$  个私有坐标组成  $P$ ，令  $Q$  为余集。固定  $x\in P$  后，素数原子的满支撑为

$$\{x\}\cup U,\qquad U\subseteq Q,$$

共有  $2^{s-t}$  种，每个支撑至多有  $R(m)$  个选择。对于固定  $x$ ，全部阶梯原子中至多一个能在  $x$  坐标达到满指数。因此

$$\#\mathcal M_m
\le
U_s(R(m)),$$

其中

$$U_s(r):=
\sum_{t=1}^{s}
\binom st\bigl(r\,2^{s-t}+1\bigr)^t.
\tag{14}$$

由于  $r\ge1$ ，

$$U_s(r)\le r^sU_s(1).
\tag{15}$$

令

$$b_s=\sum_t\binom st2^{t(s-t)}.$$

当  $t\le3s/4$  时，

$$(2^{s-t}+1)^t
=
2^{t(s-t)}
\left(1+2^{-(s-t)}\right)^t
=
(1+o(1))2^{t(s-t)}$$

一致成立；而  $t>3s/4$  的总贡献相对于中央项为  $2^{-s^2/16+O(s)}$ 。故

$$U_s(1)\sim b_s.$$

调用 Hearne–Wagner 的公开枚举与 split-graph 中心渐近，有  $C_s\sim b_s$ ，从而存在绝对常数  $K$  使

$$U_s(r)\le K r^s C_s
\tag{16}$$

对所有  $s,r\ge1$  成立。Hearne–Wagner，Troyka
由唯一连通块分解，

$$\#(\mathcal M_n\setminus\mathcal M_n^{\rm conn})
=
\sum_{\substack{\Pi\in\operatorname{Part}(V)\\|\Pi|\ge2}}
\prod_{C\in\Pi}M^{\rm conn}(n_C).
\tag{17}$$

应用 (16)，

$$\#(\mathcal M_n\setminus\mathcal M_n^{\rm conn})
\le
\sum_{\Pi\ne\{V\}}
K^{|\Pi|}
\prod_{C\in\Pi}
C_{|C|}R(n_C)^{|C|}.
\tag{18}$$

公开中心渐近给出一致的两侧估计

$$C_s\asymp
(s+1)^{-1/2}2^{s^2/4+s}.
\tag{19}$$

若  $\Pi$  的块大小为  $s_1,\dots,s_r$ ，则由 (12)、(19)，

$$\frac{
K^r\prod_i C_{s_i}R(n_{C_i})^{s_i}}
{C_k}
\ll
K_1^r\sqrt{k}\,
\exp\left\{
-\frac{\log2}{2}\Delta(\Pi)
+\sum_i s_i\log R(n_{C_i})
\right\}.
\tag{20}$$

在 (BW) 下，右端为

$$K_1^r\sqrt{k}\,
\exp\left\{
-\left(\frac{\log2}{2}-o(1)\right)\Delta(\Pi)
\right\}.
\tag{21}$$

若最大块不超过  $k/2$ ，则  $\Delta(\Pi)\ge k^2/4$ ，而全部集合分拆数至多  $k^k$ ，故该部分为  $\exp(-\Omega(k^2))C_k$ 。
若最大块大小为  $k-j>k/2$ ，则

$$\Delta(\Pi)\ge j(k-j).$$

选择其余  $j$  个元素并分拆它们的方法数至多

$$\binom kj B_j\le (ek)^j.$$

将此代入 (21)，对  $1\le j<k/2$  求和，所得总量为

$$\exp\left[
-\left(\frac{\log2}{2}-o(1)\right)k
\right]C_k.$$

最后，现稿已经严格证明

$$M^{\rm conn}(n)\ge(1-o(1))C_k.$$

与 (18) 比较即得 (13)。
若 (BW') 成立，则

$$\begin{aligned}
\sum_{C\in\Pi}|C|\log R(n_C)
&\le
\eta_k\sum_{C\in\Pi}|C|(k-|C|)\\
&=
2\eta_k\Delta(\Pi),
\end{aligned}$$

其中  $\eta_k\to0$ ，故 (BW) 成立。证毕。

五、稿件应作的结论性修改


无条件删除任何“全体非连通最小生成元渐近可忽略”的表述。当前连通下界只能说明连通部分实现全部已知下侧支撑熵。


将定理 1 加入算术接口部分。它严格证明多秩类窗口聚合不是 (H2) 的剩余障碍；唯一剩余量是 (4)。


将 Conjecture 6.11 改称“Mean sparse-window hypothesis”，并加入命题 2。否则稿件会遗漏一个与其方向相反的、直接针对  $\omega(F_n)$  的公开预测。


若需保留非连通可忽略结论，只能采用定理 3，并明确列出 (BW) 或更强的 (BW′)。平均假设 (H2) 本身不能推出 (BW)：前者控制整数平均，后者要求对同一  $n$  的全部真坐标块  $n_C$  作一致控制。


因此，现阶段严谨结论不是“(H2) 已证”或“已否定”，而是：窗口求和困难已被无条件消除；真正开放量已归约为单秩可见除数最大函数；且现有 Fibonacci 素因子数预测提供了反对 (H2) 的定量条件证据。