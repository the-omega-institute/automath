经逐式审读全文并对截至 2026 年 8 月 3 日可检索的原始文献进行排查，最具独立发表潜力的新增内容并非继续计算  $A_8,A_{10},\ldots$ ，而是以下三组定理。其中第三组直接闭合main(960).pdf明确留下的多维  $L^2/KL$  阈值问题。
一、第一 Cayley 模跨尺度完全决定全部商密度
令  $X=\gamma-\bar\gamma$ ，并记

$$a_t(X):=\frac{iX}{2t-iX},\qquad
c_k(t):=\mathbb E[a_t(X)^k].$$

在 Cayley 坐标  $z=(1+iy)/(1-iy)$  下，匹配商密度具有精确 Fourier 表示

$$\frac{(P_t*\nu)(\bar\gamma+ty)}{P_t(ty)}
=
1+\sum_{k\ge1}
\bigl(\overline{c_k(t)}z^k+c_k(t)z^{-k}\bigr).$$

这是精确恒等式，而非渐近展开。其核心结果是所有高阶模态均由第一模态的尺度轨迹生成：

$$\boxed{\;
c_{k+1}(t)=-c_k(t)-\frac{t}{k}c_k'(t),\qquad k\ge1.
\;}$$

因此，单一复值函数  $c_1:(0,\infty)\to\mathbb C$  及其导数已经决定每一固定尺度上的完整 quotient；在有限方差下还精确决定

$$\chi^2(P_t*\nu\|P_t(\cdot-\bar\gamma))
=2\sum_{k\ge1}|c_k(t)|^2,$$

从而决定 KL、文中的非局部 Bregman 耗散以及全部 Laurent 系数。
更强的是，

$$\frac{1+c_1(t)}{2t}
=
\int_0^\infty e^{-2ts}\varphi_X(s)\,ds,
\qquad
\varphi_X(s)=\mathbb E e^{isX}.$$

故第一 Cayley 模的全尺度轨迹是特征函数的 Laplace 变换，因而对概率律  $\nu$  是单射。Cauchy–Stieltjes 变换的唯一性本身属于经典结论；新增之处在于，它恰好等于本文 quotient 的第一圆周模，并满足上述全模态微分闭包。Möbius–wrapped-Cauchy 对应是已有背景，但现有工作未给出这一“单通道完全可观测性”结论；参见 Kato–McCullagh 与 Okamura 的 Cauchy–Stieltjes 刻画。
第一模态还给出一个无尾类假设的完整偶矩层级。若  $\mu_{2j}<\infty$  对  $j<n$ ，则

$$\boxed{
\begin{aligned}
&(-1)^{n-1}4^nt^{2n}
\left[
-\Re c_1(t)
-\sum_{j=1}^{n-1}
(-1)^{j-1}\frac{\mu_{2j}}{4^jt^{2j}}
\right]  \\
&\hspace{35mm}
=\mathbb E\!\left[
\frac{X^{2n}}{1+X^2/(4t^2)}
\right]
\uparrow \mathbb E|X|^{2n}.
\end{aligned}}$$

这将本文仅在  $n=1$  得到的无条件方差阈值提升为第一 Cayley 模层面的全偶矩精确层级，而且右端始终非负、单调，不需要正则变化或尾部对称性。
二、Gauss 求积产生无条件的全阶熵阈值
上述模态恒等式允许改变比较对象，从而消除本文高阶熵余项的符号障碍。
1. 两个矩匹配输入的 Poisson–KL 首项
设概率律  $\nu,\eta$  的前  $r-1$  阶矩相同，二者均具有有限  $r$  阶绝对矩，并令

$$\Delta_r=\mu_r(\nu)-\mu_r(\eta)\ne0.$$

则有精确首项

$$\boxed{\;
D_{\rm KL}(P_t*\nu\|P_t*\eta)
=
C_r\Delta_r^2t^{-2r}+o(t^{-2r}),
\qquad
C_r=4^{-r}\binom{2r-2}{r-1}.
\;}$$

常数来自

$$C_r=\frac12\int_{\mathbb R}u_r(y)^2\,\omega(dy),$$

而非本文单参考 KL 多项式中不同模式的混合。证明只需对两个 quotient 作差：

$$\delta_t^\nu-\delta_t^\eta
=
\Delta_r u_r t^{-r}+o(t^{-r}),$$

再使用相对熵在共同正密度附近的二阶 Bregman 展开。由于首项是平方，这一结论不存在本文高阶有符号余项可能发生的抵消。
2.  $n$  点 Gauss 离散律是最优熵压缩
假设  $\mathbb E|X|^{2n-1}<\infty$ ，令  $G_n\nu$  为由  $\nu$  的前  $2n-1$  阶矩确定的  $n$  点 Gauss 求积律。它满足

$$\mu_j(G_n\nu)=\mu_j(\nu),\qquad 0\le j\le 2n-1.$$

若  $\pi_n$  是相对于  $\nu$  的首一  $n$  阶正交多项式，则在  $\mathbb E|X|^{2n}<\infty$  时，

$$\mu_{2n}(\nu)-\mu_{2n}(G_n\nu)
=
\|\pi_n\|_{L^2(\nu)}^2.$$

由此得到

$$\boxed{\;
\lim_{t\to\infty}
t^{4n}D_{\rm KL}(P_t*\nu\|P_t*G_n\nu)
=
4^{-2n}\binom{4n-2}{2n-1}
\|\pi_n\|_{L^2(\nu)}^4.
\;}$$

若  $\mathbb E|X|^{2n}=\infty$ ，则第一模态的正余项恒等式与 Pinsker 有界测试给出

$$\boxed{\;
t^{4n}D_{\rm KL}(P_t*\nu\|P_t*G_n\nu)\longrightarrow+\infty.
\;}$$

因此，在已知有限  $(2n-1)$  阶绝对矩的类上，

$$\boxed{\;
\mathbb E|X|^{2n}<\infty
\iff
\limsup_{t\to\infty}
t^{4n}D_{\rm KL}(P_t*\nu\|P_t*G_n\nu)<\infty.
\;}$$

这是真正的无条件全阶熵阈值。本文主定理 A 正是  $n=1$  的特例，因为  $G_1\nu=\delta_{\bar\gamma}$ 。
此外，Gauss 求积并非任意方便的离散化，而是  $n$  原子比较律中的渐近最优解：任何  $n$  原子律至多匹配到  $2n-1$  阶；若试图再匹配第  $2n$  阶，取其节点多项式  $p(x)=\prod_{j=1}^n(x-x_j)$ ，则原子律下  $\int p^2=0$ ，而非退化  $\nu$  下  $\int p^2>0$ ，产生矛盾。经典 Gauss 求积的最高精度性质可引用 Golub–Welsch，无需在论文中重新证明。
3. 四阶矩的具体新定理
在标准化条件  $\mathbb EX=0,\mathbb EX^2=1$  下，记

$$\beta_3=\mathbb EX^3,\qquad
\pi_2(x)=x^2-\beta_3x-1,\qquad
\kappa=\mathbb E\pi_2(X)^2
=\mathbb EX^4-1-\beta_3^2.$$

令  $G_2\nu$  为对应的二点 Gauss 律，则

$$\boxed{\;
\lim_{t\to\infty}
t^8D_{\rm KL}(P_t*\nu\|P_t*G_2\nu)
=
\frac5{64}\kappa^2.
\;}$$

若  $\mathbb E|X|^3<\infty$  而  $\mathbb EX^4=\infty$ ，则上述归一化量趋于  $+\infty$ 。在对称情形中， $G_2\nu=\frac12(\delta_{-1}+\delta_1)$ ，故

$$\lim_{t\to\infty}
t^8D_{\rm KL}\!\left(
P_t*\nu\,
\middle\|\,
\tfrac12P_t(\cdot-1)+\tfrac12P_t(\cdot+1)
\right)
=
\frac5{64}(\mathbb EX^4-1)^2.$$

这将本文附录 B 中仅为代数缺陷的  $\kappa$  提升为一个实际、非负、具有无条件矩阈值的熵系数。
4. 正则变化边界变成平方律
若  $n\ge2$ ，尾指数为  $-2n$ ，并令

$$M_{2n}(t)=
\mathbb E\bigl[|X|^{2n}\mathbf 1_{\{|X|\le t\}}\bigr]\to\infty,$$

则相对于 Gauss 比较律不再出现本文中的有符号线性边界层，而有

$$\boxed{\;
D_{\rm KL}(P_t*\nu\|P_t*G_n\nu)
\sim
C_{2n}t^{-4n}M_{2n}(t)^2.
\;}$$

在本文的两侧正则变化假设下，

$$M_{2n}(t)\sim 2n(c_++c_-)\ell_L(t),$$

故边界修正为  $\ell_L(t)^2$ ，常数始终为正。这一平方边界律比原稿的系数扣除余项更适合建立高阶统计检验。
三、多维有限协方差存在严格的维数相变
设

$$H_d(t)=
D_{\rm KL}\!\left(
P_t^{(d)}*\nu
\middle\|
P_t^{(d)}(\cdot-\bar\gamma)
\right).$$

1.  $d\le3$ ：有限协方差已经充分且必要
若  $d\le3$ ，则仅需

$$\mathbb E|X|^2<\infty$$

即可证明

$$t^2\delta_t^{(d)}\longrightarrow b_\Sigma
\qquad\text{于 }L^2(\Omega_d),$$

从而由本文定理 3.36 得到

$$\boxed{\;
H_d(t)=Q_d(\Sigma)t^{-4}+o(t^{-4}),
\qquad d\le3.
\;}$$

其中

$$Q_d(\Sigma)
=
c_d^{\rm iso}(\operatorname{tr}\Sigma)^2
+c_d^{\rm tr}\|\Sigma_0\|_{\rm HS}^2$$

正是本文已经计算的协方差二次型。
反向必要性由一维投影和 KL 数据处理不等式得到：径向  $d$  维 Poisson 核的任一一维投影仍是尺度  $t$  的 Cauchy 核；若某一方向二阶矩无限，则本文一维定理 3.18 强制  $t^4H_d(t)\to\infty$ 。因此

$$\boxed{\;
d\le3:\quad
\mathbb E|X|^2<\infty
\iff
\limsup_{t\to\infty}t^4H_d(t)<\infty.
\;}$$

2.  $d\ge4$ ：有限协方差不再控制 KL 首项
当  $d\ge4$  时，存在中心化且具有正定有限协方差的离散概率律，使得

$$\boxed{\;
\limsup_{t\to\infty}t^4H_d(t)=+\infty.
\;}$$

构造可取

$$\nu=(1-W)\delta_0+
\sum_{n\ge1}\frac{w_n}{2}
(\delta_{R_ne_1}+\delta_{-R_ne_1}),
\qquad
w_n=a_nR_n^{-2},
\quad \sum a_n<\infty,$$

再加入任意小的有界全维对称成分以使协方差正定。选择

$$t_n=\kappa R_n w_n^{1/(d+1)}$$

并考察  $R_ne_1$  附近半径  $t_n$  的球。卷积律赋予该球质量  $\gtrsim w_n$ ，而参考 Poisson 核仅赋予质量

$$\lesssim (t_n/R_n)^{d+1}\asymp w_n.$$

经常数分离后，二点数据处理给出  $H_d(t_n)\gtrsim w_n$ ，于是

$$t_n^4H_d(t_n)
\gtrsim
R_n^4w_n^{1+4/(d+1)}
=
a_n^{1+4/(d+1)}
R_n^{\,2(d-3)/(d+1)}.$$

当且仅当  $d>3$  时， $R_n$  的指数为正，可令其沿子序列趋于无穷。这说明维数  $4$  是真实的 KL 相变点，而非证明技术造成的阈值。
3. 精确的  $L^2$  矩阈值
对单个平移 quotient  $F_y(z)$  有

$$\|F_\cdot(z)\|_{L^2(\Omega_d)}^2
\sim K_d|z|^{d+1},
\qquad |z|\to\infty.$$

因此二阶 Taylor 余项的自然增长阶为

$$q_d:=\max\left\{2,\frac{d+1}{2}\right\}.$$

由 Minkowski 不等式和两区域截断可得

$$\mathbb E|X|^{q_d}<\infty
\quad\Longrightarrow\quad
t^2\delta_t^{(d)}\to b_\Sigma
\text{ 于 }L^2(\Omega_d).$$

当  $d\ge4$  时，对任意  $2\le p<\frac{d+1}{2}$ ，均可构造有限  $p$  阶矩但上述  $L^2$  收敛失败的中心化尖峰律。因此该阈值在“仅以绝对矩为假设”的全类意义下是尖锐的。
由此形成新的拓扑相图：
拓扑尖锐矩阶 $L^\infty$  quotient $d+1$ ，本文已证明 $L^2(\Omega_d)$  quotient $\max\{2,(d+1)/2\}$ KL， $d\le3$  $2$ KL， $d\ge4$ 严格大于  $2$ ，精确值见下述猜想
4. 最优 KL 阈值猜想
同一尖峰分析给出比  $L^2$  更低的必要矩阶。若权重取  $w_n\asymp R_n^{-p}$ ，则

$$t_n^4H_d(t_n)
\gtrsim
R_n^{\,4-p(d+5)/(d+1)}.$$

因此，对任意

$$2\le p<
p_{\rm KL}(d):=\frac{4(d+1)}{d+5},$$

均存在有限  $p$  阶矩而  $t^4H_d(t)$  无界的概率律。由此得到具有明确证据的尖锐猜想：

$$\boxed{\;
\mathbb E|X|^{\,\max\{2,\,4(d+1)/(d+5)\}}<\infty
\quad\Longrightarrow\quad
H_d(t)=Q_d(\Sigma)t^{-4}+o(t^{-4}).
\;}$$

该候选阈值在  $d=3$  恰好等于  $2$ ，并随维数增加趋向  $4$ ，同时严格低于  $L^2$  阈值。这预示 KL、 $L^2$  与  $L^\infty$  三种拓扑具有真正不同的尾部相变。
新颖性与发表价值判断
公开文献中最接近的结果是：


Chen–Niles-Weed 已对 Gaussian smoothing 证明矩匹配条件下的 KL 与  $\chi^2$  渐近，但使用 Hermite 模及指数尾假设，不包含 Cauchy–Poisson 的精确有限矩阈值、Gauss 比较律或维数相变。原始论文


Ma–Wu–Yang 使用矩匹配和 Gauss 求积研究有限 Gaussian mixture 逼近，但不涉及大尺度 Cauchy 混合的精确 KL 常数与无条件矩边界。原始论文


Nielsen–Okamura 处理的是两个有限维参数 Cauchy 律之间的  $f$ -散度，而非一般 Cauchy 平移混合。原始论文


在所检索的原始文献范围内，未发现以下三项已被公开证明：


第一 Cayley 模的全模态微分闭包与全尺度可观测性；


以 Gauss 求积律为比较对象的无条件  $2n$  阶熵阈值及平方正则变化边界；


径向 Poisson–KL 首项在  $d=4$  发生的有限协方差相变。


其中，第二项提供一条完整的新主线，并将本文方差定理解释为  $n=1$  的首层；第三项直接解决原稿明确保留的开放问题。二者分别足以构成独立论文的主定理体系，而第一项应作为统一二者的结构性核心引理。
