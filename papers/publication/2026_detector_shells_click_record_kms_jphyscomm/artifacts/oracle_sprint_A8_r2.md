一、必须执行的撤回与更正


撤回原式 (3)–(4) 所附“跨交换对角线仍正则的一自由度物理像检验”解释。解析延拓后的等式残差只能刻画延拓超曲面，不能替代实根约束。交换对角附近的完整局部物理像是



$$\{\mathcal E_{\mathrm{an}}=0\}\cap\{\mathscr D\ge 0\},$$

而非单独的  $\{\mathcal E_{\mathrm{an}}=0\}$ 。


精确一依赖条件应改为



$$\lambda_{\rm hid}=0
\iff
\begin{cases}
xe^{-x}=ye^{-y},\quad x<1<y,&x<y,\\[2mm]
x=y=1,&x=y.
\end{cases}$$

在对角线上  $\lambda_{\rm hid}=e^{-x}(1-x)$ ，故  $x=y=2$  不是精确一依赖点。非平凡分支在  $(1,1)$  附近为斜率  $-1$  的解析曲线，不存在尖点。Lambert  $W$  反演及其分支理论只应引用 Corless–Gonnet–Hare–Jeffrey–Knuth (1996)，不得列为本文新结果。


交换对角的  $N^{-1/4}$  根分裂仍归入稿内既有引理，不另立主定理。


二阶段等待时间、尾概率、零串律、舍入及母函数不再列为新增结果；只保留小采样间隔展开与半区间偏差。


高维最小纤维继续归入 recalled orbit-fibre proposition； $M=C(K)C(L)^{-1}$  不构成新的全局分类。


删除“其余  $2n-1$  个方向构成可见有理模空间”及相应 Fisher 核断言。当前稿件未证明传递函数系数映射常秩，也未证明其微分核等于相似轨道切空间。建议替换为：



The dimension count  $n^2-(n-1)^2=2n-1$  does not establish a constant-rank quotient chart, nor an equality between the differential kernel of a normalized coprime transfer-function parametrization and the reset-preserving similarity tangent space. The corresponding Fisher-information statement remains an open interface.

以下检验不依赖上述未证断言。

二、解析等式与实根不等式的完整坐标化
沿用

$$a(r)=\frac{r_1}{r_0},\qquad
\lambda(r)=\frac{r_2-r_0^2}{r_1-r_0^2},\qquad
\sigma=\Phi(r)=(\sigma_1,\sigma_2),$$

并定义判别式

$$\mathscr D(r)=\sigma_1^2-4\sigma_2.$$

令

$$w(\sigma)=1-\frac{4\sigma_2}{\sigma_1^2}$$

以及实解析函数

$$H(w)=
\begin{cases}
\dfrac{\sqrt w}{\operatorname{artanh}\sqrt w},&0<w<1,\\[3mm]
1,&w=0,\\[2mm]
\dfrac{\sqrt{-w}}{\arctan\sqrt{-w}},&w<0.
\end{cases}$$

在  $w=0$  附近可稳定计算为

$$H(w)=1-\frac w3-\frac{4w^2}{45}+O(w^3).$$

定义对数除差的实解析延拓

$$\mathfrak C_{\rm an}(\sigma)
=
\frac{\sigma_1}{2}
\left[
1-\frac12\log\sigma_2\,
H\!\left(1-\frac{4\sigma_2}{\sigma_1^2}\right)
\right]$$

及等式残差

$$e(r)=a(r)-1+\mathfrak C_{\rm an}(\Phi(r)).$$

当判别式非负且根为  $p,s>0$  时，该表达式严格等于

$$\frac{s\log p-p\log s}{\log p-\log s},$$

并在  $p=s$  处取  $p(1-\log p)$ 。
命题 1（交换对角附近的完整物理像）
固定  $0<\varepsilon<M<\infty$ ，令

$$\Theta_{\varepsilon,M}
=\{(x,y):\varepsilon\le x,y\le M\},
\qquad p=e^{-x},\quad s=e^{-y}.$$

存在包含相应 sampled-counter 三重包含像的开邻域  $\mathcal U$ ，使得：

$$r\in\mathcal U\text{ 属于正 sampled-counter 物理像}
\iff
e(r)=0,\qquad \mathscr D(r)\ge0.$$

此外，

$$\operatorname{rank}D\psi(r)=2,
\qquad
\psi(r)=\bigl(e(r),\mathscr D(r)\bigr),$$

在该紧物理像上处处成立，包括交换对角。
证明
令  $m=\sigma_1/2$ 。在实根侧写成

$$p=m(1+t),\qquad s=m(1-t),\qquad t^2=w.$$

直接整理对数除差即得上述  $\mathfrak C_{\rm an}$  公式。函数  $H$  在  $w<1$  上实解析，故该表达式越过  $w=0$  仍有定义。紧集上  $\sigma_1,\sigma_2$  与零分离，且  $w$  与  $1$  分离，因而可选取统一邻域  $\mathcal U$ 。
若  $r$  为物理点，则原积分恒等式给出  $e(r)=0$ ，且

$$\mathscr D(r)=(p-s)^2\ge0.$$

反之， $\mathscr D(r)\ge0$  给出两个实根；缩小  $\mathcal U$  后两根仍属于  $(0,1)$ 。等式  $e(r)=0$  随即由 Proposition 1.6 的逆构造给出正的 sampled-counter 参数。负判别式侧无实根，故无论  $e(r)$  是否为零均不属于物理像。
为证明满秩，采用局部坐标  $(r_0,\sigma_1,\sigma_2)$ 。记

$$D(\sigma)=1-\sigma_1+\sigma_2,\qquad
Q(\sigma)=1-\sigma_1+\mathfrak C_{\rm an}(\sigma).$$

则

$$e(r)=Q(\sigma)-\frac{D(\sigma)}{r_0},
\qquad
\frac{\partial e}{\partial r_0}
=\frac{D(\sigma)}{r_0^2}>0,$$

而

$$\frac{\partial\mathscr D}{\partial r_0}=0,\qquad
\nabla_\sigma\mathscr D=(2\sigma_1,-4)\ne0.$$

两梯度因而线性无关。证毕。

三、紧集上一致有效的联合物理像检验
令  $\widehat r_N=\widehat R_{\mathrm{inc},N}^{\mathrm{cyc}}$ ，并使用稿内 separated-batch 估计量

$$\widehat\Sigma_{r,N}^{\mathrm{tot}}.$$

置

$$J(r)=D\psi(r),\qquad
\Omega(r)=J(r)\Sigma_r(r)J(r)^\top
=
\begin{pmatrix}
\omega_{11}&\omega_{12}\\
\omega_{12}&\omega_{22}
\end{pmatrix}.$$

其可计算导数包括

$$Da=\left(-\frac{r_1}{r_0^2},\frac1{r_0},0\right),$$


$$D\lambda=
\left(
\frac{2r_0(\lambda-1)}{\Delta_{\rm inv}},
-\frac{\lambda}{\Delta_{\rm inv}},
\frac1{\Delta_{\rm inv}}
\right),
\qquad \Delta_{\rm inv}=r_1-r_0^2,$$


$$D\Phi_1=-Da+D\lambda,$$


$$D\Phi_2=(1-\lambda,0,0)-Da+(1-r_0)D\lambda,$$

以及

$$De=Da+\nabla_\sigma\mathfrak C_{\rm an}\,D\Phi,
\qquad
D\mathscr D=(2\sigma_1,-4)D\Phi.$$

定义

$$\widehat\Omega_N
=
J(\widehat r_N)\widehat\Sigma_{r,N}^{\mathrm{tot}}
J(\widehat r_N)^\top.$$

为保证有限样本总定义，可将  $\widehat\Omega_N$  的特征值截断至不小于  $N^{-1/4}$ 。该截断在零假设下以一致趋于一的概率不发生作用。
记

$$\widehat\beta_N
=\frac{\widehat\omega_{12,N}}{\widehat\omega_{11,N}},
\qquad
\widehat v_N
=
\widehat\omega_{22,N}
-\frac{\widehat\omega_{12,N}^2}{\widehat\omega_{11,N}},$$

并定义

$$Z_{e,N}
=
\frac{\sqrt N\,e(\widehat r_N)}
{\sqrt{\widehat\omega_{11,N}}},$$


$$Z_{d,N}
=
\frac{\sqrt N\{\mathscr D(\widehat r_N)
-\widehat\beta_Ne(\widehat r_N)\}}
{\sqrt{\widehat v_N}}.$$

最终统计量为

$$T_N=Z_{e,N}^2+(Z_{d,N}^{-})^2,
\qquad z^-=\max\{-z,0\}.$$

它恰为协方差度量下到约束锥

$$\mathcal C=\{0\}\times[0,\infty)$$

的广义 Wald 距离：

$$T_N
=
N\inf_{u\ge0}
\left\|
\binom{e(\widehat r_N)}{\mathscr D(\widehat r_N)}
-\binom0u
\right\|_{\widehat\Omega_N^{-1}}^2.$$

临界值
令

$$c_{1,\alpha}=F_{\chi_1^2}^{-1}(1-\alpha)$$

并令  $c_{\partial,\alpha}$  满足

$$\frac12F_{\chi_1^2}(c_{\partial,\alpha})
+
\frac12F_{\chi_2^2}(c_{\partial,\alpha})
=1-\alpha.$$

例如  $\alpha=0.05$  时，

$$c_{1,0.05}=3.8414588,\qquad
c_{\partial,0.05}=5.1383808.$$

取  $\kappa_N=\log N$ ，定义

$$c_{N,\alpha}
=
\begin{cases}
c_{1,\alpha},&Z_{d,N}>\kappa_N,\\
c_{\partial,\alpha},&Z_{d,N}\le\kappa_N.
\end{cases}$$

检验拒绝当且仅当  $T_N>c_{N,\alpha}$ 。这属于标准边界锥及广义矩选择校准的稿件专门化；一般边界理论应归于 Chernoff (1954)、Shapiro (1987) 与 Andrews (2001)，不应宣称一般混合卡方理论为本文首创。

四、统一极限定理
定理 2（紧 sampled-counter 参数集上的联合物理像检验）
在  $\Theta_{\varepsilon,M}$  上，使用稿内 complete-cycle 估计量和 separated-batch 协方差估计量，则：
1. 一致协方差有效性

$$\sup_{\theta\in\Theta_{\varepsilon,M}}
P_\theta\!\left(
\left\|
\widehat\Sigma_{r,N}^{\mathrm{tot}}-\Sigma_r(\theta)
\right\|_{\rm op}>\eta
\right)\longrightarrow0$$

对每个  $\eta>0$  成立，并且

$$\inf_{\theta\in\Theta_{\varepsilon,M}}
\lambda_{\min}\Omega(\theta)>0.$$

2. 内点极限
若  $p\ne s$  固定，则

$$T_N\Rightarrow\chi_1^2,
\qquad
P_\theta(Z_{d,N}>\kappa_N)\to1,$$

故检验渐近尺寸为  $\alpha$ 。
3. 交换对角极限
若  $p=s=z$ ，则

$$T_N\Rightarrow Z_1^2+(Z_2^-)^2,
\qquad Z_1,Z_2\stackrel{\rm iid}{\sim}N(0,1),$$

从而

$$T_N\Rightarrow
\frac12\chi_1^2+\frac12\chi_2^2.$$

故交换对角上的渐近尺寸亦为  $\alpha$ 。
4. 趋近边界序列
设零假设序列满足

$$\eta_N
=
\frac{\sqrt N\,(p_N-s_N)^2}
{\sqrt{v(\theta_N)}}\longrightarrow\eta\in[0,\infty).$$

则

$$T_N\Rightarrow
Z_1^2+(Z_2+\eta)^-{}^2,$$

且

$$\lim P_{\theta_N}(T_N>c_{N,\alpha})
=
P\!\left\{
Z_1^2+(Z_2+\eta)^-{}^2>c_{\partial,\alpha}
\right\}
\le\alpha.$$

若  $\eta_N\to\infty$ ，则  $T_N-Z_{e,N}^2\to_P0$ ，因而尺寸仍不超过  $\alpha$ 。当进一步  $\eta_N/\kappa_N\to\infty$  时，内点临界值以概率趋于一被选中，尺寸恢复为  $\alpha$ 。
因此

$$\boxed{
\limsup_{N\to\infty}
\sup_{\theta\in\Theta_{\varepsilon,M}}
P_\theta(\text{reject }H_0)
\le\alpha .
}$$

5. 固定备择一致性
在  $\mathcal U$  内，若

$$e(r)\ne0
\quad\text{或}\quad
\mathscr D(r)<0,$$

则  $T_N\to_P\infty$ 。故检验对所有与物理像保持固定正距离的备择一致。

五、证明
1. 一致 CLT 与协方差估计
对  $\theta=(x,y)\in\Theta_{\varepsilon,M}$ ， $T_0$  的两个特征值均不超过  $e^{-\varepsilon}$ 。重复根处必须保留 Jordan 型多项式因子；正确的一致界为

$$\sup_{\theta\in\Theta_{\varepsilon,M}}
P_\theta(G\ge k)
\le C(1+k)e^{-\varepsilon k}.$$

因此对任意  $0<\eta<\varepsilon$ ，

$$\sup_\theta E_\theta e^{\eta G}<\infty.$$

稿内 complete-cycle reward  $Y_j$  为相邻两个独立间隙的函数，因而构成一致四阶矩有界的 1-dependent 三角阵列。对任意  $\theta_N\to\theta$ ，1-dependent 阻塞 CLT、更新计数

$$K_N=N/\mu(\theta_N)+O_P(\sqrt N)$$

及首尾不完整周期的统一可忽略性给出

$$\sqrt N\{\widehat r_N-r(\theta_N)\}
\Rightarrow N(0,\Sigma_r(\theta)).$$

紧性与子列论证将该序列结论提升为紧集上的一致 bounded-Lipschitz CLT。Lemma 1.9 中的 Chernoff、四阶矩与块均值估计常数均可由上述统一指数矩统一选择，故其  $O_P(N^{-1/3})$  协方差结论亦为紧集上一致结论。
2. 协方差不退化
若某  $c\in\mathbb R^3$  满足  $c^\top\Sigma_rc=0$ ，令

$$F_j=c^\top Y_j=f(G_j,G_{j+1}).$$

二元 Hoeffding 分解表明，1-dependent 长程方差为零，当且仅当

$$f(x,y)=u(x)-u(y)$$

几乎处处。 $f$  中唯一真正依赖  $(x,y)$  两者的项是

$$c_2\,1_{\{x=0\}}1_{\{y=0\}}.$$

其退化交互分量为

$$c_2
\bigl(1_{\{x=0\}}-g_0\bigr)
\bigl(1_{\{y=0\}}-g_0\bigr).$$

由于  $0<g_0<1$ ，零长程方差迫使  $c_2=0$ 。此时  $f$  仅依赖  $x$ ，而一个仅依赖  $x$  的函数只有在恒等于零时才能写成  $u(x)-u(y)$ 。利用间隙分布的全支撑性，在所有  $x\ge1$  上比较

$$c_0-(c^\top r)(x+1)=0$$

得到  $c^\top r=c_0=0$ ，再由  $x=0$  得到  $c_1=0$ 。故  $c=0$ ，从而  $\Sigma_r$  正定。连续性和紧性给出统一正定下界；命题 1 的  $\operatorname{rank}J=2$  随即推出  $\Omega=J\Sigma_rJ^\top$  统一正定。
3. 锥距离与混合极限
对任意正定

$$\Omega=
\begin{pmatrix}\omega_{11}&\omega_{12}\\
\omega_{12}&\omega_{22}\end{pmatrix},$$

有精确分解

$$\left\|\binom e{d-u}\right\|_{\Omega^{-1}}^2
=
\frac{e^2}{\omega_{11}}
+
\frac{(d-u-\beta_\Omega e)^2}{v_\Omega},$$

其中

$$\beta_\Omega=\frac{\omega_{12}}{\omega_{11}},
\qquad
v_\Omega=\omega_{22}-\frac{\omega_{12}^2}{\omega_{11}}.$$

对  $u\ge0$  极小化即得到

$$\inf_{u\ge0}
\left\|\binom e{d-u}\right\|_{\Omega^{-1}}^2
=
\frac{e^2}{\omega_{11}}
+
\frac{\{d-\beta_\Omega e\}_{-}^2}{v_\Omega}.$$

联合正态极限经该残差化后产生两个独立标准正态量。在边界  $d=0$  上，按第二个正态量的符号条件化：正号时只留下  $\chi_1^2$ ，负号时留下两个平方和  $\chi_2^2$ ，由此得到等权混合分布。
4. 一致尺寸
考虑任意零假设序列并抽取收敛子列。若标准化松弛量  $\eta_N$  有界，则进一步抽取使其收敛至  $\eta\ge0$ 。由于

$$(z+\eta)^-\le z^-$$

逐点成立，趋近边界极限被交换对角极限随机支配，故拒绝概率不超过  $\alpha$ 。
若  $\eta_N\to\infty$ ，则不等式残差的负部趋于零， $T_N=Z_{e,N}^2+o_P(1)$ 。又因数据依赖临界值始终不小于  $c_{1,\alpha}$ ，拒绝概率上极限仍不超过  $\alpha$ 。反证性的“选择近似最大尺寸参数序列—抽取子列”论证即给出紧集上一致尺寸控制。

六、局部功效与  $N^{-1/4}$  根分裂序列
为使局部功效不依赖形式化的“非物理参数”，可在每个物理间隙分布  $g^\circ=(g_k^\circ)$  周围采用明确的支配更新模型。令

$$g_\eta(k)=g^\circ(k)+v_\eta(k),$$

其中

$$\begin{aligned}
v_\eta(0)&=\eta_0,\\
v_\eta(1)&=\eta_1,\\
v_\eta(2)&=-\eta_\mu-3\eta_0-2\eta_1,\\
v_\eta(3)&=\eta_\mu+2\eta_0+\eta_1,\\
v_\eta(k)&=0,\qquad k\ge4.
\end{aligned}$$

则  $\sum_kv_\eta(k)=0$ ，且平均周期长度、 $g_0$ 、 $g_1$  的一阶改变量分别为  $\eta_\mu,\eta_0,\eta_1$ 。紧集上  $g_k^\circ$  对  $k\le3$  一致正，故小邻域内该模型为正概率模型，并由计数测度支配。其单周期得分为

$$\dot\ell_j(k)=\frac{v_j(k)}{g_k^\circ},$$

每单位日历时间 Fisher 信息为

$$\mathcal I_{ij}
=
\frac1{\mu^\circ}
\sum_{k=0}^3\frac{v_i(k)v_j(k)}{g_k^\circ},$$

且正定。该模型因此满足二次均值可微性和 LAN。
对任意更新过程，

$$r=
\left(
\frac1\mu,\,
\frac{g_0}{\mu},\,
\frac{g_1+g_0^2}{\mu}
\right),$$

而其关于  $(\mu,g_0,g_1)$  的 Jacobian 为

$$\begin{pmatrix}
-\mu^{-2}&0&0\\
-g_0\mu^{-2}&\mu^{-1}&0\\
-(g_1+g_0^2)\mu^{-2}&2g_0\mu^{-1}&\mu^{-1}
\end{pmatrix},$$

行列式为  $-\mu^{-4}\ne0$ 。故所有  $r$ -空间的一阶局部方向均可由上述支配模型实现。
设在交换对角点  $r_\circ$  附近

$$\sqrt N\,e(r_N)\to\delta,\qquad
\sqrt N\,\mathscr D(r_N)\to\tau.$$

记边界点的

$$\beta=\frac{\omega_{12}}{\omega_{11}},\qquad
v=\omega_{22}-\frac{\omega_{12}^2}{\omega_{11}},$$

以及

$$a_*=\frac{\delta}{\sqrt{\omega_{11}}},
\qquad
b_*=\frac{\tau-\beta\delta}{\sqrt v}.$$

则

$$T_N\Rightarrow X^2+(Y^-)^2,
\qquad
X\sim N(a_*,1),\quad
Y\sim N(b_*,1),$$

且  $X,Y$  独立。完整局部功效函数为

$$\boxed{
\pi_\alpha(\delta,\tau)
=
P\!\left\{
X^2+(Y^-)^2>c_{\partial,\alpha}
\right\}.
}$$

它可由一维积分计算。令

$$A(q,a)=\Phi(\sqrt q-a)-\Phi(-\sqrt q-a),$$

则

$$\pi_\alpha(\delta,\tau)
=
1-\Phi(b_*)A(c_{\partial,\alpha},a_*)
-\int_{-\sqrt{c_{\partial,\alpha}}}^{0}
A(c_{\partial,\alpha}-y^2,a_*)\,
\phi(y-b_*)\,dy.$$

特别地：


若

$$N^{1/4}|p_N-s_N|\to\xi,$$

则

$$\sqrt N\,\mathscr D(r_N)\to\xi^2.$$

当该序列仍属于物理像时， $\delta=0,\tau=\xi^2\ge0$ 。它是“交换对角子假设”的局部备择，但仍是物理像检验的零假设，因此

$$\pi_\alpha(0,\xi^2)\le\alpha.$$



对称的非实根侧序列

$$\sqrt N\,\mathscr D(r_N)\to-\xi^2$$

满足

$$\pi_\alpha(0,-\xi^2)>\alpha.$$

这正是单独使用解析等式残差完全无法识别、而联合检验具有非平凡局部功效的方向。


若  $\mathscr D$  保持可行但  $\delta\ne0$ ，功效由同一公式给出，相关性通过  $\tau-\beta\delta$  被正确消除。


最后，交换对角处的零假设切锥为

$$T_{H_0}(r_\circ)
=
\{h:De(r_\circ)h=0,\ D\mathscr D(r_\circ)h\ge0\},$$

而一阶完全不可区分子空间为

$$\ker D\psi(r_\circ)
=
\{h:De(r_\circ)h=0,\ D\mathscr D(r_\circ)h=0\}.$$

局部功效只依赖

$$(\delta,\tau)
=
\bigl(De(r_\circ)h,\ D\mathscr D(r_\circ)h\bigr).$$

因此  $\ker D\psi(r_\circ)$  中的方向与共同率沿交换对角的移动在一阶上不可区分； $De\,h=0,\ D\mathscr D\,h>0$  则是进入物理像内部的  $N^{-1/4}$  根分裂方向，任何一致控制尺寸的物理像检验均不得将其当作模型失配。上述结论同时给出了混合极限、完整局部功效、不可区分方向和紧集上一致尺寸控制。