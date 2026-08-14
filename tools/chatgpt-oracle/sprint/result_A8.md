以下结论均建立在  的 Assumption 1.1 上。论文已经陈述的 Theorems A–E、商逆公式、串联系统 Prony 可识别性以及局部  $(n-1)^2$  维相似轨道不再复述。此前关于商覆盖、Artin 代入失效、调和正规化及固定标签反演的结论亦已排除。
一、三重包含坐标的精确物理像：一个此前缺失的余维一方程
令  $r=(r_0,r_1,r_2)$  为论文 Theorem B 的三个可见包含概率，并定义

$$a(r)=\frac{r_1}{r_0},\qquad
\lambda(r)=\frac{r_2-r_0^2}{r_1-r_0^2},$$


$$\sigma_1(r)=1-a(r)+\lambda(r),\qquad
\sigma_2(r)=r_0\{1-\lambda(r)\}-a(r)+\lambda(r).$$

设  $p,s$  为

$$z^2-\sigma_1(r)z+\sigma_2(r)=0$$

的两个根。定义对称对数除差

$$\mathfrak C(p,s)=
\begin{cases}
\dfrac{s\log p-p\log s}{\log p-\log s},&p\neq s,\\[1.2ex]
p(1-\log p),&p=s.
\end{cases}$$

定理 1（精确物理像判别）
在  $r_0>0$ 、 $r_1-r_0^2\neq0$  且  $p,s\in(0,1)$  的自然逆域内， $r$  来源于 Assumption 1.1 的某一组正参数  $(\Gamma,\kappa_r,\Delta\tau)$ ，当且仅当

$$\boxed{\;
\mathcal E(r):=
\frac{r_1}{r_0}-1+\mathfrak C(p,s)=0.
\;}
\tag{1}$$

因此，物理 sampled-counter 子族在一般三维包含坐标空间中不是开集，而是一张精确的余维一解析曲面。
证明
置  $x=\Gamma\Delta\tau$ 、 $y=\kappa_r\Delta\tau$ ，故  $p=e^{-x}$ 、 $s=e^{-y}$ 。积分项满足

$$b=\frac{y(p-s)}{y-x},$$

从而

$$s+b=\frac{yp-xs}{y-x}
     =\frac{s\log p-p\log s}{\log p-\log s}
     =\mathfrak C(p,s).$$

由于  $a=1-s-b$ ，立即得到  $\mathcal E(r)=0$ 。
反之，若 (1) 成立，令

$$b=\mathfrak C(p,s)-s,\qquad a=1-\mathfrak C(p,s).$$

则  $b=y(p-s)/(y-x)$ 。由  $\sigma_1=p+s$  得

$$\lambda=p+s+a-1=p-b.$$

再由  $\sigma_2=ps$  得

$$r_0
 =\frac{ps+a-\lambda}{1-\lambda}
 =\frac{(1-p)(1-s)}{1-p+b},$$

这正是论文中的平稳点击率  $\rho$ 。于是  $r_1=r_0a$ ，且由  $\lambda$  的定义恢复  $r_2$ 。故整个三重坐标恰由该 sampled-counter 参数产生。证毕。
推论 1.1（对角线上的正则模型诊断）
虽然单根  $p,s$  在  $p=s$  处不可微，但  $\mathfrak C$  是对称解析函数。令

$$p=m+d,\qquad s=m-d,$$

则

$$\mathfrak C(m+d,m-d)
=
m(1-\log m)
+
\frac{d^2}{m}
\left(\frac12+\frac13\log m\right)
+O(d^4).
\tag{2}$$

由于  $m=\sigma_1/2$  且  $d^2=\sigma_1^2/4-\sigma_2$ ， $\mathcal E(r)$  在交换对角线上仍为通常可微函数。故 Theorem C 立即给出

$$\sqrt N\,\mathcal E(\widehat r_N^{\rm cyc})
\Longrightarrow
N(0,\nu_{\mathcal E}^2),
\qquad
\nu_{\mathcal E}^2
=
\nabla\mathcal E(r)^\top
\Sigma_r
\nabla\mathcal E(r).
\tag{3}$$

若  $\nu_{\mathcal E}^2>0$ ，则

$$\frac{N\,\mathcal E(\widehat r_N^{\rm cyc})^2}
     {\widehat\nu_{\mathcal E,N}^{\,2}}
\Longrightarrow \chi_1^2.
\tag{4}$$

这给出一个跨越交换对角线仍然正则的、单自由度的物理像失配检验。其逻辑含义仅是检验三重包含坐标是否落在 sampled-counter 像上；不拒绝不能证明完整时间序列模型正确。
一般 DMAP(2) 规范形与矩匹配文献处理更宽的表示类，但未给出上述 sampled-clock 对数除差像方程；参见 Mészáros–Telek 的 DMAP(2) 规范表示。Zamparo 的工作建立一般平稳更新二元序列及其极限定理，也未包含该物理像约束，Zamparo 2022。

二、隐藏模的尖锐谱界与完整相关相图
定理 2（割线谱公式）
令

$$f(t)=te^{-t},\qquad x=\Gamma\Delta\tau,\qquad y=\kappa_r\Delta\tau.$$

则论文中的非平凡隐藏特征值具有精确表示

$$\boxed{\;
\lambda_{\rm hid}
=
\frac{f(y)-f(x)}{y-x},
\;}
\tag{5}$$

在  $x=y$  时按连续延拓解释为

$$\lambda_{\rm hid}=f'(x)=e^{-x}(1-x).
\tag{6}$$

由此得到尖锐全局谱界

$$\boxed{\;
-e^{-2}\leq \lambda_{\rm hid}<1.
\;}
\tag{7}$$

下界仅在  $x=y=2$  处达到；上确界  $1$  仅在  $x,y\downarrow0$  时逼近。
证明
由

$$b=\frac{y(e^{-x}-e^{-y})}{y-x}$$

直接得到

$$e^{-x}-b
=
\frac{ye^{-y}-xe^{-x}}{y-x}.$$

这即为 (5)。由中值定理， $\lambda_{\rm hid}=f'(\xi)$ ，其中  $\xi$  位于  $x,y$  之间。函数

$$f'(t)=e^{-t}(1-t)$$

在  $t=2$  取得唯一最小值  $-e^{-2}$ ，并在  $t\downarrow0$  时趋于  $1$ ，从而得到 (7)。证毕。
推论 2.1（完整相关符号相图）
由于论文已经证明

$$\gamma_n:=\operatorname{Cov}(A_0,A_n)
=
\rho(a-\rho)\lambda_{\rm hid}^{\,n-1},
\qquad
\rho(a-\rho)<0,$$

故：

$$\begin{array}{c|c}
\lambda_{\rm hid}>0 & \gamma_n<0\ \text{对所有 }n\ge1,\\
\lambda_{\rm hid}=0 & \gamma_1<0,\ \gamma_n=0\ \text{对所有 }n\ge2,\\
\lambda_{\rm hid}<0 & \gamma_n\text{严格交替变号}.
\end{array}
\tag{8}$$

尤其在振荡区间中，

$$\left|\frac{\gamma_{n+1}}{\gamma_n}\right|
=
|\lambda_{\rm hid}|
\le e^{-2}\approx0.135335.
\tag{9}$$

因此，负隐藏模所造成的交替相关具有一个该物理子族特有的、远强于一般 D-MAP 谱界的普适衰减常数。
推论 2.2（精确 1-依赖曲线及 Lambert  $W$  参数化）
对于  $0<x\le y$ ，精确 1-依赖当且仅当

$$xe^{-x}=ye^{-y}.
\tag{10}$$

除固定点  $(1,1)$  外，该曲线必跨越  $t=1$ 。若  $0<x<1$ ，唯一对应点为

$$\boxed{\;
y=\tau(x):=-W_{-1}(-xe^{-x})>1.
\;}
\tag{11}$$

该映射为交换  $(0,1)$  与  $(1,\infty)$  的序反转对合。其端点渐近为

$$\tau(x)
=
\log\frac1x+\log\log\frac1x+o(1),
\qquad x\downarrow0,
\tag{12}$$

以及

$$\tau(1-u)
=
1+u+\frac23u^2+\frac49u^3+O(u^4),
\qquad u\downarrow0.
\tag{13}$$

因此，论文所谓的“exact 1-dependence threshold”实际上是一条具有显式全局几何、尖点分支结构和双尺度渐近的解析相界，而非单一未解析的标量条件。

三、交换对角线上的  $N^{-1/4}$  根分裂定律
论文 Theorem E 仅给出对称坐标投影的  $\sqrt N$  极限，没有给出重复根本身的极限。
定理 3（投影后重复根的二尺度极限）
令一般对角点为

$$\sigma_0=(2z,z^2),\qquad 0<z<1,$$

并假设

$$\sqrt N(\widehat\sigma_N^{\rm raw}-\sigma_0)
\Longrightarrow
Z=(Z_1,Z_2)^\top
\sim N(0,\Sigma_\sigma(z)).$$

令  $\widehat\sigma_N=\Pi_F(\widehat\sigma_N^{\rm raw})$ ，其中

$$F=\{(\sigma_1,\sigma_2):\sigma_2\le \sigma_1^2/4\}.$$

定义

$$V=zZ_1-Z_2.$$

若  $\widehat z_{-,N}\le\widehat z_{+,N}$  为投影后多项式的两个实根，则

$$\boxed{\;
N^{1/4}
\begin{pmatrix}
\widehat z_{-,N}-z\\[1mm]
\widehat z_{+,N}-z
\end{pmatrix}
\Longrightarrow
\begin{pmatrix}
-\sqrt{V_+}\\[1mm]
\sqrt{V_+}
\end{pmatrix},
\qquad V_+=\max(V,0).
\;}
\tag{14}$$

等价地，

$$N^{1/4}(\widehat z_{+,N}-\widehat z_{-,N})
\Longrightarrow
2\sqrt{V_+}.
\tag{15}$$

若  $\Delta\tau$  已知，令  $\theta_0=-\log z/\Delta\tau$ ，则根排序率满足

$$N^{1/4}
\begin{pmatrix}
-\log\widehat z_{-,N}/\Delta\tau-\theta_0\\
-\log\widehat z_{+,N}/\Delta\tau-\theta_0
\end{pmatrix}
\Longrightarrow
\frac{\sqrt{V_+}}{\Delta\tau\,z}
\begin{pmatrix}1\\-1\end{pmatrix}.
\tag{16}$$

证明
Theorem E 给出

$$X_N=\sqrt N(\widehat\sigma_N-\sigma_0)
\Longrightarrow
X=\Pi_{H_z}Z,
\qquad
H_z=\{h:h_2\le zh_1\}.$$

欧氏半空间投影满足

$$zX_1-X_2=(zZ_1-Z_2)_+=V_+.
\tag{17}$$

对判别式

$$\Delta(\sigma)=\sigma_1^2-4\sigma_2$$

作一阶展开：

$$\sqrt N\,\Delta(\widehat\sigma_N)
=
4(zX_{N,1}-X_{N,2})+o_P(1)
\Longrightarrow4V_+.$$

根的半间距为  $\sqrt{\Delta}/2$ ，因而具有  $N^{-1/4}$  尺度，根中点的  $N^{-1/2}$  扰动在该尺度下消失，由此得到 (14)–(15)。对  $-\log z/\Delta\tau$  作一阶展开即得 (16)。证毕。
在论文唯一认证点  $z=1/2$ ，

$$V=\frac12Z_1-Z_2,\qquad
\operatorname{Var}(V)
=
(1/2,-1)\Sigma_\sigma(1/2)(1/2,-1)^\top
\approx0.932336360.
\tag{18}$$

因此  $V$  为非退化中心正态变量， $V_+$  以概率  $1/2$  等于零。于是投影后两个估计根以渐近概率  $1/2$  完全粘合，其余概率下按平方根正态分裂。这一原子—连续混合分布不能由普通 delta method 得到。
此外，局部备择

$$p_N=z-hN^{-1/4},\qquad s_N=z+hN^{-1/4}$$

满足

$$(p_N+s_N,p_Ns_N)
=
(2z,z^2-h^2N^{-1/2}),
\tag{19}$$

说明根间距只能通过其平方进入  $\sqrt N$  级可见坐标；故  $N^{-1/4}$  并非投影算法的偶然缺陷，而是交换商几何的二阶识别尺度。
一般约束投影极限属于既有理论，Shapiro 2000；近碰撞 Prony 节点的病态性亦已有数值分析研究，Batenkov 2014。但上述 sampled-counter 协方差驱动的  $N^{-1/4}$  原子—平方根正态极限并非这些一般结果的现成陈述。

四、路径级离散化等价与普适半采样区间偏差
定理 4（舍入的二阶段指数等待时间表示）
在 Palm 点击时刻之后，取相互独立的

$$R\sim\operatorname{Exp}(\kappa_r),\qquad
E\sim\operatorname{Exp}(\Gamma),
\qquad W=R+E.$$

则论文中的零串长度满足路径分布恒等式

$$\boxed{\;
G\overset d=\left\lfloor\frac{W}{\Delta\tau}\right\rfloor,
\qquad
G+1\overset d=\left\lceil\frac{W}{\Delta\tau}\right\rceil.
\;}
\tag{20}$$

这不仅重新解释了  $\Gamma\leftrightarrow\kappa_r$  的不可标记对称性，而且给出概率母函数

$$\mathbb E z^G
=
\frac{
\kappa_r(1-p)/(1-pz)
-
\Gamma(1-s)/(1-sz)
}{
\kappa_r-\Gamma
},
\tag{21}$$

以及精确平均周期

$$\mu_\Delta=\mathbb E(G+1)
=
\frac{
y/(1-e^{-x})-x/(1-e^{-y})
}{
y-x
}.
\tag{22}$$

当  $\Delta=\Delta\tau\downarrow0$  而  $\Gamma,\kappa_r$  固定时，

$$\boxed{\;
\Delta\mu_\Delta
=
\frac1\Gamma+\frac1{\kappa_r}
+\frac{\Delta}{2}
+\frac{\Gamma\kappa_r(\Gamma+\kappa_r)}{720}\Delta^4
+O(\Delta^6).
\;}
\tag{23}$$

因此单位时间的可见点击强度满足

$$\frac{\rho}{\Delta}
=
\frac{\Gamma\kappa_r}{\Gamma+\kappa_r}
-
\frac{\Delta}{2}
\left(\frac{\Gamma\kappa_r}{\Gamma+\kappa_r}\right)^2
+O(\Delta^2).
\tag{24}$$

式 (23) 中的  $\Delta/2$  是一个与两种速率无关的普适半区间延迟；式 (24) 则给出边界锁存采样导致的首阶强度下偏差。该项在论文的固定  $\Delta\tau$  分析中没有出现，但对跨采样频率比较和实验设计具有直接意义。

五、高维最小纤维不是“包含一条轨道”，而是完整的全局主轨道
令

$$C(K)=[\,\mathbf1,K\mathbf1,\ldots,K^{n-1}\mathbf1\,],$$

并令  $K$  为论文 Proposition 3.1 意义下的最小内点。定义

$$\Omega_K=
\left\{
M\in G_n:
M^{-1}KM>0,\ 
(I-M^{-1}KM)\mathbf1>0
\right\}.$$

定理 5（全局纤维参数化）
最小内点  $K$  的完整可见纤维恰为

$$\boxed{\;
\mathcal F^\circ(K)
=
\{M^{-1}KM:M\in\Omega_K\},
\;}
\tag{25}$$

且轨道参数  $M$  是唯一的。若  $L=M^{-1}KM$ ，则其显式逆为

$$\boxed{\;
M=C(K)\,C(L)^{-1}.
\;}
\tag{26}$$

因此轨道映射不是仅在单位元附近的浸入，而是从开放半代数集  $\Omega_K\subset G_n$  到完整最小内点纤维的全局光滑嵌入。每个连通分支均具有精确维数

$$(n-1)^2.
\tag{27}$$

证明
经典最小实现唯一性已经保证同一可见律的两个最小核满足唯一的 reset-preserving 相似关系；该部分属于 Kalman 理论，Kalman 1963。本文所需的强化来自显式逆。
由  $L=M^{-1}KM$ 、 $M\mathbf1=\mathbf1$ ，

$$L^j\mathbf1=M^{-1}K^j\mathbf1,$$

故

$$C(L)=M^{-1}C(K).$$

最小性保证  $C(L)$  可逆，因而得到 (26)。该公式同时证明轨道参数的唯一性及逆映射的光滑性。严格正性条件正好将  $G_n$  截取为  $\Omega_K$ ，故没有额外的不可见分支。证毕。
进一步，尾生成函数

$$H_K(t)=\sum_{j\ge0}\beta K^j\mathbf1\,t^j
      =\beta(I-tK)^{-1}\mathbf1
\tag{28}$$

是完整可见律的有限维有理坐标。在一般  $\det K\neq0$  的最小层上，其归一化分子—分母具有  $2n-1$  个自由系数，而

$$n^2-(n-1)^2=2n-1.
\tag{29}$$

这表明  $(n-1)^2$  维相似轨道恰好耗尽全部结构性不可识别方向；其余  $2n-1$  个方向构成可见有理模空间。任何基于单一可见记录的似然或估计方程，其隐藏核 Fisher 信息矩阵至少具有  $(n-1)^2$  维零空间。
发表价值判断
结果建议定位价值判断精确物理像方程 (1) 与跨对角线检验 (3)–(4)新主定理最高；将“可逆”提升为“可检验的像刻画” $N^{-1/4}$  根分裂及原子—连续混合极限新主定理最高；显著超出论文现有 Theorem E割线谱公式、尖锐界及 Lambert  $W$  相界新主定理或强推论组高；给出完整相关相图与普适衰减界舍入表示及半区间采样偏差独立命题/应用定理中高；对采样设计具有直接解释力全局主轨道与  $2n-1$  维可见模空间高维结构定理高；将局部“存在”强化为完整纤维分类
其中，定理 1 与定理 3 已足以构成一条独立且具有发表价值的新理论主线：前者刻画正则的物理模型像，后者刻画同一模型像边界上不可避免的二阶识别奇异性。二者共同揭示了一个此前未被论文识别的核心事实——交换对角线对“模型归属”是正则的，而对“根分裂”却是  $N^{-1/4}$  奇异的。