结论是否定的。更强地，该“最小有界倍式次数”在 simple-Parry 情形退化为 Parry 阶，而最优因果逆长度既可严格小于它，也可严格大于它；二者之间不存在普遍的单向不等式。正确对象不是主理想  $(P_\beta)$  中元素的最小次数，而是一个随孔径变化的有界滑动同余格之消失深度，等价地，是有限碰撞图中坏初态的最大路径长度。
1. 必要的适用范围
“任意 Pisot 数的 simple-Parry 语言”必须改为“任意 simple-Parry Pisot 数”。Pisot 性保证  $d_\beta(1)$  最终周期，但不保证有限；后者才是 simple-Parry 条件。Schmidt 给出 Pisot 周期性结论，simple-Parry admissibility 则来自 Parry。
设

$$d_\beta(1)=t_1t_2\cdots t_p0^\infty,\qquad
t_1=d=\lfloor\beta\rfloor,\quad t_p>0,\quad 0\le t_i\le d,$$

并定义 Parry companion polynomial

$$P_\beta(z)=z^p-t_1z^{p-1}-\cdots-t_p.$$

采用无冗余贪婪字母表

$$A_d=\{0,1,\ldots,d\},$$

原始系统为满移位  $A_d^{\mathbb Z}$ ，而非合法语言本身。数字差集因而精确为

$$\Delta_d=A_d-A_d=[-d,d]\cap\mathbb Z,$$

不是  $[-2d,2d]$ 。
相应语言计数满足

$$Q_0=1,$$


$$Q_n=1+\sum_{i=1}^{n}t_iQ_{n-i}\quad(1\le n<p),
\qquad
Q_n=\sum_{i=1}^{p}t_iQ_{n-i}\quad(n\ge p).$$

这一 Parry–Bertrand 权序列及其合法表示语言参见 Charlier–Cisternino–Stipulanti。以下假定本文所用 colex 秩满足

$$\operatorname{Rank}_{\beta,m}(w)
 =\sum_{j=0}^{m-1}w_jQ_j$$

且在合法长  $m$  词上依次取值  $0,\ldots,Q_m-1$ 。
定义候选量

$$\mathfrak a(P_\beta,d)
 =
 \min\left\{
 \deg H:
 0\ne H\in(P_\beta),\
 H(0)\ne0,\
 [z^j]H\in\Delta_d
 \right\}.$$

由于  $P_\beta(0)=-t_p\ne0$ ，且  $1,t_1,\ldots,t_p\le d$ ，多项式  $P_\beta$  本身已经满足数字差界。另一方面，任何非零倍式的次数至少为  $p$ 。故

$$\boxed{\mathfrak a(P_\beta,d)=p.}$$

因此原问题在 simple-Parry 情形实质上等价于断言

$$\ell_{\mathrm{cau}}(\beta,m)=p$$

对每个可逆孔径成立。该断言不成立。
若“递推多项式”被解释为  $Q_n$  的约化最小特征多项式而非 Parry companion polynomial，下述两个三次反例中的多项式均不可约，故反例不受这一术语选择影响。
2. 正确刻画：有界滑动同余指数
对  $F(z)=\sum f_jz^j$ ，定义

$$\partial F=\frac{F-F(0)}z,\qquad
\pi_mF=\sum_{j=0}^{m-1}f_jz^j,$$

以及模秩泛函

$$\Lambda_m(F)
 =
 \sum_{j=0}^{m-1}Q_j[z^j]F
 \pmod{Q_m}.$$

对  $L\ge1$ ，定义坏滑动同余集

$$\mathcal N_{\beta,m,L}
 =
 \left\{
 \begin{array}{l|l}
 E(z)=\displaystyle\sum_{i=0}^{m+L-2}e_iz^i&
 \begin{array}{l}
 e_i\in\Delta_d,\quad e_0\ne0,\\[2mm]
 \Lambda_m(\pi_m\partial^tE)=0,\quad
 0\le t<L
 \end{array}
 \end{array}
 \right\}.$$

等价地，令  $T_{m,L}$  为带状 Toeplitz 矩阵

$$T_{m,L}=
\begin{pmatrix}
Q_0&Q_1&\cdots&Q_{m-1}&&\\
&Q_0&Q_1&\cdots&Q_{m-1}&\\
&&\ddots&\ddots&&\ddots
\end{pmatrix},$$

则

$$\mathcal N_{\beta,m,L}
 =
 \left\{
 e\in\Delta_d^{\,m+L-1}:
 e_0\ne0,\quad
 T_{m,L}e\equiv0\pmod{Q_m}
 \right\}.$$

定理：精确因果刻画
在上述假设下，

$$\boxed{
\ell_{\mathrm{cau}}(\beta,m)
 =
 \min\{L\ge1:\mathcal N_{\beta,m,L}=\varnothing\},
}$$

其中若所有  $\mathcal N_{\beta,m,L}$  均非空，则右端定义为  $\infty$ 。
证明
设两个原始块  $u,v\in A_d^{m+L-1}$  产生相同的  $L$  个连续输出，令  $e_i=u_i-v_i$ 。colex 秩在合法代表上为双射，故第  $t$  个输出相等当且仅当

$$\sum_{j=0}^{m-1}Q_j e_{t+j}\equiv0\pmod{Q_m}.$$

因此  $u_0\ne v_0$  等价于相应差多项式属于  $\mathcal N_{\beta,m,L}$ 。
反之，对任意  $e_i\in[-d,d]$ ，取

$$u_i=\max(e_i,0),\qquad v_i=\max(-e_i,0).$$

则  $u_i,v_i\in A_d$  且  $u_i-v_i=e_i$ 。故  $\mathcal N_{\beta,m,L}$  中的每个元素均实现为两个真实原始块，并可任意延拓为双无限输入。因此：


若  $\mathcal N_{\beta,m,L}\ne\varnothing$ ，则  $L$  个未来输出不能确定首位；


若  $\mathcal N_{\beta,m,L}=\varnothing$ ，则每个可出现的  $L$ -输出块具有唯一首位原像。有限性保证存在局部函数

$$a_t=\psi(y_t,\ldots,y_{t+L-1}).$$



证毕。
等价碰撞图
令图  $\Gamma_{\beta,m}$  的顶点集为

$$V=\Delta_d^{\,m-1}.$$

从  $v=(v_0,\ldots,v_{m-2})$  向
 $w=(w_0,\ldots,w_{m-2})$  引边，当且仅当

$$w_i=v_{i+1}\quad(0\le i<m-2)$$

且

$$\sum_{j=0}^{m-2}Q_jv_j+Q_{m-1}w_{m-2}
 \equiv0\pmod{Q_m}.$$

记坏顶点集

$$B=\{v\in V:v_0\ne0\}.$$

则：

$$\ell_{\mathrm{cau}}(\beta,m)
 =
 1+\sup\{\text{从 }B\text{ 出发的有向路径边数}\}.$$

若有从  $B$  可达的有向环，则上确界为  $\infty$ 。
此外：

$$\Phi_{\beta,m}\text{ 可逆}
\iff
\Gamma_{\beta,m}\text{ 中唯一的双无限路径是零路径}.$$

因而“可逆”本身并不充分保证有限因果逆。对已经可逆的孔径，

$$\ell_{\mathrm{cau}}(\beta,m)<\infty
\iff
0^{m-1}\text{ 不可由 }B\text{ 到达}.$$

这正是所需的附加假设：可逆性必须加强为右向因果可逆性。
该图有  $(2d+1)^{m-1}$  个顶点；循环检测与可达无环子图上的最长路径即可精确求出  $\ell_{\mathrm{cau}}$ 。
3. 最小非恒等反例与无界分离族
令  $\beta_p$  为  $p$ -bonacci Pisot 数，即

$$P_p(z)=z^p-z^{p-1}-\cdots-z-1,\qquad p\ge3.$$

其为次数  $p$  的 Pisot 数，且

$$d_{\beta_p}(1)=1^p0^\infty.$$

这些标准事实可参见 Kalle；更一般的 confluent-Parry/Pisot 结论见 Dombek–Masáková–Vávra。
字母表为  $\{0,1\}$ 。在长度小于  $p$  时所有二元词均合法，故

$$Q_j=2^j\quad(0\le j<p).$$

长度  $p$  仅排除  $1^p$ ，长度  $p+1$  排除在两个位置出现  $1^p$  的三个词，因此

$$Q_p=2^p-1,\qquad
Q_{p+1}=2^{p+1}-3.$$

取孔径  $m=p+1$ 。则

$$\boxed{\ell_{\mathrm{cau}}(\beta_p,p+1)=2},
\qquad
\boxed{\mathfrak a(P_p,1)=p}.$$

证明
记

$$C=2^p-1,\qquad M=2^{p+1}-3.$$

若一个输出不能确定首位，则存在
 $e_0,\ldots,e_p\in\{-1,0,1\}$ 、 $e_0\ne0$ ，使

$$A+Ce_p\equiv0\pmod M,
\qquad
A=\sum_{j=0}^{p-1}2^je_j.$$

由于  $e_0\ne0$ ，整数  $A$  为奇数；且

$$|A+Ce_p|\le2C=M+1<2M.$$

若  $e_p=0$ ，则  $|A|<M$ ，而  $A\ne0$ ，不可能整除  $M$ 。若  $e_p=\pm1$ ，则  $A+Ce_p$  为偶数，不能等于奇数  $\pm M$ ，故必为零：

$$A=-Ce_p.$$

由于  $C$  是  $\sum_{j=0}^{p-1}2^j$  的极值，必有某个
 $\varepsilon\in\{\pm1\}$  使

$$(e_0,\ldots,e_{p-1},e_p)
 =
(\varepsilon,\ldots,\varepsilon,-\varepsilon).$$

该差块确实给出一个输出碰撞，因此  $\ell_{\mathrm{cau}}>1$ 。
若再要求第二个输出相等，则必须存在  $e_{p+1}\in\{-1,0,1\}$  使

$$\sum_{j=0}^{p}Q_je_{j+1}
 =
-\varepsilon+Ce_{p+1}
 \equiv0\pmod M.$$

然而

$$|-\varepsilon+Ce_{p+1}|
\le C+1=2^p<M,$$

且该数不可能为零。因此不存在两个连续输出仍不能确定首位的差块，故  $\ell_{\mathrm{cau}}=2$ 。
另一方面  $P_p$  本身系数属于  $\{-1,0,1\}$ ，且次数为  $p$ ，故
 $\mathfrak a(P_p,1)=p$ 。证毕。
由此得到无界分离：

$$\boxed{
\mathfrak a(P_p,1)-\ell_{\mathrm{cau}}(\beta_p,p+1)
=p-2\longrightarrow\infty.
}$$

最小实例为三次 Tribonacci 基数

$$\beta^3-\beta^2-\beta-1=0,\qquad m=4,$$

其中

$$(Q_0,Q_1,Q_2,Q_3,Q_4)=(1,2,4,7,13),$$

并有

$$\ell_{\mathrm{cau}}(\beta,4)=2,\qquad
\mathfrak a(P_\beta,1)=3.$$

其在三重意义下均为最小：次数  $3$  是问题允许的最小次数，二元字母表是最小非平凡字母表；对该基数， $m<3$  的 fold 为恒等映射， $m=3$  因  $1^3$  与  $0^3$  的循环碰撞而不可逆，故  $m=4$  是首个非恒等可逆孔径。
4. 反向失配：有界倍式次数也不是上界
令  $\gamma$  为

$$R(z)=z^3-z^2-1$$

的实根。该多项式不可约，另两根为共轭复根且模为  $\gamma^{-1/2}<1$ ，故  $\gamma$  为三次 Pisot 数。由

$$\gamma^3=\gamma^2+1$$

直接得到

$$d_\gamma(1)=1010^\infty.$$

相应权序列为

$$(Q_0,Q_1,Q_2,Q_3,Q_4)=(1,2,3,4,6).$$

在孔径  $m=4$  时，碰撞同余为

$$e_t+2e_{t+1}+3e_{t+2}+4e_{t+3}\equiv0\pmod6.$$

固定  $e_0=1$ ，利用整体变号对称性，逐次解此同余所得的全部坏差块如下：
连续输出数全部代表元（忽略整体变号）1 $(1,-1,-1,1)$ ,  $(1,-1,1,1)$ ,  $(1,0,-1,-1)$ ,  $(1,0,1,-1)$ ,  $(1,1,-1,0)$ ,  $(1,1,1,0)$ 2 $(1,-1,-1,1,0)$ ,  $(1,-1,1,1,-1)$ 3 $(1,-1,1,1,-1,0)$ 4无
第一行按  $e_3=-1,0,1$  分组求解二元同余即得；以后各行只需对上一行附加  $e_i\in\{-1,0,1\}$  并代入下一同余，故表格为穷尽性的整数证明。最后一个三输出碰撞不能延长，因为第四个窗口要求

$$1-2+4e_6=-1+4e_6\equiv0\pmod6,$$

而  $e_6=-1,0,1$  分别给出  $-5,-1,3$ 。
因此

$$\boxed{\ell_{\mathrm{cau}}(\gamma,4)=4}.$$

但  $R$  本身已经是系数位于  $[-1,1]$  的三次倍式，故

$$\boxed{\mathfrak a(R,1)=3<4}.$$

结合 Tribonacci 例，已经得到

$$\ell_{\mathrm{cau}}<\mathfrak a
\quad\text{和}\quad
\ell_{\mathrm{cau}}>\mathfrak a$$

均可在三次、二元、孔径四的最小参数层发生。因此  $\mathfrak a$  既不是因果逆长度的上界，也不是下界。
5. 与共轭根几何的精确关系
5.1 有界倍式次数的根模障碍
设  $R\in\mathbb Z[z]$ ，且存在

$$H(z)=\sum_{j=0}^{r}h_jz^j\in(R),\qquad
h_0\ne0,\quad |h_j|\le d.$$

若  $\alpha$  是  $R$  的根， $0<|\alpha|=s<1$ ，则

$$1\le |h_0|
 =
 \left|\sum_{j=1}^{r}h_j\alpha^j\right|
 \le
 d\,\frac{s(1-s^r)}{1-s}.$$

因此：

$$s\le\frac1{d+1}
\quad\Longrightarrow\quad
\mathfrak a(R,d)=\infty.$$

若  $s>1/(d+1)$ ，则有次数下界

$$r\ge
\left\lceil
\frac{
\log\!\left(1-\frac{1-s}{ds}\right)
}{
\log s
}
\right\rceil.$$

对 simple-Parry companion polynomial，由于  $P_\beta$  自身已经是有界倍式，这同时推出其每个单位圆内根都满足

$$|\alpha|>\frac1{d+1}.$$

然而  $\mathfrak a(P_\beta,d)=p$  已由次数强制，故在 simple-Parry companion 约定下， $\mathfrak a$  本身不再含有可变的共轭根几何信息。
5.2 符号并非独立决定因素
对单个实根而言，负号本身不改变有界倍式问题：变换

$$H(z)\longmapsto H(-z)$$

把根  $s$  变为  $-s$ ，并将系数  $h_j$  变为  $(-1)^jh_j$ ，保持次数、常数项及对称差界  $[-d,d]$  不变。因此，单个共轭根的正负号不能解释  $\mathfrak a$  的变化；真正相关的是所有根共享同一整数系数向量所产生的联合约束。
在 squarefree 情形，次数  $r$  的有界倍式存在，等价于某个非零整数  $h_0$  满足

$$-h_0(1,\ldots,1)
\in
\left\{
\sum_{j=1}^{r}h_j
  (\alpha_1^j,\ldots,\alpha_s^j):
h_j\in[-d,d]\cap\mathbb Z
\right\}.$$

右端是一个离散复 zonotope：


根模决定各生成向量的径向衰减；


正实根不产生相位旋转；


负实根产生  $\pi$ -交替；


非实根  $\rho e^{i\theta}$  产生  $j\theta$  的旋转；


同一组  $h_j$  必须同时消去所有根，因此完整的模—辐角配置而非单根符号起决定作用。


现有受限系数倍式算法正是通过模  $R$  的余式图判定这种存在性；参见 Drungilas–Jankauskas–Šiurys。该余式图与本文所需的模  $Q_m$  滑动碰撞图不是同一对象。
5.3 因果长度只通过权序列间接受根几何控制
Parry companion matrix为本原非负矩阵，故  $\beta$  是唯一主模根。设其他特征根的最大模为  $\eta<\beta$ 。取任意

$$\max\{1,\eta\}<\rho<\beta.$$

标准线性递推展开给出

$$Q_n=c\beta^n+O(\rho^n).$$

于是碰撞方程

$$\sum_{j=0}^{m-1}Q_je_{t+j}=k_tQ_m$$

可归一化为

$$k_t
 =
 \sum_{r=1}^{m}
 e_{t+m-r}\beta^{-r}
 +
 O_{\beta,d}\!\left(
 \left(\frac{\rho}{\beta}\right)^m
 \right).$$

因此：


非主根的模控制有限孔径同余图趋近 signed- $\beta$  展开几何的速率；


实根符号及复根辐角控制误差项的振荡；


但边是否存在仍是精确整数同余事件，不能由模或符号单独判定。


若  $P_\beta\ne M_\beta$ ，Parry companion polynomial 还含有 cofactor roots；此时仅知道  $\beta$  的 Galois 共轭根甚至不足以确定  $\mathfrak a$  或  $Q_n$  的次主谱。上述两个三次反例均满足  $P_\beta=M_\beta$ ，故这种因子歧义不能解释反例。
最后， $p$ -bonacci 族还直接排除了“共轭根符号决定因果长度”的可能性。对

$$P_p(z)=z^p-z^{p-1}-\cdots-1,$$

当  $p$  为偶数时，

$$P_p(-1)=1,\qquad P_p(0)=-1,$$

故存在负实共轭根；当  $p$  为奇数时，对任意  $x\ge0$ ,

$$P_p(-x)
 =
-x^p-\frac{1+x^p}{1+x}<0,$$

故不存在负实共轭根。然而两种奇偶情形在孔径  $p+1$  均满足

$$\ell_{\mathrm{cau}}=2.$$

由此得到最终刻画：

$$\boxed{
\text{最优因果逆长度由有界滑动模同余的最长存活深度决定，
而非由有界多项式倍式的最小次数决定。}
}$$

受限系数倍式仅能在其系数完整落入单个窗口时证明“一输出不足”；连续多少个移位仍被消去、模  $Q_m$  的边界绕回以及孔径相关的右向合并，均由  $\mathcal N_{\beta,m,L}$  或  $\Gamma_{\beta,m}$  控制。这一替代定理、无界分离族及双向最小反例构成了可独立发表的高次数理论单元。