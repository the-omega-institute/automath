可形成独立新增章节的定理体系：局部谱稳定、精确负温配分函数与临界奇性
记

$$C_m(k):=\#\{x\in X_m:d_m(x)=k\},\qquad k\ge 1,$$

并令  $\Psi(k)$  为 Weinstein 的  $k$ -层生成轨道数。以下结论均未在本文中陈述；其核心并非复述 Weinstein 的单层稳定定理，而是将其与本文特有的“两相邻 Fibonacci 层”恒等式结合，获得有限窗纤维谱的极限理论。
定理一：有限窗微正则谱的最终稳定
对一切  $m\ge1$ ，

$$C_m(1)=2.$$

更精确地，唯一的两个单点纤维对应于剩余类

$$r=F_{m+1}-1,\qquad r=F_{m+2}-1.$$

对  $k\ge2$ ，有一致估计

$$C_m(k)\le 4\Psi(k),$$

并且在本文 uniform layer-count lemma 所给出的加强阈值下，

$$\boxed{\ C_m(k)=4\Psi(k)\qquad(m\ge2k).\ }$$

特别地，

$$C_m(2)=4\qquad(m\ge4).$$

因此，计数测度

$$\nu_m:=\sum_{x\in X_m}\delta_{d_m(x)}
      =\sum_{k\ge1}C_m(k)\delta_k$$

在离散空间  $\mathbb N$  上局部收敛于

$$\boxed{\ \nu_\infty
   =2\delta_1+4\sum_{k\ge2}\Psi(k)\delta_k.\ }$$

证明
由本文式 (4.10)，纤维重数多重集等于  $R(n)$  在两个相邻层

$$I_m=[F_{m+1}-1,F_{m+2}-1),\qquad
I_{m+1}=[F_{m+2}-1,F_{m+3}-1)$$

上的取值多重集。故

$$C_m(k)=N_m(k)+N_{m+1}(k).$$

对  $k=1$ ，每一非空层恰含一个  $R(n)=1$  的点，因而  $C_m(1)=2$ 。这两个点分别为  $F_{m+1}-1$  与  $F_{m+2}-1$ ，且均落在 Theorem 4.1 的第二区间中，故它们同时也是纤维剩余类。
对  $k\ge2$ ，本文加强的逐层估计给出  $N_j(k)\le2\Psi(k)$ ，而稳定区间内  $N_j(k)=2\Psi(k)$ 。相加即得结论。Weinstein 公开发表的原始结果给出了单层稳定及其轨道解释；本文的早层分析将其延伸至所需端点，而上述有限窗谱测度并未见于该文。Weinstein, Notes on Fibonacci Partitions
这一定理说明：虽然纤维总数以  $\varphi^m$  增长，每个固定有限重数的绝对简并度却最终停止增长。有限窗的低能谱不是趋向连续密度，而是趋向一个由 Weinstein 生成轨道完全编码的离散无限测度。

定理二：负温配分函数的显式极限及其精确收敛边界
令  $\sigma _0>2$  由

$$\frac{\zeta(\sigma _0-1)}{\zeta(\sigma _0)}=2$$

唯一确定。对  $s>\sigma _0$ ，有非指数归一化的强极限

$$\boxed{\ 
\lim_{m\to\infty}S_{-s}(m)
 =\mathcal Z(s)
 :=\frac{4}{\,2-\zeta(s-1)/\zeta(s)\,}-2.
\ }$$

而且，对任意实数  $t$ ，

$$\boxed{
\begin{aligned}
t<-\sigma _0&\Longrightarrow S_t(m)\longrightarrow
 \frac{4}{\,2-\zeta(-t-1)/\zeta(-t)\,}-2<\infty,\\
t\ge-\sigma _0&\Longrightarrow S_t(m)\longrightarrow+\infty.
\end{aligned}}$$

因此， $-\sigma _0$  虽未必是零压力区间的真实端点，却是未经指数归一化的有限窗配分函数的精确收敛临界点。
证明
由定理一及支配收敛，

$$S_{-s}(m)=\sum_{k\ge1}C_m(k)k^{-s}
 \longrightarrow 2+4\sum_{k\ge2}\frac{\Psi(k)}{k^s},
\qquad s>\sigma _0.$$

Weinstein 的轨道 Dirichlet 级数为

$$1+\sum_{k\ge2}\frac{\Psi(k)}{k^s}
 =\left(2-\frac{\zeta(s-1)}{\zeta(s)}\right)^{-1},$$

从而得到显式公式。
若  $0<s\le\sigma _0$ ，上述  $\Psi$ -级数发散。任取  $K$ ，当  $m\ge2K$  时，

$$S_{-s}(m)\ge
2+4\sum_{2\le k\le K}\Psi(k)k^{-s}.$$

令  $K\to\infty$  即得  $S_{-s}(m)\to\infty$ 。当  $t\ge0$  时，由  $d_m(x)\ge1$ ，

$$S_t(m)\ge |X_m|=F_{m+2}\to\infty.$$

证毕。

定理三：极限 Gibbs 谱及一级临界极点
置

$$\kappa:=
-\left.\frac{d}{ds}\frac{\zeta(s-1)}{\zeta(s)}
  \right|_{s=\sigma _0}
=\sum_{n\ge2}\frac{\varphi_{\!E}(n)\log n}{n^{\sigma _0}}
>0.$$

数值上，

$$\kappa=2.58918437999\ldots .$$

当  $s\downarrow\sigma _0$  时，

$$\boxed{\ 
\mathcal Z(s)
 =\frac{4}{\kappa(s-\sigma _0)}+O(1).
\ }$$

故该临界点具有严格的一阶极点，临界指数为  $1$ 。
进一步，定义负温 Gibbs 测度在纤维重数上的推前

$$Q_{m,s}(k):=
\frac{C_m(k)k^{-s}}{S_{-s}(m)}.$$

对每个  $s>\sigma _0$ ， $Q_{m,s}$  依全变差收敛于

$$\boxed{
Q_s(1)=\frac2{\mathcal Z(s)},\qquad
Q_s(k)=\frac{4\Psi(k)k^{-s}}{\mathcal Z(s)}
\quad(k\ge2).
}$$

在临界点附近，

$$Q_s(1)\sim \frac{\kappa}{2}(s-\sigma _0),$$

并且若  $K$  表示极限 Gibbs 谱下的纤维重数，则

$$\mathbb E_s[\log K]
   =\frac1{s-\sigma _0}+O(1),
\qquad
\operatorname{Var}_s(\log K)
   =\frac1{(s-\sigma _0)^2}+O(1).$$

证明
由于

$$\frac{\zeta(s-1)}{\zeta(s)}
 =\sum_{n\ge1}\frac{\varphi_{\!E}(n)}{n^s},$$

其导数在  $s=\sigma _0>2$  处严格为负。因此

$$2-\frac{\zeta(s-1)}{\zeta(s)}
 =\kappa(s-\sigma _0)+O((s-\sigma _0)^2),$$

代入定理二即得极点展开。全变差收敛由

$$C_m(k)k^{-s}\le4\Psi(k)k^{-s}$$

及可求和支配函数推出。最后，

$$-\frac{d}{ds}\log\mathcal Z(s)=\mathbb E_s[\log K],
\qquad
\frac{d^2}{ds^2}\log\mathcal Z(s)
 =\operatorname{Var}_s(\log K),$$

再对极点展开求导即可。
其含义在于：本文已经证明的零压力半直线内部并非热力学上完全平凡。指数压力恒等于零，但未经指数归一化的谱配分函数在  $\sigma _0$  处发生具有显式临界指数的相变；该现象不能由本文现有的压力结论观察到。

定理四：生成轨道数的 Tauber 型渐近
有

$$\boxed{\ 
\sum_{k\le x}\Psi(k)
 \sim \frac{x^{\sigma _0}}{\sigma _0\kappa}.
\ }$$

相应地，

$$\boxed{\ 
\sum_{k\le x}\frac{\Psi(k)}{k^{\sigma _0}}
 \sim \frac1\kappa\log x.
\ }$$

因此临界有限窗配分函数满足

$$\left(\frac4\kappa+o(1)\right)\log m
 \le S_{-\sigma _0}(m)
 \le
\left(\frac{2\log\varphi}{\kappa}+o(1)\right)m .$$

证明要点
令

$$A(s)=\sum_{n\ge2}\frac{\varphi_{\!E}(n)}{n^s}
 =\frac{\zeta(s-1)}{\zeta(s)}-1.$$

则

$$1+\sum_{k\ge2}\frac{\Psi(k)}{k^s}
 =\frac1{1-A(s)}.$$

在直线  $\Re s=\sigma _0$  上，除  $s=\sigma _0$  外有

$$|A(\sigma _0+i\tau)|<A(\sigma _0)=1.$$

否则正系数三角不等式取等将迫使  $2^{-i\tau}$  与  $3^{-i\tau}$  同时等于  $1$ ，与  $\log2/\log3\notin\mathbb Q$  矛盾。因此右端在闭半平面边界上只有一个留数为  $1/\kappa$  的简单极点。Wiener–Ikehara 定理遂给出第一式，分部求和给出第二式。
临界下界取已稳定的  $k\le m/2$ ；上界使用  $k\le D_m$  与

$$\log D_m\sim \frac m2\log\varphi.$$

Weinstein 给出了 Dirichlet 级数，但检索到的公开版本未给出这一关于  $\Psi(k)$  的 Tauber 型增长律。Weinstein 原文

定理五：零压力转变区间可由  $0.4787$  压缩至  $0.2082$ 
令

$$p_m(t):=\frac1m\log S_t(m),\qquad
\beta_*:=\frac{\log\varphi}{\log(2/\varphi)}
       =2.27055945396\ldots .$$

对  $0<s<\sigma _0$ ，

$$\boxed{
\begin{aligned}
\max\!\left\{0,\,
\log\varphi-s\log\frac2\varphi\right\}
&\le \liminf_{m\to\infty}p_m(-s),\\
\limsup_{m\to\infty}p_m(-s)
&\le
\min\!\left\{\log\varphi,\,
\frac{\sigma _0-s}{2}\log\varphi\right\}.
\end{aligned}}$$

特别地，

$$\boxed{\ 
\liminf_{m\to\infty}p_m(t)>0
\qquad(t>-\beta_*).
\ }$$

结合本文的  $p_m(t)\to0$ （ $t\le-\sigma _0$ ），任何可能的零压力相变点只能位于

$$\boxed{
[-\sigma _0,-\beta_*]
=[-2.4787507857\ldots,-2.2705594540\ldots].
}$$

因此本文所谓的整个  $(-\sigma _0,\infty)$ “残余未知区间”在零压力判定意义下过宽；真正尚未决定的条带宽度至多为

$$\sigma _0-\beta_*=0.2081913318\ldots .$$

证明
在  $X_m$  上取均匀分布。因  $u\mapsto u^{-s}$  为凸函数，

$$\frac{S_{-s}(m)}{F_{m+2}}
 \ge
\left(\frac{2^m}{F_{m+2}}\right)^{-s}.$$

故

$$\liminf_{m\to\infty}p_m(-s)
\ge (s+1)\log\varphi-s\log2
=\log\varphi-s\log(2/\varphi).$$

另一方面，任取  $a>\sigma _0$ 。由定理一，

$$S_{-s}(m)
\le2+4D_m^{a-s}
       \sum_{k\ge2}\frac{\Psi(k)}{k^a}.$$

利用  $m^{-1}\log D_m\to\frac12\log\varphi$ ，再令
 $a\downarrow\sigma _0$ ，即得上界。
该结果不解决非整数实倾斜下压力极限的存在性或解析性；它无条件证明的是：在  $t>-\beta_*$  上，任何极限或子序列极限均不可能为零。

定理六：有限窗折叠的精确信息损失率
令原始字均匀分布于  $\Omega_m$ ，其折叠输出分布为

$$p_m(x)=\frac{d_m(x)}{2^m},$$

并令  $u_m$  为  $X_m$  上的均匀分布。设  $\rho\in(2,3)$  为

$$\rho^3-2\rho^2-2\rho+2=0$$

的最大根，即

$$\rho=2.48119430409\ldots .$$

则 Hartley、collision 与 min-entropy 的单位窗极限分别为

$$\boxed{
\begin{aligned}
\lim_{m\to\infty}\frac{H_0(p_m)}m
 &=\log\varphi,\\
\lim_{m\to\infty}\frac{H_2(p_m)}m
 &=\log\frac4\rho,\\
\lim_{m\to\infty}\frac{H_\infty(p_m)}m
 &=\log\frac2{\sqrt\varphi}.
\end{aligned}}$$

三者严格满足

$$\log\frac2{\sqrt\varphi}
<
\log\frac4\rho
<
\log\varphi.$$

数值上分别为

$$0.4525412680,\qquad
0.4775543426,\qquad
0.4812118251.$$

此外，

$$\boxed{
\lim_{m\to\infty}
\frac1m\log\!\left(1+\chi^2(p_m\Vert u_m)\right)
=
\log\frac{\varphi\rho}{4}
=0.00365748243\ldots>0.
}$$

故折叠映射虽对全部  $F_{m+2}$  个合法字满射，其输出在  $L^2$  意义下并不渐近均匀，而是以严格正指数偏离均匀分布。
证明
由本文二次矩递推，

$$S_2(m)=c_\rho\rho^m(1+o(1)),\qquad c_\rho>0.$$

于是

$$H_2(p_m)
=-\log\sum_xp_m(x)^2
=2m\log2-\log S_2(m).$$

又由  $D_m$  的精确极值公式，

$$H_\infty(p_m)=m\log2-\log D_m,
\qquad
\frac1m\log D_m\to\frac12\log\varphi.$$

最后，

$$1+\chi^2(p_m\Vert u_m)
=F_{m+2}\sum_xp_m(x)^2
=\frac{F_{m+2}S_2(m)}{4^m}.$$

现有 Chow–Jones 工作研究同一三次多项式在 Fibonacci 分拆方差中的出现，但不包含上述有限窗折叠的信息论结论。Chow–Jones
原创性与发表价值判断
公开文献中的已知边界为：


Weinstein 证明了单个 Fibonacci 层中固定  $k$  水平集的最终稳定，并给出  $\Psi(k)$  的 Dirichlet 级数；


Sanna 处理正整数幂矩及其高阶端点律，并未处理负实倾斜或有限窗 Gibbs 极限。Sanna


Kempton 通过无理旋转余循环研究  $R(n)$  的局部乘法结构，研究对象与上述有限窗低重数谱不同。Kempton


在截至 2026 年 8 月 3 日检索到的公开文献中，未见下列结论的明文发表：有限窗局部谱测度  $\nu_\infty$ 、显式极限配分函数  $\mathcal Z(s)$ 、其精确收敛临界点与一级临界极点、负温 Gibbs 全变差极限、压缩后的零压力条带，以及有限窗折叠的精确 Rényi 熵率。
其中最具发表价值的核心不是单独的固定层计数，而是“微正则稳定  $\Rightarrow$  显式谱 ζ 函数  $\Rightarrow$  精确配分函数临界性  $\Rightarrow$  Gibbs 临界律”这一完整链条。该链条足以构成本文新的主结果组，并显著超出目前以对应关系和既有极值定理迁移为主的贡献边界。