临界充分性成立。关键并非  $L^2(\Omega_d)$ ，而是与 KL 增长及尖峰尺度同时匹配的临界空间

$$q_d:=\frac{d+5}{d+1}\in(1,2),\qquad
p_d:=\frac{4(d+1)}{d+5},\qquad p_dq_d=4.$$

定理（高维 KL 临界矩阈值）
设  $d\ge4$ ， $\nu$  是  $\mathbb R^d$  上的概率律，

$$X=\gamma-\bar\gamma,\qquad \mathbb E|X|^{p_d}<\infty,
\qquad \Sigma=\mathbb E[XX^{\mathsf T}].$$

则

$$D_{\mathrm{KL}}\!\left(P_t^{(d)}*\nu\,\middle\|\,P_t^{(d)}(\cdot-\bar\gamma)\right)
=\mathcal Q_d(\Sigma)t^{-4}+o(t^{-4}).$$

其中

$$\mathcal Q_d(\Sigma)=\frac12\int_{\mathbb R^d}b_\Sigma(y)^2\,\Omega_d(dy),$$

且

$$b_\Sigma(y)=\frac{d+1}{2}
\left[
-\frac{\operatorname{tr}\Sigma}{1+|y|^2}
+\frac{(d+3)y^{\mathsf T}\Sigma y}{(1+|y|^2)^2}
\right].$$

因此，结合稿件已证明的  $2\le r<p_d$  尖峰反例， $p_d$  是“仅以有限绝对矩表述”的精确 KL 阈值，包括临界端点。
证明
记

$$a=\frac{d+1}{2},\qquad
\Omega_d(dy)=c_d(1+|y|^2)^{-a}\,dy,$$

并定义平移商

$$F_y(z)=\left(\frac{1+|y|^2}{1+|y-z|^2}\right)^a.$$

经平移和尺度变换，

$$1+\delta_t(y)
:=\frac{(P_t^{(d)}*\nu)(\bar\gamma+ty)}
        {P_t^{(d)}(ty)}
=\mathbb E F_y(X/t).$$

1. 临界平移商估计
令  $q=q_d$ 、 $p=p_d$ 。直接计算得

$$\begin{aligned}
\|F_\cdot(z)\|_{L^q(\Omega_d)}^q
&=c_d\int_{\mathbb R^d}
\frac{(1+|y|^2)^{a(q-1)}}
     {(1+|y-z|^2)^{aq}}\,dy .
\end{aligned}$$

置  $u=y-z$ ，并使用

$$1+|u+z|^2\le 2(1+|u|^2)(1+|z|^2),$$

可得

$$\|F_\cdot(z)\|_q^q
\le C_d(1+|z|^2)^{a(q-1)}
      \int_{\mathbb R^d}(1+|u|^2)^{-a}\,du.$$

由于

$$a(q-1)=2,\qquad a>\frac d2,$$

故

$$\boxed{\quad
\|F_\cdot(z)\|_{L^q(\Omega_d)}^q
\le C_d(1+|z|^4).
\quad}                                                    \tag{1}$$

这正是临界四阶尺度；取  $q$  次方根即得到大平移增长率

$$\|F_\cdot(z)\|_q\lesssim |z|^{4/q}=|z|^p.$$

令

$$m=\lfloor p\rfloor
=
\begin{cases}
2,&4\le d\le10,\\
3,&d\ge11,
\end{cases}$$

其中  $d=11$  时  $p=3$ 。记

$$T_m(y,z)=\sum_{|\alpha|\le m}U_\alpha^{(d)}(y)z^\alpha,
\qquad
R_m(y,z)=F_y(z)-T_m(y,z).$$

局部 Taylor 估计给出

$$\|R_m(\cdot,z)\|_q\le C_d|z|^{m+1},
\qquad |z|\le1.$$

另一方面，由 (1)、各  $U_\alpha^{(d)}$  的有界性以及  $m\le p$ ，

$$\|R_m(\cdot,z)\|_q\le C_d|z|^p,
\qquad |z|>1.$$

故全局成立

$$\boxed{\quad
\|R_m(\cdot,z)\|_q\le C_d|z|^p .
\quad}                                                    \tag{2}$$

定义

$$r_t(y):=\mathbb E R_m(y,X/t).$$

由 Minkowski 不等式，

$$\|r_t\|_q
\le \mathbb E\|R_m(\cdot,X/t)\|_q.$$

根据 (2)，

$$t^p\|R_m(\cdot,X/t)\|_q\le C_d|X|^p.$$

而对每个固定  $X$ ，因  $m+1>p$ ，局部 Taylor 估计给出

$$t^p\|R_m(\cdot,X/t)\|_q
\le C_d|X|^{m+1}t^{p-m-1}\longrightarrow0.$$

支配收敛遂得端点余项

$$\boxed{\quad
\|r_t\|_{L^q(\Omega_d)}=o(t^{-p}).
\quad}                                                    \tag{3}$$

这一步只使用临界  $p$  阶矩，不需要任何  $p+\varepsilon$  阶矩。
2. 有界低阶层
由于  $\mathbb EX=0$ ，一次项消失。因此

$$\delta_t=u_t+r_t,$$

其中

$$u_t=
\begin{cases}
t^{-2}b_\Sigma,&m=2,\\[2mm]
t^{-2}b_\Sigma+t^{-3}B_3,&m=3,
\end{cases}$$

而  $B_3$  是由三阶矩构成的有界模式。故

$$\|u_t\|_\infty=O(t^{-2}).                                  \tag{4}$$

此外  $F_y(z)\Omega_d(dy)=P_1^{(d)}(y-z)\,dy$ ，所以

$$\int F_y(z)\,\Omega_d(dy)=1.$$

比较 Taylor 系数可知所有正次数模式的  $\Omega_d$ -积分均为零。
3. 非线性 KL 尾部的端点控制
令

$$\Phi(s)=(1+s)\log(1+s)-s,\qquad s\ge-1.$$

对任意  $1<q<2$ ，存在  $C_q$ ，使得当  $|u|\le1/4$  且  $u+v\ge-1$  时，

$$0\le
\Phi(u+v)-\Phi(u)-\log(1+u)v
\le C_q|v|^q.                                               \tag{5}$$

事实上，当  $|v|\le1/2$  时由  $\Phi''(s)=(1+s)^{-1}$  得到  $O(v^2)$ ，而
 $v^2\le |v|^q$ ；当  $|v|>1/2$  时，利用
 $\Phi(s)=O(1+s^q)$  即得 (5)。该估计同时覆盖  $u+v\downarrow-1$  和任意大的正尖峰。
取  $u=u_t$ 、 $v=r_t$ 。由 (4)，充分大  $t$  时可应用 (5)。Hölder 不等式与 (3) 给出

$$\begin{aligned}
\left|
\int\Phi(\delta_t)\,d\Omega_d
-\int\Phi(u_t)\,d\Omega_d
\right|
&\le
C\|\log(1+u_t)\|_{q'}\|r_t\|_q
  +C\|r_t\|_q^q                                                    \\
&\le
O(t^{-2})\,o(t^{-p})+o(t^{-pq})                                    \\
&=o(t^{-4}),
\end{aligned}                                                     \tag{6}$$

因为  $p>2$  且  $pq=4$ 。
式 (5)–(6) 即为所需的完整非线性 KL 尾控机制。它不要求商一致趋于零，也不把尖峰强行置于  $L^2$ ；任意大的局部密度比均由  $q$ -次增长吸收。
该估计同时证明  $\Phi(\delta_t)\in L^1(\Omega_d)$ 。因此变换公式合法，并且

$$H_d(t)=\int_{\mathbb R^d}\Phi(\delta_t(y))\,\Omega_d(dy).$$

4. 协方差系数
由  $\|u_t\|_\infty=O(t^{-2})$ ，

$$\Phi(u_t)=\frac12u_t^2+O(|u_t|^3)$$

在  $y$  上一致成立。因此

$$\int\Phi(u_t)\,d\Omega_d
=
\frac12t^{-4}\int b_\Sigma^2\,d\Omega_d+o(t^{-4})
=
\mathcal Q_d(\Sigma)t^{-4}+o(t^{-4}).                       \tag{7}$$

结合 (6) 与 (7) 即得定理。
与尖峰必要性的精确闭合
稿件尖峰尺度为

$$t_j=\kappa R_jw_j^{1/(d+1)}.$$

二元数据处理下界具有尺度

$$t_j^4H_d(t_j)
\gtrsim R_j^4w_j^{\,1+4/(d+1)}
=\bigl(w_jR_j^{p_d}\bigr)^{q_d}.                             \tag{8}$$

若仅有  $r<p_d$  阶矩，取  $w_j=\alpha_jR_j^{-r}$  后，(8) 含有正幂

$$R_j^{\,4-rq_d},$$

故快速增长的  $R_j$  产生既有反例。
在临界端点  $r=p_d$  时，该幂严格归零，(8) 退化为

$$\bigl(w_jR_j^{p_d}\bigr)^{q_d}.$$

有限临界矩要求

$$\sum_jw_jR_j^{p_d}<\infty.$$

更重要的是，(1)–(6) 通过 Minkowski 不等式对所有同尺度及不同尺度尖峰作整体控制，尾部代价至多为其临界矩质量的  $q_d$  次方；因此不存在由尖峰聚集产生的额外对数损失。下界中的  $q_d$  与上界中的  $L^{q_d}$ -增长完全相同。
故稿件中的候选指数应提升为精确阈值：

$$\boxed{\displaystyle
p_{\mathrm{KL}}(d)=\frac{4(d+1)}{d+5},\qquad d\ge4,
}$$

且临界端点属于充分侧。