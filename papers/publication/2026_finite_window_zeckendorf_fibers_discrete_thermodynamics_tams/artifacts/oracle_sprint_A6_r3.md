校正后的更新恒等式为

$$\Lambda _0(s)=0,
\qquad
\Lambda_j(s)
 =1+u_j(s)+2\sum_{\ell=1}^{j-1}u_\ell(s)
 =2\sum_{\ell=0}^{j-1}u_\ell(s)+u_j(s)-1,
\quad j\ge1.$$

有限窗恒等式对全部  $m\ge1$  保持不变。以下仅处理全实倾斜问题。
全实倾斜压力定理
令

$$a_d(s):=b_{2d+1}(s),\qquad d\ge1,$$

并以  $\mathfrak P(\theta)$  表示 Stern–Brocot 压力

$$\mathfrak P(\theta)
 =\lim_{d\to\infty}\frac1d
   \log\sum_{T\in\mathcal T_d}|T|^\theta .$$

其已发表性质为： $\mathfrak P$  在  $(-\infty,1)$  上实解析且严格为正，在  $[1,\infty)$  上恒等于零。本文仅调用这一既有输入及其领先本征值估计，不主张其优先权。Kesseböhmer–Stratmann 与 Fiala–Kleban–Özlük 给出了所需的 Stern–Brocot/Knauf 对应及定量压力结论。
则有：


 $B_s$  的收敛半径为

$$\boxed{\;
R_B(s)=\exp\!\left(-\frac12\mathfrak P(s/2)\right).
\;}$$

因而

$$R_B(s)<1\quad(s<2),\qquad R_B(s)=1\quad(s\ge2).$$



设  $\sigma _0>2$  是

$$\frac{\zeta(\sigma _0-1)}{\zeta(\sigma _0)}=2$$

的唯一解。方程  $B_s(r)=1$  的非负实根结构为

$$\begin{array}{c|c}
s<\sigma _0 & \text{唯一根 }r_s\in(0,R_B(s))\\
s=\sigma _0 & \text{唯一根 }r_{\sigma _0}=1=R_B(\sigma _0)\\
s>\sigma _0 & [0,R_B(s)]\text{ 内无根}.
\end{array}$$



对每个  $s\in\mathbb R$ ，极限

$$\lim_{m\to\infty}\frac1m\log S_{-s}(m)$$

均存在，并且

$$\boxed{
P(-s)=
\begin{cases}
-\log r_s,&s<\sigma _0,\\[2mm]
0,&s\ge\sigma _0.
\end{cases}}$$

等价地，若  $t>-\sigma _0$ ，则  $P(t)>0$  是方程

$$\boxed{\;
\sum_{q\ge2}\ \sum_{\substack{1\le p<q\\(p,q)=1}}
     q^t e^{-P(t)c(p/q)}=1
\;}$$

的唯一正解；若  $t\le-\sigma _0$ ，则  $P(t)=0$ 。故最大正压力相恰为

$$\boxed{(-\sigma _0,\infty)}.$$



 $P$  在  $(-\sigma _0,\infty)$  上实解析且严格凸；但在
 $t_c=-\sigma _0$  处不可微，左右导数分别为

$$P'_-(t_c)=0,\qquad
P'_+(t_c)=
\frac{\displaystyle
  \sum_{q\ge2}\sum_{(p,q)=1}q^{-\sigma _0}\log q}
{\displaystyle
  \sum_{q\ge2}\sum_{(p,q)=1}c(p/q)q^{-\sigma _0}}
>0.$$

因而临界点具有两个有限单侧导数，但不是  $C^1$  接合。


证明
1. 字母层的指数增长与  $B_s$  的半径
负连分数参数化给出

$$a_d(s)=
\sum_{\substack{0<p<q,\ (p,q)=1\\d(p/q)=d}}q^{-s}.$$

深度为  $d$  的分数共有  $2^{d-1}$  个，并满足

$$d+1\le q\le F_{d+2}.$$

因此

$$\begin{aligned}
2^{d-1}F_{d+2}^{-s}
 &\le a_d(s)\le2^{d-1}(d+1)^{-s},
 &&s\ge0,\\
2^{d-1}(d+1)^{-s}
 &\le a_d(s)\le2^{d-1}F_{d+2}^{-s},
 &&s\le0.
\end{aligned}
\tag{1}$$

特别地，每个  $B_s$  均具有正且有限的收敛半径。
该深度层恰为 Knauf 模型的第  $d$  个新分母层。已发表的领先本征值/Gibbs 估计给出，对每个固定的  $s<2$ ，存在常数
 $0<C_s^-\le C_s^+<\infty$ ，使得

$$C_s^-e^{d\mathfrak P(s/2)}
 \le a_d(s)
 \le C_s^+e^{d\mathfrak P(s/2)}.
\tag{2}$$

在  $s\ge2$  时，

$$\lim_{d\to\infty}\frac1d\log a_d(s)=0.
\tag{3}$$

由于

$$B_s(z)=z\sum_{d\ge1}a_d(s)z^{2d},$$

Cauchy–Hadamard 公式立即给出

$$R_B(s)=e^{-\mathfrak P(s/2)/2}.$$

当  $s<2$  且  $|z|=R_B(s)$  时，由 (2)

$$|a_d(s)z^{2d+1}|\asymp_s1,$$

故通项不趋于零，边界上处处发散。对  $s=2$ ， $R_B(2)=1$ ，且正实边界发散。对  $s>2$ ，则

$$B_s(1)
 =\sum_{q\ge2}\frac{\varphi(q)}{q^s}
 =\frac{\zeta(s-1)}{\zeta(s)}-1<\infty,
\tag{4}$$

故单位圆上绝对收敛。由此完成所需边界分类。
2.  $B_s(r)=1$  的根
当  $s\le2$  时，正实边界值为  $+\infty$ ；当  $2<s<\sigma _0$  时，(4) 给出  $B_s(1)>1$ 。由于系数非负且  $b_3(s)>0$ ， $B_s(r)$  在正实收敛区间严格递增，故在这两种情形均存在唯一内部根。
当  $s=\sigma _0$  时， $B_s(1)=1$ 。当  $s>\sigma _0$  时，
 $B_s(1)<1$ ，故不存在非负实根。
此外，若  $s<\sigma _0$  且  $B_s(r_s)=1$ ，则对
 $|z|\le r_s$ 

$$|B_s(z)|\le B_s(|z|)\le1.$$

等号要求所有非零项具有同一相位。因支持集包含  $3$  与  $5$ ，其最大公因数为  $1$ ，故

$$B_s(z)=1,\quad |z|\le r_s
\quad\Longrightarrow\quad z=r_s.
\tag{5}$$

因此  $1-B_s$  在最小模圆上仅有单根  $r_s$ 。
3. 更新序列的精确半径
由形式恒等式

$$U_s(z)=\frac1{1-B_s(z)}$$

及 (5)，当  $s<\sigma _0$  时， $U_s$  的精确收敛半径为  $r_s$ 。
当  $s=\sigma _0$  时， $B_s(1)=1$ ，故半径为  $1$ 。当
 $s>\sigma _0$  时，

$$U_s(1)=\frac1{1-B_s(1)}<\infty,$$

所以其半径至少为  $1$ ；另一方面，一字母词已经给出
 $u_j(s)\ge b_j(s)$ ，故  $U_s$  的半径不可能超过  $B_s$  的半径  $1$ 。于是

$$R_U(s)=
\begin{cases}
r_s,&s<\sigma _0,\\
1,&s\ge\sigma _0.
\end{cases}
\tag{6}$$

字母代价  $3,5$  均出现，因此  $u_j(s)>0$  对所有  $j\ge8$  成立。词连接给出

$$u_{m+n}(s)\ge u_m(s)u_n(s).$$

对这一余有限支持应用移位后的 Fekete 论证，得到真正的极限而非仅有上极限：

$$\lim_{j\to\infty}\frac1j\log u_j(s)
 =-\log R_U(s).
\tag{7}$$

4. 向有限窗的双向指数传递
令

$$H_m(s)=\sum_{j=0}^m u_j(s).$$

修正后的有限窗恒等式直接给出，对每个  $m\ge1$ ，

$$\boxed{\;
H_m(s)\le S_{-s}(m)\le4H_{m+1}(s).
\;}
\tag{8}$$

由 (7) 及  $R_U(s)\le1$ ，

$$\lim_{m\to\infty}\frac1m\log H_m(s)
 =-\log R_U(s).$$

再由 (8)，

$$\lim_{m\to\infty}\frac1m\log S_{-s}(m)
 =-\log R_U(s),$$

从而得到全实倾斜公式。
5. 解析性与严格凸性
取  $t>-\sigma _0$ ，并定义字母概率

$$\mu_t(p/q)
 :=q^t e^{-P(t)c(p/q)}.$$

根方程说明其总质量为  $1$ 。由于根严格位于  $B_{-t}$  的收敛圆内，存在指数余量；结合

$$\log q\ll d(p/q),\qquad c(p/q)=2d(p/q)+1,$$

可知任意阶的  $t$ -导数及  $P$ -导数均局部一致收敛。解析隐函数定理因而适用，不涉及任何待验证的算子假设。
记

$$X=\log q,\qquad C=c(p/q).$$

微分根方程得

$$P'(t)=\frac{\mathbb E_{\mu_t}X}{\mathbb E_{\mu_t}C},
\tag{9}$$

以及

$$P''(t)
 =\frac{\mathbb E_{\mu_t}\!\left[(X-P'(t)C)^2\right]}
        {\mathbb E_{\mu_t}C}.
\tag{10}$$

分数  $1/2$  与  $1/3$  分别具有  $(C,q)=(3,2)$  与
 $(5,3)$ ，而

$$\frac{\log2}{3}\ne\frac{\log3}{5}.$$

故 (10) 严格为正，证明实解析性与严格凸性。
6. 临界单侧导数
若

$$\frac pq=[0;a_1,\ldots ,a_r]$$

采用末项  $a_r>1$  的正规连分数约定，则

$$d(p/q)=a_1+\cdots+a_r-1,\qquad
c(p/q)=2(a_1+\cdots+a_r)-1.
\tag{11}$$

Panov–Liehl 的固定分母平均定理给出

$$\frac1{\varphi(q)}
\sum_{\substack{1\le p<q\\(p,q)=1}}
(a_1+\cdots+a_r)
 \sim\frac6{\pi^2}(\log q)^2.$$

该结果及其现代定量形式可见 Aistleitner–Borda–Hauke。因此

$$\sum_{q\ge2}q^{-\sigma _0}
 \sum_{\substack{1\le p<q\\(p,q)=1}}c(p/q)
 \ll
 \sum_{q\ge2}q^{1-\sigma _0}(\log q)^2<\infty.
\tag{12}$$

同理，

$$\sum_{q\ge2}\varphi(q)q^{-\sigma _0}\log q<\infty.
\tag{13}$$

故可在 (9) 中令  $t\downarrow-\sigma _0$ ，得到所述有限正右导数。冻结侧恒等于零，左导数为零。因此压力在临界点连续但不可微。
综上，现稿中“非整数  $t>-\beta_*$  的压力存在性仍开放”以及“正压力相的解析严格凸性仍开放”均可删除；其精确替代是上述全实倾斜定理。Weinstein 的自由幺半群参数化、乘法性及最大指标公式仅作为既有输入，参见其原文 Notes on Fibonacci partitions。