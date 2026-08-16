先固定两项勘误。正确数值为

$$\boxed{\kappa=2.589184379946924126\ldots } .$$

稿件中所有依赖  $\kappa$  的数值系数相应为
系数正确数值 $4/\kappa$  $1.544888046977171\ldots$  $\log(4/\kappa)$  $0.434951446220798\ldots$  $\kappa/2$  $1.294592189973462063\ldots$  $1/\kappa$  $0.386222011744293\ldots$  $1/(\sigma_0\kappa)$  $0.155813167651677\ldots$  $2\log\varphi/\kappa$  $0.371709198299325\ldots$ 
因此 Theorems 5.3–5.4 中的符号公式保持不变，但相应数值展开须采用上表。以下证明不调用 Weinstein 的层稳定定理；尤其不把  $j=2k$  归入其公开定理。该端点仍是本稿利用最大生成元引理所得的独立加强。
定理：实负倾斜压力的精确更新方程
令  $s=-t$ 。对每个

$$s\in[\beta_*,\sigma_0],$$

极限

$$P(-s)=\lim_{m\to\infty}\frac1m\log S_{-s}(m)$$

存在。更精确地，令  $p/q\in(0,1)$  为既约分数，并写出其唯一负连分数

$$\frac pq=
\cfrac1{a_1-\cfrac1{a_2-\ddots-\cfrac1{a_r}}},
\qquad a_i\ge2.$$

定义

$$d(p/q):=\sum_{i=1}^r(a_i-1),\qquad
c(p/q):=2d(p/q)+1.$$

则  $P(-s)$  是方程

$$\boxed{\;
\sum_{q=2}^{\infty}
\sum_{\substack{1\le p<q\\(p,q)=1}}
q^{-s}\exp\!\bigl(-P(-s)c(p/q)\bigr)=1
\;}
\tag{1}$$

的唯一非负解。因而

$$P(-\sigma_0)=0,\qquad
P(-s)>0\quad(\beta_*\le s<\sigma_0).$$

故零压力集合的右端点精确为

$$\boxed{t_c=-\sigma_0
=-2.478750785733960\ldots } .$$

证明
记

$$I_j=[F_{j+1}-1,F_{j+2}-1),\qquad
\Lambda_j(s):=\sum_{n\in I_j}R(n)^{-s}.$$

本稿的精确双层恒等式给出

$$S_{-s}(m)=\Lambda_m(s)+\Lambda_{m+1}(s).
\tag{2}$$

1. 长度标记的自由幺半群
对向量  $\mathbf a=(a_1,\ldots ,a_r)$ ，令

$$D(\varnothing)=1,\quad D(a_1)=a_1,$$


$$D(a_1,\ldots ,a_r)
=a_rD(a_1,\ldots ,a_{r-1})
-D(a_1,\ldots ,a_{r-2}).
\tag{3}$$

若  $\mathbf a$  是  $p/q$  的上述负连分数，则  $D(\mathbf a)=q$ 。
使用 Weinstein 的自由幺半群参数化，每个生成元  $g$  唯一对应于一个非空有序字

$$w=\frac{p_1}{q_1}\times\cdots\times\frac{p_r}{q_r},$$

并且

$$R(g)=\prod_{i=1}^r q_i,\qquad
L(g)=\sum_{i=1}^r c(p_i/q_i).
\tag{4}$$

这里只使用其生成元双射、分母乘法性及显式  $H$ -作用公式，而不使用层稳定定理；参见 Weinstein, §§3–4。
定义单字母权

$$b_\ell(s):=
\sum_{\substack{0<p<q,\ (p,q)=1\\c(p/q)=\ell}}q^{-s}.
\tag{5}$$

固定  $\ell$  时该和有限。事实上，若  $\ell=2d+1$ ，则

$$b_{2d+1}(s)=
\sum_{r=1}^{d}
\ \sum_{\substack{e_1+\cdots+e_r=d\\e_i\ge1}}
D(e_1+1,\ldots ,e_r+1)^{-s},
\qquad b_{2d}(s)=0.
\tag{6}$$

故这些系数可由有限组合和递推式 (3) 独立计算。
令

$$u_0(s)=1,\qquad
u_j(s)=\sum_{\ell=1}^{j}b_\ell(s)u_{j-\ell}(s).
\tag{7}$$

由自由字的唯一分解，

$$u_j(s)
=\sum_{\substack{g\text{ 为生成元}\\L(g)=j}}R(g)^{-s}.
\tag{8}$$

相应生成函数满足严格的形式恒等式

$$B_s(z):=\sum_{\ell\ge1}b_\ell(s)z^\ell,
\qquad
U_s(z):=\sum_{j\ge0}u_j(s)z^j
=\frac1{1-B_s(z)}.
\tag{9}$$

2. 更新方程精确表示有限窗和
每个生成元  $g$  属于 Weinstein 的奇首指标分支，故

$$L([a]g)=L(g)+2a,\qquad
L([a]\tau g)=L(g)+1+2a,$$

以及

$$L(\sigma n)=L(n)+1.
\tag{10}$$

又因  $R(n)>1$  时

$$n\in I_j\iff L(n)=j,$$

且  $H$ -作用自由、不同生成元的轨道不交，所以生成元  $g$  的整个轨道在  $I_j$  中贡献的点数恰为

$$\begin{cases}
0,&j<L(g),\\
1,&j=L(g),\\
2,&j>L(g).
\end{cases}
\tag{11}$$

每个  $I_j$  还恰有一个  $R(n)=1$  的左端点。因此

$$\boxed{\;
\Lambda_j(s)
=1+u_j(s)+2\sum_{\ell=1}^{j-1}u_\ell(s)
=2\sum_{\ell=0}^{j-1}u_\ell(s)+u_j(s)-1.
\;}
\tag{12}$$

结合 (2)，得到本文有限窗和的精确更新表示

$$\boxed{\;
S_{-s}(m)
=4\sum_{j=0}^{m-1}u_j(s)+3u_m(s)+u_{m+1}(s)-2.
\;}
\tag{13}$$

这不是层计数类比或上下界，而是逐轨道、逐有限窗的恒等式。
3. 更新方程的指数率存在
自由字连接给出

$$u_{m+n}(s)\ge u_m(s)u_n(s).
\tag{14}$$

字母  $1/2$  与  $1/3$  的代价分别为  $3,5$ ，故  $u_j(s)>0$  对所有  $j\ge8$  成立。于是尾序列  $\log u_j(s)$  超可加。对任意固定  $k\ge8$ ，把充分大的  $N$  写成

$$N=qk+r,\qquad 8\le r\le k+7,$$

由 (14) 得

$$\log u_N(s)\ge q\log u_k(s)+\log u_r(s).$$

因此广义 Fekete 论证给出极限

$$\gamma_s:=\lim_{j\to\infty}\frac1j\log u_j(s).
\tag{15}$$

另一方面，因为  $s>2$ ，

$$B_s(1)
=\sum_{q\ge2}\frac{\varphi_{\!E}(q)}{q^s}
=\frac{\zeta(s-1)}{\zeta(s)}-1<\infty.
\tag{16}$$

令  $r_s\in(0,1]$  为  $B_s(r_s)=1$  的解。对  $0\le z<r_s$ ，有  $B_s(z)<1$ ，故  $U_s(z)<\infty$ ；而在  $z=r_s$  处，

$$U_s(r_s)=\sum_{k\ge0}B_s(r_s)^k=+\infty.$$

所以  $U_s$  的收敛半径正是  $r_s$ 。由 Cauchy–Hadamard 公式及 (15)，

$$\gamma_s=-\log r_s.
\tag{17}$$

令  $H_j(s)=\sum_{\ell=0}^ju_\ell(s)$ 。由 (15)，

$$\lim_{j\to\infty}\frac1j\log H_j(s)=\gamma_s.
\tag{18}$$

而 (12) 给出

$$H_{j-1}(s)\le\Lambda_j(s)\le2H_j(s).$$

故

$$H_m(s)\le S_{-s}(m)\le4H_{m+1}(s).
\tag{19}$$

对数除以  $m$  并令  $m\to\infty$ ，由 (18) 得

$$P(-s)=\gamma_s=-\log r_s.$$

将  $r_s=e^{-P(-s)}$  代入  $B_s(r_s)=1$ ，即得方程 (1)。
4. 相变点
由 (16) 及  $\sigma_0$  的定义，

$$B_{\sigma_0}(1)=1.$$

所以  $r_{\sigma_0}=1$ ，从而

$$P(-\sigma_0)=0.$$

若  $\beta_*\le s<\sigma_0$ ，则逐项严格单调性给出

$$B_s(1)>B_{\sigma_0}(1)=1.$$

由于  $B_s(0)=0$  且  $B_s$  在  $[0,1]$  上连续严格递增，唯一根满足

$$0<r_s<1,$$

故

$$P(-s)=-\log r_s>0.$$

结合本稿已证明的  $P(t)=0$  对所有  $t\le-\sigma_0$  成立，遂得

$$\{t\le-\beta_*:P(t)=0\}=(-\infty,-\sigma_0],$$

尤其

$$\boxed{t_c=-\sigma_0}.$$