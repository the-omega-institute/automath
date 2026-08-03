结论是否定性的：在现行 (U1)–(U4) 下， $a_0$  及其环境仿射块半群不是数制的不变量，因而不存在以其为基础的统一有限判定分类。正确的局部对象是递推初态生成的饱和可达模上的限制作用。该修正给出精确必要条件，但充分性仍含不可由有限  $p$ -主数据表达的全局素因子预算。下述分离例同时证明：即使规范语言均为正则语言、尾系数素因子集合完全相同，逃逸行为仍可相反。
1. 可达递推模与真正的坏素数集
令

$$z_J=(U_J,\ldots,U_{J+d-1})^{\mathsf t},\qquad
V_U=\mathbb Q[C]z_J,\qquad
\Lambda_U=V_U\cap\mathbb Z^d .$$

由于  $\Lambda_U$  是饱和  $C$ -不变格， $C$  在其上的限制

$$C_{\mathrm r}:=C|_{\Lambda_U}$$

是一个整矩阵。定义

$$\Delta_U:=\bigl|\det C_{\mathrm r}\bigr|,
\qquad
S_{\mathrm r}:=\{p:p\mid\Delta_U\}.$$

等价地，若  $\mu_U(X)$  是尾序列的最小递推多项式，则  $V_U$  是循环  $C$ -模，故

$$\Delta_U=|\mu_U(0)|.$$

由于  $\mu_U$  整除所选递推的特征多项式，

$$S_{\mathrm r}\subseteq S=\{p:p\mid a_0\}.$$

对  $\lambda=e_1^{\mathsf t}|_{\Lambda_U}$ ，数字块在真正可达的仿射格
 $\mathbb Z\oplus\Lambda_U$  上作用为

$$D^{\mathrm r}_\varepsilon
=
\begin{pmatrix}
1&\varepsilon\lambda\\
0&C_{\mathrm r}
\end{pmatrix},
\qquad
\det D^{\mathrm r}_\varepsilon=\det C_{\mathrm r}.$$

因此它模  $q$  可逆当且仅当  $\gcd(q,\Delta_U)=1$ 。Seki–Matsumura–Fujii–Kasami 的弱泵引理仅需应用于这一限制作用；不需要、亦未使用一般 MCFL 已知失效的强泵结论。Seki–Matsumura–Fujii–Kasami，Kanazawa–Kobele–Michaelis–Salvati–Yoshinaka
由此得到下述严格强化。
可达坏素数定理。
若某个无限 MCFL  $L\subseteq\mathcal R_U$  满足

$$\sup_{w\in L}\omega_{S^c}(\operatorname{val}_U(w))<\infty,$$

则必存在

$$p\in S_{\mathrm r}$$

使

$$\sup_{w\in L}v_p(\operatorname{val}_U(w))=\infty.$$

特别地，若  $\Delta_U=1$ ，则不存在题设所要求的  $L$ ，即使所选非最小递推具有  $|a_0|>1$ 。
证明只需把原有论证中的允许模数由  $\gcd(q,a_0)=1$  扩大为
 $\gcd(q,\Delta_U)=1$ 。相应拓扑严格取为

$$\tau_{S_{\mathrm r}}
=
\Bigl\langle
(n+q\mathbb Z)\cap\mathbb N_{\ge1}:
\gcd(q,\Delta_U)=1
\Bigr\rangle_{\mathrm{top}}.$$

若所有  $p\in S_{\mathrm r}$  的赋值均有界，则

$$\omega_{S_{\mathrm r}^c}(n)
\le
\omega_{S^c}(n)+|S\setminus S_{\mathrm r}|$$

亦一致有界。于是仍落入某个参数满足
 $E\in\mathbb N_0^{S_{\mathrm r}}$  的局部素因子层；在其子空间拓扑中取内在 Cantor–Bendixson 导集即可产生矛盾。此处不涉及环境导集。
 $\Delta_U$  可由有限数据计算：求 Krylov 序列

$$z_J,Cz_J,\ldots,C^dz_J$$

的首个有理线性关系，取其本原整系数多项式，即得  $\mu_U$  与  $\Delta_U=|\mu_U(0)|$ 。因此，“哪些素数可能承担逃逸”是有限可判定的必要条件。
2. 精确的半群—语法语义判据
固定一个由弱泵引理允许的同步模式

$$\sigma:\quad
W_\sigma(t)=
au_1v_1^tw_1s_1^tu_2\cdots
u_kv_k^tw_ks_k^tu_{k+1}.$$

称其为规范允许的，若

$$W_\sigma(t)\in\mathcal R_U\quad(t\ge0),
\qquad
\sum_i(|v_i|+|s_i|)>0.$$

对  $p\mid\Delta_U$  和  $m\ge1$ ，令

$$\Gamma_{p,m}
=
\bigl\langle D^{\mathrm r}_\varepsilon\bmod p^m:
\varepsilon\in A\bigr\rangle$$

为有限奇异仿射块半群，并定义同步轨道

$$\mathcal O_{\sigma,p,m}
=
\{
M_{W_\sigma(t)}\bar z_0:t\ge0
\}.$$

令  $H_{p,m}$  为“记数坐标等于零”的超平面。则

$$\sup_t v_p(\operatorname{val}_U(W_\sigma(t)))=\infty
\iff
\mathcal O_{\sigma,p,m}\cap H_{p,m}\ne\varnothing
\quad\text{对每个 }m\ge1.
\tag{1}$$

对于任一泵块矩阵  $B$ ，其稳定核与稳定像为

$$K_\infty(B)=\bigcup_{j\ge0}\ker B^j,
\qquad
I_\infty(B)=\bigcap_{j\ge0}\operatorname{im}B^j.$$

在模  $p^m$  的有限模上，两条链均在有限步内稳定； $B$  在
 $I_\infty(B)$  上最终周期，在  $K_\infty(B)$  上承担全部瞬态消失。因而 (1) 对每个固定  $m$  可由有限半群枚举判定。但必须检验的是同步乘积轨道与输出超平面的相交，而非仅检验某个泵块是否具有非零稳定核。
题设存在性具有如下精确语义等价：

$$\begin{aligned}
&\exists\,k,L,p
\text{ 满足题设}\\
\Longleftrightarrow\;&
\exists\,\sigma,\ p\in S_{\mathrm r},\ K\ge0
\text{ 使}\\
&\quad W_\sigma(t)\in\mathcal R_U\quad(t\ge0),\\
&\quad \mathcal O_{\sigma,p,m}\cap H_{p,m}\ne\varnothing
\quad(m\ge1),\\
&\quad \omega_{S^c}(\operatorname{val}_U(W_\sigma(t)))\le K
\quad(t\ge0).
\end{aligned}
\tag{2}$$

必要性来自弱泵轨道；该固定同步射线自身由有限扇出的线性 MCFG 生成，故可再次应用可达坏素数定理。充分性则直接取
 $L=\{W_\sigma(t):t\ge0\}$ 。
然而，(2) 不是有限局部分类：前两行在给定有限自动机和固定  $m$  时可判定，最后一行是涉及所有  $\ell\notin S$  的全局素因子条件，不能由任何有限层  $p^m$  半群推出。更根本地，(U1)–(U4) 并未要求  $\mathcal R_U$  具有有限语法或有效编码，故在当前公理体系内，“由有限数据判定”并未定义一个统一算法问题。
3. 相同尾素集而逃逸行为相反的两个系统
任取素数  $p$ 。
系统一：普通  $p$  进制
取

$$U_n=p^n,\qquad A=\{0,\ldots,p-1\},$$

并取通常的 LSD-first 规范表示语言。最小递推为

$$U_{n+1}=pU_n,$$

故

$$a_0=p,\qquad S=S_{\mathrm r}=\{p\}.$$

正则射线

$$L_p=\{0^n1:n\ge0\}$$

满足

$$\operatorname{val}_U(0^n1)=p^n,\qquad
\omega_{S^c}(p^n)=0,\qquad
v_p(p^n)=n.$$

其可达递推模为  $\Lambda_U=\mathbb Z$ ， $C_{\mathrm r}=[p]$ 。模  $p^m$  时

$$K_\infty(C_{\mathrm r})=\mathbb Z/p^m\mathbb Z,
\qquad
I_\infty(C_{\mathrm r})=0.$$

初态完全位于收缩核方向，末端数字  $1$  将  $p^n$  读入记数坐标。
系统二：带非最小非单位递推的 Zeckendorf 系统
取

$$F_0=1,\qquad F_1=2,\qquad F_{n+2}=F_{n+1}+F_n$$

及通常的 LSD-first Zeckendorf 规范语言。对同一素数  $p$ ，该序列亦满足

$$F_{n+3}
=
-pF_n+(1-p)F_{n+1}+(p+1)F_{n+2}.
\tag{3}$$

因此，以 (3) 作为 (U4) 中的所选递推时，

$$a_0=-p,\qquad S=\{p\},$$

与普通  $p$  进制完全相同。
其三维伴随矩阵的特征多项式为

$$(X-p)(X^2-X-1).$$

模  $p^m$  时两因子互素，因为

$$p^2-p-1\equiv-1\pmod p.$$

故环境递推模具有 Fitting 分解

$$(\mathbb Z/p^m\mathbb Z)^3
=
V_{p,m}\oplus V_{\mathrm{Fib},m},$$

其中

$$C|_{V_{p,m}}=pI,\qquad
(C^2-C-I)|_{V_{\mathrm{Fib},m}}=0.$$

于是

$$K_\infty(C)=V_{p,m},
\qquad
I_\infty(C)=V_{\mathrm{Fib},m}.$$

但规范初态

$$z_0=(1,2,3)^{\mathsf t}$$

满足

$$(C^2-C-I)z_0=0,$$

故  $z_0\in V_{\mathrm{Fib},m}$ ，并且所有规范前缀的递推坐标始终停留在该稳定像中。环境中的  $p$ -奇异核完全不可达。
事实上，该系统的最小可达多项式仍为

$$\mu_U(X)=X^2-X-1,
\qquad
\Delta_U=1,
\qquad
S_{\mathrm r}=\varnothing.$$

若存在无限 MCFL  $L$  满足

$$\omega_{S^c}(\operatorname{val}_U(w))\le K,$$

则

$$\omega(\operatorname{val}_U(w))\le K+1$$

在  $L$  上一致有界。这与该最小单位系统已经建立的单位整除树结论矛盾。因此，该系统不存在任何题设射线或更一般的题设 MCFL。
由此得到严格分离：

$$S_{\text{base }p}=S_{\text{inflated Fibonacci}}=\{p\},$$

但前者具有正则逃逸射线，后者不存在任何有限扇出 MCFL 逃逸语言；两者的规范表示语言均为正则语言。
4. 对真正非单位 Pisot 情形的界定
上述反例揭示，现有 (U4) 中“非单位”是递推表示依赖的，而不是  $(U,A,\mathcal R_U)$  的不变量。任何单位最小递推  $\mu(X)$  都可乘以  $X-p$ ，人为制造尾系数含  $p$  的非单位环境伴随矩阵，同时不改变任何表示、数值或语言性质。
因此稿件应作如下修正：

$$\boxed{
\text{以最小可达多项式 }\mu_U
\text{ 取代任意所选递推，并定义 }
S_{\mathrm r}=\{p:p\mid\mu_U(0)\}.
}$$

只有在额外假定“所选递推即最小可达递推”后，诸如

$$X^2-2X-2$$

这类真正非单位 Pisot 多项式才构成尚未解决的逆问题。对该收紧类别，条件 (1) 给出逐层有限可判定的必要条件，但是否存在满足全局素因子预算的规范允许同步轨道，当前材料尚不能证明充分性或有限可判定性。任何在未加入最小可达性假设前声称统一肯定分类的表述均不成立。