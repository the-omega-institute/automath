判定
在现有无条件理论下，尚不能判定

$$S(x):=\sum_{n\le x}\omega(n)\log A^*(n)
=o\!\left(x(\log\log x)^2\right)$$

是否成立。困难不在原始素因子的存在性，而在 fibotomic 层的不同素因子数：现有结果控制其对数质量，却不能排除该质量长期集中于一个巨素数，也不能证明其通常分散于  $(\log d)^c$  个素数。
不过可以得到如下严格强于 Stroiński 累计估计、并直接作用于  $A^*(n)$  的无条件结果。
定理（fibotomic 秩熵与可见最大函数）
记

$$\Phi=\frac{1+\sqrt5}{2},\qquad
\mathfrak F_d:=\prod_{r\mid d}F_r^{\mu(d/r)}\quad(d\ge3),$$

并令  $\varphi$  表示 Euler 函数。对  $k\ge0$  定义

$$m=\left\lfloor\frac{k}{2}\right\rfloor,$$


$$\mathcal H_d(k):=
k\log\frac{2d}{3}
+2\log(m!)
+(k-2m)\log(m+1).$$

则存在绝对常数  $C_F<\infty$ ，使得：

$$\boxed{\quad
\mathcal H_d(a(d))
\le \varphi(d)\log\Phi+C_F
\quad(d\ge3).
\quad} \tag{1}$$

更强地，对任意有限支撑权重  $\lambda_d\ge0$ ，有

$$\boxed{\quad
\sum_{d\ge3}\lambda_d\mathcal H_d(a(d))
\le
(\log\Phi)\sum_{d\ge3}\lambda_d\varphi(d)
+C_F\sum_{d\ge3}\lambda_d .
\quad} \tag{2}$$

其推论为

$$a(d)\le
\left(\frac{\log\Phi}{2}+o(1)\right)
\frac{\varphi(d)}{\log d}, \tag{3}$$

其中  $o(1)$  对所有  $d\to\infty$  一致；进而

$$\boxed{\quad
A^*(n)\le
\left(\frac{\log\Phi}{2}+o(1)\right)
\frac{\varphi(n)}{\log n}.
\quad} \tag{4}$$

因此

$$\boxed{\quad
S(x)\le
\sum_{n\le x}\omega(n)\log\varphi(n)
-x(\log\log x)^2
+O(x\log\log x).
\quad} \tag{5}$$

另一方面，无条件地有

$$\boxed{\quad
S(x)\ge
\left(\frac{2\log2}{25}+o(1)\right)x\log\log x .
\quad} \tag{6}$$

证明
Cameron Byer–Dvorachek–Eckard–Harrington–Wise–Wong 的 fibotomic 分解给出

$$F_d(x)=\prod_{r\mid d}\Psi_r(x),
\qquad
\mathfrak F_d=\Psi_d(1)\in\mathbb N.$$

这里只调用其公开分解，不将之计为新结果。Byer et al., Adv. Appl. Math. 138 (2022), 102344
由 Binet 公式，

$$F_r=\frac{\Phi^r}{\sqrt5}
\left(1-(-\Phi^{-2})^r\right).$$

对  $r\mid d$  作 Möbius 乘积，并使用

$$\sum_{r\mid d}\mu(d/r)=0,\qquad
\sum_{r\mid d}r\mu(d/r)=\varphi(d),$$

得到

$$\log\mathfrak F_d
=\varphi(d)\log\Phi+E_d,$$

其中

$$|E_d|
\le
\sum_{j\ge1}
\left|\log\left(1-(-\Phi^{-2})^j\right)\right|
=:C_F<\infty. \tag{7}$$

这给出全部  $d$  上的一致估计

$$e^{-C_F}\Phi^{\varphi(d)}
\le\mathfrak F_d
\le e^{C_F}\Phi^{\varphi(d)}. \tag{8}$$

若  $\alpha(p)=d$ ，则  $p\mid F_d$  而  $p\nmid F_r$  对所有真因子  $r\mid d$  成立。由

$$F_d=\prod_{r\mid d}\mathfrak F_r$$

可知

$$\prod_{\alpha(p)=d}p\mid\mathfrak F_d. \tag{9}$$

除  $p=2,5$  外，经典秩同余给出

$$d=\alpha(p)\mid p-\left(\frac5p\right),$$

故  $p\equiv\pm1\pmod d$ ；这是 Wall–Vinson 理论的标准结论。Wall, Amer. Math. Monthly 67 (1960), 525–532 特殊秩  $d=3,5$  分别只有  $p=2,5$ ，满足下述估计。
将秩为  $d$  的素数递增排列为

$$p_1<\cdots<p_k,\qquad k=a(d).$$

每个区间层  $jd\pm1$  至多贡献两个候选数，因而

$$p_i\ge
d\left\lceil\frac{i}{2}\right\rceil-1
\ge
\frac{2d}{3}\left\lceil\frac{i}{2}\right\rceil .$$

于是

$$\prod_{i=1}^{k}p_i
\ge
\left(\frac{2d}{3}\right)^k
(m!)^2(m+1)^{k-2m}. \tag{10}$$

结合 (8)–(10)，取对数即得 (1)；乘以任意  $\lambda_d\ge0$  后作有限求和即得 (2)，不存在条件收敛或求和交换问题。
由 Stirling 下界

$$\log(m!)\ge m\log m-m$$

可从 (1) 导出

$$a(d)\bigl(\log d+\log a(d)-O(1)\bigr)
\le \varphi(d)\log\Phi+O(1). \tag{11}$$

若

$$a(d)\le\frac{\varphi(d)}{(\log d)^2},$$

则 (3) 显然成立。否则，利用一致下界

$$\varphi(d)\gg\frac{d}{\log\log(3d)}$$

可得

$$\log a(d)=\log d-o(\log d).$$

代入 (11) 即给出

$$(2+o(1))a(d)\log d
\le\varphi(d)\log\Phi,$$

从而证明 (3)。
设  $d_n\mid n$  使  $a(d_n)$  在所有  $d\mid n$  中最大。若

$$d_n\le\frac{n}{(\log n)^3},$$

则由 (3) 的粗化形式  $a(d)\ll d/\log(2d)$  及

$$\varphi(n)\gg\frac{n}{\log\log(3n)}$$

有

$$a(d_n)=o\!\left(\frac{\varphi(n)}{\log n}\right).$$

若  $d_n>n/(\log n)^3$ ，则

$$\log d_n=(1+o(1))\log n,\qquad
\varphi(d_n)\le\varphi(n),$$

故 (3) 同样给出 (4)。由于  $D^+(n)$  只是全部除数的子集，(4) 对题设  $A^*(n)$  成立。
取对数并求和得到

$$\log A^*(n)
\le
\log\varphi(n)-\log\log n
+\log\frac{\log\Phi}{2}+o(1). \tag{12}$$

经典平均阶

$$\sum_{n\le x}\omega(n)
=x\log\log x+O(x)$$

以及

$$\sum_{n\le x}\omega(n)\log\log n
=x(\log\log x)^2+O(x\log\log x) \tag{13}$$

遂给出 (5)。式 (13) 可直接由前一平均阶证明：在  $n>\sqrt x$  上
 $\log\log n=\log\log x+O(1)$ ，而  $n\le\sqrt x$  的贡献为  $o(x)$ 。
最后证明 (6)。Jarden 已证明：对每个素数  $p>5$ ，Lucas 数  $L_{5p}$  至少有两个不同的 primitive prime divisors。Jarden, Fibonacci Quarterly 6 (1968), 407 设  $q$  为其中之一。由

$$F_{2r}=F_rL_r,\qquad \gcd(F_r,L_r)\mid2$$

以及  $5p$  为奇数可知

$$\alpha(q)=10p.$$

事实上，若  $\alpha(q)=2r$  且  $r\mid5p$ 、 $r<5p$ ，则  $q\mid L_r$ ，与  $q$  对  $L_{5p}$  的原始性矛盾。因此

$$a(10p)\ge2\qquad(p>5\text{ prime}). \tag{14}$$

考虑

$$n=10m,\qquad 5\nmid m,$$

且  $m$  含有某个素因子  $p>5$ 。令  $d=10p$ 。则  $d\mid n$ ，并且

$$\nu_5(d)=\nu_5(n)=1,$$

所以  $T_n(d)\ne\varnothing$ 。由 (14)，

$$A^*(n)\ge2.$$

不含大于  $5$  的素因子的这些  $m$  仅为  $2^a3^b$ ，共有  $O((\log x)^2)$  个，可以忽略。
置  $y=x/10$ 。有限交换求和给出

$$\begin{aligned}
\sum_{\substack{m\le y\\5\nmid m}}\omega(m)
&=
\sum_{\substack{q\le y\\q\ {\rm prime}\\q\ne5}}
\left(
\left\lfloor\frac yq\right\rfloor
-
\left\lfloor\frac y{5q}\right\rfloor
\right)\\
&=
\frac45y\sum_{\substack{q\le y\\q\ne5}}\frac1q
+O(\pi(y))\\
&=
\frac45y\log\log y+O(y).
\end{aligned}$$

又  $\omega(10m)=\omega(m)+O(1)$ ，故

$$\sum_{\substack{n\le x\\A^*(n)\ge2}}\omega(n)
\ge
\frac{2}{25}x\log\log x+O(x).$$

乘以  $\log2$  即得 (6)。
定量缺口
(1)–(3) 严格蕴含 Stroiński 的累计界，因为

$$\sum_{d\le x}\frac{\varphi(d)}{\log d}
\sim \frac{3}{\pi^2}\frac{x^2}{\log x},$$

从而

$$\limsup_{x\to\infty}
\frac{\log x}{x^2}\sum_{d\le x}a(d)
\le\frac{3\log\Phi}{2\pi^2}.$$

但 (1)–(2) 还保留了逐秩  $a(d)\log a(d)$  熵、任意权重及 Euler 因子  $\varphi(d)$ ，故不是对该累计定理的改名重述。Stroiński, Theorem 7
令  $L=\log\log x$ 。现有无条件范围为

$$\left(\frac{2\log2}{25}+o(1)\right)xL
\le S(x)
\ll x\log x\,L.$$

题设临界尺度为  $xL^2$ 。因此：


要无条件否定该估计，现有下界仍须增强一个因子  $L$ ；


要无条件证明该估计，现有上界仍须节省因子  $\log x/L$ ，并得到 little- $o$ ；


fibotomic 熵已经穷尽仅由“primitive part 的大小 +  $p\equiv\pm1\pmod d$ ”能够提供的信息。跨越剩余缺口必须控制  $\mathfrak F_d$  的对数质量在不同素数之间的无条件分散，而这正是当前公开理论未能提供的部分。