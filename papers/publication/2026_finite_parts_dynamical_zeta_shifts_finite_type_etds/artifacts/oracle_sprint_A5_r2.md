结论是否定的。即使  $\Gamma$  固定、 $G=C_{2}$ 、两 cocycle 均满足严格扭曲谱隙，全部逐类 Mertens 常数仍不能恢复逐长度本原周期数据。
定理：严格谱隙下的精确边界碰撞
令  $G=C_{2}=\{1,s\}$ ， $\varepsilon(s)=-1$ 。取四个顶点，并令底图邻接矩阵为

$$A=
\begin{pmatrix}
0&4&0&0\\
1&1&0&2\\
0&0&0&4\\
0&2&1&1
\end{pmatrix}.$$

每行和为  $4$ ，故 Perron 根为  $\lambda=4$ 。底图强连通，且顶点  $2,4$  有环，因而  $A$  本原。
对每个  $A_{ij}$  条带标记平行边，按下列两个符号矩阵规定标签：

$$B=
\begin{pmatrix}
0&-2&0&0\\
-1&-1&0&-2\\
0&0&0&-2\\
0&2&-1&1
\end{pmatrix},
\qquad
B'=
\begin{pmatrix}
0&-4&0&0\\
1&1&0&0\\
0&0&0&-4\\
0&0&1&1
\end{pmatrix}.$$

具体地，在 cocycle  $\tau$  中，从  $i$  到  $j$  的  $1$ -标记边和  $s$ -标记边数分别为

$$\frac{A_{ij}+B_{ij}}2,\qquad \frac{A_{ij}-B_{ij}}2;$$

对  $\tau'$  则以  $B'$  代替  $B$ 。这些数均为非负整数，故给出了同一带标记有向多重图上的两个显式 cocycle。其非平凡扭曲矩阵分别为

$$A_{\varepsilon,\tau}=B,\qquad A_{\varepsilon,\tau'}=B'.$$

记

$$Q(z)=1-z+4z^{2}.$$

直接按整数行列式计算得

$$\det(I-zB)=1-z^{2}+4z^{4}=Q(z^{2}),$$

而

$$\det(I-zB')
 =1-2z+9z^{2}-8z^{3}+16z^{4}
 =Q(z)^{2}.$$

严格谱隙
矩阵  $B$  的特征方程为

$$x^{4}-x^{2}+4=0.$$

若  $y=x^{2}$ ，则  $y^{2}-y+4=0$ ，故  $|y|=2$ ，从而

$$\operatorname{rad}(B)=\sqrt2<4.$$

矩阵  $B'$  的特征方程为

$$(x^{2}-x+4)^{2}=0,$$

其根的模均为  $2$ ，故

$$\operatorname{rad}(B')=2<4.$$

因此  $[\tau],[\tau']\in\mathcal T_{\mathrm{gap}}(\Gamma,C_{2})$ 。
全部逐类常数精确相等
令

$$L_B(z)=-\log\det(I-zB),
\qquad
L_{B'}(z)=-\log\det(I-zB'),$$

取从  $0$  出发的实径向分支。由于

$$\psi^{m}\varepsilon=
\begin{cases}
\varepsilon,&m\ \text{为奇数},\\
\mathbf1,&m\ \text{为偶数},
\end{cases}$$

Adams–Möbius坐标中依赖 cocycle 的差为

$$F_{\varepsilon}^{\tau}(z)-F_{\varepsilon}^{\tau'}(z)
 =
\sum_{k\ge1}\frac1k
 \left(\sum_{\substack{m\mid k\\m\ {\rm odd}}}\mu(m)\right)
 \bigl(L_B(z^k)-L_{B'}(z^k)\bigr).$$

奇因子上的 Möbius 和满足

$$\sum_{\substack{m\mid k\\m\ {\rm odd}}}\mu(m)
=
\begin{cases}
1,&k=2^{j},\\
0,&\text{其他情形}.
\end{cases}$$

因而

$$F_{\varepsilon}^{\tau}(z)-F_{\varepsilon}^{\tau'}(z)
 =
\sum_{j\ge0}2^{-j}
 \bigl(L_B(z^{2^{j}})-L_{B'}(z^{2^{j}})\bigr).$$

置  $z_j=z^{2^j}$ 。由两个精确行列式恒等式，

$$L_B(z_j)-L_{B'}(z_j)
 =2\log Q(z_j)-\log Q(z_{j+1}).$$

由于  $\log Q(z_j)=O(z_j)$ ，该级数绝对收敛，并严格望远镜化为

$$F_{\varepsilon}^{\tau}(z)-F_{\varepsilon}^{\tau'}(z)
 =2\log Q(z).$$

在 Perron 边界  $z=\lambda^{-1}=1/4$  上，

$$Q(1/4)=1-\frac14+\frac14=1,$$

故

$$F_{\varepsilon}^{\tau}(1/4)
 =
F_{\varepsilon}^{\tau'}(1/4).$$

底矩阵相同，且  $C_{2}$  仅有一个非平凡角色；因此稿件中逐类常数公式立即给出

$$K_{\{1\}}^\tau=K_{\{1\}}^{\tau'},
\qquad
K_{\{s\}}^\tau=K_{\{s\}}^{\tau'}.$$

这里没有任何数值截断。常数相等完全来自

$$Q(z^{2})\quad\text{与}\quad Q(z)^{2}$$

在二进制边界泛函下的精确 coboundary 消去。附带地，

$$\det(I-zA)
 =(1-4z)(1+2z-3z^{2}-4z^{3}),
\qquad C(A)=\frac45,$$

所以两个 cocycle 的标量归一化亦逐项相同。
有限长度本原数据不同
底图恰有两个长度  $1$  环，分别位于顶点  $2,4$ 。对  $\tau$ ，这两个环的标签分别为  $s,1$ ；对  $\tau'$ ，二者均为  $1$ 。故

$$p_{1,\{1\}}(\tau)=1,\qquad
p_{1,\{s\}}(\tau)=1,$$

而

$$p_{1,\{1\}}(\tau')=2,\qquad
p_{1,\{s\}}(\tau')=0.$$

特别地，全部常数相等而长度  $1$  的本原周期数据已经不同。
两 cocycle 也不属于同一 switching–整体共轭类： $C_{2}$  的整体共轭作用平凡，而顶点 switching 不改变环的标签。等价地，switching 只会以对角符号矩阵共轭  $B$ ，不可能将两个不同的特征多项式互相变换。
可认证最小性
为避免把不可判定的“偶然超越数相等”混入有限反例比较，采用如下自然的代数证书复杂度。考虑正则  $C_{2}$ -底图上的二次二进制 coboundary 证书：

$$Q(z)=1-kz+kmz^{2},\qquad
\det(I-zB)=Q(z^{2}),\qquad
\det(I-zB')=Q(z)^{2},$$

其中底图为  $m$ -出正则， $\lambda=m$ ，且  $Q(1/m)=1$ 。按

$$\bigl(|G|,\deg Q,|V|,m,|E|\bigr)$$

作字典序比较。本例的复杂度为

$$(2,2,4,4,16).$$

它在该精确证书类中最小：


非平凡有限群必有  $|G|\ge2$ ，本例达到等号。


若  $Q(0)=Q(1/m)=1$  且  $Q$  非常数，则  $\deg Q\ge2$ 。


 $\deg Q=2$  时， $Q(z^{2})$  的次数为  $4$ ；而  $\det(I-zB)$  的次数不超过  $|V|$ ，故  $|V|\ge4$ 。


当  $m=2$  时严格谱隙迫使  $k=1$ 。四顶点二出正则底图的每一行只有十种多重边型： $2e_i$  或  $e_i+e_j$ 。对全部  $10^{4}$  个邻接矩阵作整数分类，其中恰有  $2208$  个本原矩阵；利用

$$\det(I-zB)
=1-t_1z+\frac{t_1^2-t_2}{2}z^2
-\frac{t_1^3-3t_1t_2+2t_3}{6}z^3
+\det(B)z^4,
\quad t_r=\operatorname{tr}(B^r),$$

逐一枚举兼容符号矩阵。恰有  $48$  个底矩阵支持
 $1-z^2+2z^4$ ，但没有任何本原底矩阵支持
 $(1-z+2z^2)^2$ 。这是有限整数枚举，不含浮点判定。


当  $m=3$  时，每个兼容符号矩阵满足
 $B\mathbf1\equiv\mathbf1\pmod2$ ，故
 $\det(I-B)\equiv0\pmod2$ 。另一方面

$$Q(1)=1-k+3k=1+2k\equiv1\pmod2,$$

与  $\det(I-B)=Q(1)$  矛盾。


因此  $m\ge4$ ，而本例在  $m=4$  实现；正则性给出

$$|E|=m|V|\ge16,$$

本例再次达到等号。
这一最小性针对“以有限多项式恒等式证明常数相等”的自然证书复杂度；它不把尚无有限证书的孤立超越值碰撞伪装成已完成的全局分类。
信息损失机制
对  $C_{2}$  定义二进制边界泛函

$$\mathscr M_x(P):=-\sum_{j\ge0}2^{-j}\log P(x^{2^j}).$$

则

$$\mathscr M_x\!\bigl(Q(z^{2})\bigr)
-\mathscr M_x\!\bigl(Q(z)^2\bigr)
=2\log Q(x).$$

因此，当  $Q(\lambda^{-1})=1$  时， $\mathscr M_{\lambda^{-1}}$  消灭非零的行列式 coboundary

$$Q(z^{2})/Q(z)^2.$$

这正是  $\Phi$  的结构性核：它不保存扭曲行列式函数，只保存其在一个 Perron 边界点上的 Mahler 加权值。该核中的元素可以改变最低次迹，甚至改变长度  $1$  本原数据，而边界常数完全不变。
此现象严格弱于既有的 represented  $G$ -cospectrality：后者要求全部扭曲行列式相等，并因而保存全部周期数据；本例两个行列式明显不同。因此它不属于已有的 cospectral/switching 构造范围。相关的完整周期数据框架见 Boyle–Schmieding；一般 Mahler 型无穷乘积背景可参见 Badziahin。
恢复刚性的最弱自然增强
令

$$D_C(z):=\sum_{n\ge1}
\bigl(p_{n,C}(\tau)-p_{n,C}(\tau')\bigr)\log(1-z^n).$$

严格谱隙给出某个  $\beta<\lambda$ ，使

$$p_{n,C}(\tau)-p_{n,C}(\tau')=O(\beta^n/n),$$

故  $D_C$  在  $|z|<\beta^{-1}$  内解析，并包含  $z=\lambda^{-1}$ 。
若不只知道单点常数，而假设对每个  $C$ ，相应的亚临界类 Euler 坐标在某个具有域内聚点的集合  $S$  上相等，即

$$D_C(z)=0\qquad(z\in S),$$

则解析恒等定理给出  $D_C\equiv0$ 。若  $n_0$  是首个本原数据不同的长度，则  $D_C$  的  $z^{n_0}$  系数恰为

$$-\bigl(p_{n_0,C}(\tau)-p_{n_0,C}(\tau')\bigr),$$

产生矛盾。因此

$$p_{n,C}(\tau)=p_{n,C}(\tau')
\qquad(n\ge1,\ C\in\operatorname{Conj}(G)).$$

只需取例如  $S=\{\lambda^{-r}:r\ge2\}$ ；其聚点为  $0$ 。这是自然的“全温度径向剖面”增强。它恰好排除上述碰撞，因为本例在任意径向参数  $z$  上满足

$$F_{\varepsilon}^{\tau}(z)-F_{\varepsilon}^{\tau'}(z)=2\log Q(z),$$

而  $Q(z)=1$  在  $0<z\le1/4$  中仅于  $z=1/4$  成立。故碰撞确为孤立的 Perron 边界取值，而非两个周期生成函数的恒等。