可发表级核心结论
本文最具潜力的延伸，并非继续加强上下文无关语言的泵引理，而是将其提升为一个连接多重上下文无关语言、局部同余拓扑与整数整除结构的统一理论。
设  $(U,A,R_U)$  满足本文条件 (U1)–(U4)，递推尾系数为  $a_0\neq0$ ，并记

$$S=\{p:p\mid a_0\}.$$

称一个语言具有 MCF-免疫性，若它不含任何无限的多重上下文无关子语言，即不含无限的  $k$ -MCFL 子语言，对任意有限  $k$  均成立。
下述论证仅调用本文引理4.5的仿射矩阵结论以及 Seki–Matsumura–Fujii–Kasami 的弱泵引理，不重复其既有证明。
定理一：同步同余轨道定理
任取无限  $k$ -MCFL  $L\subseteq R_U$ 。则存在固定分块

$$W(t)=a\,u_1v_1^tw_1s_1^t\cdots
u_kv_k^tw_ks_k^tu_{k+1}\in L,\qquad t\ge0,$$

其中

$$\sum_{j=1}^{k}\bigl(|v_j|+|s_j|\bigr)>0,$$

使得  $N(t)=\operatorname{val}_U(W(t))$  严格递增，并满足：

$$\forall q\ge2,\quad (q,a_0)=1
\Longrightarrow
\exists H(q)\ge1,\quad
N(t+H(q))\equiv N(t)\pmod q$$

对所有  $t\ge0$  同时成立。
证明要点为：先取长度  $J$  的固定前缀，使全部泵块位于递推稳定区间；多重上下文无关语言对固定词左商封闭。每个泵块矩阵在模  $q$  下可逆，令  $H(q)$  为所有非空泵块矩阵阶的公倍数，即得上述同步同余。严格递增性来自 (U3)。
该定理与本文逐级重新选取泵分解的方式本质不同：同一个一参数轨道同时控制全部与  $a_0$  互素的模数。

定理二：MCFL 的有理数—Cantor 拓扑指纹
在  $\mathbb N_{>0}$  上定义  $S$ -删失同余拓扑

$$\tau_S=\bigl\{\,n+q\mathbb Z:(q,a_0)=1\,\bigr\}.$$

则定理一中的数值轨道

$$Y=\{N(t):t\ge0\}$$

在  $\tau_S$  中没有孤立点。因此：

$$Y\cong\mathbb Q.$$

进一步，在局部完备化

$$\widehat{\mathbb Z}_{S^c}
   =\varprojlim_{(q,a_0)=1}\mathbb Z/q\mathbb Z
   \cong\prod_{p\notin S}\mathbb Z_p$$

中， $\overline Y$  是非空、紧致、零维且无孤立点的度量空间，故

$$\overline Y\cong\text{Cantor 集}.$$

这里仅使用了 Broughan 的 adic 拓扑与完备化理论以及 Sierpiński 的可数无孤立点度量空间分类。
由此得到一个一般性免疫判据：

若算术集合  $A\subseteq\mathbb N_{>0}$  在  $\tau_S$  中是散射空间，则其表示语言

$$\operatorname{Rep}_U(A)
=\{w\in R_U:\operatorname{val}_U(w)\in A\}$$

具有 MCF-免疫性。

换言之，任何无限 MCFL 表示集合都必须在局部同余拓扑中包含一份  $\mathbb Q$ ，并在相应的局部完备化中生成一个 Cantor 子集。这是比“素因子数无界”更本质的拓扑障碍。

定理三：局部素因子层的精确 Cantor–Bendixson 秩
给定  $K\ge0$  及整数向量  $E=(E_p)_{p\in S}$ ，定义

$$X_{K,E}
 =
 \left\{
 n\ge1:
 \omega_{S^c}(n)\le K,\;
 v_p(n)\le E_p\quad(p\in S)
 \right\},$$

其中  $\omega_{S^c}(n)$  只计算不属于  $S$  的不同素因子。
若  $D_S$  表示在  $\tau_S$  中取 Cantor–Bendixson 导集，则有精确恒等式

$$D_S X_{K,E}=X_{K-1,E}\qquad(K\ge1),$$

从而

$$D_S^{\,j}X_{K,E}=X_{K-j,E},
\qquad
D_S^{\,K+1}X_{K,E}=\varnothing.$$

因此  $X_{K,E}$  的 Cantor–Bendixson 高度恰为  $K+1$ 。
证明的关键在于两种相反机制：


若  $n$  已具有恰好  $K$  个  $S$  外素因子，则利用这些素因子的高一阶幂模数，并增加一个避开有限个  $S$ -光滑差值的辅助素数，可以在  $X_{K,E}$  中孤立  $n$ 。


若  $\omega_{S^c}(n)<K$ ，则对任意允许模数  $q$ ，由 Dirichlet 定理选取新素数  $r\equiv1\pmod q$ ，于是

$$nr\equiv n\pmod q,\qquad nr\in X_{K,E},$$

故  $n$  不是孤立点。


Broughan 已研究全同余拓扑中按重数计算的  $\Omega$ -分层闭包；上述结论处理的是不同素因子函数  $\omega$ 、删失素数集合  $S$  以及受限  $S$ -进赋值的联合精确秩，不能由其公开结论直接等同替代。

定理四：非单位系统的唯一可能逃逸方向
任意无限 MCFL  $L\subseteq R_U$  必满足

$$\sup_{w\in L}\omega_{S^c}(\operatorname{val}_U(w))=\infty,$$

或者存在某个  $p\mid a_0$ ，使得

$$\sup_{w\in L}v_p(\operatorname{val}_U(w))=\infty.$$

否则，全部数值均落入某个有限高度的  $X_{K,E}$ ；但定理二给出的无孤立点轨道会存活于每一阶导集，与

$$D_S^{K+1}X_{K,E}=\varnothing$$

矛盾。
这给出以下新免疫结论：
算术目标一般递推系统单位系统素数MCF-免疫MCF-免疫 $\Omega(n)\le K$ MCF-免疫MCF-免疫 $\omega(n)\le K$ 仅可能沿  $p\mid a_0$  的无界赋值逃逸MCF-免疫有限素数支撑若所有  $p\mid a_0$  的赋值有界，则 MCF-免疫MCF-免疫
特别地，本文的素数 CF-免疫性可提升为：

$$\boxed{\text{每个满足 (U1)–(U4) 的系统，其素数表示语言均为 MCF-免疫。}}$$

而且对非单位系统，所有有界  $\Omega$  表示语言同样 MCF-免疫；这一结论不需要单位性。
该二择一结论具有最优性。普通  $b$  进制满足  $a_0=b$ ，正则语言

$$\{0^n1:n\ge0\}$$

表示  $b^n$ 。其不同素因子数恒为  $\omega(b)$ ，但每个  $p\mid b$  的赋值均无界。因此，非单位情形下不可能无条件推出有界  $\omega$  语言的 MCF-免疫性。

定理五：单位系统中的任意深度超同余链
若  $|a_0|=1$ ，则对任意正整数序列  $M_i$  和  $r_i\ge1$ ，每个无限 MCFL  $L\subseteq R_U$  都包含严格递增序列

$$N_{i+1}=N_iQ_i,
\qquad Q_i>1,$$

满足任意指定的同余深度

$$Q_i\equiv1\pmod{M_iN_i^{r_i}}.$$

事实上，在同步轨道中取模数

$$q_i=M_iN_i^{r_i+1}$$

即可得到

$$Q_i=1+c_iM_iN_i^{r_i},\qquad c_i\ge1.$$

若令  $M_i$  包含所有不超过预定阈值  $B_i$  的素数，则

$$\min\{p:p\mid Q_i\}>B_i.$$

因此商因子不仅彼此引入新素数，而且其最小素因子可以按任意给定速度趋于无穷。

定理六：全分支整除树嵌入
在单位系统中，每个无限 MCFL  $L\subseteq R_U$  均包含映射

$$\Phi:\mathbb N^{<\omega}\longrightarrow L$$

使得

$$\operatorname{val}_U(\Phi(\sigma))
\mid
\operatorname{val}_U(\Phi(\tau))
\quad\Longleftrightarrow\quad
\sigma\preceq\tau,$$

其中  $\preceq$  为有限序列的前缀关系。
此外，可以使所有边商

$$Q_e=
\frac{\operatorname{val}_U(\Phi(\text{child}(e)))}
     {\operatorname{val}_U(\Phi(\text{parent}(e)))}$$

两两互素，并使每条边商的最小素因子超过任意预先指定的阈值。
构造时按“父节点先于子节点”枚举全部边。设当前父值为  $P$ ，令  $R$  包含根值、全部既有边商及所需的素数初段；在同步轨道上使用模数  $P^2R$ ，即可选出新子节点并获得

$$Q_e\equiv1\pmod{PR}.$$

故新边商与根及全部旧边商互素。节点值恰为根值乘以其路径上的边商，由唯一素因子支撑立即得到整除关系与前缀关系的完全等价。
因此，每个无限 MCFL 在单位递推记数系统中，不仅包含无限整除链，而且同时包含无限整除反链，并包含整个可数全分支树的诱导副本。该结构远强于单一的互素商链。
文献边界与发表判断
Seki 等人的弱泵引理是形式语言输入；Kanazawa 等人已证明一般 MCFL 不存在所期望的强泵引理，而最新的 Duncan–Elder–Frenkel–Lyu 替换引理亦未涉及递推记数、素数免疫或整除树。上述结果表明，本文的矩阵算术只需要弱泵轨道，因而绕过了 MCFL 强泵理论的障碍。
截至 2026 年 8 月 3 日可检索的公开文献，尚未发现以下三项命题的明确先例：


递推记数中素数及有界  $\Omega$  语言的完整 MCF-免疫性；


“MCFL  $\Rightarrow$  局部同余拓扑中的  $\mathbb Q$  副本及完备化中的 Cantor 闭包”；


无限 MCFL 内部的全分支整除树与任意粗糙边商构造。


这三项结果足以组成一篇独立论文。最适合的中心命题可表述为：

$$\boxed{
\text{递推记数中的无限多重上下文无关语言必携带 Cantor 型同余动力学；}
\\
\text{单位系统中该动力学进一步强制出现普适整除树，}
\\
\text{非单位系统的唯一可能逃逸方向是尾系数素数上的无界赋值。}
}$$