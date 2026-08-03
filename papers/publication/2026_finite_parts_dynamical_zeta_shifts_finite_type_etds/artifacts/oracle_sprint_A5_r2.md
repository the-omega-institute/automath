经逐式推导与文献排查，本文框架中至少蕴含三项未被稿件识别、具有独立发表价值的结论。其中最重要者将“存在一个  $S_3$  反例”提升为：对于任何非平凡且满足严格扭曲谱隙的有限群扩张，旧 Artin 常数在单位 Frobenius 类上必然错误，并且误差具有正的、完全显式的覆盖轨道乘积。
以下记  $\gamma_E$  为 Euler 常数， $\mathcal P$  为本原轨道集， $\ell(\omega)=|\omega|$ ， $g_\omega$  为轨道标签。
一、商覆盖分裂因子与普遍 Artin 失效定理
设  $H\triangleleft G$ ， $Q=G/H$ ， $q=|Q|$ 。令

$$K_H:=\prod_{\substack{C\in\operatorname{Conj}(G)\\C\subset H}}K_C,$$

并以  $\widetilde A_Q$  表示  $Q$ -正则斜积的邻接矩阵。对本原轨道  $\omega$ ，定义商群中的 holonomy 阶

$$q_H(\omega):=\operatorname{ord}_{Q}(g_\omega H).$$

定理 1（商覆盖精确分解）
在本文严格扭曲谱隙假设下，

$$\boxed{
K_H=
\left(\frac{e^{-\gamma_E}}{C(\widetilde A_Q)}\right)^{1/q}
\prod_{\substack{\omega\in\mathcal P\\q_H(\omega)>1}}
\left(1-\lambda^{-q_H(\omega)\ell(\omega)}\right)^{-1/q_H(\omega)} .
}
\tag{A}$$

其中无穷乘积绝对收敛。
第一因子恰为将本文式 (37) 中全部  $F_\rho(\lambda^{-1})$  错换为  $L_\rho(\lambda^{-1})$  后所得的 Artin 候选常数：

$$K_H^{\mathrm{Art}}
=
\left(\frac{e^{-\gamma_E}}{C(\widetilde A_Q)}\right)^{1/q}.
\tag{B}$$

因此

$$\boxed{
\log\frac{K_H}{K_H^{\mathrm{Art}}}
=
-\sum_{\substack{\omega\in\mathcal P\\q_H(\omega)>1}}
\frac{1}{q_H(\omega)}
\log\!\left(1-\lambda^{-q_H(\omega)\ell(\omega)}\right)>0
}
\tag{C}$$

只要存在一个  $g_\omega\notin H$  的本原轨道。
证明
标准正则表示分解给出

$$\det(I-z\widetilde A_Q)
=
\prod_{\sigma\in\operatorname{Irr}(Q)}
P_\sigma(z)^{\dim\sigma}.$$

在 Perron 径向端点取约化行列式，得到

$$\log C(\widetilde A_Q)
=
\log C(A)
+
\sum_{\sigma\ne\mathbf1}
(\dim\sigma)L_\sigma(\lambda^{-1}).$$

将其代入本文式 (37) 对所有  $C\subset H$  的和，立即得到 (B)。
另一方面，令  $\mathbf1_H$  为  $H$  的示性类函数。虽然
 $F_{\mathbf1_H}(\lambda^{-1})$  与  $L_{\mathbf1_H}(\lambda^{-1})$ 
分别发散，但径向差

$$\Delta_H
:=
\lim_{z\uparrow\lambda^{-1}}
\bigl(L_{\mathbf1_H}(z)-F_{\mathbf1_H}(z)\bigr)$$

绝对收敛。若  $g_\omega\in H$ ，则  $g_\omega^r\in H$  对所有  $r$  成立，该轨道对差值贡献为零。若  $g_\omega\notin H$ ，则

$$g_\omega^r\in H
\iff q_H(\omega)\mid r,$$

故其贡献为

$$\sum_{k\ge1}
\frac{\lambda^{-kq_H(\omega)\ell(\omega)}}{kq_H(\omega)}
=
-\frac1{q_H(\omega)}
\log\!\left(1-\lambda^{-q_H(\omega)\ell(\omega)}\right).$$

由于  $q_H(\omega)\ge2$ ，本原轨道数的  $O(\lambda^n/n)$  上界保证绝对收敛。又由本文的角色展开，

$$\log\frac{K_H}{K_H^{\mathrm{Art}}}=\Delta_H,$$

从而得到 (A)–(C)。证毕。
推论 1（普遍失效，而非偶然反例）
取  $H=\{e\}$ 。若  $G\neq\{e\}$ ，则严格扭曲谱隙蕴含存在非单位标签的本原轨道。因此

$$\boxed{
\frac{K_{\{e\}}}{K_{\{e\}}^{\mathrm{Art}}}
=
\prod_{\substack{\omega\in\mathcal P\\g_\omega\ne e}}
\left(
1-\lambda^{-\operatorname{ord}(g_\omega)\ell(\omega)}
\right)^{-1/\operatorname{ord}(g_\omega)}
>1.
}
\tag{D}$$

故旧 Artin 公式对单位 Frobenius 类不仅“有时失败”，而是在每一个非平凡、满足严格谱隙的有限群扩张中必然严格低估正确常数。
这一结论实质上取代了本文的  $S_3$  见证：无需寻找特殊符号表示或偶然消失的 Artin 通道。错误的几何本质是，覆盖空间 zeta 函数纳入了那些必须重复  $q_H(\omega)>1$  次才闭合的提升轨道，而固定标签乘积只选取立即完全分裂的轨道。标准图覆盖 Artin 分解可参见 Stark–Terras；式 (A) 中临界 Mertens 分裂因子并未见于该理论。
二、全部代数阶修正均为普适量
令  $\mathscr U\subseteq G$  为任意共轭不变子集，

$$\alpha_{\mathscr U}:=\frac{|\mathscr U|}{|G|},\qquad
P_{\mathscr U}(N):=
\prod_{\substack{\omega\in\mathcal P\\
                  \ell(\omega)\le N,\ g_\omega\in\mathscr U}}
\left(1-\lambda^{-\ell(\omega)}\right),$$

并令  $K_{\mathscr U}$  为相应常数。
设

$$\theta=\max_{\nu\in\operatorname{Spec}(A),\,\nu\ne\lambda}|\nu|,
\qquad
q_*=
\max\left\{
\frac{\theta}{\lambda},
\frac{\eta}{\lambda},
\lambda^{-1/2}
\right\}<1.$$

定理 2（调和正规化后的指数收敛）
对任意  $q_*<\xi<1$ ，

$$\boxed{
P_{\mathscr U}(N)
=
K_{\mathscr U}N^{-\alpha_{\mathscr U}}
\exp\!\left[
-\alpha_{\mathscr U}
\bigl(H_N-\log N-\gamma_E\bigr)
\right]
\bigl(1+O_\xi(\xi^N)\bigr).
}
\tag{E}$$

因此，除常数  $K_{\mathscr U}$  外，整个  $N^{-1}$  渐近展开完全不依赖底图、cocycle、群结构或所选共轭类；所有系统特异性在移除调和因子后均降为指数小量。
特别地，

$$\begin{aligned}
P_{\mathscr U}(N)
=K_{\mathscr U}N^{-\alpha_{\mathscr U}}
\Bigg[
1
&-\frac{\alpha_{\mathscr U}}{2N}
+\frac{\alpha_{\mathscr U}(3\alpha_{\mathscr U}+2)}{24N^2}\\
&-\frac{\alpha_{\mathscr U}^2(\alpha_{\mathscr U}+2)}{48N^3}
+O(N^{-4})
\Bigg].
\end{aligned}
\tag{F}$$

更一般地，其对数的全阶展开为

$$\boxed{
\log\frac{P_{\mathscr U}(N)N^{\alpha_{\mathscr U}}}
             {K_{\mathscr U}}
\sim
-\frac{\alpha_{\mathscr U}}{2N}
+
\alpha_{\mathscr U}
\sum_{j\ge1}
\frac{B_{2j}}{2j\,N^{2j}}.
}
\tag{G}$$

证明
记  $p_{n,\mathscr U}$  为长度  $n$ 、标签属于  $\mathscr U$  的本原轨道数，并置

$$a_n=p_{n,\mathscr U}\lambda^{-n}
-\frac{\alpha_{\mathscr U}}n,
\qquad
b_n=p_{n,\mathscr U}
\sum_{r\ge2}\frac{\lambda^{-rn}}r.$$

本文估计 (33)–(34) 与标量 Möbius 公式共同给出

$$a_n=O_\xi(\xi^n),\qquad
b_n=O(\lambda^{-n}/n).$$

由乘积定义及常数定义可得精确恒等式

$$\log\frac{P_{\mathscr U}(N)N^{\alpha_{\mathscr U}}}
             {K_{\mathscr U}}
=
-\alpha_{\mathscr U}
(H_N-\log N-\gamma_E)
+
\sum_{n>N}(a_n+b_n).$$

尾和为  $O_\xi(\xi^N)$ ，从而得到 (E)。将标准 Euler–Maclaurin 展开

$$H_N-\log N-\gamma_E
\sim
\frac1{2N}
-\sum_{j\ge1}\frac{B_{2j}}{2jN^{2j}}$$

代入即得 (F)–(G)。证毕。
公开的 sofic-shift 轨道增长结果给出的是首阶 Mertens 渐近与抽象常数，而没有上述“精确调和因子＋指数余项”的结论，参见 Nordin–Noorani–Mohd。
三、Frobenius 常数向量的 Fourier 刚性
令  $\operatorname{Conj}(G)$  为共轭类集合，并取  $c_C\in C$ 。记

$$S_A:=\gamma_E+\log C(A),\qquad
F_\rho:=F_{\chi_\rho}(\lambda^{-1}).$$

定理 3（常数—固定标签坐标的精确反演）
本文式 (37) 的逆变换为

$$\boxed{
S_A=-\sum_{C\in\operatorname{Conj}(G)}\log K_C,
}
\tag{H}$$

以及对每个非平凡不可约表示  $\rho$ ，

$$\boxed{
F_\rho
=
-\sum_{C\in\operatorname{Conj}(G)}
\chi_\rho(c_C)\log K_C.
}
\tag{I}$$

证明仅需将式 (37) 乘以  $\chi_\rho(c_C)$ ，对共轭类求和，并使用角色表的行正交关系。
由此立即得到两个结构性推论：

$$\boxed{
\prod_{C\in\operatorname{Conj}(G)}K_C
=
\frac{e^{-\gamma_E}}{C(A)}.
}
\tag{J}$$

该乘积完全独立于 cocycle；全部 Frobenius 类常数中的非平凡群信息严格相互抵消。
其次，对同一底图上的两个严格谱隙 cocycle  $\tau,\tau'$ ，

$$K_C^\tau=K_C^{\tau'}\quad\forall C
\iff
F_\rho^\tau=F_\rho^{\tau'}\quad\forall\rho\ne\mathbf1.
\tag{K}$$

因此，Frobenius Mertens 常数向量既不只是若干孤立常数，也不编码完整周期数据；它恰好是 Perron 边界处固定标签坐标的角色 Fourier 变换。这与 Boyle–Schmieding 所研究的完整周期数据不变量形成严格层级关系；后者确实能够区分远多于单点边界坐标的信息，Boyle–Schmieding。
发表价值判断
上述结果中：


定理 1 与推论 1 为最高价值结论。它们把本文目前的“显式  $S_3$  反例”提升为适用于所有非平凡严格谱隙扩张的普遍不可能性定理，并给出缺失因子的覆盖几何解释。


定理 2 显著强化主定理的  $1+O(N^{-1})$ ：整个代数阶渐近 jet 均为普适 Bernoulli 多项式，系统依赖仅存在于  $K_{\mathscr U}$  与指数小余项中。


定理 3 给出常数族的完整可逆结构及 cocycle 无关守恒律，适合作为新的结构定理，而非附带计算。


截至 2026 年 8 月 3 日，在本文参考文献、有限群扩张周期数据文献、图覆盖 Artin-zeta 文献及可检索的 dynamical Mertens 文献中，未发现 (A)、(D)、(E) 或 (I) 的同式陈述。最稳妥的论文改写方式，是以定理 1 取代“单一  $S_3$  反例”作为第二主定理，以定理 2 作为主渐近定理的强化，并将定理 3 作为常数空间的 Fourier 刚性部分。