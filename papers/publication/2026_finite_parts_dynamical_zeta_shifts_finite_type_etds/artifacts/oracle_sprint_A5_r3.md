A: 经逐式推导与文献排查，本文框架中至少蕴含三项未被稿件识别、具有独立发表价值的结论。其中最重要者将“存在一个  $S_3$  反例”提升为：对于任何非平凡且满足严格扭曲谱隙的有限群扩张，旧 Artin 常数在单位 Frobenius 类上必然错误，并且误差具有正的、完全显式的覆盖轨道乘积。
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
A: 经逐式推导与文献排查，本文框架中至少蕴含三项未被稿件识别、具有独立发表价值的结论。其中最重要者将“存在一个  $S_3$  反例”提升为：对于任何非平凡且满足严格扭曲谱隙的有限群扩张，旧 Artin 常数在单位 Frobenius 类上必然错误，并且误差具有正的、完全显式的覆盖轨道乘积。
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
A: 结论：在现行假设下，完整碰撞核不能无条件刻画为 Mahler coboundary 子群；同时，现有文献亦未提供满足全部可实现性条件的非 coboundary 碰撞。严格可证明的是“有限有理 Mahler 证书”的完备正规形，而把该正规形提升为全部数值碰撞的分类，等价于一个目前尚未解决的临界非线性 Mahler 特殊值提升问题。因此，不得在稿件中断言完整核分类成立，也不得把“尚无反例”写成肯定结论。
1. 可实现边界群与精确可实现性条件
设  $A$  为原始非负整数底图矩阵， $\lambda=\rho(A)$ ， $x=\lambda^{-1}$ 。对  $C_{2}$  cocycle，非平凡角色块  $B=A_{\varepsilon,\tau}$  可实现于底图  $A$  当且仅当

$$B\in M_d(\mathbb Z),\qquad
B_{uv}\equiv A_{uv}\pmod 2,\qquad
|B_{uv}|\le A_{uv},$$

因为此时

$$A_{+,uv}=\frac{A_{uv}+B_{uv}}2,\qquad
A_{-,uv}=\frac{A_{uv}-B_{uv}}2$$

恰为两类标签边的非负整数重数。故一对同底图 cocycle 对应于

$$B\equiv B'\equiv A\pmod2,\qquad |B|,|B'|\le A$$

以及严格谱隙

$$\rho(B),\rho(B')<\lambda .$$

这给出兼容性的必要充分条件，而非附加的谱多项式条件。令

$$H(z)=\frac{P_\tau(z)}{P_{\tau'}(z)}
 =\frac{\det(I-zB)}{\det(I-zB')}.$$

严格谱隙保证  $P_\tau(t),P_{\tau'}(t)>0$  对  $0\le t\le x$  成立。定义

$$\Pi_x(H)
 :=\prod_{j\ge0}H(x^{2^j})^{2^{-j}}
 =\exp\!\bigl(-\mathscr B_x(H)\bigr).$$

则边界碰撞等价于  $\Pi_x(H)=1$ 。
2. 有限 Mahler 证书的唯一正规形
令

$$\sigma R(z):=R(z^2),\qquad
\delta R:=\frac{\sigma R}{R^2}
          =\frac{R(z^2)}{R(z)^2}.$$

定理（有限有理 Mahler 证书正规形）
设  $H\in\mathbb Q(z)^\times$ 、 $H(0)=1$ ，且  $H>0$  于  $[0,x]$ 。下列条件等价：


 $H$  具有由有限次二进制 Mahler coboundary、公共行列式因子消去、零块稳定化及有理函数恒等式组成的边界碰撞证书；


存在唯一的  $R\in\mathbb Q(z)^\times$  使

$$R(0)=1,\qquad
H(z)=\frac{R(z^2)}{R(z)^2},\qquad
R(x)=1.$$



此外，允许  $R$  具有代数系数不会扩大证书类。
证明。
首先，对任意  $R(0)=1$ ，有限截断严格望远镜化为

$$\begin{aligned}
\prod_{j=0}^{N}
\left(
 \frac{R(x^{2^{j+1}})}
      {R(x^{2^j})^2}
\right)^{2^{-j}}
&=
\frac{R(x^{2^{N+1}})^{2^{-N}}}{R(x)^2}.
\end{aligned}$$

由于  $R(x^{2^{N+1}})\to R(0)=1$ ，故

$$\Pi_x(\delta R)=R(x)^{-2},\qquad
\mathscr B_x(\delta R)=2\log R(x).$$

若  $\delta R=H>0$  于  $[0,x]$ ，则  $R$  在该区间不得有零点或极点：若  $R(t_0)=0$ ，恒等式迫使  $R(t_0^2)=0$ ，迭代后零点聚于  $0$ ，与  $R(0)=1$  矛盾；极点同理。因此  $R>0$ ，碰撞条件恰为  $R(x)=1$ 。
其次，

$$\prod_{i=1}^{s}(\delta R_i)^{e_i}
  =\delta\!\left(\prod_{i=1}^{s}R_i^{e_i}\right),$$

故有限个 coboundary 不产生更大的生成类；公共行列式因子、相似变换和零块稳定化在  $H=P_\tau/P_{\tau'}$  中均消去。
最后， $\delta$  在  $R(0)=1$  的有理函数群上单射。若  $\delta U=1$ ，则

$$U(z^2)=U(z)^2.$$

若  $U(z)=1+a z^n+O(z^{n+1})$  且  $a\ne0$ 、 $n$  最小，则左端最低非零项次数为  $2n$ ，右端最低非零项为  $2az^n$ ，矛盾；故  $U=1$ 。唯一性随即成立。
若  $R\in\overline{\mathbb Q}(z)$ 、 $\delta R=H\in\mathbb Q(z)$ ，则对任意
 $\gamma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ ，

$$\delta(\gamma R/R)=1,\qquad (\gamma R/R)(0)=1.$$

由单射性得  $\gamma R=R$ ，故  $R\in\mathbb Q(z)$ 。证毕。
因此，一个完整的有限证书只需列出

$$(A,B,B',R)$$

并精确核验：

$$B\equiv B'\equiv A\pmod2,\quad |B|,|B'|\le A,$$


$$P_\tau(z)R(z)^2=P_{\tau'}(z)R(z^2),
\qquad R(x)=1,$$

再附上  $A$  的 Perron 根隔离证书及  $B,B'$  的严格谱隙证书。所有核验均为有限代数运算。
3. 为何这不是完整碰撞核定理
令

$$\mathcal C_x
 :=
 \left\{
 \delta R:
 R\in\mathbb Q(z)^\times,\ R(0)=1,\ R(x)=1
 \right\}.$$

上述定理只给出

$$\mathcal C_x
\subseteq
\ker \Pi_x.$$

把包含关系提升为等号，需要证明如下特殊值提升命题：

若  $H\in\mathbb Q(z)^\times$  且

$$F_H(x):=\prod_{j\ge0}H(x^{2^j})^{2^{-j}}=1,$$

则该单点代数关系必由函数层关系
 $H=\delta R$  提升而来。

该函数满足临界非线性 Mahler 方程

$$F_H(z)^2=H(z)^2F_H(z^2).$$

现有 Adamczewski–Faverjon 提升定理针对线性正则奇异 Mahler 系统，不能直接作用于此 Kummer 型非线性方程；其适用对象与提升机制见 Mahler’s method in several variables II。Greuel 对隐式 Mahler 方程给出了特殊值代数独立性准则，但其次数不等式在这里的临界配置

$$d=2,\qquad \deg_Y\!\bigl(Y^2-H(z)^2U\bigr)=2$$

恰好不成立，参见 Greuel, Acta Arith. 93 (2000)。
此困难在可实现子类中已经出现。取奇数  $a$ ，令底图矩阵的对角元为  $a$ 、非对角元为同一正偶数；其 Perron 根为整数。对两组奇整数  $c_i,d_i$ ，可取

$$B=\operatorname{diag}(c_1,\ldots,c_r),\qquad
B'=\operatorname{diag}(d_1,\ldots,d_r),$$

从而在同一原始底图上得到

$$P_\tau(z)=\prod_i(1-c_i z),\qquad
P_{\tau'}(z)=\prod_i(1-d_i z).$$

故完整核分类已经包含对数值

$$E_c(x):=\prod_{j\ge0}(1-cx^{2^j})^{2^{-j}},
\qquad
E_c(z)^2=(1-cz)^2E_c(z^2)$$

之间全部乘法关系的分类。该问题不因同底图兼容性而消失。
Kubota 的经典结果处理通常的无权 Mahler 乘积，见 Kubota 1975–76。2025 年的一篇预印本对

$$T_p(z)=\prod_{j\ge1}(1-z^{p^j})^{-1/p^j}$$

主张了单个代数点值的超越性，但同时明确指出一般非线性多参数依赖缺乏零估计；它并未给出任意  $P/P'$  的乘法关系分类，参见 Lam, arXiv:2512.14077。因此即使接受该预印本的单值结论，也不能推出  $\ker\Pi_x=\mathcal C_x$ 。
动力系统与增益图谱文献同样不提供这一缺失步骤。Boyle–Schmieding 处理完整周期数据及有限群扩张的不变量，其论文并不分类单个 Perron 边界特殊值；Cavaleri–Donno 的 represented  $G$ -cospectrality 等价定理涉及全部表示谱，其论文亦不能将一个标量边界等式提升为完整扭曲行列式等式。Stark–Terras 的 Artin–Ihara 分解属于完整覆盖 zeta 的行列式分解背景，而非上述非线性特殊值核定理。
4. 可写入稿件的最终边界
截至 2026 年 8 月 3 日，可无条件写入的最强结论为：

$$\boxed{
\ker_{\mathrm{finite\ Mahler\ cert}}\Pi_x
=
\left\{
\frac{R(z^2)}{R(z)^2}:
R\in\mathbb Q(z)^\times,\ R(0)=R(x)=1
\right\},
}$$

并与矩阵条件

$$B\equiv B'\equiv A\pmod2,\qquad
|B|,|B'|\le A,\qquad
\rho(B),\rho(B')<\rho(A)$$

取交得到同底图可实现证书类。
不得把它升级为实际数值核的必要充分分类。实际等号

$$\ker\Pi_x=\mathcal C_x$$

目前是一个临界非线性 Mahler 特殊值提升问题；现阶段既无完整证明，也无满足题设全部条件的已认证非 coboundary 反例。强行选择题设所要求的“是”或“否”之一，都会超出现有证明。
