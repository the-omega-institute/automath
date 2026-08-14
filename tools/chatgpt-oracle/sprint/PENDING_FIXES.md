# 待修（独立核实所得，按论文分列）

每条都已对 Crossref 记录核实过，含 DOI。修完删除对应条目。

## A5 `finite_parts` — Nishioka 是两个人，我们当成了一个

`references.bib` 把两条都写作 `K.~Nishioka`，正文又以单数指称
（"Nishioka's special-value **and** algebraic-solution rationality theorems"、
"both Nishioka theorems"）。实际是两位不同的数学家：

| 键 | 真实作者 | 出处 | DOI |
|---|---|---|---|
| `Nishioka1982MahlerFunctionValues` | **Kumiko** Nishioka | J. Austral. Math. Soc. Ser. A **33**(3) (1982) 386–393 | `10.1017/S1446788700018814` |
| `Nishioka1985AlgebraicSolutions` | **Keiji** Nishioka | Arch. Math. (Basel) **44** (1985) 330–335 | `10.1007/BF01235775` |

Keiji Nishioka 另有 Nagoya Math. J. **109** (1988) 63–67 的 Painlevé 论文
（`10.1017/S0027763000002762`），确认与 Kumiko 非同一人。

期刊、卷、页码我们写的都对，错的只有作者身份与正文的单数指称。

**为什么要紧**：这正是审稿人要求我们让出优先权的那一处。Mahler 理论方向的审稿人
一眼就能看出把 Kumiko 与 Keiji 混为一人。审稿人自己的报告也只写了 "K. Nishioka
1985"，所以他没纠正我们——这处得我们自己发现。

需改：`references.bib` 两条 author 字段；`main.tex` 88–89、135–137；
`sec_inverse_introduction.tex` 90–93、207–211、232–236；
`sec_inverse_conclusion.tex` 30；`sec_refocused_boundary_collisions_part1.tex`
256、385–397、456–457、484；`artifacts/literature_check.md`。
正文须分别称 "Kumiko Nishioka" 与 "Keiji Nishioka"，不得再出现
"both Nishioka theorems" 这类合指写法。

## A6 `zeckendorf_fibers` — 引文年份与出处（供修复 agent 采用）

审稿人据以否定我们优先权的四条，均已核实存在且内容相符：

- Sidorov & Vershik, *Ergodic properties of the Erdős measure, the entropy of the
  goldenshift, and related problems*, Monatsh. Math. **126**(3) (1998) 215–261,
  `10.1007/BF01367764`。摘要确载 "we study central measures on the **Fibonacci
  graph**"，与"$f_m(k)$ 即 Fibonacci graph 顶点频数"的说法相符。
- Lau–Ngai 有多篇相关工作，A6 实际引的是
  *$L^q$-spectrum of the Bernoulli convolution associated with the golden ratio*,
  Studia Math. **131** (1998), no. 3, 225–251 —— 标题即审稿人所指内容，选得比我
  先前找到的那篇更贴切。**先前那条"1998 与 1999 年份不符"的提醒作废**：它针对的是
  另一篇 *Multifractal Measures and a Weak Separation Condition*,
  Adv. Math. **141** (1999) 45–96, `10.1006/aima.1998.1773`，与 A6 所引不是同一篇，
  后续 agent 不要据此去"订正"一个本来正确的引用。
  Studia Math. 131 那条我未能在 Crossref / Google Scholar 独立确认（该刊 2000 年前
  卷次 DOI 收录很差），但同作者相邻工作确实存在，例如
  *$L^q$-spectrum of Bernoulli convolutions associated with P.V. numbers*,
  Osaka J. Math. **36**(4) (1999)。定稿前值得再核一次页码。
- Feng & Olivier, *Multifractal analysis of weak Gibbs measures and phase
  transition—application to some Bernoulli convolutions*, Ergodic Theory Dynam.
  Systems **23**(6) (2003) 1751–1784, `10.1017/S0143385703000051`。
- Feng, *The limited Rademacher functions and Bernoulli convolutions associated
  with Pisot numbers*, Adv. Math. **195**(1) (2005) 24–101,
  `10.1016/j.aim.2004.06.011`。

Hu 那条（TAMS，黄金分割 Bernoulli 卷积的局部维数）尚未独立核实，引用前须补。

## A8 `detector_shells` — 审稿人指认的三条先验工作，独立核实结果

**核实通过，但审稿人的署名不全**：

- Ramírez-Cobo, Lillo **& Wiper**, *Nonidentifiability of the Two-State Markovian
  Arrival Process*, J. Appl. Probab. **47**(3) (2010) 630–649,
  `10.1239/jap/1285335400`。审稿人写作"Ramírez-Cobo–Lillo",**漏了 Wiper**,著录时
  须补上。该文主题正是 MAP$_2$ 的不可识别性,与我们的二态 fibre 弧直接同域,
  确属必须逐式比较的对象。
  注意 Crossref 有两条 DOI 指向同一篇(另一条 `10.1017/s0021900200006975`),
  以 `10.1239/jap/1285335400` 为准。
  同组另有 *Identifiability of the MAP$_2$/G/1 queueing system*, TOP **22**(1)
  (2014) 274–289, `10.1007/s11750-012-0254-8`,以及 *Bayesian Analysis of the
  Stationary MAP$_2$*, Bayesian Anal. **12**(4) (2017), `10.1214/16-ba1026`。

**已了结**：Wiper 署名已补入 `RamirezCoboLilloWiper2010MAP2Nonidentifiability`。

**Bickel–Kwon 已核实（此前四处索引查不到）**：Google Scholar 经 JSTOR
`stable/24306883` 收录，P. J. Bickel 与 J. Kwon，*Inference for semiparametric models:
some questions and an answer*，2001，摘要与所述内容相符；另有 McNeney–Wellner 的
Comments 篇，符合 Statistica Sinica 讨论稿体例，也印证 863–960 这一长跨页码。
A8 现引作 Statistica Sinica **11**, 863–960 (2001)，**属实，非杜撰**。
教训记下：Crossref/OpenAlex/Semantic/DBLP 全查不到，不等于文献不存在——
Statistica Sinica 2000 年前后卷次这四处收录都很差，须改用 Google Scholar 或 JSTOR 复核。

- **He–Zhang** 的 generalized-Erlang / Coxian 理论仍未核实，引用前须确认。

## A9 `homological_visibility` — Giraud 遗漏的确切位置（已定位到行）

审稿人称我们漏了一条**定理层级**的先例。核实结果：**不是没引 Giraud，是引错了章**。

`references.bib:230` 的 `Giraud1971` 条目本身正确（Jean Giraud, *Cohomologie non
abélienne*, Grundlehren der math. Wiss. **179**, Springer-Verlag, 1971），书名法文
变音符缺失（`abelienne` → `abélienne`）可顺手补。

问题在于全文**只引 `[Chap.~IV]`**（banded gerbe 按 $H^2$ 的**分类**），而审稿人指出
所缺的是 **Chap. III, Prop. 2.1.5.3** 的**构造**：对任意 stack $S$，投影
$S	o\pi_0(S)$ 使其成为其连通分支层上的 gerbe，沿 $\pi_0(S)$ 的截面拉回即得相应的
极大子 gerbe。这正是 Theorems 4.8(i) 与 4.9 的结构内容。

**最该动的一行**：`sec_gerbe_obstruction.tex:349` ——

> Thus any two objects of $\mathfrak E_r[v](U)$ are locally isomorphic. The full
> substack $\mathfrak E_r[v]$ is therefore a gerbe \cite[Chap.~IV]{Giraud1971},
> \cite[Tag 06NY]{StacksProject}.

此处手工验证了局部同构再引 Chap. IV 的分类，而 III.2.1.5.3 直接给出该构造。
其余 `[Chap.~IV]` 引用点：`sec_gerbe_obstruction.tex` 的 17、227、365、647，
`sec_homological_visibility_intrinsic.tex:533`，`sec_introduction.tex:30`。

审稿人给出的最小修复原文（置于 Theorem 4.8 之前）：

> By Giraud III.2.1.5.3, $E	o\pi_0(E)$ is a gerbe over its component sheaf, and the
> pullback along a section is the corresponding maximal subgerbe. The following theorem
> records this standard construction together with the compatibility needed for our
> later presheaf comparison.

他同时明确：$v\mapsto[E[v]]$ 这个打包**有用但不是新的构造原理**。
另外他说未找到把那条两标签 wedge 分类逐字发表过的定理，但**这不构成实质优先权**——
由标准等价复合出来的精确陈述可以形式上是新的，而几乎没有独立的数学优先权。

## A5 — Keiji Nishioka 1985 核验:缺口已收窄,但未闭合

原文仍拿不到(Springer 将 Arch. Math. **44**, 330–335 置于订阅墙后,Unpaywall
无 OA 副本;未走盗版站点)。但找到一份**开放获取且可逐字核对**的相邻权威陈述,
足以厘清该引哪一条:

Bell, Coons & Rowland, *The rational–transcendental dichotomy of Mahler functions*,
arXiv:1210.2070v2,**Corollary 8**:

> Let $k\ge2$ and $F(z)\in\mathbb C[[z]]$ be a $k$-Mahler function. If $F(z)$ is
> algebraic, then $F(z)$ is a rational function.

其出处标为 **Ku. Nishioka**, *Mahler Functions and Transcendence*, Lecture Notes in
Mathematics **1631**, Springer-Verlag, 1996, **Theorem 5.1.7**。

**"Ku." 即 Kumiko** —— 该领域文献用 "Ku. Nishioka" 与 "Ke. Nishioka" 区分二人,
这个书写惯例我们也该采用。

**关键限制,不可含糊**:Corollary 8 针对的是 $k$-Mahler 函数,即由**线性**方程
$\sum_j a_j(z)F(z^{k^j})=0$ 定义者。我们的方程
$$F(z^2)=H(z)^{-1}F(z)^2$$
**关于 $F$ 是二次的,非线性**,故 Kumiko 的 Theorem 5.1.7 **不覆盖我们这一步**。
反过来,这恰好**佐证 Keiji 才是正确署名**:他 1985 年那篇处理的类
$f(z^p)=\mathscr R(z,f(z))$($\mathscr R$ 有理)正是非线性类,与我们的形式吻合;
审稿人说 Ostrowski 1968 只处理线性乘性方程,也与此一致。

**结论**:Keiji 1985 仍是承重且仍未核验,**不能用 Bell–Coons–Rowland 顶替**。
但应在正文补上 Ku. Nishioka LNM 1631 Thm 5.1.7 作为线性情形的标准对照,并明写
我们的方程非线性、故线性定理不适用 —— 这既堵住审稿人"为何不直接引标准 Nishioka
定理"的追问,也把两位 Nishioka 的分工讲清楚。已据此派 agent。
