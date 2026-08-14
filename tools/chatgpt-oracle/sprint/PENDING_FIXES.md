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

**未能独立核实，引用前必须自行确认**：

- **Bickel–Kwon**(known-marginal Markov tangent 与 additive projection)。
  Crossref、OpenAlex、Semantic Scholar、DBLP 四处均查不到。推测为
  Statistica Sinica 2001 年那篇(该刊早期卷次 Crossref 收录很差),但**这是推测,
  不是核实**。审稿人称漏引它是本轮优先权审计最重要的发现,所以这条**不能凭印象
  著录** —— 必须先确认确切出处(刊名、卷、页、年)与定理内容,再写进论文。
  若无法确认,宁可在正文中以"据审稿意见指出的先验结果"方式谨慎处理,也不要
  编造一条参考文献。
- **He–Zhang** 的 generalized-Erlang / Coxian 理论,同样尚未核实。
