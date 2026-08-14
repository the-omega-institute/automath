外审意见
稿件： Visible renewal laws and quotient inversion for a killed-leakage sampled-counter D-MAP
目标期刊： Journal of Physics Communications
建议： 拒稿；经实质性重构、重新核定优先权并补全关键证明后，可作为新稿另行投稿。
这里的拒稿建议并非基于“结果层级不够高”。Journal of Physics Communications 明确不以预期影响力或主观新颖程度筛选稿件，而以科学有效性、方法严谨性及对物理知识的贡献为标准；Research Paper 亦无篇幅上限。IOPscience - Publishing Support 当前障碍是三项合取：


稿件中存在一组可修复但尚未修复的证明缺口，尤其集中于统一检验、移动维数 Gaussian coupling 及奇异似然实验；


优先权叙述遗漏了至少两组会改变原创性边界的直接先验工作；


现稿的主体实际上是应用概率、realization theory 与渐近统计，而 sampled-counter 的物理实现目前主要充当模型解释，而非被分析、验证或比较的物理系统。


我没有发现足以直接推翻记录律、三坐标商逆或二态 fibre 弧的反例。因而，这不是“核心公式明显错误”的拒稿，而是“整篇稿件尚未达到其当前声称的完整性和优先权标准”的拒稿。

1. 数学正确性
1.1 总体判断
下列部分在现有契约下原则上成立，经过局部补证即可达到发表标准：


killed-reset 导致的更新结构、Palm gap 公式及单模协方差；


三个 inclusion probabilities 到 (p+s,ps) 的商逆；


二态 reset-preserving similarity fibre 的显式弧；


纯串联模型中无序率多重集的可识别性；


最小内点相似轨道的 (n−1)2 维数；


固定维数的 regenerative CLT 与 separated-root delta method。


但下列更强部分目前只能视为可信的证明纲要，尚不能作为完整定理接受：


OP​(N−1/3) 的 stopped separated-batch 协方差估计；


compact-uniform physical-image test；


complete-visible-law test 的 uniform null calibration；


Markov–Palm 路径的完整 stationary-record likelihood 展开；


Helmert 层的“充要”Gaussian coupling 边界；


奇异交换实验的完整 stationary-record likelihood 结论。


此外，稿件的主定理编号与依赖图存在正式上的不可接受矛盾。

1.2 Blocker：主定理编号和依赖关系不一致
稿件前部声明 C 是 retained-record CLT、D 是 delta method、E 是 projection example，并称全文有“五个 paper-level theorems A–E”。 
但正文实际安排为：


Theorem D：complete visible-law specification test；


Theorem E：quotient delta method；


Theorem F：projection example。


证明末尾又回到“A–D 加 E projection”的旧依赖图。 这不仅是排版问题，因为“哪些是 paper-level original theorems”“哪些统计结论依赖哪些前件”以及 priority comparison 均由该编号体系组织。
解除异议所需修改：


建立一张唯一、权威的 theorem registry；


全文统一主定理编号、摘要、引言、证明、related work、supplement 和代码测试名称；


给出一张依赖图，明确 population algebra、fixed-setting inference、specification tests、tangent analysis 和 singular experiment 的逻辑顺序；


不应通过简单重命名掩盖版本混合，应逐一核对公式引用和假设传递。


在此问题解决前，正式审稿无法准确判断作者究竟请求接受哪一组定理。

1.3 Theorem A：核心结论可信，但证明中有一处错误陈述，且 Markov 性结论应改引已有判据
Theorem A 的 regeneration 论证是成立的：T1​=ceD⊤​ 使每次 click 后隐藏状态确定为 D，从而 Palm gaps 为独立同分布。主定理陈述见 。
然而证明称 “The entries of T0​ are strictly positive”。这在模型定义下为假，因为 T0​(R,D)=0 是结构性零。 该错误不推翻 gk​>0，但现有理由错误。
正确修复应直接证明：从 post-click 状态 D 出发，对每个 k≥0，存在具有正概率的长度 k 零路径，且随后 click 的概率为正；或者直接从闭式 gk​ 及其等速极限证明严格正性。
“任何正参数下均非有限阶 Markov 链”的结论也正确，但其一般结构依据并非新发现：对 stationary renewal binary sequence，有限阶 Markov 性等价于 gap tail 最终几何，即 hazard 最终常数；Zamparo 已给出这一判据。巴里大学 稿件只需将严格递增 hazard 代入该已有判据，而不宜将这一推理呈现为独立的一般性发现。
解除异议所需修改：


删除 T0​>0 的错误句；


加入独立的 gk​>0 引理，包括 Γ=κr​；


将“非有限阶 Markov”明确写成 Zamparo 判据的模型专门化；


明确区分：


新的模型闭式 hazard；


已有的 renewal-to-Markov 判据；


两者结合所得的推论。




单模 covariance 公式及 λhid​=0 与 exact 1-dependence 的等价在该二态核中可以成立；但一般 MAP2 的几何衰减和相关符号恒定或交替已有直接先例，Ramírez-Cobo–Carrizosa 已系统研究这一结构。Project Euclid+1 因而原创部分是该 sampled-counter 子族中的显式系数、阈值和物理参数表达式，而不是“MAP2 correlation is geometric”本身。

1.4 Theorem B 与三坐标物理像：代数正确性较强，但 sufficiency 证明省略了关键正性引理
商逆
a=r0​r1​​,λ=r1​−r02​r2​−r02​​,Φ(r)=(p+s,ps)
与正文推导相符。 在正 sampled-counter 模型内，
r1​−r02​=ρ(a−ρ)<0,
故 inverse denominator 实际不会退化。建议区分：


“物理模型内的全局非退化”；


“为离像点和统计邻域定义的 rational chart 条件”。


Proposition 1.6 的必要性没有明显问题。但 sufficiency 部分由 E(r)=0 直接宣称
b=C(p,s)−s,a=1−C(p,s)
是“precisely the strictly positive integral weights”。 这一步承担了整个 “if and only if”，不能仅以“precisely”带过。尤其需要证明：
b>0,a>0,a+b+s=1
对任意 p,s∈(0,1) 成立，并处理 p=s 的连续极限。
解除异议所需修改：
加入一个完整引理。令 x=−logp、y=−logs，证明
b=y−xy(p−s)​=y∫01​e−yt−x(1−t)dt>0,
并由原始积分表示证明
a=∫01​ye−yt(1−e−x(1−t))dt>0.
对角线应通过积分或显式极限单独给出，而非仅写“continuous interpretation”。
Proposition 1.7 还应补一个定量邻域引理：在紧物理像的足够小邻域 U 内，
D≥0
不仅保证二次根为实数，还保证二根均严格落在 (0,1)。目前正文仅以 compactness 一句处理。 这在局部上应当可证，但必须给出距 {0,1} 的统一 margin。

1.5 二态 fibre 弧：证明基本成立，但需排除“已知 weak-equivalence 公式的直接代入”
Theorem 3.2 从
G2​={(q0​1−q1​):q=0}
出发，计算完整 similarity orbit 与 substochastic cone 的交，继而得到 q∈I∗​。该证明链在代数上连贯；特别是由 upper-right entry 决定的区间条件以及 killing deficits 的正性检查是足够具体的。
但“完整 fibre”需要再补一项技术说明：由同一可见律推出比较核 L 也是 rank-two minimal 的论证，目前借 leading Hankel factorization 一句完成。应明确写出哪一个 2×2 Hankel minor 非零，以及为什么所有同律 L 均共享该非零 minor。
更重要的是，Ramírez-Cobo–Lillo 已给出 weakly equivalent MAP2 的完整刻画，而 Mészáros–Telek 已建立离散 order-two DMAP/DRAP 的 canonical representation。IDEAS/RePEc+1 因此必须判断当前 K(q) 是否只是这些通式在 deterministic-reset 约束下的直接代入。
解除异议所需修改：


将 Ramírez-Cobo–Lillo 的 weak-equivalence 参数化或 canonical coordinates 显式写出；


代入本文 reset constraints；


逐项比较其自由参数与 q；


说明闭区间 I∗​、strict positivity、仅有两个 triangular endpoints 以及 diagonal collapse 中，哪些未由先验公式直接给出。


若 K(q) 可由已有 weak-equivalence 公式一行代入得到，则 Theorem 3.2 应降格为“explicit cone-intersection corollary”；原创点应限定为：


Markovian admissible interval 的精确求交；


两个 physical rate-swapped endpoints；


interior nontriangular positivity；


diagonal singleton criterion。



1.6 纯串联 n 态识别：结论正确，但当前原创性措辞高于证明内容
对于纯串联 generator，吸收时间是独立指数变量之和；Laplace transform 的极点及重数决定无序率多重集。采样后，Palm tail 为 confluent exponential polynomial，前 2n 个 tail coordinates 通过 Hankel recurrence 恢复 annihilator。正文证明对此是充分的。
需要修正的是定位。generalized Erlang、Coxian minimal representations、重复实极点、triangular order 及等价表示已有广泛理论。He–Zhang 特别研究了 generalized Erlang 的 minimal Coxian representations，并明确处理最小表示和重复极点所对应的结构。滑铁卢大学工程系
因此：


“无序率多重集由完整分布识别”本质上是 classical generalized-Erlang factorization；


“重复率不破坏 population identifiability”也是极点重数理论的直接结果；


可能仍属本文新增的是：由离散 sampled Palm tails 的前 2n 项作有限坐标恢复，以及将其明确置入 killed-reset D-MAP visible-law 语言。


解除异议所需修改：
将 Corollary 3.3 重写为：

generalized-Erlang identifiability 与 confluent Prony recurrence 在 sampled killed-reset visible law 中的有限-coordinate corollary。

并补引至少：


Cumani 的 failure-time canonical representation；


O’Cinneide 的 PH nonuniqueness/invariant-polytope 工作；


He–Zhang 关于 minimal Coxian/generalized Erlang representations 的工作；


如声称 discrete-specific novelty，则说明 continuous PH 文献为何没有直接给出“前 2n 个 sampled tails”这一有限数据陈述。



1.7 内部 fibre 的 (n−1)2 维数：证明正确，但只是一项简洁的 Lie-orbit 推论
Theorem 3.4 的维数计算
gn​={B:B1=0, en⊤​B=0},dimgn​=(n−1)2
正确。由 reachability 证明 [K,B]=0⇒B=0，继而得到 orbit map 微分单射，也正确。严格 positivity 由开性保持。
但该结果是经典 minimal-realization similarity orbit 在 reset-preserving subgroup 上的直接有限维计算。Telek–Horváth 已将 MAP minimal representation 的参数冗余和 stationary-behaviour equivalence 作为中心问题处理。Roundcube Webmail
解除异议所需修改：


不再称其为“higher-state identifiability theorem”的主要突破；


改称“quantitative local orbit-dimension corollary”；


明确“dimension exactly”指的是 minimal fibre 的局部 orbit，而非对非最小表示、cone boundary strata 或所有 augmentations 的全局 fibre 维数；


将标准 similarity theorem 与本文唯一新增的 subgroup dimension/positivity calculation 分开陈述。



1.8 Theorem C：CLT 可信；OP​(N−1/3) 协方差率需要独立的 stopped-prefix 定理
Theorem C 的 reward
Yj​=Uj​−rLj​
依赖 (Gj​,Gj+1​)，因此为 1-dependent；随机 renewal count 替换和端点删除在指数矩下应给出所述 CLT。
问题集中在 Lemma 1.10。证明先对确定 prefix 的 separated blocks 使用独立性，再迅速替换为随机 MN​ 和 KN​。  当前论证尚未明确控制：


停止索引与最后一个 block 的依赖；


随机 MN​ 的矩阵平均相对确定 block count 的误差；


plug-in centering 与随机 block lengths 的交叉项；


uniform version 中所有常数对 θ 的共同可控性；


“operator norm”结论与逐 entry maximal inequality 之间的固定维数依赖。


这些问题在 d=3 时大概率可解决，但需要正式引理。
解除异议所需修改：
给出一个 standalone stopped independent-block lemma，明确：


filtration；


stopping index；


deterministic bracketing；


overshoot 和 incomplete block 的界；


plug-in perturbation 的矩阵范数估计；


点态版与 compact-uniform 版。


在没有该引理前，OP​(N−1/3) 不应作为已完整证明的 rate theorem 使用。

1.9 Physical-image test：点态极限可信，compact-uniform size 证明需要更明确的序列分类
约束
e(r)=0,D(r)≥0
在 exchange diagonal 形成一条 smooth equality 与一个 active inequality；残差化后得到
Ze2​+(Zd−​)2
及 21​χ12​+21​χ22​ 是标准的 cone-projection 结构。正文的点态结论可信。
compact-uniform size 证明则把所有 null sequences 分为“ηN​ bounded”与“ηN​→∞”，但临界值选择用的是 Zd,N​>logN。需要显式处理：
ηN​→∞,ηN​/logN→c∈[0,∞],
以及估计 covariance 和 eigenvalue truncation 对该选择事件的影响。目前文本说明了若 ηN​/logN→∞ 则选择 interior critical value，却没有逐类写出 intermediate regime 为什么仍满足 uniform size。
解除异议所需修改：


给出包含所有 subsequences 的三分法；


对 intermediate regime 证明无论选择哪一个临界值，拒绝概率上极限不超过 α；


明确 c∂,α​≥c1,α​；


将“off-gate no rejection”的数学测试与“withhold report”的操作协议分开，前者用于定理，后者只作为应用说明。



1.10 Complete-visible-law test：核心构造可行，但两个关键步骤被压缩
Theorem D 的 distributional-distance guard 与相邻 gap score 是合理组合，且显式 Qη​ 路径确实可以保持 r0​,r1​,r2​ 而改变更长字概率。
然而下列两步需完整证明。
（a）由 minimizer 到 σN​−σθ​=OP​(N−1/2)
正文指出长度不超过三的字概率包含 r0​,r1​,r2​，随后直接使用 quotient map 得到 root-symmetric coordinates 的 root-N consistency。 应当写出一个确定性不等式：
∥rN​−r(θN​)∥≤C⎩⎨⎧​dN​+∣w∣≤3∑​∣PN​[w]−Pθ0​​[w]∣⎭⎬⎫​,
再利用 θN​ 的 minimizer 性质和 uniform chart bounds。
（b）stationary record likelihood 与 Palm gap likelihood
LAN 证明主要对 complete gap product 展开，端点项被概括为 OP​(1) 或可忽略。 必须给出 stationary binary renewal record 的精确 likelihood factorization，包括：


左 equilibrium delay；


complete gaps；


右 censored tail；


cycle-mean normalization；


Palm inversion Jacobian，若使用不同 dominating measure。


解除异议所需修改：
增加“stationary renewal likelihood decomposition”引理，并逐项证明在 ηN​=t/N​ 下端点 log-likelihood 为 oP​(1)，且该界在所称紧 null 族上一致。

1.11 Markov–Palm tangent：代数内容大体正确，但核心 tangent 结构已有直接先验结果
在固定 gap marginal g 下，Markov transition score 的 row 和 invariant-marginal 条件给出双条件中心化；保持 r2​ 再加上 q(0,0)=0。由此得到
T={q:E(q∣G0​)=E(q∣G1​)=0, q(0,0)=0}
是可信的。正文的 truncation-plus-projection path construction 也可能给出两侧 Doeblin paths。
但是稿件目前将“双中心化 interaction tangent”和其对 additive marginal scores 的正交性呈现得过于接近原创。Bickel–Kwon 已在已知 stationary marginal 的 Markov chain model 中明确给出
Hs​={w:Qw=Q−w=0},
即 score 与所有 u(x)+v(y) 正交，并以相应投影给出 canonical gradient。统计信息网+2统计信息网+2 这与本文 Hint​ 的主体结构直接重合。
因此当前 priority narrative 存在实质遗漏。
本文仍可能原创的部分是：


sampled-counter 三坐标约束额外删去 e0​⊗e0​ 方向；


q(0,0)=0 的精确 atom interpretation；


positivity-compatible、精确保 marginal 和三坐标的两侧 realizing paths；


calendar-time information factor μ−1；


exchange-local null calibration。


解除异议所需修改：


将 Bickel–Kwon 置于定理陈述之前，而非泛称“一般 semiparametric theory”；


把
E(q∣G0​)=E(q∣G1​)=0
明确标为已有 fixed-marginal Markov tangent；


将本文定理重写为“该已有 tangent 与单个 atom constraint 的正交截面”；


明确定义 nuisance space：


所有 renewal marginal perturbations；


sampled-counter 两维参数 nuisance；
两者虽都与 interaction space 正交，但并非同一模型；




对每个 QMD path 给出 stationary-record endpoint condition，不能只对特制 realizing paths证明后再以附加假设覆盖其余路径。



1.12 Helmert coupling：这是全稿最需要补强的技术定理
Proposition 1.14 声称
nN​SJN​2​→∞
是 moving-dimensional Euclidean Gaussian coupling 的充要条件，并给出 sharp second-order boundary。
其充分性路线是有价值的：independent-block decomposition、Meckes 型 Stein regularity 与 Zolotarev–Wasserstein bridge。Meckes 的多元正态逼近工具确为已有结果；Bołbotowski–Bouchitté 的 Z2​/W2​ 比较亦是外部输入，而非本文一般不等式。arXiv+2arXiv+2 稿件对此归属基本正确。
但“sharp if and only if”依赖若干只被概述的专门估计：


local-null partition cell density-ratio bound；


从该 bound 到整个 dJ​-维 covariance operator 的 O(J2N−1/2) 控制；


random calendar stop 的 OP​(JN−1/4) Euclidean error；


covariance square-root perturbation的 uniform constants；


当 nN​SJN​2​ 有界但不趋于零时，corner coordinate 为什么不可能 Gaussian；


rare adjacent-tail events 的 Poisson/cluster 论证；


coupling 构造对全部 σ∈HN​(C) 的可测性和一致性。


这些步骤集中在数页内。 必要性部分则主要由 moving corner coordinate 与 zero block 直觉支持。
解除异议所需修改：
至少增加四个独立引理：


Helmert cell-ratio lemma： 给出原子和 tail cell 的显式导数界；


moving covariance lemma： operator norm、mean shift 和 lag-one covariance 的统一估计；


calendar stopping lemma： 精确说明为何误差阶为 JN−1/4，而非仅引用 martingale maximal inequality；


necessity lemma： 分别处理
nSJ2​→0,nSJ2​→c∈(0,∞),0<liminfnSJ2​≤limsupnSJ2​<∞,
并证明非 Gaussian 极限或 Lindeberg 失败。


在这些引理完成前，标题中的 “sharp” 和 “necessary and sufficient” 应撤回，最多保留为充分条件与必要 corner condition。

1.13 奇异交换实验：显式展开可信，但“complete experiment”措辞过强
对
pN​=z+hN−1/4,sN​=z−hN−1/4
而言，对称坐标的首次变化为 h2N−1/2，故出现
h2ΔN​−21​h4I(z)
是合理的，显式 Bz​、bz​ 和 I(z) 也与这一二阶路径结构一致。
主要缺口仍是从 iid complete Palm gaps 到 stationary N-bin binary record。证明用一段文字说明 likelihood ratio 仅多出 equilibrium delay、censored tail 和 cycle mean，并声称其导数有 polynomial envelopes。 对普通收敛论证这可能足够，但不足以支持“uniform likelihood-ratio processes”及“complete singular experiment”。
解除异议所需修改：


写出完整 Radon–Nikodym derivative；


明确 dominating measure；


对左右端点的 q=d2 一阶、二阶导数给出统一界；


证明 uniform exponential-tail event 上 remainder 为 oP​(1)；


证明补事件概率统一趋零；


说明初始 stationary delay 对 z 和 q 的可微性。


此外，现定理只研究预先指定的 symmetric split submodel。它证明的是：

该对称 split 子实验的 compact-uniform LAQ/Gaussian limit。

它没有证明所有向 diagonal 接近的局部 perturbations 均与此一维实验等价，也没有给出双向 Le Cam equivalence。因此“complete singular experiment”应改为：

complete likelihood limit along the specified symmetric split subexperiment。

除非作者另证该路径对全部可辨局部方向具有穷尽性。

1.14 Projection example：正确但不应占据主定理位置
固定 z0​=1/2 下，smooth inequality boundary 的 metric projection 极限
N​{ΠF​(σ)−σ0​}⇒ΠH​Z
是标准方向可微投影结果。正文也明确否认检验、置信区间或 coverage 解释。 interval certificate 仅证明该点 covariance 非奇异，这一界限表述是正确的。
该结果数学上没有明显错误，但原创增量非常小，且加剧全文架构膨胀。
解除异议所需修改：


移至 appendix 或 supplement；


不再列为 paper-level Theorem E/F；


certificate 仅保留为 reproducibility note；


不应以单点数值证书补偿全稿其他解析证明的缺失。



1.15 机器核验材料的证据地位
正文正确声明计算测试不能替代证明。不过本次提供给审稿人的材料中，能够直接审阅的是 PDF；文中列出的 scripts、JSON transcript、hashes 和 unit tests 未作为可访问的独立附件出现。正文的 data-availability 声明列出了路径，但路径本身不是可归档的审稿材料。
解除异议所需修改：


将代码和证书置于带版本号和 DOI 的公开归档；


提供 commit hash、运行环境、精确命令和预期输出；


将每个数值测试映射到对应 theorem/lemma；


明确哪些测试只是 regression tests，哪些是 directed interval certificates；


对 Helmert coupling 和 singular LAN 等无限样本定理，数值测试只能作为 sanity check，不能作为缺失 uniform remainder 证明的替代。



2. 新颖性和优先权叙述
2.1 总体结论
现稿并非“整体已被先验结果包含”。我没有找到直接给出以下全部组合的先验论文：


特定 killed-leakage sampled-counter 核的完整闭式 renewal law；


三个 binary inclusion probabilities 到 (p+s,ps) 的显式 rational quotient；


该 physical triangular kernel 与 killed-reset cone 的显式闭弧交；


同一模型的物理像方程、boundary test、特定 Markov-gap path 和显式 diagonal score。


因此文章存在可发表的模型专门化增量。
但当前 priority narrative 尚不准确。至少有三处必须实质改写：


Markov–Palm 双中心化 tangent 的主要部分已有 Bickel–Kwon；


二态 fibre 必须与完整 weak-equivalent MAP2 分类逐式比较，而不能只称其为“nearest comparator”；


纯串联识别必须正面纳入 generalized Erlang/minimal Coxian 文献，尤其 He–Zhang，而不仅以 Cumani/O’Cinneide 作宽泛背景。



2.2 逐项优先权判断
（a）记录律、hazard、covariance、1-dependence
最近先例：


general D-MAP/MAP framework：Neuts、Lucantoni、Alfa–Neuts；


renewal binary process 的 finite-dimensional law、CLT 与 finite-order Markov criterion：Zamparo；


MAP2 covariance 几何衰减及恒号/交替号：Ramírez-Cobo–Carrizosa。巴里大学+1


可保留的原创性：


从该 killed-reset physical kernel 推导出的具体 Palm law；


严格递增 hazard 的参数化证明；


精确 λhid​=0 threshold；


λhid​ 的 sharp range；


sampled-boundary 小 Δ expansion。


必须降格的叙述：


renewal binary process 的一般法则；


finite-order Markov 判据；


two-state MAP covariance 几何模式。


（b）三坐标商逆与物理像
Mészáros–Telek 已证明 order-two DMAP/DRAP 的 Markovian canonical form 可以描述整个 order-two class。Springer 稿件自己也承认，不排除三坐标恒等式是 canonical coordinates 的隐式专门化。 这是一项诚实但尚不充分的声明。
正式 revision 必须做的工作不是继续说“可能是 implicit”，而是实际完成比较：


将 canonical DMAP2 coordinates 写成与本文 kernel convention 相同的 orientation；


计算本文 r0​,r1​,r2​ 在该 canonical form 中的位置；


判断 Φ(r) 是否只是已有 moment-to-canonical map 的限制；


如是，则将 novelty 限定为 unusually low-order binary-inclusion formula、physical image equation 和稳定 chart；


如否，则明确指出先验 canonical map 需要哪些额外 observables，而本文为何只需三个 inclusion probabilities。


在完成这一比较前，“three-inclusion quotient inverse”可以作为候选原创结果，但不能作已充分核定的优先权主张。
（c）二态完整 fibre
Ramírez-Cobo–Wiper–Lillo 已证明 MAP2 不可识别并给出不同参数产生相同 stationary observable law 的条件；Ramírez-Cobo–Lillo 随后给出 weakly equivalent MAP2 的完整刻画。剑桥大学出版社+1
因此，“完整 fibre”三个字要求作者证明的不是“我们的公式看起来更显式”，而是：
已有完整 weak-equivalence class∩killed-reset substochastic cone={K(q):q∈I∗​}.
若这一定理确实只是该交集的一次精确计算，仍然可以新颖，但应如此命名。不能将“完整 MAP2 nonidentifiability”本身重新归为本文发现。
（d）纯串联 n 态识别
该部分的直接先例应包括 generalized Erlang、acyclic PH、Coxian minimality 与 triangular order。He–Zhang 的工作明确讨论 generalized Erlang 的 minimal Coxian representation，并建立相应算法和结构条件。滑铁卢大学工程系 当前引用链不足以使读者判断 Corollary 3.3 与这些结果的真实差异。
可保留原创性：


离散 sampled Palm tail 的前 2n 项足以恢复全部重复 sampled poles；


killed-reset D-MAP visible-law formulation；


与一般 interior similarity fibre 的并置对比。


不可作为主要原创性：


hypoexponential/generalized-Erlang 分布由无序率多重集决定；


repeated poles 通过 confluent exponential terms 保留 multiplicity；


Coxian/PH representation 的一般 minimality。


（e）内部 fibre 维数
这是经典 realization uniqueness 加 reset-preserving subgroup 的 Lie algebra 维数计算。它可以是新 lemma，但不足以单独承担“higher-state theorem”叙事。
建议改为：

The classical minimal-realization orbit, when intersected locally with the strict killed-reset Markov cone, has reset-preserving dimension (n−1)2.

（f）CLT、delta method 与协方差估计
regenerative CLT、batch means、delta method 均已正确标为引入。本文可能新增的是 complete-cycle bookkeeping、特定 reward vector 和 uniform compact chart specialization。当前 priority narrative基本准确，但不宜将 sorted-root CLT 列为独立的重要创新。
（g）physical-image test
Chernoff/Shapiro/Andrews 的 cone/boundary theory是正确先例。新意可以限定为：


该具体 analytic image equation；


equality-plus-discriminant 的二维约束；


compact chart 上 covariance nondegeneracy；


N−1/4 diagonal transition 与预设 critical-value selector。


“chi-bar-square mixture”本身不是新结果。
（h）complete visible-law test
Ryabko 系列提供 distributional-distance consistency，serial-independence score 和 Gaussian-shift calculus也已有成熟文献。本文新意主要是：


与 sampled-counter null family 的组合；


root-free exchange-uniform score；


精确保 r0​,r1​,r2​ 的 rank-one Markov-gap alternative；


对字 10101 的显式分离；


该一维 subexperiment 的 envelope。


这一定位基本准确。
（i）Markov–Palm tangent 与 omnibus
现稿遗漏 Bickel–Kwon 是本轮 priority audit 中最重要的发现。已知 marginal Markov model 的双中心化 tangent 与 additive nuisance orthogonality并非本文新增。统计信息网
因此应将原创性重写为：
Bickel–Kwonknown-marginal Markov interaction tangent​​∩three-coordinate constraint{q(0,0)=0}​​,
加上 exact positivity paths、calendar scaling 和 exchange calibration。
（j）Helmert boundary
一般 Gaussian approximation 输入归属基本诚实。真正候选新结果是特定 sampled-counter equal-rate gap law下
nSJ2​→∞
的 moving-layer boundary。该项若证明补全，具有独立技术价值；但它不应被描述成一般 Hilbert-space或 Yurinskii 理论的新结论。
（k）奇异交换实验
N−1/4 loss-of-identifiability 机制已有经典理论。本文可主张的仅是：


该具体 renewal likelihood 的显式二阶 score；


显式 information series；


z 紧集上的 uniformity；


sign invisibility 的模型内实现。


“complete singular experiment”须限于所指定的 symmetric split path。
（l）单点 projection example
这基本是标准定理的演算示例，无需原创性主张。现稿对此已经相当克制。

3. 是否足以发表于 Journal of Physics Communications
3.1 按现状：不建议发表
Journal of Physics Communications 并不要求结果具有被编辑主观认定的高影响力，但仍要求文章贡献于 physics knowledge，而不只是给一个概率模型附加物理命名。IOPscience - Publishing Support
现稿目前的物理连接不足，原因不是没有数据本身——纯理论论文当然可以发表——而是：


killed-leakage/reset rule 被作为模型契约给定，而非从一个已接受的 detector dynamics、electronic latch protocol 或 coarse-graining limit 推导；


Γ,κr​,Δτ 虽被赋予 attempt/recovery/sampling 名称，但正文没有建立它们与具体装置可测参数、实验设计或误差机制的映射；


大部分篇幅转向 semiparametric tangent spaces、distributional-distance tests、moving-dimensional Gaussian coupling 与 Le Cam local experiments；


detector literature 主要承担“近邻但不同”的说明，而非用于验证、比较或形成可检验的物理结论；


正文明确没有经验数据、模拟拟合或 validation data。 这不是单独的缺陷，但与上述结构合在一起，使文章更像一篇由 sampled counter 激发的概率统计论文。


因此，即使所有数学缺口被补全，现有架构仍不是 Journal of Physics Communications 的自然稿件形态。
3.2 何种修改可能解除 JPC scope 异议
若坚持投稿该刊，至少需要：


从一个明确的 detector/counter mechanism 推导 Assumption 1.1，而非仅定义它；


给出 Γ,κr​,Δτ 的实验可解释性和估计尺度；


与 nonparalyzable dead-time、continuous exponential recovery、same-bin recovery 等标准模型作定量比较；


展示 killed-reset convention 在何种电子或光子计数协议中真实成立；


说明 quotient inversion 或 exact 1-dependence threshold 能回答什么物理问题；


至少给出受控模拟或公开实验记录上的 proof-of-principle，不将诊断结果误述为模型验证；


将抽象 semiparametric 和 Gaussian-coupling部分移至 supplement 或另文。


达到这些条件后，文章可以作为一篇“物理计数模型的严格随机过程分析”重新评估。
3.3 更合适的具体期刊
首选：Methodology and Computing in Applied Probability
该刊明确接收强调 methodology 与 computing 的 applied probability 工作，覆盖 stochastic processes、reliability、communication networks、mathematical physics 等主题；其当前栏目亦直接包括 Markov 与 semi-Markov processes。Springer+1
本稿的核心——D-MAP、PH realization、renewal inference、identifiability、specification testing 和 reproducible certificates——与其范围高度一致。更重要的是，Ramírez-Cobo–Lillo 关于 weakly equivalent MAP2 的直接先例本身即发表于该刊，因此编辑和审稿人群体与本稿的 priority 问题高度匹配。IDEAS/RePEc
次选：Stochastic Models
该刊接收概率理论及其在自然科学模型中的应用。泰晤士在线 若文章缩减统计测试和 semiparametric 部分，集中于 record law、identifiability、similarity fibres 与串联 PH 结构，该刊也较合适。
3.4 长度与架构
JPC 对 Research Paper 没有形式上的篇幅上限，故“62 页”本身不是拒稿理由。IOPscience - Publishing Support 真正问题是架构非同质：


前半是一篇 explicit D-MAP/renewal inverse 论文；


中部是一篇 constrained specification-testing 论文；


后部又是一篇 semiparametric tangent、moving-dimensional Gaussian coupling 与 singular LAN 论文。


建议至少分为：


结构论文： record law、quotient inverse、physical image、two-state fibre、serial n-state identifiability、interior orbit dimension；


推断论文： complete-cycle CLT、image test、complete-law test、Markov–Palm tangent、Helmert boundary、singular exchange experiment。


若坚持单篇，则必须显著压缩标准输入、projection example 和操作性 gates，并建立清楚的单一问题主线。

4. Revision 必做修改清单
4.1 Blockers
B1. 统一定理版本和编号
问题： A–E/F 编号、摘要、依赖图和证明不一致。
解除条件： 唯一 theorem registry；全文和 supplement/code 同步；明确哪些是原创主定理。
B2. 完成二态 fibre 的优先权归约
问题： 未证明显式弧不是 Ramírez-Cobo–Lillo weak-equivalence 分类或 Mészáros–Telek canonical form 的直接代入。
解除条件： 将先验参数化与 K(q) 逐式比较；若为直接 specialization，则降格为 cone-intersection corollary。
B3. 修订 Markov–Palm tangent 的 priority claim
问题： 漏引 Bickel–Kwon 的 known-marginal Markov tangent 与 additive projection。
解除条件： 明确将双中心化主体归入先验工作，只主张 atom constraint、exact paths、calendar information 和 boundary calibration。
B4. 补全 generalized Erlang/Coxian 文献比较
问题： serial n-state identifiability 的现有叙述未充分覆盖 He–Zhang 等直接先例。
解除条件： 区分经典无序极点识别与本文前 2n sampled tails 的有限坐标结论。
B5. Helmert “充要边界”完整证明
问题： local-null covariance、calendar stop 和 necessity 仍为压缩论证。
解除条件： 增加前述四个独立引理；否则撤回“sharp iff”。
B6. 奇异 stationary-record likelihood factorization
问题： 从 iid Palm gaps 到完整 stationary binary record 的端点似然只以一段文字处理。
解除条件： 写出精确 Radon–Nikodym factorization 和 uniform endpoint bounds；将“complete experiment”限制于已证明的 subexperiment。
B7. 期刊 scope
问题： 物理系统连接不足以满足当前 JPC 定位。
解除条件： 增加真实 detector protocol derivation、参数可测性、标准物理模型比较和至少一项受控数值/实验展示；或者改投 applied probability 期刊。

4.2 Major revisions
M1. 修正 Theorem A 证明中的 T0​>0 错误
以路径或闭式公式证明 gk​>0，并引用 renewal finite-order Markov 判据。
M2. 补物理像 sufficiency 正性引理
严格证明 a,b>0，包括对角极限；给出局部 root-in-(0,1) 的统一 margin。
M3. 证明 stopped separated-batch rate
建立随机停止、矩阵平均、plug-in centering 和 compact-uniform 版本的完整引理。
M4. 补 physical-image test 的 intermediate null sequences
处理 ηN​/logN 的全部可能子序列，并证明 critical-value selector 不破坏 uniform size bound。
M5. 补 complete-law minimizer 的 root-N 引理
从 truncated word distance 到 inclusion coordinates，再到 symmetric root coordinates，给出确定性 Lipschitz bounds。
M6. 明确 stationary Palm inversion likelihood
该引理应同时服务 complete-law LAN、Markov–Palm paths 和 singular exchange experiment，避免三处重复使用未经证明的 endpoint negligibility。
M7. 收窄“完整”“精确”“最优”等措辞


“complete singular experiment”改为指定 split subexperiment；


“complete tangent”应注明相对于 declared Markov-gap path class；


“optimal”仅限一维 Gaussian-shift subexperiment；


“exact fibre dimension”注明 minimal interior stratum；


“all alternatives”始终保留 stationary ergodic/separation/moment 条件。


M8. 重组稿件
将标准 background、操作 gates、代码接口、单点 projection example 和长 comparator tables移出主线。

4.3 Minor revisions


统一 row/column vector convention，尤其 eD⊤​、β、T1​=cβ；


“roots p,s∈(0,1), with equality allowed”应改为“允许 p=s”以免被理解为允许端点；


将 Δinv​=0 在物理模型中自动成立的证明放在 Theorem B 前；


区分 visible root ordering 与 physical attempt/recovery labeling；


将“diagnostic”“test”“withhold report”三种概念分开；


对所有 compact-uniform 结论列出共同参数集和共同 dominating constants；


将代码测试结果放入 reproducibility appendix，不在数学证明附近以数值残差增强可信度；


对最新的 Gaussian-comparison 文献给出最终发表状态与版本日期，避免引用版本漂移；


related-work 部分应采用“prior theorem—本文 specialization—严格剩余增量”的三列表，而非以宽泛领域段落代替逐定理比较；


删除或降格所有仅说明标准 delta method、metric projection 或一般 Kalman uniqueness 的“paper-level theorem”标签。



最终裁决
数学上： Theorem A、B、二态 fibre 与纯串联识别的核心机制大概率正确；没有发现一个立即摧毁整篇论文的反例。但 Helmert sharp boundary、complete stationary-record likelihood 以及若干 compact-uniform 结论尚未以可接受的完整度建立。
优先权上： 当前叙述需要实质修正。Bickel–Kwon 对 fixed-marginal Markov tangent 的先验结果是明确遗漏；Ramírez-Cobo–Lillo 的完整 weak-equivalence 分类和 He–Zhang 的 generalized-Erlang/Coxian 理论也必须从“邻近背景”提升为逐式比较对象。完成比较后，文章仍可能保有真实的新颖部分，但其中心应是特定 constrained model 的显式 specialization，而不是一般 realization、tangent 或 singular-LAN 理论。
期刊适配上： 即使数学补全，现有版本与 Journal of Physics Communications 的物理贡献要求仍不匹配。最合适的投稿对象是 Methodology and Computing in Applied Probability；若压缩统计部分并强化 D-MAP/PH 结构，则 Stochastic Models 亦合适。
因此，我对当前投稿的正式建议是：Reject，允许作者经根本性重构后作为新稿提交，而非在本轮作普通 major revision。