匿名审稿意见
稿件： Minimal preimages of the Fibonacci rank map: squarefree fibers and weighted covers
编辑建议： 拒稿，但明确允许在实质性重构后重新投稿（reject and resubmit，而非普通大修）。
总体评价
稿件包含一个具有发表价值的数学核心：将精确秩纤维 Bn​=α−1(n) 的整除极小元归约为带“降阶见证”的不可约 lcm-覆盖，并由此识别平方自由指标上的规范平方自由切片及其加权计数。我没有在主文中发现足以断言该核心分类为假的反例。
但是，现稿尚不能接受，原因并非期刊层级不足，而是以下两项结构性缺陷：


**送审文件不是一份可独立核验的完整证明。**定理 5.1 和定理 5.10 的上界部分明确调用仅存在于未附补编中的 prime–ladder alternative 与 prime-power lifting 结果；这两处直接支撑第 4、5 项主张，而不是可选的技术补充。 


**现行优先权叙事遗漏了最接近结构主定理的先行工作：Carl G. Wagner 1978 年的 “Minimal multiplicative covers of an integer”。**该文直接研究满足
lcm(d1​,…,dr​)=n,lcm(d1​,…,di​​,…,dr​)<n
的整除元组，并明确将其视为有限集极小覆盖的乘法推广。这与本文平方自由／素原子部分的组合骨架高度重合。Mathematics+1


只要这两项得到彻底处理，我认为修改后的核心成果原则上达到《The Fibonacci Quarterly》的发表门槛；现状则不达到。

一、数学正确性
1. 见证覆盖分类与 ω(m)≤ω(n)
判断：主文中的证明成立。
Lemma 4.3 正确地把整除极小性化为逐个素坐标降低一次后的 lcm 严格下降。这里检验 m/pi​ 已足够：任一真因子至少在一个素坐标上不超过 ei​−1，而秩对整除关系单调。Lemma 4.5 对满指数坐标逐坐标比较，准确刻画了降低原子后何时仍保持总 lcm=n。Theorem 4.6 随后给出的双射及由唯一分解得到的逆映射没有缺口；私人坐标也确实给出原子集到 P(n) 的单射。 
这里需要修改的是优先权定位而非证明本身。见证覆盖定理不应继续表述成首次发现的不可约 lcm-覆盖机制；其新部分是：


将 Wagner 型删除一个因子的条件推广为把一个 prime-power rank label d(θ) 降到 d−(θ)；


证明 Fibonacci prime-power arithmetic 只产生素原子与梯级原子；


将抽象覆盖的算术可实现性与 Mn​ 唯一对应。


**消除异议所需修改：**增加一个专门的比较命题，明确说明在所有原子均为素数、因而 d−(θ)=1 时，本文条件退化为 Wagner 的 minimal multiplicative cover；再说明梯级原子是本文真正新增的“lowered-label”结构。

2. 素数逆向射线及两个动力学推论
判断：论证正确，但原创性等级显著低于现稿标题化处理所暗示的等级。
Theorem 3.1 的迭代是有效的。初始 y≥7、y=12 有精确秩素数；以后每个前驱都是不小于 7 的素数，故不会落入例外秩 6,12。若射线中有重复素数，就产生周期点；结合固定点分类和无非平凡周期可排除。最后
pr​∣Fpr−1​​,pr​≤Fpr−1​​<φpr−1​
给出所声明的迭代指数上界。x=12 时采用 7↦8↦6↦12 的桥接也正确。
FitzGibbons–Javaheri–Miller–Verga 的正式问题确实分别询问：


每个 k≥1 是否存在无穷多个两两互素、固定点阶为 k 的整数；


每个固定点 x>5 的吸引域是否含无穷多个两两互素元素。Taylor & Francis Online+1


因此，从逻辑结论看，本文得到无穷多个不同素数，确实同时回答了两个问题，而且所得结论强于“两两互素整数”。正文第 459–464 行的实质判断是正确的。
但从独立新结果的门槛看，我的裁决是：


它达到“新的、值得记录的推论或应用”的门槛；


它不达到“独立的素数存在性定理”或本论文首要数学创新的门槛；


它不能单独支撑本稿发表，因为证明只是逐次调用进口的精确秩素数存在定理，并未建立新的素数构造、分布或筛法机制。


“strictly strengthen and resolve”在形式逻辑上可以辩护，但在摘要和引言中容易造成原创机制上的过度印象。
**消除异议所需修改：**将措辞改为：

“As a direct corollary of classical exact-rank prime existence, we answer both questions affirmatively in the stronger prime form.”

并将该部分降为较短的应用节，明确写出“no new prime-existence input is proved here”。不必删除该结果，但不应让它先于见证覆盖定理成为摘要中的主要卖点。

3. 秩纯部分、例外支撑、平方自由切片及极小横截模型
判断：主文中的核心论证成立。
Theorem 5.4 对例外支撑的分析正确：nS​=2,6,12 所对应支撑至多两个，且基数至多二；不同支撑给出不同的 nS​，故所选择的精确秩素数也不同。对非例外不可约覆盖，每个素原子满足
En​(pS​)=Tn​(pS​)=S,
因此不可约覆盖条件与见证覆盖条件完全一致，唯一性由整数唯一分解和 α(pS​)=nS​ 恢复。
平方自由指标上的反向包含也正确：若 m∈Mn​ 平方自由，则其全部原子均为素原子；因 n 平方自由，任一秩 d(p)∣n 必等于对应满支撑的 nS​，从而落入所构造的秩纯部分。平方自由精确纤维中的极小性与全纤维中的极小性一致，因为平方自由数的所有因子仍平方自由。
这里真正有实质新意的部分是：


加权和对一个标准精确纤维切片的精确计数；


平方自由指标上的规范性识别；


Fibonacci 精确秩素数对经典不可约覆盖的算术实现。


Corollary 5.5 的 minimal-transversal 表述本身是标准超图对偶的应用，应继续作为解释性重述，而不应列为独立组合突破。
**消除异议所需修改：**增加至少一个完整手算实例，分别展示：


一个无例外的奇平方自由层；


一个含 2,6 或 12 例外支撑的偶数层；


n=91 中 169 位于非秩纯部分的边界现象。


现有抽象证明正确，但对于该刊读者，缺少实例会显著降低可读性和可核查性。

4. #Mn​ 的上下界及平均界
判断：下界和粗平均界可跟随；精细上界在当前送审材料中不可核验。
非空性证明正确：对 n≥3，严格递增性给出 α(Fn​)=n，故有限偏序集 Bn​ 有极小元。私人坐标构造的下界也成立：选取避开坐标 2,3 的 r=⌊k/2⌋ 个私人坐标，保证每个构造秩含一个不在 {2,3} 中的素坐标，因而避开精确秩素数存在定理的例外。不同映射 H 产生不同支撑族及不同乘积。
问题出现在上界。证明依赖以下未在主文证明的断言：


任一有效原子族或者是若干精确秩素数的并，或者是至多含一个元素的梯级族；


非空本质支撑只能满足 I=J 或 ∣I∣=1。


这些结论被指向未附补编，而随后正是它们给出每个私人坐标至多
2R(n)2k−s
种选择。
因此，当前不能认证：


第 4 项中的精细上界；


由该上界导出的 (log2/4)k2+klogR(n)+O(k)；


所有依赖该上界的条件渐近结论。


粗界 L(n)≤ω(n)logn、Wigert 型包络和平均上界不受此缺失影响。
**消除异议所需修改：**以下两种方案任选其一：


将完整的 prime-power rank-lifting 公式、prime–ladder dichotomy、原子族有限性及“每个梯级槽至多一个候选”的证明移入正文或正式附录；


将完整补编作为同一投稿包的可审稿组成部分，并在正文中使用稳定的定理编号，而非“Supplement, section ‘Low-support classifications’”这类不稳定指引。


若不提供这些证明，则必须删除精细上界、定理 5.1 及所有由 R(n) 推出的结论；这会实质性削弱论文，不能以“标准事实”一句代替。

5. 秩窗去聚合与 fibotomic 熵界
5.1 秩窗去聚合
判断：推导在 prime–ladder 结论成立的前提下可信，但当前同样不完整。
窗口基数
#WJ​(n)=ℓ∈/J∏​νℓ​(n)
及
0≤logR(n)−logA∗(n)≤log2+ℓe∥n∑​loge
之后的均值估计没有明显错误。双重级数
p∑​j≥2∑​pjlogj​
绝对收敛，足以给出 O(xloglogx)。然而关键夹逼
P(n)≤R(n)≤P(n)+1
仍依赖未附的梯级原子分类。
**消除异议所需修改：**与上一项相同；缺少 prime–ladder 定理时，Theorem 5.1 不可保留为已证结果。
5.2 Fibotomic rank entropy
判断：证明思路成立，未发现反例；但文献归属和若干中间断言需写得更自足。
由 fibotomic 分解得到
Fd​=Ψd​(1)∈N,logFd​=φ(d)logφ+O(1),
精确秩素数的乘积整除 Fd​，再结合
p≡±1(modd)
对第 i 个精确秩素数给出下界，最后用 Stirling 公式得到系数 logφ/2。这一链条在数学上是一致的。
当前仍须补足：


明确证明带负 Möbius 指数的表达式为何等于正整数 Ψd​(1)；


单独陈述
α(p)=d∏​p∣Fd​
的引理，并说明不会因 Möbius 商式而发生约消；


将 d=3,5 以及空精确秩层 d=6,12 的处理统一列出；


在“一致 o(1)”处明确量词，而不是仅以二分情形隐含完成。


这些是可修复的写作缺口，不是我所发现的数学错误。

6. 固定总质量下的加权不可约覆盖极值
判断：命题及等号分类正确。
展开 wS​=1+xS​ 后，
S∈C∏​(1+xS​)≥1+S∈C∑​xS​
并对全部不可约覆盖求和。每个非空支撑至少出现一次，而全支撑只出现在单元素覆盖中，故得到锐界。对 k≥3，每个真非空支撑至少出现在两个不可约覆盖中，因此等号迫使全部真支撑的超额质量为零。
该结果是一个正确而有用的支持性引理，但证明十分初等，不宜作为论文独立主要创新。其价值在于精确说明“仅知 ω(Fn​) 的总质量不足以控制加权覆盖和”，而不是建立新的深层极值理论。

7. H1、H2 与 BLMS 猜想的关系尚未陈述完整
现稿只指出 BLMS 猜想会迫使 H2 失败。事实上，稿件自己的估计还推出 H1 也会失败。
在 BLMS 猜想下，对几乎所有平方自由合数 n，稿件已得到
logR(n)≥loglogn−ω(n)log2+O(1).
再利用平方自由整数上的正常阶
ω(n)=(1+o(1))loglogn,
可得
ω(n)logR(n)​≥1−log2+o(1)
在一个正密度集合上成立。因此，对任意
0<ε<1−log2,
H1 中的异常集不可能是 o(x)。 BLMS 原文确实猜测复合指标上 ω(Fn​)≫logn。Samir Siksek
这不使任何无条件定理失效，也不使“H1 蕴含条件正常阶”这一逻辑命题失效；但把 H1、H2 无限定地命名为“Conjecture”会隐去它们与一项已发表猜想的直接冲突。
消除异议所需修改：


最稳妥的方案是改称 sufficient hypotheses；


若作者坚持将 H1、H2 作为自己的反向猜想，则必须明确写出：BLMS 猜想将同时否定 H1 和 H2；


Corollary 5.14 应表述为纯条件推论，不应暗示这些条件目前有正面算术证据。



二、新颖性与优先权
1. Wagner（1978）是必须补入的最近结构先行工作
这是本报告最重要的优先权意见。
Wagner 的 Minimal multiplicative covers of an integer 并非仅仅讨论普通集合覆盖；其定义直接是由 n 的因子组成的元组，整体最小公倍数为 n，而删除任一分量后最小公倍数严格小于 n。他还明确指出，在 n 为不同素数乘积时，该问题推广了有限集的极小覆盖枚举。Mathematics+1
与本文的精确关系如下：


在平方自由极小元或一般秩纯素原子部分，d−(p)=1，本文见证条件正是 Wagner 条件的无序版本，再附加精确秩素数的算术选择；


对梯级原子，本文把“删除 di​”推广为“将 di​ 降到 di−​”；


本文的新增内容是这种降低操作的 Fibonacci prime-power 实现、唯一原子分解、平方自由规范切片以及精确秩乘数权重。


因此，现稿仍可能具有新意，但不能再将其表述为首次把精确纤维极小元归约为不可约 lcm-覆盖而不讨论 Wagner。
足以消除异议的修改：


在引言中增加 Wagner 1978 的独立小节；


给出上述退化／推广关系的正式命题；


将“witness-cover classification”的新颖性限定为 Fibonacci exact-rank realization and lowered-label refinement of minimal multiplicative covers；


在摘要中避免给出“覆盖机制本身此前未知”的暗示。


在该修改完成前，我不能认可现行的全球优先权叙事。

2. 经修正后仍可成立的新颖性主张
在我所检索的文献中，未发现下列组合被先行工作明确给出：


Fibonacci 精确秩纤维 α−1(n) 的全部整除极小元与 lowered-label 原子覆盖之间的双射；


平方自由指标上，秩纯构造恰等于 Mn​ 的平方自由部分；


该切片按精确秩素数重数 a(nS​) 加权后的精确计数；


非平方自由梯级原子与平方自由切片之间的系统分界。


这里的否定性检索当然不是优先权证明；但在纳入 Wagner 后，我没有发现另一项会使上述 Fibonacci 专属结论直接退化为已知定理的文献。适宜的叙述应是“we are not aware of an earlier Fibonacci exact-fiber realization of this weighted multiplicative-cover structure”，而不是排他性的首次发现声明。

3. 素数逆向射线的优先权等级
我未在所核查的动力学论文中看到“无限素数逆向射线”被明确陈述。FitzGibbons 等人的正式问题确实仍停留在两两互素整数层面。Taylor & Francis Online+1
因此，该推论可以作为新结果保留。但其新颖性属于：

先前公开问题 + 经典精确秩素数存在定理之间此前未被写出的直接组合。

它不是新的 primitive-divisor theorem，也没有提供精确秩素数的新存在范围。建议将“解决公开问题”与“证明机制完全进口”同时写在定理附近，而不能只在后文附带说明。

4. 固定点分类、轨道终止性和 lcm 恒等式的署名必须改正
现稿把固定点分类和所有轨道终止性作为 FitzGibbons 等人的“recalled classification”使用。 这在二手引用意义上不算虚假，但不符合优先权审查所要求的第一来源署名：


z(n)=n 当且仅当 n=5k 或 12⋅5k 的证明应直接引用 Diego Marques。数学系


迭代最终到达固定点的较早证明应直接引用 Luca–Tron；其 Theorem 2.2 的证明明确以“the sequence of iterates eventually hits a fixed point”为起点。arXiv


α(lcm(a,b))=lcm(α(a),α(b)) 在 Luca–Tron 的基本引理中已明确列出；Renault 可以保留为更一般 (a,b)-Fibonacci 版本的来源，但不能替代对 Fibonacci 直接先行来源的署名。arXiv


**消除异议所需修改：**参考文献中补入 Marques 和 Luca–Tron，并在每一处区分：


original theorem；


later alternative proof；


present application。



5. Fibotomic 分解的历史归属不完整
现稿只把所用分解归于 Byer–Dvorachek–Eckard–Harrington–Wise–Wong。 其论文自身的历史说明是：Webb–Parberry 早在 1969 年研究了 Fibonacci polynomial 的不可约性，fibotomic polynomial 的定义由 Levy 于 2001 年引入，而 Byer 等人提供了较新的系统研究。NSF Public Access Repository
**消除异议所需修改：**补引 Levy 和 Webb–Parberry；准确说明本文究竟使用的是定义、分解恒等式、不可约性还是 Byer 等人的某个具体命题。仅以最新综述性来源覆盖历史来源，对本稿当前的优先权敏感程度而言不足。

6. Ck​∼bk​ 的引用链尚未闭合
稿件从 Hearne–Wagner 的精确式转向 Bender–Richmond–Wormald／Troyka 的 labelled split-graph 渐近，并直接写出
Ck​∼bk​∼ϑε​(⌊k/2⌋k​)2k2/4.

这里存在“标号对象”与“同构类对象”的引用风险：


Royle 明确说明其表格及对应关系计数的是非同构对象，而非 labelled objects。滑铁卢大学计算机科学系+1


Troyka 则明确区分 labelled 与 unlabeled split graphs，并把 Bender–Richmond–Wormald 的结果归入 labelled 枚举。Combinatorics+1


所声明的 Ck​∼bk​ 很可能是正确的，也可以从 Hearne–Wagner 精确式直接分析得到；问题在于现稿没有给出把“标号不可约覆盖”连接到“标号 split/bicolored graph”渐近的完整桥梁。
消除异议所需修改：


增加一个短引理，从 Hearne–Wagner 公式直接证明 Ck​/bk​→1；或


给出精确匹配 labelled minimal covers 的文献定理，而不依赖 Royle 的非标号对应；


若作者不愿补证明，则删除精确 ϑε​ 渐近，只保留并直接证明主结果实际需要的
logCk​=4log2​k2+O(k).



7. 对 Kiss、Stroiński、Sanna 和 Cera Da Conceição 的算术边界描述基本准确
现稿关于“固定整除条件不等于增长精确纤维”的区分是正确的：


Sanna 计数固定奇数 d 满足 d∣ρU​(p) 的素数，而非 ρU​(p)=d。arXiv


Cera Da Conceição 的 2026 年结果给出固定 d 下同一整除条件的 Dirichlet 密度，仍未局部化到增长的精确纤维。arXiv


Stroiński 的工作是关于在 Fibonacci 数处求值的 Dirichlet 乘积及原始因子求和，目前所列来源仍是 arXiv 预印本。arXiv


因此，Kiss／Stroiński 可以继续被称为最近的算术分布先行工作。需要删除的是把它们称为不加限定的“nearest prior work”；在结构方向上，Wagner 1978 明显更接近本文主分类。

三、是否足以发表于《The Fibonacci Quarterly》
现稿
不足。建议拒稿。
拒稿理由不是主题不合，也不是全部结果过弱，而是：


关键上界依赖未送审证明；


最近结构先行工作缺失，导致主定理的原创边界尚未正确建立；


若干基础进口定理未引用第一来源；


标号覆盖渐近的引用链不完整；


H1 与 BLMS 的冲突只陈述了一半；


素数逆向射线在摘要中的地位高于其证明机制所支持的地位。


这些问题无法通过局部勘误解决，故我不建议“major revision”后在同一轮直接接收。
完整重投后的期刊适配
《The Fibonacci Quarterly》明确以 Fibonacci 数及相关序列为核心，并自 2025 年起强调面向研究数学家和较早职业阶段读者的研究文章。本文的精确秩纤维、primitive divisors、fibotomic 分解及 Fibonacci 算术覆盖均高度符合其范围。Fibonacci Association
经实质修订后，以下组合足以支撑该刊论文：


lowered-label witness-cover classification；


与 Wagner minimal multiplicative covers 的严格比较；


平方自由精确纤维的规范识别；


加权精确计数；


一个完整、自足但不过度展开的熵上下界；


素数逆向射线作为简短应用。


我不会在这些修改完成后仅以“增量不足”为由拒绝。
若作者坚持保留当前全部长篇算术接口、条件猜想、支持谱及大量补编结构，而不愿压缩为更自足的 Fibonacci 主线，则 Journal of Integer Sequences 或 INTEGERS 在主题结构上也相称：前者专门刊载整数序列及密切相关主题，后者明确覆盖组合数论、乘法数论、序列、超图和极值组合。滑铁卢大学计算机科学系+1 但当前送审包在补足证明和优先权之前，不宜原样改投任何期刊。

四、重投前的必要修改
1. 提供完整、稳定、可审稿的证明包
必须将 prime-power lifting、prime–ladder dichotomy、梯级槽唯一性及全部被引用的补编结果纳入正式送审材料。正文中的每一项依赖均须指向有编号的命题。否则删除 Theorem 5.1、Theorem 5.10 精细上界及其后继结果。
这是接收的绝对前提。
2. 重写优先权小节
必须加入 Wagner 1978，并正式说明：


Wagner 条件；


素原子情形如何退化到 Wagner；


梯级原子如何构成真正推广；


本文的 Fibonacci 算术实现与加权部分何处新增。


这是第二项绝对前提。
3. 修正第一来源署名
至少补入：


Marques：固定点分类；


Luca–Tron：轨道终止性和 Fibonacci lcm 恒等式；


Levy、Webb–Parberry：fibotomic 历史；


Renault：保留为更一般序列版本；


FitzGibbons 等：仅用于其新问题、术语及其自身证明。


4. 降低素数逆向射线的标题权重
摘要中保留一至两句即可；改称 classical exact-rank existence 的直接应用。将“strictly strengthen and resolve”替换为“answer affirmatively in the stronger prime form”。不得暗示本文证明了新的 primitive-divisor existence theorem。
5. 补全 Ck​∼bk​ 的证明或删除精确渐近
必须解决 labelled/unlabeled 对象的转换。若只需二次对数主项，建议直接证明
logCk​=4log2​k2+O(k)
并把 theta-refined 精确式移至补编。
6. 改写 H1、H2
须明确 BLMS 猜想同时排斥 H1 和 H2。建议将两者改名为 sufficient maximum-window hypotheses；如仍称猜想，必须说明作者实际上在此点上采取了与 BLMS 不相容的预测。
7. 使 fibotomic 熵证明自足
增加关于 Fd​=Ψd​(1)、精确秩 radical 整除性、例外小秩和一致误差项的独立引理；同时补全历史引用。
8. 重组论文主线
建议顺序改为：


经典输入及优先权；


Wagner 比较与见证覆盖分类；


Fibonacci prime-power realization；


秩纯与平方自由切片；


加权覆盖与熵界；


素数逆向射线的短应用；


未解决的算术接口。


现行结构先突出直接进口推论，再进入真正原创的覆盖分类，不利于准确传达贡献层级。
9. 增加可核查实例
至少完整计算一个奇平方自由例、一个含例外支撑的偶数例，以及 169∈M91​∖R91rp​；每个实例应同时展示原子、Tn​、En​、覆盖和乘积。
10. 规范计算证据
若继续宣称“reproducible finite computations”，应提供稳定公开归档、环境锁定文件、SHA256 清单、运行入口以及“测试—定理”对应表。否则只应称为 finite checks，并删去可能被理解为独立证明证据的表述。有限核验不需要扩大范围；当前 n≤210 的覆盖已足以承担反例筛查功能。

最终裁决
**数学裁决：**没有发现见证覆盖主分类、平方自由规范切片、素数逆向射线或加权极值命题中的具体反例；但第 4、5 项主张的关键部分因补编缺失而尚不能认证。
**优先权裁决：**现行叙事不准确。遗漏 Wagner 1978 是实质性遗漏，足以阻止按现稿接受；固定点、轨道终止和 fibotomic 历史也须改为第一来源署名。对 Sanna、Cera、Stroiński 等增长精确秩分布边界的描述则基本准确。
**新颖性裁决：**素数逆向射线是新的直接推论，足以作为应用，但不足以作为独立核心定理。修正 Wagner 关系后，lowered-label Fibonacci witness classification、平方自由精确纤维识别及精确加权和仍构成可发表的新内容。
出版裁决：
Reject and invite a fully reconstructed resubmission.​
若完整补足证明、重建优先权边界并压缩叙事，我认为重投《The Fibonacci Quarterly》是合理且有实质成功可能的；不需要因结果层级本身而预先降投。