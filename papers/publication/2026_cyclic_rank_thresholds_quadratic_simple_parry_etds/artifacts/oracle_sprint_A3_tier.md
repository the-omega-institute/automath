总裁决
严格结论：按现有机器，只增加“固定 θ 的精确深度公式”仍不足以使论文上升一个完整层级。
它会显著加强论文，因为它同时固定了代数次数、基数、Parry 语言和二进制字母表，排除了 Bassino 族中“无界性只是参数和字母表一起增长”的解释；但它仍然是对本文自定义 cyclic rank-fold 的另一个精确模型。较高层级审稿人仍可用一句话压住它：

这是一个精巧构造族的精确分析，而不是关于 Pisot numeration、β-normalization 或 β-dynamics 的结构定理。

现稿自己已经非常清楚地区分了整数语言秩同余与数值 β-normalization，且指出两者没有被识别。 现有 Fischer 状态数也明确依赖固定输出字母表，而非共轭不变量。
因此：

若“可达”要求成功概率至少约 1/2，则诚实答案是：当前不存在一个同时可达且足以升一层的单一结果；按现有机器，不能升。

但有一个边缘可达、且一旦成功我会承认它足以升层的精确定理。它应成为唯一的升层目标。

1. 单一最有价值的新结果
首选：固定基数线性因果深度与 sharpness 定理
建议把目标写成下面这个完整定理，而不是只写固定 θ 的公式。
定理 A：Pisot numeration 的固定基数线性深度定理
设 U=(uj​)j≥0​ 是一个严格递增的 Pisot numeration system，允许非标准初值，u0​=1，其 canonical greedy digit set 为有限集
DU​={0,…,dU​}.
设 XU,m​⊂DUm​ 是长度 m 的 canonical greedy U-正规词集；等价地，
x=(x0​,…,xm−1​)∈XU,m​⟺j=0∑k​xj​uj​<uk+1​(0≤k<m).
于是
ValU,m​(x)=j=0∑m−1​xj​uj​
把 XU,m​ 双射到 {0,…,um​−1}。定义
FoldU,m​(w)=(ValU,m​∣XU,m​​)−1(ValU,m​(w)modum​)
及相应滑动码 ΦU,m​。
假设 U preserves zeros，亦即其 leading Pisot root 满足 Condition F。则存在一个可由 U 的递推、canonical digit set 和 bounded-zero normalization automaton 有效计算的常数
CU​<∞
使得，对每个 m≥2，
ΦU,m​ 单射⟹ℓcau​(U,m)≤CU​m.(A1)
等价地，在相应差分碰撞图中，若首坐标非零状态不可达有向环，则所有从该初态集出发的有向路径长度均至多 CU​m−1。
此外，令 θ 为
x3−2x2+x−1
的实根，并令 Uθ=(Qj​(θ))j≥0​。则对所有 m≥4，
Φθ,m​ 单射,ℓcau​(θ,m)=2⌊2m​⌋−1.(A2)
更强地，若
λm​=2⌊2m​⌋−1,
则应证明
Nθ,m,λm​−1​=∅,Nθ,m,λm​​=∅,(A3)
并最好进一步分类出
Nθ,m,λm​−1​={±Em​}
的唯一终端碰撞对。
由此
m→∞lim​mℓcau​(θ,m)​=1,
所以固定 Pisot numeration 下的线性上界在增长阶上不能改进为 o(m)。

为什么这个定理能升层
它完成了三件固定 θ 公式单独做不到的事。
第一，它把研究对象从“某个自定义 β-rank-fold 的若干参数族”提升为标准 Pisot numeration system 上的统一复杂度定理。
第二，它把现稿一般界
ℓcau​≤(2d+1)m−1−1
从状态枚举给出的指数界，压到固定系统下的线性界。现稿的指数界来自差分图非零顶点数，本身没有使用 Pisot 收缩或 normalization automaton 的细结构。
第三，固定 θ 的公式成为 matching lower bound，而不再是孤立的漂亮例子。这样论文的中心会从：

“我们精确算出了几个 arithmetic local codes”

转变为：

“固定 Pisot numeration 的 cyclic normalization 深度至多线性，而且线性阶在一个固定二进制三次系统上精确达到。”

这是结构性结论，而不是再增加一个族。

上一轮固定 θ 候选的裁决
若只证明
∀m≥4,Φθ,m​ 单射,ℓcau​(θ,m)=2⌊m/2⌋−1,(Θ)
我的判断是：
数学上有价值，优先权明显增强，但仍不足以稳定升一个完整层级。
它确实排除了：


字母表随 n 增长；


基数随 n 增长；


Parry word 长度随 n 增长；


Bassino 参数中大首位数字带来的强分离。


所以它比现稿的 Bassino 定理有真正不同的含义。现稿的 Bassino 结果依靠参数一致的两窗口 carry exclusion 和精确终端路径归纳。  但固定 θ 仍然只说明本文映射的一种新现象，未给出全类上界，也没有把该深度变成标准 numeration invariant。
我的层级影响评分只有约 0.45/1：足以让现稿更强，不足以单独改变审稿人的根本分类。

次选：完全闭合二次负共轭室
精确定理应为：
定理 B：负共轭二次 Pisot 的统一两输出解码
令 β 为
x2−ax−b,a≥b≥1
的 Pisot 根。则对每个 m≥3，
ℓcau​(β,m)=2.(B)
这会把二次结论完整化为
ℓcau​(β,m)=⎩⎨⎧​2,3,​β′<0, m≥3,β′>0, m≥3.​
但它只是关闭现稿已经明确列出的接口。现稿也准确指出，所缺的是对全部 bounded-carry branches 的穷尽不变量，而不能只按 Qm​ 的倍数和商的符号分类。 因而它是很好的 completion theorem，却不是升层定理。

2. 各候选能否由现有 machinery 达到
2.1 定理 A：统一线性上界加固定 θ sharpness
现有机器中可直接输入的部分
现稿已经给出最重要的第一步：
ℓcau​(β,m)=min{L:Nβ,m,L​=∅},
并把它等价成差分图中从首坐标非零状态出发的最长生存路径。
还已有：


差分状态商保留全部碰撞，而不是只给必要条件；


零状态唯一前驱；


单射、有限 future-only inverse、不可达有向环三者等价；


有向环给出周期碰撞证书；


Bassino carry exclusion；


Bassino terminal-path induction；


quadratic recurrence annihilator 与 nearest-multiple separation。


现稿已经把 classical pair graph 与新的 arithmetic quotient 分开，这一定位现在是正确的。
真正可用的标准对象桥
设一个碰撞窗口满足
j=0∑m−1​uj​et+j​=kt​um​.
则它等价于一个标准 U-零表示：
[et​,et+1​,…,et+m−1​,−kt​]U​=0,(2.1)
其中最后一个坐标位于权 um​。
对固定 U，由于 uj​≍βj，
∣kt​∣≤dU​um​∑j<m​uj​​
有一个与 m 无关的统一上界。因此所有窗口都属于某个固定有限字母表上的 bounded zero-representation language。
这是真正的非循环桥。Pisot numeration 的 bounded zero representations 构成正则语言，是标准 normalization 理论中的结果。arXiv 2026 年的新工作又把这类零表示、normalization 和 zero-preservation 常数 Kc​ 放入标准 U-adic 框架。arXiv
真正缺少的新 ingredient
缺少的不是“再画一张 pair graph”，而是：

重叠零表示条带的线性压缩/泵引理。

具体必须证明：
给定固定的 bounded-zero automaton，若长度 m+1 的 accepted zero words 按一个坐标逐次重叠，且相应差分路径不存在可泵成双边周期碰撞的循环，则该重叠链长度至多 CU​m。
标准正则语言 pumping lemma 本身不够。宽度为 m 的重叠积可以有指数多个 strip states；如果不使用 Pisot recurrence 的边界消去、共轭收缩或 carry 单调性，仍然只能得到指数界。
所需新引理应同时使用：


固定阶递推消去窗口内部；


kt​ 的固定有限 carry alphabet；


两端边界状态，而非整个 m−1 位差分词；


Pisot 共轭方向的收缩；


“重复相同边界类型会泵出可达周期碰撞”的严格结论。


这是一个真实的新证明部件，而不是把目标定理改名为“线性路径引理”。
可达性判断
边缘可达，成功概率约 0.35。
风险在于一般固定 Pisot recurrence 的重叠条带可能仍具有比线性更长的无环暂态；正则性不会自动排除这一点。要么找到上述两端压缩，要么就可能发现定理 A 本身为假。
若它为假，而能构造一个固定 Pisot numeration 上超线性、甚至指数级的 ℓcau​，那反例本身也会是较高层级结果；但现稿目前没有任何数据支持这种方向。

2.2 固定 θ 精确公式
对
θ3−2θ2+θ−1=0
有
dθ​(1)=11010∞,
且
Q0​=1,Q1​=2,Q2​=4,Qj+3​=2Qj+2​−Qj+1​+Qj​.
现有机器可以输入：


Theorem 6.2 的 Toeplitz obstruction；


zero-predecessor lemma；


Bassino terminal induction 的组织方式；


cubic conjugate energy estimate 的思路；


有限图中提示的唯一终端路径及奇偶配对。


真正缺的是：
两步 aperture renormalization
需要证明一个 m↦m−2 的精确递归：


所有非终止 carry branches 都被排除；


唯一最长路径在去掉两端固定短块后化为 aperture m−2 的唯一最长路径；


奇数 m=2r+1 与前一个偶数 2r 具有同一非零核心，只多一个终端零；


终端 obstruction 只有 ±Em​。


现稿 Bassino 的 Lemma 6.7 不能直接移植。那里关键使用
Qj+1​>nQj​
以及随参数 n 增大的强分离；固定 θ 的比例不到 2，而其最小递推还含负系数。现稿的 quadratic nearest-multiple separation 也不能替代这一工作。
因此上一轮的 0.82 成功率偏高。我的复评是：
0.70​
它仍是当前最可做的内部加强，但参数一致的“无旁支”证明是实质困难，不是有限枚举后补一个归纳句即可。

2.3 负共轭二次室的 ℓcau​=2
现有输入非常充分：


Lemma 5.3 nearest-multiple separation；


Lemma 5.4 bounded sliding congruences；


二次递推的二阶消去；


Pa,b−​ 的短 bounded multiple (b,a,−1)；


Theorem 6.2 的最长路径判据。


真正缺少的仅是现稿自己指出的：

对两个连续同余的全部 carry types 给出闭合且参数一致的有限状态不变量。

这里不需要引进 natural extensions、tiles 或外部数论。成功概率很高：
0.88​
但即使成功，仍只是完成二次表格；层级影响有限。

3. “成功概率 × 层级影响”排序
这里“层级影响”取 0 到 1：1 表示在证明和写作都合格时，足以实质改变论文的优先级判断；不是对定理真假的概率。
排名候选成功概率层级影响乘积裁决1定理 A：固定 Pisot numeration 下 O(m) 上界，加固定 θ 的 Θ(m) sharpness0.350.950.333唯一真正升层候选2固定 θ：ℓcau​=2⌊m/2⌋−1 及唯一终端路径0.700.450.315最佳内部加强，但单独不升层3全部负共轭二次基数、全部 m≥3：ℓcau​=20.880.180.158应闭合，但只是 completion4标准 Fibonacci numeration 的最优 zero-preservation 常数 K2​0.550.250.138标准对象，但体量太小，宜另文5把 rank-fold 深度直接识别为 U-adic 群上平移或环面编码的标准 delay0.080.980.078影响极高，但当前桥很可能不存在6Hejda–Steiner 的 quadratic β-adic prefix 问题0.021.000.020当前机器到不了
第四项值得附带说明。2026 年 8 月的 U-adic 预印本定义了 Kc​，并称计算提示 Fibonacci 情形 K2​=3。arXiv 但按其定义，取标准 Fibonacci 权
u0​=u1​=1, u2​=2,…
及
g5​=−2,g6​=2,g7​=−2,g9​=−2
而其余坐标为零，则
[g]U​=−2u5​+2u6​−2u7​−2u9​=−142.
另一方面
142=u10​+u8​+u6​+u4​+u1​=89+34+13+5+1,
故
ord(g)=5,νU​(g)=1,
从而
K2​≥4.
所以“K2​=3”不能作为可直接证明的目标；较合理的小目标是判定 K2​=4 还是更大。即使证明 K2​=4，它也不足以承担本论文的升层任务。

4. 四种升层杠杆逐项裁决
(a) 解决具名公开问题：目前不适用
Hejda–Steiner 的原始公开问题中，问题 (C) 明确问：

“一般二次 β 的整数 β-adic 展开前缀具有什么结构？”

同页还列出 γ(β)=1、γ(β)=0 和 cubic Pisot 情形的问题。arXiv
但 β-adic 前缀的定义是
x−i=0∑n−1​ui​βi∈βnZ[β].
这是 Z[β] 中按主理想 βnZ[β] 的同余。arXiv
现稿处理的是
j=0∑m−1​Qj​et+j​∈Qm​Z,
即普通整数环中模整数 Qm​ 的同余。两者之间没有现成的同态，也没有理由令 Qm​Z 对应 βmZ[β]。
什么会解决这一反对：
必须证明一个独立的比较定理，把 rank congruence 的有限前缀纤维嵌入或双射到 β-adic prefix classes，并证明该比较对移位和 carry 相容。
现稿没有这样的桥；fixed θ 公式也不产生它。因此不能把任何 Hejda–Steiner 问题报作可达目标。

(b) 对标准对象证明结果：有条件适用，而且这是正确方向
正确的标准对象不是数值 β-normalization本身，而是：
Pisot numeration 的 bounded zero representations 与 normalization automaton​
标准数值 normalization 保持的是
∑cj​βj
的精确数值，而现稿只保持整数 rank 的模 Qm​ 余数。Pisot 基数上的数值 normalization 可由有限 transducer 实现，但那仍是另一张映射。arXiv
真正可用的桥是前述恒等式
j<m∑​uj​et+j​=kt​um​⟺[et​,…,et+m−1​,−kt​]U​=0.
它把每个窗口碰撞变成标准 U-零表示。bounded zero representations 的正则性已有标准理论。arXiv
但是不要声称
lim​Z/um​Z≅ZU​.
新的 U-adic 工作明确指出，Pisot carries 可向两个方向传播，所得 ZU​ 一般不是 profinite group；而有限群逆极限必为 profinite。因此这种最直观的模 um​ 逆极限识别在拓扑上不可能成立。arXiv 初值的选择还会改变环面映射是 tiling、covering 还是不满射，进一步说明 Qj​ 的非标准初值不能被静默忽略。arXiv
所以 (b) 的可行版本正是定理 A，而不是“把 rank-fold 改称 U-adic normalization”。

(c) 删除真实假设：剩余杠杆很弱
Pisot 假设在 simple-Parry 差分图、aperture-two 三分中已经被真实删除；这是现稿的有效增量。
剩下可删的主要是假设 simple-Parry。但一般 eventually-Parry 或一般 sofic β-shift 中，canonical colex rank 通常不再是单一标量权重
∑xj​Qj​;
它会依赖 automaton state。此时差分商需要附加语言状态，容易退化回标准 pair graph。即使技术上扩展成功，也未必保留本文最有特色的 Toeplitz arithmetic quotient。
因此：


“simple-Parry → eventually-Parry”成功概率不低；


但它很可能只是 state-augmented classical construction；


单独不足以升层。


负共轭二次室的 ℓ=2 也不是 hypothesis removal，而是结论补全。

(d) sharpness / matching bound：这里最适用
这是当前唯一真实强杠杆。
现稿的一般上界是指数级状态界，而 Bassino 族只证明某个随基数变化的线性下界。固定 θ 公式会证明：
ℓcau​(θ,m)≍m
即使基数、次数和字母表全部固定，深度仍无界。
但这只排除了 Oθ​(1)；它尚未说明现稿指数界的正确增长阶。
真正的 matching result 必须是：
ℓcau​(U,m)=OU​(m)
对全部固定的相关 Pisot numeration 成立，同时固定 θ 给出
ℓcau​(θ,m)∼m.
这才是 sharpness，而不是再增加一个 exact example。

5. 即使首选定理证明后，最强的审稿反对意见
即使定理 A 完整成立，最难的一条反对仍会是：

论文所量化的仍是人为选择的 cyclic finite-section normalization 的 decoder depth；它是否揭示了 Pisot numeration 或 β-dynamics 的内在现象，而非某种特殊坐标编码的复杂性？

这一反对很强，因为：


阈值以上的 Yβ,m​ 共轭于 full shift；


Fischer 状态数和 Markov 阶是在固定输出字母表下的 presentation complexity，而非共轭不变量；


现稿明确不主张 numerical β-normalization、signed digits、natural extension 或 tile 结论。


结论部分也承认，现有机器不处理 β-value equality、一般高次非 simple-Parry 基数或标准 Pisot substitution interfaces。


真正消除这一反对所需的结果
定理 A 之后还应当给出一个比较推论，但不必再是一整篇新理论。最低合格形式是：

线性常数 CU​ 可以由标准 bounded-zero automaton 的某个 canonical synchronization exponent 或 zero-preservation constants Kc​(U) 有效控制；并且固定 θ 的精确终端路径同时给出该标准 normalization invariant 的精确线性下界。

也就是说，最终应出现一个不再提 Fold 的结论，例如：

对固定 Pisot numeration U，所有宽度 m 的、逐位重叠的 bounded zero-representation strips，要么可泵成周期零表示，要么在 OU​(m) 步内同步；该阶在 Uθ 上为 Θ(m)。

这样，rank-fold 会成为发现和证明标准零表示定理的工具，而不是论文的最终对象。
若做不到这一比较，最强反对意见不会彻底消失；但定理 A 的统一性和 matching bound 仍可能足以使论文上升一个层级。若只加入固定 θ 公式，该反对意见几乎原封不动地保留。

最终 go/no-go


把固定 θ 公式作为现稿加强：Go。


把固定 θ 公式单独当作升层工程：No-go。


把“固定 Pisot numeration 下 O(m) 上界 + 固定 θ 的精确 Θ(m) 下界”作为唯一升层目标：Go，但成功概率仅约 0.35。


若无法建立新的重叠零表示条带压缩引理，则应接受结构性封顶：本稿可以变得更完整、更漂亮，但不能仅靠同类 exact-depth 计算再上一个层级。


最后，这一层级判断仍以当前 Lemma 5.3、6.7、6.8 的全参数证明最终可签署为前提。现稿自己正确声明脚本只是 regression 与廉价证伪，而不是统一证明证书。