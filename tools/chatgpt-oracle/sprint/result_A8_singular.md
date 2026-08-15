审稿结论
建议：当前版本不应直接接收；应作实质性 major revision，若期刊流程不允许修改中心定理，则应 reject and resubmit。
这不是因为 headline 机制失败。相反，我的核查结论是：


sampled pole-order nondegeneracy 的核心计算成立；


平稳 renewal record 的 exact likelihood 结构正确，随机 complete-gap 数目确实产生 1/μ 的 calendar-time information；


由 LAN 推出半空间 Gaussian experiment、one-sided efficient test 和两点 contiguity lower bound 的基本路线成立；


N−1/4 的来源确实是 regular quotient coordinate δ 的 root-N 估计与平方根奇异映射的复合，而不是旧的 batch-means N−1/3。


但是，现稿仍有：


一条按当前表述为假的全局带标签估计结论；


两处决定 compact-uniform LAN 是否成立的证明缺口；


一处 efficient-score plug-in 缺口；


若干较小但在正式审稿中必须闭合的 uniform atlas、measurability 和 quantitative lower-bound 细节。


因此，我不能按现状签署“Theorem G 已证明”。更准确的裁决是：

Theorem G 的数学核心高度可信且大概率可修复，但当前证明尚未达到可发表的闭合程度。

修复下述问题后，我会把它视为一项真正的新、非平凡的固定阶 serial phase-type singular-inference theorem，而不是二状态计算的机械扩写。

1. 正确性审查
1.1 Sampled pole-order nondegeneracy：核心正确，但 uniform score-envelope 尚未证明
文中的变换为
Hη,δ​(s)=s1​{1−(s+c)2−δc2−δ​Bη​(s)}.
在 c=λ,δ=0 处，稿件计算
∂δ​Hη,0​(s)=Bη​(s)(s+λ)4s+2λ​,∂c​Hη,0​(s)=−(s+λ)32λBη​(s)​,
并指出各 separated-rate derivative 在自己的极点处具有二阶极点。
这部分我核对后认为是正确的：


由于其余 rates 与 λ 一致分离，Bη​(−λ)=0，故 ∂δ​H 在 −λ 处确有精确四阶极点；


∂c​H 在同一点仅有三阶极点；


∂θj​​H 在 −θj​ 处有精确二阶极点，而其他坐标在该点至多一阶；


inverse Laplace transform 后分别产生
k3e−λΔτk,k2e−λΔτk,ke−θj​Δτk;


first difference g(k)=S(k)−S(k+1) 不会消灭最高次数项，因为每个采样基底 z=e−θΔτ 满足 0<z<1；


不同 exponential-polynomial bases 以及同一 base 上不同最高多项式次数线性独立。


因此，由
a⊤ℓ˙(k)=0in L2(g)
以及 g(k)>0 推出每个 k 上的 mass derivative 恒等式，再恢复 tail derivative 恒等式，逐次迫使 aδ​,aθj​​,ac​ 为零，这一论证成立。稿件对这一点的叙述基本正确。
真正缺失的是 relative/log-derivative 的 uniform bound
稿件先证明了绝对导数上界
∣∂aSη,δ​(k)∣≤Ca​(1+k)ma​e−εΔτk/2,
随后一句话声称：

“Ratios by S or g have polynomial growth uniformly.”

再据此断言三阶 log derivatives 满足 Lemma 4.1 的条件。
这一步目前不能由前一条绝对上界推出。要控制
∂alogg(k),∂alogS(k),
必须控制诸如
g(k)∂g(k)​,g(k)∂2g(k)​,S(k)∂S(k)​
的比值。仅有 numerator 的指数上界并不能排除 denominator 因 exponential-polynomial cancellation 而更小。
这不是形式性遗漏：它正是 third-order Taylor remainder、endpoint factors 和 compact-uniform LAN 所需的主要 domination 条件。
解除异议所需的 lemma
建议增加一条独立的 uniform sampled-bin/tail score lemma：

对固定 n,ε,M,c0​,Δτ，存在碰撞 stratum 的公共单侧邻域，使得对所有 ∣a∣≤3，
qsup​∣∂qa​loggq​(k)∣≤Ca​(1+k)ma​,
并且对所有 ∣a∣≤2，
qsup​∣∂qa​logSq​(k)∣≤Ca​(1+k)ma​.

可以用两种方式证明。
方式 A：complete-holding-time conditional score。 将碰撞二元组压缩为 Y=X1​+X2​，其密度可写成
fc,δ(2)​(y)=(c2−δ)e−cyδ​sinh(δ​y)​,
在 δ=0 通过幂级数解析延拓。对 (c,δ) 的前三阶 complete-data score 是 y 的多项式增长函数；其他 rate scores 是 1/θj​−Xj​。条件在
kΔτ≤W<(k+1)Δτ
时所有 holding times 均被 O(k) 控制，因此 bin-score bounds 直接成立。tail-score 部分则需证明统一的条件矩界
Eq​[Wm∣W>kΔτ]≤Cm​(1+k)m.
方式 B：分情形使用有限 confluent expansion。 按最慢 pole 是 double cluster 还是某个 simple pole 分成有限个 separation chambers，证明 dominant coefficient 统一不为零，从而得到 S(k) 和 g(k) 的相对下界，再与导数的 confluent expansion 比较。
在该 lemma 出现之前，我接受点态与 uniform information nondegeneracy 的代数思想，但不接受由此已经完成了 compact-uniform LAN regularity。

1.2 Exact stationary likelihood：公式正确；random stopping 的 uniform CLT 仍需单列证明
稿件使用
Pq(N)​(record)=μq​1​Sq​(A)j=1∏J−1​gq​(Gj​)Sq​(R).

我没有发现 off-by-one 错误：


A=C1​ 是从窗口左端到第一个 click 的 forward recurrence；


对 lattice renewal，平稳 forward recurrence mass 的确是
P(A=a)=μS(a)​;


complete gaps 的质量为 g(Gj​)；


最后一个 click 后有 R=N−1−CJ​ 个无 click 格，要求下一 gap 满足 G≥R，故因素为 S(R)；


J=0 的全零记录需要另行写公式，但其概率在统一指数尾下指数小，因而不会影响 root-N local experiment。


端点与 normalization 的消失也合理。若
A,R=OP​(logN)
且 log-tail derivatives 具有多项式增长，则
logμq+h/N​​μq​​,logSq​(A)Sq+h/N​​(A)​,logSq​(R)Sq+h/N​​(R)​=oP​(1).
稿件正是这样使用 endpoint control。
随机 J 产生
NJ​→μq​1​,
故一周期信息 E(ℓ˙ℓ˙⊤) 被换算为 calendar information
I(q)=μq​1​Eq​[ℓ˙q​(G)ℓ˙q​(G)⊤].
这里不需要再加一个与 cycle length 相关的 variance correction，因为 one-cycle score 的均值为零；renewal-reward CLT 中应中心化的 reward 已是 score 本身。
当前缺口
稿件用“uniform renewal LLN/CLT or maximal inequality”“stopped i.i.d. score CLT”和最后的 subsequence criterion 处理全部 uniformity。 
这在研究提纲中足够，但在 headline theorem 的正式证明中太短。至少要明确证明或引用以下统一三角阵列结论：
q∈Q0​sup​dBL​(Lq​[N−1/2j=1∑JN​−1​ℓ˙q​(Gj​)],N(0,I(q)))→0,
并同时证明：


stopped Hessian LLN；


JN​=N/μq​+OPq​​(N​) 的 uniform 版本；


maximum gap、age、residual 的 OP​(logN) uniform bound；


local triangular array qN​=q+hN​/N​ 下相同结论；


third-order remainder 的 uniform integrability。


“每个参数序列取收敛子列”确实是一种合法的 compact-uniform 证明策略，但仍需在子列上写明 joint renewal-reward CLT 的条件如何统一满足，而不能只以一句“common envelopes give everything”代替。
解除异议所需条件
增加一条约一至两页的 uniform stopped renewal-score lemma，或引用一个完全匹配以下设置的定理：


gap law 随 compact 参数变化；


score 与 cycle length 相关；


stopping index由相同 gaps 决定；


local triangular array；


bounded-Lipschitz uniformity。


我认为该 lemma 是可证明的，不会改变定理，但目前它仍是证明闭合条件。

1.3 一条实质错误：全局带标签 η 的 root-N 估计不可能
这是现稿最明确的问题。
Theorem G 和 Lemma 4.3 声称存在估计量
(η​N​,δN​)
使
η​N​−ηN​=OP​(N−1/2)
在整个 compact stratum 上一致成立。 
但是稿件没有规定
θ3​,…,θn​
的排序。可见 generalized-Erlang law 对所有 rate permutation 不变。对 n≥4，取两个参数点
η=(c,a,b,θ5​,…),η′=(c,b,a,θ5​,…),
其中 ∣a−b∣≥c0​。它们产生完全相同的每个有限 N 记录分布，但带标签的参数向量相距至少 c0​。
若同一个估计量分别满足
η​N​−η=oP​(1),η​N​−η′=oP​(1),
则在同一概率分布下，它必须同时以趋于一的概率落入两个最终不相交的邻域，这是不可能的。
所以：

P6 按当前带标签向量形式为假。

这不破坏 unordered rate multiset 的结论，但必须修改 theorem、lemma 和 test construction。
两种正确修复
修复 A：规定 canonical sorting。
将 stratum 定义为例如
θ3​<θ4​<⋯<θn​,
或用排序后的 separated-rate vector
(θ(3)​,…,θ(n)​)
作为 η。由于 rates 彼此至少相隔 c0​，局部排序稳定，root-N 坐标理论不受影响。
修复 B：完全使用 quotient/multiset 表述。
把 P6 改成
dm​({{θ3,N​,…,θn,N​}},{{θ3​,…,θn​}})=OP​(N−1/2),
并说在高概率唯一 optimal matching 下，每个 noncollision rate 的匹配误差为 root-N。
同样，null nuisance fit 和 efficient score 计算必须使用排序坐标或局部 quotient chart。
这是一项必须修正的 correctness condition，不是文字润色。

1.4 “root-N null fit 代入 efficient score 只改变 oP​(1)”尚未证明
Theorem G 的 testing proof 写道：由 Lemma 4.3 得到 null fit，在 (η​N​,0) 处评价 scores 和 information，只会使标准化 efficient central sequence 改变 oP​(1)。
仅有
η​N​−η0​=OP​(N−1/2)
通常不足以推出该结论。
因为对
ΔN​(η)=N−1/2j≤JN​∑​ψη​(Gj​)
作参数展开时，
∂η​ΔN​(η0​)=N−1/2j≤JN​∑​∂η​ψη0​​(Gj​)
若其期望不为零，则该导数是 OP​(N​)，乘以 root-N 参数误差只得到 OP​(1)，而非 oP​(1)。
这里预计可以利用 efficient-score orthogonality 修复。令
ψeff​=sδ​−Iδη​Iηη−1​sη​.
则
E[ψeff​sη⊤​]=0.
对恒等式 Eη​ψeff,η​=0 求导，可得
Eη​[∂η​ψeff,η​]=−Eη​[ψeff,η​sη⊤​]=0.
于是 parameter derivative 的经验和是中心化的 OP​(N​)，经过前面的 N−1/2 和 root-N 参数误差后才是 oP​(1)。
解除异议所需 lemma
增加一个 uniform stochastic-equicontinuity statement：
∥η′−η∥≤M/N​sup​∣Δeff,N​(η′)−Δeff,N​(η)∣=oPη​​(1),
并对 estimated information 给出相同 uniform consistency。
由于这里使用的是 recurrence estimator，而不是满足 likelihood score equation 的 MLE，不能仅引用“M-estimator plug-in 标准结论”；必须明确用 efficient orthogonality。

1.5 Recurrence estimator 的局部代数是对的，但需要有限 atlas，而不是单一“fixed contours”
稿件正确地利用了：


repeated pole 时 leading Hankel matrix 仍可逆；


recurrence coefficients 是 sampled tails 的光滑函数；


separated simple roots 可由 implicit function theorem 恢复；


double cluster 的
A=z1​+z2​,B=z1​z2​
可由 contour power sums 解析恢复；


squared arcosh 在 collision 处可解析延拓；


δ root-N 后，平方根产生 N−1/4。



我没有发现这里的基本代数错误。
但“uniform separation permits disjoint fixed contours”不能按字面理解为在整个未排序 compact stratum 上存在一组全局固定、带标签的 contours。根会在允许区间内移动并交换位置。
解除异议所需条件
采用以下任一写法：


先排序 roots，然后在每个 collision base 周围构造稳定的局部 contours；


由 compactness 取有限个局部 contour charts，再规定确定性的 chart-selection rule；


直接用 Riesz projection/cluster power sums 给出不依赖单个 root 标签的局部解析映射。


同时说明 estimator 的 measurable construction，以及落在所有有效 chart 之外的 exceptional event 的概率如何一致趋零。
这是技术性但必要的 uniformization；与前述带标签不可识别问题一起修复最自然。

1.6 Contiguity lower bound：思路正确，建议增加明确的两点 testing lemma
稿件固定 η=η0​，比较
v=0,v=v0​,
两组 rate multisets 在 matching metric 下相距
v0​​N−1/4.
LAN 使两列实验 mutually contiguous；若估计量在两点的误差都小于
aN−1/4,a<v0​​/2,
则选取离估计结果更近的 candidate 就给出一致检验，矛盾。
该逻辑是正确的。特别是：


alternatives 是物理可行的；


两个半径 aN−1/4 的球最终不交；


mutual contiguity 排除两类错误同时趋零；


若
Nliminf​RN​inf​vmax​Pv​(error)=0,
可沿子列选近似最优估计量，从而仍产生违反 contiguity 的检验。


我建议将其写成一条明确的 Le Cam two-point lemma。可以使用
ϕinf​max{P0​(ϕ=1),P1​(ϕ=0)}≥21−∥P0​−P1​∥TV​​,
或直接写 mutual-contiguity contradiction。若希望给出显式 asymptotic constant，则还需证明两点实验的 testing risk 收敛到相应 Gaussian-shift risk；现有定理只要求“严格正的下极限”，不必做这一步。
因此：

下界路线成立；问题是应把当前一段论述升级为正式 lemma，而不是改变结论。


2. “matching local minimax rate”是否诚实
2.1 目前确实证明了什么
若修复上述证明问题，稿件建立的是：


uniform upper rate：在 compact collision stratum 和 bounded local alternatives 上，
dm​(RN​,RN​)=OP​(N−1/4);


pointwise local two-point lower rate：在每个固定 collision base，存在两个 local alternatives v=0,v0​，使任何估计量都不能在两点同时达到 oP​(N−1/4)。


这两项确实构成了速率意义上的 matching lower and upper bound。稿件也明确给出了 upper 和 two-point lower 的形式。
所以，“matching local minimax rate”并非虚假措辞。
2.2 但它不是完整的 local asymptotic minimax risk theorem
现有证明没有给出：


一个明确 loss L 下的 minimax risk 极限；


Gaussian limit experiment 上的最优风险常数；


对整个 bounded v-区间的 exact supremum risk；


compact base 上统一正的 lower-bound constant；


一个达到同一 minimax constant 的估计量。


因此，不应写成：


“the estimator is asymptotically minimax”；


“the exact local minimax bound is attained”；


“the minimax risk is characterized”；


“sharp minimax constant”。


一般的 local asymptotic minimax theorem要求指定局部参数集合和 loss，并比较极限风险，而不仅是证明一个 OP​ upper rate 与一个 two-point impossibility lower rate。Stanford University+1
2.3 建议采用的准确表述
我建议正文统一改为：

The unordered-multiset rate N−1/4 is uniformly attainable over compact bounded local alternatives and is pointwise locally minimax-optimal in rate at every collision base, as witnessed by a two-point threshold-risk lower bound.

中文对应为：

无序 rate multiset 的 N−1/4 速率在 compact bounded local alternatives 上一致可达，并且在每个固定碰撞基点处，由两点 threshold-risk 下界证明其在局部 minimax 速率意义下最优。

标题或摘要中可以保留：

“matching local minimax rate N−1/4”

但首次出现时必须附上“uniform upper / pointwise two-point lower / rate only”这一限定。
2.4 若要升级为完整 matching minimax theorem
需要增加：


局部参数集，例如
HV​={(η0​+u/N​,v/N​):∥u∥≤U, 0≤v≤V};


明确 loss，例如
LN​(R,R)=min{C,N1/2dm​(R,R)2},
或 threshold loss；


证明
Nliminf​RN​inf​h∈HV​sup​Eh​LN​(RN​,R(h))≥R⋆;


构造 estimator 达到同一个 R⋆。


当前论文不必完成这些，除非希望使用“exact asymptotic minimax”而非“matching minimax rate”。

3. 是否真正移出了二状态模型
3.1 我的判断：是，数学中心已经实质移出二状态，但尚未进入一般 phase-type 理论
这不是把二状态公式机械地把下标改成 n。
Theorem G 中真正新增的高阶内容包括：


nuisance dimension 从一个 centre 扩展为 n−1；


必须同时区分 collision base 上的多项式次数和 n−2 个不同 exponential bases；


information nondegeneracy 不是二状态 covariance determinant 的复制，而是一个任意固定阶的 pole-order triangular elimination；


estimator 必须从 order-n confluent recurrence 恢复 simple roots 和 double cluster 的 elementary symmetric functions；


optimal matching 需要利用 c0​ 把 double cluster 与其余 roots 一致分离。


这些都是 n-state 证明中的真实结构。Theorem G 也明确把二状态 Theorem F 作为先行特例，而非最终 headline。
Generalized-Erlang/hypoexponential family本身是标准的 serial phase-type 对象；He–Zhang 的工作专门研究 generalized-Erlang 的 Coxian 表示与 minimal Coxian representation，因此它不是为本论文临时设计的模型类。PubsOnline+1
3.2 但范围仍然很窄
现稿限制为：


fixed known order；


known Δτ；


deterministic serial chain；


exactly one double collision；


all other rates simple and uniformly separated；


reset-induced renewal record；


no simultaneous collisions；


no nonserial PH representation。


稿件对这些限制写得诚实。
所以正确定位是：

这是一个对标准 serial/generalized-Erlang family 的完整 singular stationary-record inference theorem；不是一般 phase-type、Coxian、MAP 或 D-MAP collision theorem。

它不再是 bespoke two-state calculation，但仍是 constrained structured family。
3.3 哪些证据会改变判断
以下任一扩展都会明显提高 generality：


多个 disjoint double collisions，极限参数锥变成 product cone；


multiplicity m≥3 的 collision block，并确定相应 root recovery rate；


unknown order 的一致选择与 collision recovery；


general Coxian/acyclic PH 在 canonical identifiable chart 上的 collision theorem；


unknown sampling interval 与 rates 的联合可识别性和 LAN；


minimal nonserial killed-reset kernel 的谱碰撞理论。


这些不是当前论文被接受的必要条件。当前所需的是把“fixed-order serial theorem”准确定位，而不是再扩大范围。

4. 新颖性与优先权
4.1 检索结论
截至 2026 年 8 月 15 日，我检索了以下组合：


sampled phase-type/generalized-Erlang renewal + LAN；


colliding rates/repeated poles + stationary record；


hypoexponential collision + N−1/4；


sampled renewal + singular experiment；


phase-type repeated eigenvalues + local minimax；


dead-time binary records + LAN；


near-colliding Prony systems。


我没有发现一篇先行论文同时证明：


sampled generalized-Erlang stationary binary record 的 exact finite-window likelihood reduction；


isolated double rate collision 的 quotient LAN；


sampled fourth-order-pole information nondegeneracy；


nuisance-adjusted one-sided Gaussian power envelope；


unordered rates 的 N−1/4 upper 与 two-point lower。


因此，组合定理很可能是新的。但检索无法逻辑上证明“世界上不存在先例”，所以不建议声称“the first theorem”。
4.2 最接近先行结果的逐项分类
本文成分最接近先行工作审稿判断Generalized-Erlang/Coxian 表示、minimality、非唯一表示He–Zhang 的 generalized-Erlang Coxian representations 与 minimal Coxian algorithm不是本文的新内容；本文 population recurrence 是其 sampled finite-coordinate specialization。PubsOnline+1MAP2/DMAP2 weak equivalence 与 canonical coordinatesRamírez-Cobo–Lillo、Ramírez-Cobo–Lillo–Wiper；Mészáros–Telek这些工作限制二状态 hidden representation priority，但不推出 Theorem G 的 singular stationary inference。Springer Link+2剑桥大学出版社+2Boundary Gaussian cone、one-sided LRTChernoff、Self–Liang、Dacunha-Castelle–Gassiat、Liu–Shao一旦 LAN 和 information 已证明，half-space test 与 power envelope 基本是标准推论，不应作为独立新原理宣传。Project Euclid+2JSTOR+2N−1/4 singular recovery phenomenonChen；Ho–Nguyen；Heinrich–Kahn 的 mixture singularity/minimax 文献N−1/4 这一指数和“regular quadratic coordinate 经平方根恢复”的现象并非普遍意义上的新发现；本文的新意在具体 sampled renewal experiment 中证明它并给出 matching rate。arXiv+3Project Euclid+3arXiv+3Confluent recurrence 和 near-colliding root instabilityBatenkov–Yomdin、Akinshin–Goldman–Yomdin 等 Prony 文献repeated/near-colliding nodes 的不稳定性、confluent Prony 和 matching-order reconstruction bounds 已有系统研究；本文 recurrence estimator 是有统计内容的非平凡 specialization，但不能说首次发现 root collision instability。美国数学学会+2工业与应用数学学会+2平稳 renewal window 的 age/residual censoring经典 equilibrium renewal theory；Gill 等关于 finite-window stationary renewal observation 的工作endpoint length bias 与 censored complete gaps 是经典结构；本文有价值的是把它做成 compact-uniform parametric LAN lemma。arXivdead-time binary records 的 LAN 和 efficient estimationJorgensen–Johnson 2026 对 periodic nonparalyzable dead-time event detection 的 LAN、Fisher information 和 efficient estimators这是应用背景中很接近的新先行结果，但模型和奇异性不同：它不处理 generalized-Erlang rate collision，也不产生 N−1/4 root recovery。正文必须明确比较，而不应只把它放在参考文献中。arXiv+1
4.3 必须补充的优先权引用
现稿已经引用一般 locally conic/loss-of-identifiability 理论，并把模型特定增量描述为 pole-order、stationary reduction 和 rate matching。
但仍建议加入三组引用：
A. Singular estimation rate
至少加入：


Chen, Optimal Rate of Convergence for Finite Mixture Models；


Ho–Nguyen 关于 singularity structures/rates；


Heinrich–Kahn 关于 local minimax rates。


并写清这些是相邻模型中的先例，不是本文定理的直接来源。尤其 Heinrich–Kahn 对早期 mixture-rate 叙述作过修正，不能只孤立引用 Chen 并把 N−1/4 描述为一般规律。Project Euclid+2Project Euclid+2
B. Near-collision Prony
至少加入：


Batenkov–Yomdin, On the Accuracy of Solving Confluent Prony Systems；


Akinshin–Goldman–Yomdin, Geometry of Error Amplification in Solving the Prony System with Near-Colliding Nodes。


说明本文不是首次观察 root collision instability，而是把 quotient-coordinate recurrence recovery 嵌入一个 stationary statistical experiment，并匹配其 statistical lower bound。工业与应用数学学会+1
C. 2026 dead-time LAN comparator
Jorgensen–Johnson 必须在主文 comparison section 中出现，而不仅列入 references。他们已经对另一类 non-i.i.d. binary dead-time event records 建立 LAN、information lower bounds 和 efficient estimation。本文应准确说区别在于：


renewal reset vs periodic gated DED；


regular parameter vs double-rate loss of first-order identifiability；


root-N regular estimation vs N−1/4 unordered collision recovery。arXiv


4.4 建议使用的 priority language
建议写：

To our knowledge, no previous result gives the stationary finite-window LAN experiment at an isolated rate collision for a sampled generalized-Erlang renewal record, together with sampled pole-order information nondegeneracy and matching N−1/4 unordered-rate recovery. The boundary Gaussian experiment, singular-rate phenomenon, confluent Prony algebra, and phase-type representation ingredients each have substantial antecedents cited below; the contribution is their model-specific stationary-record synthesis and proof.

不建议写：


“we discover the N−1/4 phenomenon”；


“the first collision minimax theorem”；


“a new general phase-type singularity theory”；


“the first LAN theory for dead-time binary records”。



5. 层级、venue 与文章结构
5.1 是否达到此前所说的“整级提升”
在数学实质上，达到了。
旧中心是一个 constrained two-state quotient 及其 visible-law inference。新中心是：


任意固定 serial order；


n-维局部实验；


compact-uniform stationary LAN；


model-specific information nondegeneracy；


efficient one-sided testing；


singular quotient estimation；


upper/lower rate matching。


这已经把论文从“特定二状态模型的较完整分析”提升为“标准 structured stochastic family 上的一项 singular statistical experiment theorem”。
但这个提升的终点是：

扎实的 applied-probability / stochastic-model methodology paper，带有真正的统计奇异性定理。

它尚未成为：


一般 phase-type collision theory；


一般 hidden Markov loss-of-identifiability theorem；


顶级统计期刊意义上的完整 local asymptotic minimax theory。


所以，“整级提升”成立，但不能再向上夸成 general PH breakthrough。
5.2 Methodology and Computing in Applied Probability 是否合适
合适，而且是当前最自然的 venue。
MCAP 的官方 scope 明确强调 applied probability 中的方法论与计算；该刊也发表过 Ramírez-Cobo–Lillo 关于 MAP2/MAP3 weak equivalence 的直接相关工作。Springer Link+1
本稿修复后与该刊的契合点是：


applied-probability model；


renewal/MAP/phase-type 交界；


inferential methodology；


explicit recurrence algorithm；


nonstandard asymptotic experiment。


当前没有真实数据或 substantive case study 并不是 scope violation；但 numerical algorithm 的实现和 finite-sample illustration 若完全缺席，会使“Computing”一侧偏弱。官方 scope 将 detailed case studies 说成特别关注，而非所有稿件的硬性要求。Springer Link
当前形式下的决定
由于带标签 P6 为假、uniform score bounds 和 plug-in lemma 尚缺，我不会建议 MCAP 直接接收。修正后则是可信且相当有竞争力的 MCAP 稿件。
5.3 其他期刊
Stochastic Models
这是合理备选。该刊覆盖随机模型的理论与应用，phase-type、renewal 和 inferential structure 均在其自然范围内。Taylor & Francis Online+1
若文章保留较多 D-MAP representation、fibre 和 model-specific algebra，Stochastic Models 可能比纯统计期刊更自然。
Advances in Applied Probability
属于有理由尝试但偏 reach 的选择。AAP 强调对 applied probabilists 有广泛兴趣的数学和科学工作。剑桥大学出版社
以当前“一次 double collision、fixed serial order”的一般性，我认为尚不足以使 AAP 成为稳妥目标。以下任一改进会明显增强 AAP 可行性：


multiple collision blocks；


multiplicity m 的统一 theorem；


broader Coxian/acyclic PH class；


更抽象的 stationary regenerative singular-LAN mechanism；


把 Theorem G 提炼为短而集中的核心文章。


Queueing Systems
并非最佳选择。该刊的中心是广义 resource-sharing/queueing models；本文使用 phase-type 对象，但并未研究 queue performance、resource sharing 或网络排队。Springer Link
仅凭 generalized-Erlang 与 MAP 背景，不足以使其成为比 MCAP 更自然的 venue。
物理期刊
不建议重新转向物理 venue。稿件自己已经准确承认 sampled counter 是 constrained kernel 的 interpretation，而不是独立分析的物理系统。
新 theorem 提高的是概率与统计层级，不会自动把模型解释变成新的 detector physics。

6. Article architecture 是现在最大的非证明性限制
目前摘要和前半篇仍给 two-state quotient、three-inclusion inverse、specification tests、fibre arc 和 covariance certificate 很大篇幅；摘要甚至继续突出一个“candidate original result pending complete reduction”。
虽然稿件称 Theorems F–G 为中心，实际 Theorem G 到第 35 页左右才出现。
正式审稿人很可能产生如下印象：

作者把一个新的、较强的 serial collision theorem 附加到了原有二状态论文后面，而不是围绕新 theorem 重新设计文章。

这会削弱“整级提升”的呈现。
建议的重组条件


标题、摘要、引言第一问全部围绕 Theorem G。


第一主结果直接给 fixed-order serial theorem。


紧接着给 stationary renewal LAN lemma、pole-order lemma、test、estimator 和 lower bound。


Theorem F 改为 n=2 的 motivating corollary 或 worked example。


Two-state A–E、three-inclusion diagnostic、fibre arc、pointwise certificate 大幅压缩或移入 supplement/companion paper。


sampled-counter physics 只作为 application subsection，而不是与 headline theorem 并列的主叙事。


删除摘要中的“candidate original result pending complete reduction”；尚未完成 priority reduction 的 secondary result 不应占用 headline abstract。


若不重组，论文仍可能适合 MCAP，但编辑和审稿人会低估 Theorem G 的贡献，并质疑 article coherence。

最终逐项裁决
问题 1：证明是否正确？
核心路线正确，但当前证明不完整，且有一条带标签估计结论为假。
必须修复：


将 θ3​,…,θn​ 排序或改为 multiset/optimal-matching 表述；


增加 uniform log-bin/log-tail derivative lemma；


增加 uniform stopped renewal-score CLT/LLN lemma；


增加 efficient-score plug-in equicontinuity lemma；


用 finite analytic atlas 或 quotient root map 处理 recurrence estimator；


将 contiguity lower bound 写成正式 two-point lemma。


完成这些后，我没有看到阻止 Theorem G 成立的结构性反例。
问题 2：minimax 措辞是否诚实？
“matching local minimax rate”在速率意义下可以成立。
但应明确：


upper bound 是 compact-uniform；


lower bound 是 fixed-base、two-point、threshold-probability lower bound；


不包含 exact minimax risk constant。


最准确的表述是“uniformly attainable and pointwise locally minimax-optimal in rate”。
问题 3：是否真正移出二状态？
是。
它是标准 generalized-Erlang family 上的任意固定阶 theorem，不是二状态 notation inflation。但它仍是 serial、single-double-collision、known-order、known-Δτ 的 structured theorem，不是一般 PH theorem。
问题 4：是否新颖？
组合 theorem 很可能新颖；各组成机制并不分别新颖。
最可能的新贡献是：


exact stationary finite-record reduction；


sampled pole-order uniform information proof；


generalized-Erlang collision half-space experiment；


recurrence upper bound 与 stationary-experiment lower bound 的组合。


必须补充 singular-rate、near-colliding Prony、stationary renewal censoring 和 2026 dead-time LAN 文献，并显著收窄 priority language。
问题 5：层级与 venue？
修复后：MCAP 合适，并且确实比旧二状态版本提高一个数学层级。
当前版本：不应接收。
修复证明但不重组：solid MCAP / Stochastic Models 稿件。
修复并以 Theorem G 重组全文：较强的 MCAP 稿件，并可把 AAP 视为有风险的上探。
物理联系仍只是模型解释；新结果提升的是概率统计层级，而不是物理内容。

最终 referee recommendation

Major revision / reject and resubmit.
The central fixed-order serial collision theorem appears mathematically substantial and probably correct after repair. The sampled pole-order argument and the stationary-record reduction are convincing at the structural level, and the N−1/4 two-point lower bound is sound. However, the current statement contains a false globally labelled root-N estimator claim, and the compact-uniform LAN and plug-in efficient-score assertions rely on unproved relative-score and stochastic-equicontinuity bounds. Acceptance should be conditional on correcting the quotient parametrization, supplying these uniform lemmas, tightening the minimax language, completing the priority comparison, and reorganizing the article around Theorem G.