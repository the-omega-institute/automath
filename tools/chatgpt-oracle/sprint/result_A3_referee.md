匿名审稿报告
审稿建议：Major Revision。若编辑部不允许对优先权叙述、主定理层级和核心证明作实质重构，则建议 Reject and Resubmit。
本文对研究对象的界定是清楚的：所研究者是固定长度 greedy β-语言的整数秩模 Qm​ 循环化及其滑动重叠，而非 Z[β] 中的数值正规化；这一收缩是必要且正确的。 
我的总体判断如下。


没有发现一个可立即推翻主定理的反例或内部矛盾。


现稿尚不足以使审稿人签署“证明完整”：Lemma 5.3、Lemma 6.7、Lemma 6.8 的若干参数一致估计和穷尽步骤压缩过度。


现稿的优先权叙述存在一项确定的实质遗漏：Theorem 6.2/Corollary 6.3 所用的碰撞图—有向环—可逆性判定，属于经典的一维局部码、tessellation automata、cellular automata 和 fiber-product/pair-graph 传统，不能作为整体的新框架提出。


在修正该优先权问题并补全证明后，本文的真正新增量足以支撑 DCDS-A 论文：全部二次 Pisot 基数的精确阈值、精确有限块起点及 Markov 阶；simple-Parry 算术差分图的特殊压缩和孔径二分类；以及 Bassino 三次族上的精确无界未来解码深度。现稿不需要再附会任何具名公开问题。



一、数学正确性
1. Lemma 5.3 是当前最严重的证明审查障碍
Lemma 5.3 的最近倍数分离估计是 Lemma 5.4 乃至全部二次主定理的算术承重点。 Theorem 5.5 随后直接以 Lemma 5.4 消灭全部长度 m 的滑动差分核。
我未发现该引理的数值结论明显错误，但目前无法充分核验下列两段。
第一，正号递推情形中，式 (5.12) 的 Euclidean-division 分支在 p=r 后引入整数 w，继而从 w>0 或 w<0 直接进入两个清分母后的“穷尽终端不等式”。现稿没有完整展示这些不等式如何由前述整除条件推出，也没有在同一位置逐一处理可能的端点等号。
第二，负号递推情形从整数范数 ν 转入 δ、D、H 后，最后两个严格裕量虽然被列出，但从这些裕量到
kb−gU−​>1
的参数一致推导仍过于压缩，尤其应明确所有分母的正性以及 b=a−2、e=a−1 等边界参数。
足以消除异议的修订：


将 Lemma 5.3 分成正递推与负递推两个独立引理；


对每个 quotient/remainder 分支写出清分母前后的等价式；


列明各分母正性、严格端点以及非互素 a,b 情形；


将 w>0、w<0 两个终端分支整理成一张完整代数表，不能只陈述最终不等式；


最后单独给出从 ∣hRr​−skb∣≥1 到距离估计的闭合步骤。


**裁决影响：**若上述补充成立，本项异议消除；若不能给出，则 Theorem 5.5 及其后续精确阈值、Fischer cover 和 Markov 阶结论均失去统一证明，裁决应改为拒稿。

2. Lemma 6.7 的共轭估计需要改写为可逐行核验的独立引理
Lemma 6.7 中，前半段的 carry 范围和末位数字限制是清楚的；困难在于从三次共轭递推
uj+2​=suj+1​−puj​
转入二次型 Ij​，再由 Ij​=pjI0​ 得到 ∣uj​∣<2，最终推出
n<B<Qr​−n.
现稿把这条链压缩在极少数行内。 对上界的最后一步又仅以“减去误差后仍超过 n”结束，没有将其化为一个显式的、对 n≥4 单调为正的多项式裕量。
这里并非要求增加计算实验，而是要求证明文本本身能够表明：


0<p<1 在所用范围内为何成立；


二次型严格正定；


Ij​=pjI0​ 的直接验证；


∣uj​∣<2 所用的准确分母；


B>n 与 Qr​−B>n 的最终显式下界；


小孔径 r=2,3 与统一论证之间没有遗漏接缝。


**足以消除异议的修订：**增加一项“conjugate-error lemma”，把上述五个结论列为分项，并把最后两个裕量写成 n,r 的显式正表达式。
**裁决影响：**完成后，本项不会阻碍发表；未完成时，Theorem 6.9 的关键两窗口排除未经充分证明，三次无界定理不能接受。

3. Lemma 6.8 的归纳分类逻辑可信，但“force”步骤必须展开
Lemma 6.8 是三次主定理的另一承重点。现稿在归纳步中删除首、末坐标，将中间向量归入 Kn,r−1,r−2​，随后以“the exact window sums force the final coordinate to be zero；the first congruence then forces the initial coordinate”完成分类。 这两个“force”正是排除额外终端路径的所在，不应以文字略过。
足以消除异议的修订：


明确写出删除坐标前后各窗口编号的对应关系；


对中间向量为 0,En,r−1​,−En,r−1​ 的三个分支分别列出最后窗口和第一窗口方程；


证明所确定的首、末坐标在 [−n,n] 内唯一；


说明不存在通过改变 carry c0​ 而得到另一首坐标的可能；


最好给出一张 r↦r+1 的坐标模板，而非依赖读者自行追踪下标。


Theorem 6.9 完全依赖该终端分类把
Nβn​,r,r−1​={±En,r​},Nβn​,r,r​=∅
代入碰撞准则。
**裁决影响：**补全后可接受；若仍仅保留当前文字归纳，则三次主定理应视为证明不完整。

4. Theorem 5.9 有两个较小但确实存在的缺口
现稿为证明自然重叠图右分解，称两个同起点边的秩差 hQm−1​ 在模 Qm​ 下非零。 这不能仅由 h=0 推出，因为一般并无 gcd(Qm−1​,Qm​)=1 的统一假设。所需事实应明确写成
Qm​>dQm−1​,
或给出与此等价的距离估计。负号室中该不等式直接；正号室中需要调用已证明的比值界。
其次，从“长度 m−1 的标签词有两条路径终止于不同 Fischer 状态”到“该词不是 intrinsically synchronizing”需要一项标准引理或一个两行证明：利用 follower-separatedness 选择只属于一个终态的后继，再利用右分解性排除另一条路径的拼接。现稿直接跨过了这一逻辑。
**足以消除异议的修订：**增加上述不等式及一项“distinct terminal follower states imply non-synchronizing”引理。
**裁决影响：**这是必须修订，但不单独改变大修结论。

5. Proposition 6.5 对非 Pisot 四次例的实根计数少了一步
现稿证明了一个正根和一个位于 (−1,0) 的负根，随后直接称另外两个根为非实共轭根。 还需排除额外实根。
**足以消除异议的修订：**使用 Descartes 符号法则，或直接分析
(x4−2x3−2)′=2x2(2x−3)
的单调区间，即可完成根的计数。
**裁决影响：**纯局部缺口，修补后完全消除，不影响主裁决。

6. 其余主链条的判断
在上述问题之外，我没有发现以下结论存在明显逻辑错误：


Theorem 6.2 中有限差分图与有限窗口碰撞的对应；


Corollary 6.3 中零状态唯一前驱从而“单射 ⇒ 有限未来逆码”；


Theorem 6.4 的孔径二三分；


Theorem 5.5 的孔径二显式解码；


Theorem 5.6 的二次两室孔径二对偶；


Theorem 5.8 的唯一双点纤维和严格 sofic 性；


Theorem 5.9 的差分证书所给出的有限块起点下界；


Lemma 6.6 中三次 Pisot 性与 Parry 词的内部一致性。


机器测试的定位也是正确的：现稿明确称其为回归测试而非全参数证明。 因而测试通过不能替代上述三处解析补全，但也不存在以有限枚举冒充证明的问题。

二、新颖性与优先权
这是现稿当前最需要重写的部分。
1. ordered-language rank：基本秩结构是既有理论，不应列为本文新增量
固定语言的 lexicographic/genealogical 排序赋值、Bertrand 数系以及 Parry 语言的线性权重表示已有明确传统：Bertrand-Mathis 1989、Bruyère–Hansel 1997、Lecomte–Rigo 2000/2001，以及 Charlier–Cisternino–Stipulanti 2022 对 Bertrand-Mathis 分类的修正。后者特别指出：simple-Parry 情形具有 canonical 与 non-canonical 两套相关 Bertrand 数系。arXiv+4施普林格自然+4科学直通车+4
现稿已经引用 Bruyère–Hansel、Lecomte–Rigo 和 2022 年修正文献，但遗漏了最直接的 Bertrand-Mathis 1989 论文。更重要的是，Proposition 5.2 的“合法词按 colex 次序由
j∑​xj​Qj​
依次赋值”为 0,…,Qm​−1，以及第 6 节所称的 Parry–Bertrand rank data，本质上应列为 canonical Parry–Bertrand 数系的标准结构；反转词方向与改称 colex 不产生新的数系理论。 
本文可以保留 Proposition 5.2 的自足证明，但贡献表应改成：

“已知 canonical Parry–Bertrand positional rank 的一个针对二次两室的直接区间证明；本文的新操作始于将该固定长度秩模 Qm​ 循环化并施加滑动重叠。”

还应明确说明 simple-Parry 部分采用的是由 dβ∗​(1) 决定的 canonical 语言，而不是由有限词 dβ​(1) 产生的 non-canonical Bertrand 系统。
**裁决影响：**增加 Bertrand-Mathis 1989、解释 2022 修正并撤回“秩本身”的原创暗示后，本项问题完全可消除；不修订则优先权叙述不能接受。

2. 碰撞图、环判据和一般可逆性算法：存在确定的遗漏先行工作
现稿把 Theorem 6.2、Corollary 6.3、Theorem 6.4 一并列为“exact bounded sliding-congruence depth, causal completeness, periodic failure certificates”等新增量。 但第 6 节直到后部才用一句话称其图为标准 fiber-product collision graph 的算术特化。 这一信用不足。
一维局部映射的 injectivity/surjectivity 判定早在 Amoroso–Patt 1972 已有决策程序；Richardson 1972 处理局部变换与可逆性；Nasu 1977 明确引入左右 bundle graphs、以其刻画 injectivity 并研究逆映射；Head 1989 又直接以有标号图和有限自动机的无歧义性判定一维 cellular automaton 的 injectivity。Wolfram Media+3ACM Digital Library+3科学直通车+3
因此，下列内容不能作为整体原创主张：


以 pair/fiber graph 表示两个输入的共同输出；


“存在非对角双边路径”等价于非单射；


有限图中可达有向环给出非单射证书；


非单射可由周期碰撞检测；


单射共轭具有某个有限滑动块逆码。


有限 decoder window 及其 look-ahead 的定量问题也有独立文献传统；Ashley 的 1988、1996 工作研究有限滑动解码窗口的上界，1991 工作则属于 right-closing/resolving factor-map 理论。它们与本文的特定算术映射并不相同，但必须进入“最近框架”比较。IBM Research+2IBM Research+2
本文仍可主张的新内容是：


pair graph 在本映射中精确商化为差分状态
Δdm−1​，而不必保留输入对；


ℓcau​ 等于从首坐标非零状态出发的最长生存路径加一；


simple-Parry 权重满足零状态唯一前驱，从而一般的有限双侧逆码被加强为记忆为零的未来单侧逆码；


因差分商图而得到的具体状态数和周期上界；


孔径二的精确三分及其唯一双点纤维；


特定二次和三次族上的精确最优深度。


足以消除异议的修订：


在第 6 节开头增加“Classical pair-graph background”；


引用 Amoroso–Patt、Richardson、Nasu 1977、Head，并保留 Nasu 1995/Lind–Marcus；


把 Theorem 6.2 分为“标准 pair-graph 命题”与“本文的差分商及精确未来深度定理”；


在摘要、引言贡献表和结论中删除把图判据本身称为新框架的措辞；


将 periodic certificate 表述为“在该差分商中得到的纯周期证书及显式较小上界”，而不是首次发现周期检测。


裁决影响：这是现稿层面的致命优先权问题，但可通过完整重写而修复。完成后，我不会因此否定本文的新颖性；不完成则应拒稿。

3. resolving/right-closing 与有限延迟逆码：应作术语上的精确切割
现稿的 ℓcau​ 定义并不是泛指“某个逆滑动块码的窗口大小”，而是记忆严格为零、只读取当前及未来输出的最小长度。 这比一般共轭逆码的存在更具方向性。
建议在引言中明确写出：
ℓcau​(β,m)−1=最小的 memory-zero inverse anticipation,
并说明是否以及在何种约定下等同于 right-closing delay。若不证明这种等价，则不应把两个术语互换。
当前最稳妥的优先权划分是：


**标准部分：**共轭的逆映射仍是滑动块码；right/left resolving、right-closing、fiber product 与有限解码窗口的普通理论。


**本文部分：**本算术映射的逆码可取 memory 0，其最小 anticipation 可由差分图精确计算，并在指定族上取精确值或无界。


**裁决影响：**补充术语比较和文献后即可消除，不影响核心定理。

4. Fischer cover 与 Markov 阶：现有信用基本适当
Fischer–Krieger cover、follower separation、intrinsically synchronizing words 和最小右分解表示均属标准背景。现稿已经明确给予该理论信用。其真正的新结论可以是：


自然重叠图恰为当前输出字母表下的 right Fischer cover；


精确状态数为 (⌊β⌋+1)m−1；


有限块单射首次发生于 N=m；


在固定输出字母表中恰为 m-step 而非 (m−1)-step SFT。


现稿也正确提醒该状态数不是任意拓扑共轭下的不变量。 这组优先权主张无需实质退让，只需完成前述 Theorem 5.9 的两项局部证明。

5. 三次 Pisot 族：当前实质信用正确，但应在定理层面更醒目
Bassino 2002 已经明确给出
x3−(k+2)x2+2kx−k
这一三次 simple-β Pisot 族，并指出其 β-展开长度为 2k+2。施普林格自然+1
现稿在摘要、引言和第 6 节已经说明 cubic expansion data 来自 Bassino，而新内容是模 Qm​ 滑动碰撞深度；这一实质划分是正确的。 
仍建议将 Lemma 6.6 改名为：

Lemma 6.6 (Bassino’s cubic family; direct verification of the required data).

并在 Theorem 6.9 的陈述首句直接写“for Bassino’s family”。直接重新验证其 Pisot 性和 Parry 词有助于自足性，但不能使该族或该展开成为本文原创。
我未检出已发表工作研究这个族的“rank modulo Qm​ sliding code”的精确未来深度 n−1。因此，经过上述归属修订后，Theorem 6.9 的新颖性主张是可信的；“未检出”仍应保留为谨慎书目判断，而非书目穷尽性证明。
**裁决影响：**措辞修订后完全可接受。

6. 二次 Pisot 精确阈值：未发现直接先行结果
现有 β-shift、Parry–Bertrand 数系、Pisot 正规化 transducer、Ostrowski 约束和 resolving-code 文献分别提供语言、秩、自动机和局部码背景；但它们不等同于本文的“固定长度秩模 Qm​ 后滑动重叠”操作。现稿对此区别的说明准确。
在检索到的文献中，没有发现下列精确结论的已发表先例：
m∗​(β)=3⟺\minpoly(β)∈{x2−ax−a}∪{x2−ax+1},
以及相应的精确有限块起点和 Markov 阶。因此，在 Lemma 5.3/5.4 的统一证明获得补全后，这应当是本文最强且最稳固的原创主定理。
建议优先权措辞使用：

“To the authors’ knowledge, the exact threshold for this cyclic fixed-length language-rank recoding has not previously been determined.”

不应使用“首次解决 β-正规化阈值”等更宽泛表述。

三、DCDS-A 的发表价值与期刊适配
主题适配不存在问题。 DCDS 已发表 intermediate β-shifts 的 finite-type 分类、经典 β-shift 的 follower/predecessor/extender 集，以及 sofic shift 的规范图表示等工作。美国数学科学研究院+2美国数学科学研究院+2
在优先权收缩后，仍剩下三项足以构成 DCDS-A 论文的组合：


全部二次 Pisot 基数上的精确阈值二分及参数极值集合；


精确有限块单射起点、固定字母表 Markov 阶和 Fischer cover；


三次 simple-Parry Pisot 类中未来单侧逆码深度的显式无界族。


其中第一项提供完整分类，第三项表明二次统一现象在三次立即破裂；两者之间有清楚的动力系统叙事。故我不认为“没有解决具名公开问题”构成拒稿理由。
不过，现稿的篇章重心仍需调整。引言称 entropy、KL、pressure 等常规后果已移至补充材料， 但正文仍保留较长的 KL 缺陷、模零统计等价和 zeta 计算。  这些结果并非错误，但稀释了真正需要审查的阈值与碰撞深度证明。
建议正文集中于：


定义及 Fibonacci 原型；


二次全分类；


精确局部结构；


classical pair graph 与新差分商的明确分界；


三次无界族。


KL、Blackwell、zeta、Fourier fiber statistics 和若干算法性推论可移入补充材料。
若作者不愿进行这种动力系统导向的重构，而希望以自动机、语言秩和有限判定为中心，则 Theoretical Computer Science 是更自然的备选期刊；该刊长期发表 β-shift symbolic dynamics 和 Bertrand numeration 工作。科学直通车+1 但在完成重构的前提下，我认为无须主动降投，DCDS-A 是合理目标。

四、修订要求的分级
A. 对现稿具有致命性的事项
A1. 重写 Theorem 6.2/Corollary 6.3 的优先权定位。
必须加入 Amoroso–Patt、Richardson、Nasu 1977、Head 及 decoder-window 文献，并把标准 pair-graph 判定与新的差分商、未来深度严格分开。完成后，本项不再阻碍接受；不完成则拒稿。
A2. 补足 ordered-language rank 的直接先行文献。
必须增加 Bertrand-Mathis 1989，并解释 Charlier–Cisternino–Stipulanti 的 canonical/non-canonical 修正；Proposition 5.2 只能主张自足证明而非秩理论本身的原创。完成后可消除；不完成则优先权不可靠。
A3. 使 Lemma 5.3、6.7、6.8 达到可逐行核验程度。
这些不是可由“测试通过”替代的细节。若完整推导成立，审稿结论可转向小修或接收；若任一参数一致分支不能闭合，则相应主定理必须撤回，届时现有论文结构不足以发表。

B. 必须大修但不单独致命的事项
B1. 修补 Theorem 5.9 的右分解与非同步词论证。
B2. 补上 Proposition 6.5 的实根计数。
B3. 统一术语。
全文宜优先使用“future-only inverse length”或“memory-zero inverse anticipation”，并另行说明与 right-closing delay 的关系。
B4. 重写贡献表。
每一项应分别列出“标准输入”“本文新增算术结论”，而不能把一个标准框架及其特殊计算整体列为新增。
B5. 在 Lemma 6.6 和 Theorem 6.9 的题名或陈述中直接标注 Bassino family。
B6. 压缩非核心后果。
正文应删除或移出 KL、Blackwell、Fourier fiber、zeta 等不参与主证明的部分。
B7. 完成可复现性归档。
现稿本身承认尚无版本化公共归档和 DOI。 最终版本应提供不可变版本、校验和、运行命令及保存输出。
B8. 修订参考文献 [21]。
Drungilas–Jankauskas–Junevičius–Klebonas–Šiurys 的论文已有正式刊载版本：Bulletin of the Korean Mathematical Society 55 (2018), 1491–1501；不应只列 arXiv。韩国文化遗产委员会
完成 B1–B8 后，若 A 类事项也已解决，我的裁决将由大修改为原则上可接受、仅需小修。

C. 可选改进


合并第 2–4 节中 Fibonacci 与 metallic 子族的重复构造；


将显式 decoder 算法和较长分支表移入附录；


增加一幅图，显示普通 pair graph 到差分图
Δdm−1​ 的商化关系；


将“未发现先行工作”统一改成限定于确切映射与确切问题的审慎表述；


在摘要中把主次顺序调整为：二次全分类、三次无界深度、一般 simple-Parry 算术差分商；不要把一般图判据列在二次定理之前。


这些改进不单独影响裁决，但会显著提高论文的可信度和可读性。

最终裁决
现稿不可直接接收。建议 Major Revision，强度接近 Reject and Resubmit。
拒绝直接接收的首要理由不是结果不足，而是：


一项确定的 pair-graph/局部码先行传统尚未得到充分承认；


canonical Parry–Bertrand rank 的最直接先行工作和 2022 修正尚未准确定位；


三个核心参数一致证明仍未达到审稿人可以无保留签署的展开程度。


若作者完成上述优先权重写，并严格补全 Lemma 5.3、6.7、6.8，则我认为：


二次 Pisot 精确阈值及精确局部阶数是可信的新结果；


三次族的 ℓcau​=n−1 是可信的新结果；


合并后的增量足以发表于 DCDS-A；


届时我会支持在小修后接收。


若作者只增加若干引用而保留当前贡献表，或以有限测试代替三处统一证明，则裁决应维持拒稿。
