设 aj​=Sj​−Sj+1​（j<J）、aJ​=SJ​，并以 qrs​=ar​as​ 表示交换点截断双计数层的单元概率。假定现稿中的更新—周期分解满足 nN​/N→ν0​∈(0,∞)，且所有既述余项界对 ∥hN​∥2​≤M 的交换点局部 null 一致成立。
定理（欧氏 Gaussian 耦合的尖锐二阶截断）。 对每个固定 M<∞，存在
ξN​∼N(0,IdJN​​​) 使
∥hN​∥2​≤Msup​PN,hN​​(∥ZJN​,N​−ξN​∥2​>ε)⟶0(∀ε>0)
当且仅当
nN​SJN​2​⟶∞.(1)
因此，令 LN​=lognN​，尖锐二阶增长区间为
2x0​JN​−LN​−2logLN​⟶−∞,(2)
等价地，
JN​=⌊2x0​lognN​+2loglognN​−ωN​​⌋,ωN​⟶∞.(3)
若以日历长度表示，则
JN​=⌊2x0​logN+2loglogN−ωN​​⌋
仍为必要充分边界；ν0​ 仅改变临界窗中的 O(1) 常数，不改变 loglogN 系数。
证明。 规范加权 Helmert 系是 L2(q) 中常数正交补的一组正交基。其 Christoffel 对角具有不依赖基选择的精确形式
KJ​(r,s)=qrs−1​−1.(4)
最小单元为尾—尾单元，qJJ​=SJ2​，故
r,smax​KJ​(r,s)=SJ−2​−1.(5)
此外，
Sj​Sj+1​​=e−x0​1+x0​j1+x0​(j+1)​≤ρx0​​<1.
因此规范尾链及其张量层满足
r=0∑J​Sr​1​≤SJ​Cx0​​​,r,s≤J∑​Sr​Ss​1​≤SJ2​Cx0​​​.(6)
将双计数层按规范 Helmert 尾链逐节点分裂。在尾矩形 (r,s) 上，子节点计数在给定父节点更新数后为二项分裂；其父节点期望规模与 nN​Sr​Ss​ 同阶。对每个分裂调用既有的一维 binomial–Gaussian quantile coupling；这里只使用其均方误差结论，不重述一般证明。相关原始输入可见 Brown–Carter–Low–Zhang, Section 5 及 Carter–Pollard。条件于父节点计数 Mrs​，标准化分裂与对应 Gaussian 坐标的均方误差由
nN​Sr​Ss​C​
控制；以 Mrs​ 替代 nN​Sr​Ss​ 所产生的随机方差校正具有同阶界。正交性与 (6) 遂给出完整理想层向量的耦合
∥ZJN​,nN​0​−ξN0​∥2​=OP​((nN​SJN​2​)−1/2).(7)
同一求和同时控制随机更新指标与 martingale 条件方差：
E[∥⟨M⟩nN​​−IdJN​​​∥F2​+∥Rindex​∥22​]≤nN​SJN​2​C​.(8)
若 VN​=⟨M⟩nN​​，以同一标准 Gaussian 向量构造
VN1/2​ξN​，则
E[∥(VN1/2​−I)ξN​∥22​∣VN​]=∥VN1/2​−I∥F2​=oP​(1),(9)
其中最后一步由 (8) 与 (1) 得到。故随机条件方差没有引入维数因子 dJ​。
对于 ∥hN​∥2​≤M，(4)–(5) 给出局部密度扰动的逐单元上界
r,ssup​​qrs​(0)qrs​(hN​)​−1​≤nN​​SJN​​CM​​=o(1).(10)
因而 (6)–(9) 的常数对全部有界局部 null 一致。加入实际日历记录的各项修正后得到
∥ZJN​,N​−ξN​∥2​=OP,M​(nN​​SJN​​1​+JN​N−1/4+JN​N−1/2+JN3​N−1/2).(11)
条件 (1) 蕴含 JN​=O(logN)，故后三项均为 oP​(1)。交换点 covariance perturbation 可通过同一 Gaussian 的平方根耦合吸收，其欧氏误差正是 (11) 的最后一项。由此证明充分性。一般 martingale Gaussian mixture 耦合的归属仍为 Cattaneo–Masini–Underwood；这里产生尖锐边界的是规范尾链的求和式 (6)，而非对其一般定理的重新陈述。
必要性取尾—尾单元计数 CJJ,N​，并令
TN​=nN​SJN​2​(1−SJN​2​)​CJJ,N​−nN​SJN​2​​.(12)
函数
uN​(r,s)=SJN​2​(1−SJN​2​)​1{(r,s)=(JN​,JN​)}​−SJN​2​​
是常数正交补中的单位向量，故 TN​ 是完整 Helmert 得分向量的一个单位投影。若欧氏 oP​(1) 耦合存在，则
TN​−⟨uN​,ξN​⟩=oP​(1),
从而 TN​⇒N(0,1)。
若 (1) 不成立，可取子列使
nN​SJN​2​⟶λ∈[0,∞).
当 0<λ<∞ 时，
CJJ,N​⇒Pois(λ),TN​⇒λ​Pois(λ)−λ​,
其特征函数不是 e−t2/2；当 λ=0 时，CJJ,N​=0 的概率趋于一，投影亦不可能趋于标准 Gaussian。因此欧氏耦合失败。该反例统计量在原始日历记录中可直接计算，不依赖改变近似距离。
最后，若
bN​:=2x0​JN​−lognN​−2loglognN​=O(1),
则直接代入尾公式得到
nN​SJN​2​=41​e−bN​{1+o(1)}.(13)
故 bN​→−∞ 恰为充分必要条件；若 bN​→c∈R，反例 (12) 的极限参数为
λ=41​e−c,
若 bN​→+∞，尾—尾单元为空的概率趋于一。由此，+2loglognN​ 是尖锐二阶项；有限常数余量仍位于非 Gaussian 临界窗内，不能纳入最大可耦合区间。