<!-- oracle metadata: {"timestamp": "2026-04-07T22:01:42.843046", "model": "chatgpt-5.4-pro-extended", "response_length": 14005} -->

1. Overall assessment

Major revision

This is a promising paper with a genuinely interesting central question: whether full sampled Unruh-DeWitt click records, rather than only mean transition rates, define operational thresholds that lift to geometric loci in static KMS spacetimes. The strongest part is Section 3, especially the finite-recovery renewal analysis. In its current form, however, I would not recommend acceptance. The main reasons are: (i) the bridge from a repeatedly measured UDW detector to the specific hidden-Markov/renewal channel is not derived in a controlled way, (ii) the explicit Lambert W formula for 
Γ
𝑐
Γ
c
	​

 is wrong and appears to contaminate Table 2, (iii) the near-horizon Schwarzschild proof sketch contains a proper-distance versus areal-radius error, and (iv) most inverse-content claims rely on a homogeneous spectral-weight assumption that is not physically justified for the black-hole examples being emphasized. I reviewed only the main manuscript. The Supplementary Material repeatedly referenced in the paper was not included in the file I received. 

main

2. Novelty rating for each main result
Result	Rating	One-line justification
Proposition 3.1	MEDIUM	Nice observation in this UDW-record setting, but mathematically it is a direct parameter match to the Parry measure on the golden-mean shift.
Proposition 3.2	HIGH	This is the paper’s core original contribution: an explicit finite-recovery renewal law with hazard monotonicity, covariance formula, and a distinguished 1-dependence threshold.
Corollary 3.3	LOW	Immediate consequence of Proposition 3.2.
Proposition 3.5	MEDIUM	Useful asymptotic bridge between finite recovery and the ideal dead-time grammar, with clear operational interpretation.
Proposition 3.6	LOW	Interesting in this context, but sub-Poissonian/antibunched counting is strongly reminiscent of standard two-state emitter physics.
Theorem 4.1	MEDIUM	Conceptually neat lift from record thresholds to geometric loci, but structurally it is obtained by substituting the local excitation rate into the threshold equations.
Corollary 4.2	LOW	Direct specialization of Theorem 4.1 under homogeneous spectral weight.
Proposition 4.3	LOW	Essentially a monotonicity argument once the homogeneous-rate reduction is made.
Theorem 5.1	LOW	Operationally useful, but algebraically it is just division of two shell equations with a shared amplitude factor.
Corollary 5.2	MEDIUM	The non-homogeneous spectral-transport identity is a worthwhile clarification of what survives beyond the idealized homogeneous regime.
Theorem 5.3	MEDIUM	The near-horizon interpretation is interesting, but it is derived from the ratio law plus a standard near-horizon expansion.
Proposition 5.4	LOW	Straight algebraic inversion in Schwarzschild once the shell temperatures are fixed.
Theorem 5.5	LOW	Mostly an implicit-function-theorem identifiability statement, not a new detector-theory mechanism.
3. Issue table

The issues below refer to the attached manuscript, mainly Sections 3 to 5, Remark 3.4, Figure 4, and Table 2. 

main

ID	Section	Severity	Description	Suggested fix
B1	3.1 to 4	BLOCKER	The detector channel is introduced phenomenologically, but the manuscript then uses the standard stationary UDW rate formula as if it directly governs a detector that is projectively read out and reset every 
Δ
𝜏
Δτ. No controlled derivation is given showing when field-induced memory is negligible and when the two-state hidden-Markov/renewal model follows from an actual repeated-measurement UDW setup.	Derive 
𝑇
0
,
𝑇
1
T
0
	​

,T
1
	​

 from a weak-coupling Markovian master equation with periodic readout/reset and explicit coarse-graining assumptions, or reframe the paper throughout as a phenomenological counter model driven by a stationary UDW rate.
B2	Remark 3.4, Table 2	BLOCKER	The closed-form Lambert W expression for 
Γ
𝑐
Γ
c
	​

 is incorrect. It is not equivalent to equation (12), and Table 2 appears to use the wrong formula. For example, solving (12) gives 
Γ
𝑐
≈
0.15862
Γ
c
	​

≈0.15862 for 
(
Δ
𝜏
,
𝜅
𝑟
)
=
(
0.5
,
8
)
(Δτ,κ
r
	​

)=(0.5,8), not 0.172283, and 
Γ
𝑐
≈
0.09148
Γ
c
	​

≈0.09148 for 
(
1.2
,
3
)
(1.2,3), not 0.102764.	Replace Remark 3.4 with the correct branch-dependent Lambert W formula, discuss branch choice explicitly, and recompute Table 2 and any dependent numerics.
B3	Theorem 5.3 proof sketch	BLOCKER	The Schwarzschild area-excess argument confuses proper distance 
𝜌
ρ with areal-radius increment. Near the horizon, 
𝑟
−
𝑟
𝐻
∼
𝜌
2
/
(
8
𝑀
)
r−r
H
	​

∼ρ
2
/(8M), not 
𝜌
ρ. The current proof sketch is therefore wrong as written.	Redo the proof in proper-distance coordinates and re-derive the area law carefully. Then verify equation (28) and any figure/table quantities that depend on it.
B4	4 to 5, Figure 4, Table 2	BLOCKER	Most of the inverse-content claims rely on the homogeneous spectral-weight regime 
𝑆
𝑥
(
Ω
)
≡
𝑆
(
Ω
)
S
x
	​

(Ω)≡S(Ω), but this is not justified for the black-hole settings emphasized in the paper. In realistic static black-hole detector problems, greybody and mode-structure effects usually make the response weight position dependent.	Either justify the approximation in a concrete regime or clearly demote the Schwarzschild inverse claims to idealized toy-model status and add at least one explicit non-homogeneous example using equation (25).
M1	3.4	MEDIUM	Exact 1-dependence is a central claim, but the main text only gives covariance collapse and an eigenvalue heuristic. Vanishing higher covariances does not by itself imply 1-dependence.	Add a direct proof showing that at 
𝜆
=
0
λ=0 the hidden transition matrix has identical rows, the hidden states become i.i.d., and the visible process is a 1-block factor, hence exact 1-dependent.
M2	3.7	MEDIUM	The finite-sample observability section is heuristic and internally inconsistent. The stated variance scaling for 
𝛾
^
2
γ
^
	​

2
	​

 does not match the subsequent sample-size estimate.	Replace the paragraph with a correct asymptotic variance derivation or a Monte Carlo power analysis with confidence intervals.
M3	3.3, abstract, discussion	MEDIUM	“Exact symbolic thermality” is nonstandard terminology and risks being mistaken for standard detector thermality. The caveat is present, but too late and too weak.	Move the caveat to the abstract and introduction, and consider renaming this benchmark as “Parry-law point” or similar.
M4	Introduction, Discussion	MEDIUM	The literature positioning is incomplete. The paper under-cites careful switching in UDW theory, quantum-optical waiting-time/antibunching work, and probability literature on 1-dependent counting processes. This makes the novelty claim sound broader than it is.	Expand the literature review and narrow the novelty claim to what is actually new: record-defined detector shells in static KMS settings.
M5	5	MEDIUM	The inverse statements establish identifiability, not robustness. There is no conditioning or error-propagation analysis, so “self-calibrating inverse principle” is stronger language than the mathematics presently supports.	Add Jacobian conditioning, first-order error propagation, and one noisy synthetic inversion example.
L1	Acknowledgements	LOW	“The authors thank the anonymous referees” is inappropriate in a submitted manuscript.	Remove until after peer review.
L2	Data availability / reproducibility	LOW	Scripts are only available “upon request,” despite the manuscript depending on nontrivial numerics.	Archive the code used for Table 2 and the figures in a repository or supplemental package.
4. Missing references

Important related work that should be cited includes the following.

UDW click rates with careful switching: Alejandro Satz, Then again, how often does the Unruh-DeWitt detector click if we switch it carefully? This is directly relevant to the paper’s framing around detector “clicks” and readout-time dependence. 
arXiv

Waiting-time and antibunching physics for two-state emitters: H. J. Carmichael et al., Photoelectron waiting times and atomic state reduction in resonance fluorescence, and H. J. Kimble et al., Photon Antibunching in Resonance Fluorescence. These are the obvious predecessors for Sections 3.5 to 3.6. 
link.aps.org
+1

Stationary 1-dependent process literature: Aaronson, Gilat, Keane, and de Valk on one-dependent processes, plus Pitman and You on stationary 1-dependent counting processes. If exact 1-dependence is a flagship concept here, the paper should situate itself in that literature. 
Project Euclid
+1

Foundational stationary point-process and renewal-process references: Daley and Vere-Jones, or at minimum Cox and Isham, should be cited if renewal and stationary counting-process language is central to the formalism. 
NoZDR
+1

UDW response in static spherical black-hole geometries: Ng et al. on static/circular detector response in Schwarzschild-AdS black holes, and Tjoa on detector dynamics in arbitrary static spherically symmetric spacetimes, are directly relevant to the manuscript’s later Sections 4 to 5 and to the question of spatially varying response weights. 
link.aps.org
+1

5. Specific improvements needed to reach acceptance

Repair the mathematics and numerics first. The wrong explicit 
Γ
𝑐
Γ
c
	​

 formula and the flawed Theorem 5.3 proof sketch must be corrected before the rest of the paper can be trusted.

Either derive the channel or narrow the claim. The paper needs a controlled derivation from a repeated-measurement UDW model, or it must explicitly present itself as a phenomenological counting model driven by a stationary UDW excitation rate.

Substantiate the homogeneous spectral-weight regime. If the authors want to keep the inverse and Schwarzschild claims prominent, they need either a physical justification for 
𝑆
𝑥
(
Ω
)
≈
const
S
x
	​

(Ω)≈const in a concrete regime, or a non-homogeneous worked example showing how the conclusions change when equation (25) is used honestly.

Make the 1-dependence claim fully transparent. This is one of the paper’s best ideas. It deserves a short, direct proof in the main text.

Strengthen the paper’s operational credibility. The finite-sample discussion needs real support, either by asymptotic theory or by simulation.

Improve positioning and terminology. The authors should cite the missing literatures above and tone down claims that sound broader than what is actually established.

6. Concrete fixes for each BLOCKER and MEDIUM issue
ID	Concrete fix
B1	Add a subsection deriving the effective sampled channel from a Born-Markov-secular master equation with periodic projective readout and reset. State explicitly the required regime: coarse-graining longer than the field correlation time, weak coupling, and neglect of back-action beyond the local rate. If such a derivation is not available, change the title/abstract/claims so the object is clearly a phenomenological counter model driven by a UDW rate, not a derived UDW measurement record.
B2	Replace Remark 3.4 by the correct formula. With 
𝑠
=
𝜅
𝑟
Δ
𝜏
s=κ
r
	​

Δτ and 
𝑥
=
Γ
𝑐
/
𝜅
𝑟
x=Γ
c
	​

/κ
r
	​

, one gets 
𝑥
=
−
𝑊
𝑘
(
−
𝑠
𝑒
−
𝑠
)
/
𝑠
x=−W
k
	​

(−se
−s
)/s, with branch 
𝑘
=
−
1
k=−1 for 
0
<
𝑠
<
1
0<s<1, 
𝑥
=
1
x=1 at 
𝑠
=
1
s=1, and 
𝑘
=
0
k=0 for 
𝑠
>
1
s>1. Then regenerate Table 2, all derived constants 
𝐶
𝑚
C
m
	​

, all 
𝛽
m
e
m
β
mem
	​

, shell radii, and any figures/scripts that use 
Γ
𝑐
Γ
c
	​

. Add a short appendix cross-checking the implicit and explicit formulas numerically.
B3	Rewrite the proof of Theorem 5.3 in Gaussian normal distance 
𝜌
ρ from the horizon. Use 
𝑁
(
𝜌
)
=
𝜅
𝐻
𝜌
+
𝑂
(
𝜌
3
)
N(ρ)=κ
H
	​

ρ+O(ρ
3
) and, in Schwarzschild, 
𝑟
−
𝑟
𝐻
=
𝜌
2
/
(
8
𝑀
)
+
𝑂
(
𝜌
4
)
r−r
H
	​

=ρ
2
/(8M)+O(ρ
4
). Then 
𝐴
(
𝜌
)
−
𝐴
𝐻
=
2
𝜋
𝜌
2
+
𝑂
(
𝜌
4
)
A(ρ)−A
H
	​

=2πρ
2
+O(ρ
4
). Check whether equation (28) remains unchanged after the corrected derivation, and update the text accordingly.
B4	Add one of the following. Either: a concrete calculation of 
𝑆
𝑥
(
Ω
)
S
x
	​

(Ω) in a static spherical example, together with a regime where its variation is negligible. Or: a non-homogeneous worked example using equation (25), so the reader sees how shell ratios mix lapse information with spectral transport. If neither is done, move the inverse claims to a clearly labeled idealized subsection and soften the abstract/discussion language.
M1	Insert a 5 to 10 line proof after Proposition 3.2: at 
𝜆
=
0
λ=0, 
𝑃
=
𝑇
0
+
𝑇
1
P=T
0
	​

+T
1
	​

 has identical rows, so the hidden states are i.i.d.; 
𝐴
𝑛
A
n
	​

 depends only on adjacent hidden states; therefore blocks separated by one time step depend on disjoint i.i.d. variables and are independent.
M2	Replace the current Section 3.7 estimate with either a CLT-based calculation for 
𝛾
^
2
γ
^
	​

2
	​

 and 
ℎ
^
𝑘
h
^
k
	​

, or a simulation study showing detection power versus 
𝑁
N, 
Γ
Γ, 
𝜅
𝑟
κ
r
	​

, and 
Δ
𝜏
Δτ. Report actual confidence intervals or false-positive rates.
M3	Rename the benchmark throughout, for example to “Parry-law benchmark” or “Parry point,” and define it once near the beginning. In the abstract and first page of the introduction, explicitly distinguish it from detailed-balance thermality and Gibbs thermalization.
M4	Rewrite the literature paragraph into three pieces: UDW click-rate/switching literature, quantum-optics waiting-time and antibunching literature, and probability literature on renewal and 1-dependent processes. Then state the novelty narrowly: lifting record-level thresholds to detector-defined geometric loci in static KMS spacetimes.
M5	Add a short subsection on conditioning. Compute the Jacobian in Theorem 5.5 for the worked example, report a condition number, and propagate shell-radius errors through the inverse map. A simple noisy synthetic example would be enough.

My bottom line is that the paper has a publishable core, but it is not yet technically stable enough for acceptance. The authors need to fix the mathematical slips, tighten the physical model, and narrow or justify the later geometric claims.