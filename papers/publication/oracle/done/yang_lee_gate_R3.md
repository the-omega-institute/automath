<!-- oracle metadata: {"timestamp": "2026-04-06T18:09:41.674983", "model": "o3-mini-high", "response_length": 13195} -->

The remarks below refer to the submitted manuscript. 

main

1. Overall assessment

Major revision.

The manuscript contains a potentially publishable family-specific calculation, and several spot-checked algebraic identities are consistent. However, it is not ready for acceptance in its present form. Three issues currently block publication: the advertised elliptic normalization is not proved at the projective level, the main edge-zero asymptotics are applied under stronger analytic hypotheses than are actually verified, and the manuscript has unresolved citation placeholders throughout with no bibliography. In addition, the paper is positioned too broadly for what is, at present, a detailed study of one specially chosen quartic family.

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 3.1	LOW	Minimality via coprimeness/resultant and Hankel rank is standard rational generating function theory.
Theorem 4.4	MEDIUM	The explicit elliptic reduction for this quartic is neat, but the underlying transformation is a classical completion-of-the-square/birational move.
Theorem 5.1	MEDIUM	The dominance versus subdominance classification of the real branch values is nontrivial and genuinely model-specific.
Theorem 5.5	MEDIUM	The exact real-root phase diagram is elegant, though it follows naturally once the elliptic model and real branch structure are known.
Theorem 6.1	LOW	The explicit positive branch and its monotonicity are straightforward consequences of the quadratic formula and elementary calculus.
Theorem 6.4	LOW	This is essentially a cosine reduction plus Rouché under hypotheses that already encode the local normal form.
Theorem 6.5	MEDIUM	The concrete zero-quantization formula is useful and specific to the family, though methodologically it rests on standard local singularity analysis.
Theorem 7.1	LOW	The degree law and leading coefficients follow from direct induction on the recurrence.

A remark on positioning: the most original structural observation is arguably Proposition 4.1, not one of the theorem-labeled statements.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Throughout	BLOCKER	Citation placeholders remain unresolved and no bibliography is supplied. Standard background claims, priority, and terminology are therefore uncheckable.	Replace every placeholder with an actual citation and add a complete bibliography.
B2	4.2 to 4.4	BLOCKER	The paper proves an affine change of variables to a Weierstrass model, but not the advertised normalization of the projective quartic. The singular point at infinity and the extension of the birational map are omitted.	Add a projective-normalization lemma, or weaken all occurrences of “normalization” to “affine/birational elliptic model.”
B3	6.3 to 6.5, Appendix D	BLOCKER	Theorem 6.5 is deduced through Theorem 6.4 and a complex Rouché argument, but Appendix D only verifies the remainder estimate on real compact sets 
𝑈
⊂
[
0
,
∞
)
U⊂[0,∞), not on complex discs in the 
𝑢
u-plane.	Prove complex-uniform remainder bounds, or replace the argument by a purely real zero-tracking proof.
M1	6.3	MEDIUM	Theorem 6.4 is overstated. Its hypotheses already assume the exponential branch expansions and amplitude structure that constitute the “normal form.”	Recast it as a lemma, or derive those hypotheses from generic analytic EP2 conditions on the spectral polynomial.
M2	4.4	MEDIUM	Corollary 4.6 identifies the discriminant locus with the finite branch locus too tersely. The equivalence between repeated 
𝜆
λ-roots of the fiber and ramification of 
𝑦
:
𝐸
→
𝑃
1
y:E→P
1
 is not made explicit.	Insert a short lemma using 
Π
𝑦
=
𝑌
Π
y
	​

=Y and 
𝑑
𝑦
/
𝑑
𝜆
=
−
Π
𝜆
/
𝑌
dy/dλ=−Π
λ
	​

/Y away from 
𝑌
=
0
Y=0.
M3	6.2	MEDIUM	In Proposition 6.2 for 
𝑦
>
1
y>1, the identification 
𝑞
=
𝜆
d
o
m
(
𝑦
)
q=λ
dom
	​

(y) is asserted rather than proved.	Compare the 
+
+ and 
−
− sheets directly and show that the 
−
−-sheet root is the larger positive root.
M4	1 and 10	MEDIUM	The family is treated as a partition-function/fugacity problem even though the paper explicitly declines to provide a microscopic model. This weakens motivation and overstates physical interpretation.	Either supply a model, or rewrite the paper as a purely algebraic/spectral study.
M5	1.1	MEDIUM	The manuscript does not compare itself adequately with the closest literature on zeros of recursively defined polynomial families from rational generating functions.	Add a focused literature-positioning paragraph.
L1	5 and Appendix D	LOW	Theorem 5.1 depends on later appendices, which obscures the proof architecture.	Move the local expansion lemma earlier or state it before Theorem 5.1.
L2	9	LOW	The numerical verification section is too long relative to the exact proofs.	Condense it and move plotting details to supplementary material.
L3	Throughout	LOW	Several rhetorical labels and claims are stronger than what is actually proved.	Tone down language such as “exact global description” unless supported by precise global theorems.
4. Missing references

At minimum, the manuscript should replace its placeholders with the following core sources.

Yang and Lee, 1952, Parts I and II, for the Yang-Lee framework. 
link.aps.org
+1

Fisher, 1978, if the paper keeps the “edge singularity” terminology. 
link.aps.org

Beraha, Kahane, Weiss, 1975, and Sokal, 2004, for the limit-zero mechanism and a modern proof/reformulation of the BKW theorem. 
pnas.org
+1

Kato, 1976. If the paper keeps the “exceptional point” language, it should also cite at least one modern review such as Berry, 2004 or Heiss, 2012. 
Springer Link
+2
Springer Link
+2

Silverman for elliptic-curve/Weierstrass background, and Flajolet-Sedgewick for rational generating functions and recurrence background. 
Springer Link
+1

For nearby work on zeros of polynomial sequences defined by rational generating functions, the author should discuss Tran, 2014/2015 and Forgács- Tran, 2016. 
ScienceDirect
+2
ScienceDirect
+2

5. Specific improvements needed to reach acceptance

Repair the two main proof-level defects: the normalization claim in Section 4 and the zero-quantization argument in Section 6.

Install a complete bibliography and explain precisely what is new relative to BKW/Sokal, Kato-type perturbation theory, and the rational-generating-function zero literature.

Reposition the paper. At present it is best read as an exact study of one quartic family. Either embrace that and shorten it to a note, or substantially broaden the general-family analysis around Proposition 4.1.

Either provide a genuine microscopic transfer-matrix model, or remove unsupported statistical-mechanics language from the title, abstract, keywords, and discussion.

Compress routine sections. Section 3, much of Section 9, and some of the rhetorical discussion can be shortened without loss.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. References and bibliography.
Replace the placeholder citations section by section, not only at the end. In particular: Section 1.1 should cite Yang-Lee, Fisher, BKW, Sokal, Kato, and the relevant elliptic-curve and generating-function sources; Section 9.1 should cite BKW or Sokal exactly where the accumulation-set statement is used; and any retained EP terminology should cite Kato plus a modern review. 
Analytic Combinatorics
+8
link.aps.org
+8
link.aps.org
+8

B2. Normalization claim in Section 4.
Add a lemma after Theorem 4.4. Homogenize the affine quartic to

𝐹
(
Λ
,
𝑌
,
𝑍
)
=
Λ
4
−
Λ
3
𝑍
−
(
2
𝑌
𝑍
+
𝑍
2
)
Λ
2
+
Λ
𝑍
3
+
𝑌
(
𝑌
+
𝑍
)
𝑍
2
.
F(Λ,Y,Z)=Λ
4
−Λ
3
Z−(2YZ+Z
2
)Λ
2
+ΛZ
3
+Y(Y+Z)Z
2
.

Then show that 
𝐶
‾
=
{
𝐹
=
0
}
⊂
𝑃
2
C
={F=0}⊂P
2
 has a unique point at infinity, 
[
0
:
1
:
0
]
[0:1:0], and that this point is singular. Next define

𝜈
:
𝐸
→
𝐶
‾
,
(
𝜆
,
𝑌
)
↦
[
𝜆
:
𝜆
2
−
1
2
+
1
2
𝑌
:
1
]
ν:E→
C
,(λ,Y)↦[λ:λ
2
−
2
1
	​

+
2
1
	​

Y:1]

on the affine chart, where 
𝐸
:
𝑌
2
=
4
𝜆
3
−
4
𝜆
+
1
E:Y
2
=4λ
3
−4λ+1. The inverse rational map on the affine locus is 
𝑌
=
2
𝑦
+
1
−
2
𝜆
2
Y=2y+1−2λ
2
. Using

ord
⁡
𝑂
(
𝜆
)
=
−
2
,
ord
⁡
𝑂
(
𝑦
)
=
−
4
,
ord
O
	​

(λ)=−2,ord
O
	​

(y)=−4,

show that 
𝜈
ν extends across the point 
𝑂
∈
𝐸
O∈E and that 
𝜈
−
1
(
[
0
:
1
:
0
]
)
=
{
𝑂
}
ν
−1
([0:1:0])={O}. Since 
𝐸
E is smooth projective and 
𝜈
ν is finite birational, 
𝐸
E is the normalization of 
𝐶
‾
C
. Without this, “elliptic normalization” is not yet justified.

B3. Complex remainder estimate for Theorem 6.5.
Strengthen Appendix D.2 from real compact intervals to complex discs 
𝐾
⊂
𝐶
K⊂C around each 
𝑢
𝑘
(
0
)
u
k
(0)
	​

. For 
𝑦
=
−
𝑢
2
/
𝑚
2
y=−u
2
/m
2
 with 
𝑢
∈
𝐾
u∈K, the analytic branches satisfy

𝜆
−
1
(
𝑦
)
=
−
1
−
𝑦
4
+
𝑂
(
𝑦
2
)
,
𝐶
−
1
(
𝑦
)
=
𝑦
8
+
𝑂
(
𝑦
2
)
,
λ
−1
	​

(y)=−1−
4
y
	​

+O(y
2
),C
−1
	​

(y)=
8
y
	​

+O(y
2
),
𝜆
0
(
𝑦
)
=
−
𝑦
+
𝑂
(
𝑦
2
)
,
𝐶
0
(
𝑦
)
=
−
𝑦
+
𝑂
(
𝑦
2
)
,
λ
0
	​

(y)=−y+O(y
2
),C
0
	​

(y)=−y+O(y
2
),

uniformly on 
𝐾
K. Choose an analytic branch of 
log
⁡
𝜆
−
1
(
𝑦
)
logλ
−1
	​

(y) near 
𝑦
=
0
y=0:

log
⁡
𝜆
−
1
(
𝑦
)
=
𝑖
𝜋
+
𝑦
4
+
𝑂
(
𝑦
2
)
.
logλ
−1
	​

(y)=iπ+
4
y
	​

+O(y
2
).

Then

𝜆
−
1
(
𝑦
)
𝑚
=
(
−
1
)
𝑚
exp
⁡
 ⁣
(
𝑚
𝑦
4
+
𝑂
(
𝑚
𝑦
2
)
)
,
λ
−1
	​

(y)
m
=(−1)
m
exp(
4
my
	​

+O(my
2
)),

so 
∣
𝐶
−
1
(
𝑦
)
𝜆
−
1
(
𝑦
)
𝑚
∣
≤
𝐶
𝐾
𝑚
−
2
𝑒
𝐶
𝐾
/
𝑚
=
𝑂
𝐾
(
𝑚
−
2
)
∣C
−1
	​

(y)λ
−1
	​

(y)
m
∣≤C
K
	​

m
−2
e
C
K
	​

/m
=O
K
	​

(m
−2
), and similarly 
∣
𝐶
0
(
𝑦
)
𝜆
0
(
𝑦
)
𝑚
∣
=
𝑂
𝐾
(
𝑚
−
2
𝑚
−
2
)
∣C
0
	​

(y)λ
0
	​

(y)
m
∣=O
K
	​

(m
−2m−2
). This is exactly the complex-uniform bound needed for the Rouché step in Theorem 6.4.

M1. Reframe or strengthen Theorem 6.4.
A natural formulation would start from the spectral polynomial, not from already-expanded branches. For an analytic 
𝑃
(
𝜆
,
𝑦
)
P(λ,y), assume

𝑃
(
𝜆
𝑐
,
𝑦
𝑐
)
=
𝑃
𝜆
(
𝜆
𝑐
,
𝑦
𝑐
)
=
0
,
𝑃
𝜆
𝜆
(
𝜆
𝑐
,
𝑦
𝑐
)
 
𝑃
𝑦
(
𝜆
𝑐
,
𝑦
𝑐
)
≠
0.
P(λ
c
	​

,y
c
	​

)=P
λ
	​

(λ
c
	​

,y
c
	​

)=0,P
λλ
	​

(λ
c
	​

,y
c
	​

)P
y
	​

(λ
c
	​

,y
c
	​

)

=0.

Then with 
𝑦
=
𝑦
𝑐
+
𝑠
2
y=y
c
	​

+s
2
, one gets analytic branches

𝜆
±
(
𝑠
)
=
𝜆
𝑐
±
𝛼
𝑠
+
𝛽
𝑠
2
+
𝑂
(
𝑠
3
)
,
𝛼
2
=
−
2
𝑃
𝑦
𝑃
𝜆
𝜆
(
𝜆
𝑐
,
𝑦
𝑐
)
.
λ
±
	​

(s)=λ
c
	​

±αs+βs
2
+O(s
3
),α
2
=−
P
λλ
	​

2P
y
	​

	​

(λ
c
	​

,y
c
	​

).

If the corresponding amplitudes satisfy 
𝐶
+
(
0
)
=
𝐶
−
(
0
)
≠
0
C
+
	​

(0)=C
−
	​

(0)

=0 and 
𝐶
+
′
(
0
)
=
−
𝐶
−
′
(
0
)
C
+
′
	​

(0)=−C
−
′
	​

(0), the current cosine law follows. That would make the result a genuine EP2 theorem. Otherwise, it should be demoted to a lemma.

M2. Make Corollary 4.6 precise.
Insert the identity

Π
𝑦
(
𝜆
,
𝑦
)
=
2
𝑦
+
1
−
2
𝜆
2
=
𝑌
.
Π
y
	​

(λ,y)=2y+1−2λ
2
=Y.

Hence, away from 
𝑌
=
0
Y=0,

𝑑
𝑦
𝑑
𝜆
=
−
Π
𝜆
Π
𝑦
=
−
Π
𝜆
𝑌
.
dλ
dy
	​

=−
Π
y
	​

Π
λ
	​

	​

=−
Y
Π
λ
	​

	​

.

Therefore a finite repeated root of 
Π
(
⋅
,
𝑦
0
)
Π(⋅,y
0
	​

) is equivalent to a ramification point of 
𝑦
:
𝐸
→
𝑃
1
y:E→P
1
, provided 
𝑌
≠
0
Y

=0. In the present family, 
𝑌
=
0
Y=0 cannot occur simultaneously with the finite 
𝑦
y-ramification equation, because 
𝑌
=
0
Y=0 and 
−
3
𝜆
2
+
1
=
0
−3λ
2
+1=0 would force 
𝜆
=
±
1
/
3
λ=±1/
3
	​

, which are not roots of 
16
𝜆
3
−
9
𝜆
2
+
1
16λ
3
−9λ
2
+1. This removes the hidden case distinction.

M3. Prove 
𝑞
=
𝜆
d
o
m
(
𝑦
)
q=λ
dom
	​

(y) explicitly for 
𝑦
>
1
y>1.
Define

𝑦
−
(
𝜆
)
=
𝜆
2
−
1
2
−
1
2
4
𝜆
3
−
4
𝜆
+
1
,
𝑦
+
(
𝜆
)
=
𝜆
2
−
1
2
+
1
2
4
𝜆
3
−
4
𝜆
+
1
.
y
−
	​

(λ)=λ
2
−
2
1
	​

−
2
1
	​

4λ
3
−4λ+1
	​

,y
+
	​

(λ)=λ
2
−
2
1
	​

+
2
1
	​

4λ
3
−4λ+1
	​

.

For 
𝜆
>
1
λ>1,

𝑦
+
′
(
𝜆
)
=
2
𝜆
4
𝜆
3
−
4
𝜆
+
1
+
(
3
𝜆
2
−
1
)
4
𝜆
3
−
4
𝜆
+
1
>
0
,
y
+
′
	​

(λ)=
4λ
3
−4λ+1
	​

2λ
4λ
3
−4λ+1
	​

+(3λ
2
−1)
	​

>0,

so 
𝑦
+
y
+
	​

 is strictly increasing. Also 
𝑦
+
(
𝜆
)
>
𝑦
−
(
𝜆
)
y
+
	​

(λ)>y
−
	​

(λ) for every 
𝜆
>
1
λ>1. If 
𝑦
=
𝑦
−
(
𝑞
)
=
𝑦
+
(
𝑝
)
y=y
−
	​

(q)=y
+
	​

(p), then

𝑦
+
(
𝑞
)
>
𝑦
−
(
𝑞
)
=
𝑦
=
𝑦
+
(
𝑝
)
,
y
+
	​

(q)>y
−
	​

(q)=y=y
+
	​

(p),

hence 
𝑞
>
𝑝
q>p by monotonicity of 
𝑦
+
y
+
	​

. Therefore the 
−
−-sheet root is the larger positive root, so indeed 
𝑞
=
𝜆
d
o
m
(
𝑦
)
q=λ
dom
	​

(y).

M4. Strengthen the motivation mathematically.
Two viable routes exist. Either derive the quartic from a genuine transfer-matrix model, or broaden the general-family component. A mathematically meaningful expansion would be to analyze Proposition 4.1 beyond one specialization. For example, after obtaining the finite ramification quintic

16
𝑎
𝜆
5
+
9
𝑎
2
𝜆
4
+
16
𝑑
𝜆
3
+
(
16
𝑔
+
6
𝑎
𝑑
−
4
𝑐
2
)
𝜆
2
+
𝑑
2
=
0
,
16aλ
5
+9a
2
λ
4
+16dλ
3
+(16g+6ad−4c
2
)λ
2
+d
2
=0,

classify parameter regions where the real branch locus has three versus five real points, and determine when the real locus projects to one or two intervals on the 
𝑦
y-axis. That would materially increase significance.

M5. Add a precise literature-positioning paragraph.
The comparison should be explicit: BKW and Sokal describe general accumulation mechanisms for zeros of recursively defined families, while Tran-type results study real-algebraic support sets for broad rational-generating-function families. The present paper is narrower but more explicit: its distinctive contribution is the exact elliptic reduction and the exact classification of the real branch values for one quartic family. That comparison should be stated plainly, with citations.