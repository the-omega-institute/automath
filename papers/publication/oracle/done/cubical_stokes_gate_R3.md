<!-- oracle metadata: {"timestamp": "2026-04-07T04:57:41.647344", "model": "o3-mini-high", "response_length": 16085} -->

I reviewed the manuscript as a referee/editor. 

main

1. Overall assessment

Reject

The paper is not presently suitable for journal publication. The main obstacle is not that the elementary computations are wholly wrong. In fact, most of the pointwise estimates appear recoverable after minor formal repairs. The problem is that the manuscript substantially overstates both novelty and internal logical structure. Most of the core material is a very special-case consequence of classical de Rham homotopy/Poincaré operators and standard Whitney/FEEC machinery, yet the paper contains no usable bibliography at all. Moreover, the advertised implication chain “sharp inverse ⇒ boundary rigidity ⇒ dyadic readout” is not the logic actually used in Section 6, which depends only on Stokes’ theorem and the existence of a primitive of the volume form. Classical antecedents for these topics include Iwaniec–Lutoborski and Costabel–McIntosh on bounded operators for differential forms, Dupont on Whitney constructions, and Arnold–Falk–Winther together with Arnold–Awanou on FEEC and cubical differential forms. 
arXiv
+4
Springer
+4
arXiv
+4

The only part that struck me as potentially distinctive is the equality-case boundary trace rigidity in Theorem 5.2. In the present version, however, that observation is not developed into a sufficiently strong or sufficiently connected contribution to support the rest of the manuscript.

2. Novelty rating for each theorem-level result
Result	Novelty	One-line justification
Theorem 3.1(1)	LOW	This is the classical homotopy identity for the standard radial contraction on a star-shaped domain.
Theorem 3.1(2)	LOW	The constant 
1
/
(
2
𝑘
)
1/(2k) follows immediately from (
Theorem 3.1(3)	LOW	Sharpness is an elementary Stokes lower bound on a unit 
𝑘
k-face.
Theorem 3.2	LOW	This is a direct corollary of Theorem 3.1 applied to 
𝑑
𝜔
dω.
Corollary 3.3	LOW	Merely the 
𝑘
=
1
k=1 specialization of Theorem 3.2.
Theorem 4.1	LOW	Formal transfer of the continuous estimate through Whitney and integration maps; no new discrete mechanism is introduced.
Corollary 4.2	LOW	Immediate specialization of Theorem 4.1.
Theorem 4.3	LOW	Logarithmic reformulation of Corollary 4.2.
Proposition 5.1	LOW	Standard divergence-theorem/calibration inequality.
Theorem 5.2	MEDIUM	The equality-case rigidity of all face traces is the one place where the paper contains a nontrivial additional observation beyond the basic estimates.
Corollary 5.3	LOW	Direct differentiation of an explicit primitive.
Theorem 6.1	LOW	The flux identity is immediate from Stokes with a standard volume primitive, and the dimension formula is standard dyadic counting.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Global	BLOCKER	The manuscript has no actual bibliography. In-text citations remain as [?], including the main background claims.	Add a real bibliography and cite the precise antecedents in §§2, 4, 5, 6.
B2	Introduction, §6, §7	BLOCKER	The paper claims a theorem chain “sharp inverse ⇒ boundary-rigid minimizer ⇒ dyadic readout,” but §6 uses only Stokes and 
𝑑
𝜔
0
=
v
o
l
dω
0
	​

=vol. Boundary rigidity is not used.	Either decouple §6 as an independent observation, or add a genuinely new theorem that makes Section 6 depend on §5.
M1	Theorem 3.1	MEDIUM	The identity is stated for 
1
≤
𝑘
≤
𝑛
1≤k≤n, but 
𝐾
𝑛
+
1
K
n+1
	​

 was never defined.	Restrict the identity to 
𝑘
≤
𝑛
−
1
k≤n−1, or define 
𝐾
𝑛
+
1
=
0
K
n+1
	​

=0 on 
Ω
𝑛
+
1
(
𝐼
𝑛
)
=
0
Ω
n+1
(I
n
)=0.
M2	Definition 2.1 and throughout	MEDIUM	“Decomposable” is used in a nonstandard and much narrower sense: a single coordinate wedge times a scalar.	Rename the class, e.g. “coordinate-monomial” or “single-coordinate-wedge.”
M3	§2.2, §4	MEDIUM	The discrete section relies on specific cubical Whitney maps and sup-norm bounds 
∥
𝑊
∥
∞
→
∞
≤
1
∥W∥
∞→∞
	​

≤1, 
∥
𝐼
∥
∞
→
∞
≤
1
∥I∥
∞→∞
	​

≤1, but these are neither proved nor cited precisely.	Give explicit formulas on the reference cube and prove the bounds, or cite standard cubical FEEC references.
M4	Title, Abstract, Introduction	MEDIUM	Novelty claims are inflated relative to classical de Rham/Poincaré operators and FEEC/Whitney theory.	Reframe the paper as a sharp estimate for the classical radial homotopy on a very restricted coefficient class.
M5	Theorem 6.1	MEDIUM	The theorem conflates a routine volume-decay estimate with the independent flux identity, and the notation should be 
dim
⁡
‾
𝑀
dim
M
	​

 because a 
lim sup
⁡
limsup is used.	Split the theorem into separate statements and define upper Minkowski dimension explicitly.
L1	Theorem 3.2 proof; Cor. 3.3 proof	LOW	The sharpness proofs cite Theorem 3.1(3), but the argument actually uses the lower bound for every primitive, not an operator-norm statement.	State that primitive lower bound separately and cite it correctly.
L2	Abstract, Introduction	LOW	The paper calls itself “self-contained,” which is false without proofs or citations for Whitney machinery and Minkowski-dimension facts.	Remove the claim or supply the missing proofs/references.
L3	§4	LOW	The Whitney-decomposable class on the hypercube is extremely restrictive, but this is not emphasized and no nontrivial examples/classification are given.	Add examples and a characterization of when a square-defect cochain is Whitney-decomposable.
L4	Table 1, §5	LOW	The “boundary minimizers” summary reads more general than what is actually proved, namely only for 
𝑑
𝜂
=
𝑑
𝑥
1
∧
⋯
∧
𝑑
𝑥
𝑘
dη=dx
1
	​

∧⋯∧dx
k
	​

 on 
𝐼
𝑘
I
k
.	Narrow the wording.
4. Missing references

At minimum, the following should be cited.

Bott and Tu, Differential Forms in Algebraic Topology, or Loring Tu, An Introduction to Manifolds, for the classical de Rham homotopy formula and homotopy invariance background. 
math.auckland.ac.nz
+1

Iwaniec and Lutoborski (1993), “Integral estimates for null Lagrangians”, and Costabel and McIntosh (2010), “On Bogovskiĭ and regularized Poincaré integral operators for de Rham complexes on Lipschitz domains”, for bounded Poincaré/de Rham operators on differential forms and analytic right-inverse constructions. 
Springer
+1

Dupont (1976), “Simplicial de Rham cohomology and characteristic classes of flat bundles”, for Whitney forms and chain-level de Rham constructions. 
sciencedirect.com

Arnold, Falk, Winther (2006), “Finite element exterior calculus, homological techniques, and applications”, and Arnold, Awanou (2014), “Finite element differential forms on cubical meshes”, for the FEEC viewpoint and cubical differential forms. 
Cambridge University Press & Assessment
+1

Evans and Gariepy, Measure Theory and Fine Properties of Functions, or Maggi, Sets of Finite Perimeter and Geometric Variational Problems, for Gauss-Green/fine perimeter background. 
USTC Home
+1

Falconer, Fractal Geometry, or Mattila, Geometry of Sets and Measures in Euclidean Spaces, for box/Minkowski dimension; and a standard source noting that balls and cubes yield the same upper box dimension in 
𝑅
𝑛
R
n
. 
Wiley Online Library
+2
Cambridge University Press & Assessment
+2

5. Specific improvements needed to reach acceptance

First, the paper must be rewritten with an honest scope. The correct contribution is not a new general inverse theory on cubes, but at most a sharp coefficient-sup estimate for the classical radial homotopy on a very narrow class of coordinate-monomial forms, plus an equality-case face-trace observation.

Second, the theorem statements must be repaired formally, especially Theorem 3.1 at top degree and the notation in Theorem 6.1.

Third, the discrete section requires either explicit cubical Whitney formulas and proofs of the norm bounds, or precise references. At present it rests on unproved black boxes while simultaneously claiming self-containment.

Fourth, the narrative architecture must be corrected. Section 6 is not a consequence of Sections 3 to 5 in its present form. This is not merely a matter of style. It changes the paper’s central claim.

Fifth, the only part with potentially publishable distinctiveness is the rigidity statement in Theorem 5.2. If the author wants a journal paper rather than a short note, that theorem must be deepened substantially, for example by developing an actual equality-case characterization or a uniqueness statement with geometric consequences not already implied by ordinary Stokes.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Missing bibliography and placeholders

A minimally acceptable repair is the following.

After Definition 2.2 and formula (2.1), cite a standard de Rham homotopy source such as Bott–Tu or Tu, and an analytic/right-inverse source such as Iwaniec–Lutoborski or Costabel–McIntosh. In §2.2 and §4, cite Dupont for Whitney forms and Arnold–Falk–Winther / Arnold–Awanou for FEEC and cubical meshes. In §5 cite Evans–Gariepy or Maggi for Gauss-Green background, and in §6 cite Falconer or Mattila for upper Minkowski dimension and dyadic covering counts. 
Cambridge University Press & Assessment
+8
math.auckland.ac.nz
+8
Springer
+8

The manuscript should then replace every placeholder [?] by an actual citation and delete the sentence claiming self-containment unless all such facts are proved in full.

B2. False logical chain connecting §§3 to 6

The mathematically correct statement is:

If 
𝑑
𝜂
=
𝑑
𝑥
1
∧
⋯
∧
𝑑
𝑥
𝑛
 on a neighborhood of 
𝑈
𝑚
(
𝐴
)
,
 then 
∫
∂
𝑈
𝑚
(
𝐴
)
𝜂
=
Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
If dη=dx
1
	​

∧⋯∧dx
n
	​

 on a neighborhood of U
m
	​

(A), then ∫
∂U
m
	​

(A)
	​

η=Vol(U
m
	​

(A))

by Stokes alone.

That statement does not use optimality, the constant 
1
/
(
2
𝑘
)
1/(2k), or the boundary rigidity theorem. Therefore the introduction and discussion should be rewritten to say that §6 is an independent geometric observation.

A precise revision would be:

delete the implication “boundary-rigid minimizer 
⇒
⇒ dyadic boundary readout”;

replace it by two parallel outputs:

classical radial homotopy
+
coefficient sup norm
⇒
sharp constant on coordinate-monomial forms
,
classical radial homotopy+coefficient sup norm⇒sharp constant on coordinate-monomial forms,
Stokes
+
𝑑
𝜔
0
=
v
o
l
⇒
dyadic flux/volume identity
.
Stokes+dω
0
	​

=vol⇒dyadic flux/volume identity.

If the author wants a genuine connection, a new theorem is needed. For example, one could prove that among all 
𝐿
∞
L
∞
-minimizers of 
𝑑
𝜂
=
v
o
l
dη=vol on 
𝐼
𝑛
I
n
, the trace on every boundary face is canonical, and then derive a uniqueness statement for boundary probes within the minimizer class. But the present Section 6 does not do this.

M1. Theorem 3.1 is ill-posed at 
𝑘
=
𝑛
k=n

The clean fix is to replace Theorem 3.1(1) by:

𝑑
𝐾
𝑘
𝜔
+
𝐾
𝑘
+
1
(
𝑑
𝜔
)
=
𝜔
,
1
≤
𝑘
≤
𝑛
−
1
,
dK
k
	​

ω+K
k+1
	​

(dω)=ω,1≤k≤n−1,

and separately,

𝑑
𝐾
𝑛
𝜔
=
𝜔
,
𝜔
∈
Ω
s
m
𝑛
(
𝐼
𝑛
)
,
dK
n
	​

ω=ω,ω∈Ω
sm
n
	​

(I
n
),

since 
𝑑
𝜔
=
0
dω=0 automatically on 
𝐼
𝑛
I
n
.

Equivalent alternative: define 
𝐾
𝑛
+
1
:
=
0
K
n+1
	​

:=0 on 
Ω
𝑛
+
1
(
𝐼
𝑛
)
=
{
0
}
Ω
n+1
(I
n
)={0} immediately after Definition 2.2. Then the existing formula becomes formally correct.

M2. Nonstandard use of “decomposable”

Replace Definition 2.1 by:

A
 
smooth
 
𝑘
-form
 
is
 
coordinate-monomial
 
if
 
𝜔
=
𝑓
(
𝑥
)
 
𝑑
𝑥
𝑖
1
∧
⋯
∧
𝑑
𝑥
𝑖
𝑘
.
A smooth k-form is coordinate-monomial if ω=f(x)dx
i
1
	​

	​

∧⋯∧dx
i
k
	​

	​

.

Then add the remark:

(
𝑑
𝑥
1
+
𝑑
𝑥
2
)
∧
𝑑
𝑥
3
(dx
1
	​

+dx
2
	​

)∧dx
3
	​


is decomposable in the standard algebraic sense, but it is not coordinate-monomial. Under the coefficient sup norm, estimate (3.2) already fails for this example, exactly as shown in Remark 2.4.

This one remark would prevent the paper from appearing to claim results about general decomposable forms.

M3. Whitney machinery and norm bounds are currently unsupported

If the author wants §4 to stand on its own, the following explicit construction should be inserted.

Let 
𝜎
𝐼
,
𝜀
σ
I,ε
	​

 be the oriented 
𝑘
k-face parallel to the coordinate directions 
𝐼
=
{
𝑖
1
<
⋯
<
𝑖
𝑘
}
I={i
1
	​

<⋯<i
k
	​

} and fixed by 
𝑥
𝑗
=
𝜀
𝑗
∈
{
0
,
1
}
x
j
	​

=ε
j
	​

∈{0,1} for 
𝑗
∉
𝐼
j∈
/
I. Define

𝑊
𝜎
𝐼
,
𝜀
=
(
∏
𝑗
∉
𝐼
𝜆
𝑗
𝜀
𝑗
(
𝑥
𝑗
)
)
 
𝑑
𝑥
𝑖
1
∧
⋯
∧
𝑑
𝑥
𝑖
𝑘
,
𝜆
𝑗
0
=
1
−
𝑥
𝑗
,
 
𝜆
𝑗
1
=
𝑥
𝑗
.
Wσ
I,ε
	​

=(
j∈
/
I
∏
	​

λ
j
ε
j
	​

	​

(x
j
	​

))dx
i
1
	​

	​

∧⋯∧dx
i
k
	​

	​

,λ
j
0
	​

=1−x
j
	​

, λ
j
1
	​

=x
j
	​

.

Then:

𝐼
∘
𝑊
=
I
d
I∘W=Id on basis cochains, because on the face 
𝜎
𝐼
,
𝜀
σ
I,ε
	​

 the product factor is 
1
1, while on any other parallel face at least one factor vanishes.

𝑑
𝑊
=
𝑊
𝑑
dW=Wd, because differentiating the product introduces exactly the codimension-one faces with the correct cubical signs:

𝑑
𝜆
𝑗
0
=
−
𝑑
𝑥
𝑗
,
𝑑
𝜆
𝑗
1
=
𝑑
𝑥
𝑗
.
dλ
j
0
	​

=−dx
j
	​

,dλ
j
1
	​

=dx
j
	​

.

If 
𝜃
=
∑
𝐼
,
𝜀
𝜃
𝐼
,
𝜀
𝜎
𝐼
,
𝜀
θ=∑
I,ε
	​

θ
I,ε
	​

σ
I,ε
	​

, then the coefficient of 
𝑑
𝑥
𝐼
dx
I
	​

 in 
𝑊
𝜃
Wθ is

∑
𝜀
𝜃
𝐼
,
𝜀
∏
𝑗
∉
𝐼
𝜆
𝑗
𝜀
𝑗
(
𝑥
𝑗
)
,
ε
∑
	​

θ
I,ε
	​

j∈
/
I
∏
	​

λ
j
ε
j
	​

	​

(x
j
	​

),

which is a convex combination of the face values 
𝜃
𝐼
,
𝜀
θ
I,ε
	​

. Hence

∥
𝑊
𝜃
∥
∞
≤
∥
𝜃
∥
∞
.
∥Wθ∥
∞
	​

≤∥θ∥
∞
	​

.

If 
𝛼
=
∑
𝐼
𝑎
𝐼
(
𝑥
)
 
𝑑
𝑥
𝐼
α=∑
I
	​

a
I
	​

(x)dx
I
	​

, then for every unit 
𝑘
k-face 
𝜎
σ,

∣
𝐼
𝛼
(
𝜎
)
∣
=
∣
∫
𝜎
𝛼
∣
≤
sup
⁡
𝜎
∣
𝑎
𝐼
∣
≤
∥
𝛼
∥
∞
,
∣Iα(σ)∣=
	​

∫
σ
	​

α
	​

≤
σ
sup
	​

∣a
I
	​

∣≤∥α∥
∞
	​

,

because each face has 
𝑘
k-dimensional volume 
1
1. Therefore

∥
𝐼
𝛼
∥
∞
≤
∥
𝛼
∥
∞
.
∥Iα∥
∞
	​

≤∥α∥
∞
	​

.

With these four lines, Theorem 4.1 becomes genuinely self-contained.

M4. Overstated novelty and title/abstract language

The manuscript should stop presenting the result as a new “optimal bounded Poincaré–Stokes inverse” in any broad sense. A mathematically accurate title would be closer to:

“A sharp coefficient-sup estimate for the classical radial homotopy on coordinate-monomial forms, with cubical and dyadic corollaries.”

Likewise, the abstract should say explicitly that the operator is the standard radial homotopy and that the sharp constant is obtained only on the restricted coordinate-monomial class. This would align the manuscript with the existing literature rather than pretending to replace it. The surrounding literature on bounded de Rham operators and FEEC is extensive. 
arXiv
+3
Springer
+3
arXiv
+3

M5. Section 6 should be split and the dimension notation corrected

A rigorous restructuring is:

Proposition 6.1. For every smooth 
(
𝑛
−
1
)
(n−1)-form 
𝜔
ω on a neighborhood of 
𝐼
𝑛
I
n
,

∣
∫
∂
𝑈
𝑚
(
𝐴
)
𝜔
∣
≤
∥
𝑑
𝜔
∥
∞
 
Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
.
	​

∫
∂U
m
	​

(A)
	​

ω
	​

≤∥dω∥
∞
	​

Vol(U
m
	​

(A)).

If additionally 
Vol
⁡
(
𝐴
𝜀
)
≤
𝐶
𝐴
𝜀
𝑛
−
𝑑
Vol(A
ε
	​

)≤C
A
	​

ε
n−d
, then

Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
≤
𝐶
𝐴
𝑛
(
𝑛
−
𝑑
)
/
2
2
−
𝑚
(
𝑛
−
𝑑
)
.
Vol(U
m
	​

(A))≤C
A
	​

n
(n−d)/2
2
−m(n−d)
.

Proposition 6.2. If 
𝜂
η satisfies 
𝑑
𝜂
=
𝑑
𝑥
1
∧
⋯
∧
𝑑
𝑥
𝑛
dη=dx
1
	​

∧⋯∧dx
n
	​

 on a neighborhood of 
𝑈
𝑚
(
𝐴
)
U
m
	​

(A), then

∫
∂
𝑈
𝑚
(
𝐴
)
𝜂
=
Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
.
∫
∂U
m
	​

(A)
	​

η=Vol(U
m
	​

(A)).

Corollary 6.3. Writing 
𝑁
𝑚
(
𝐴
)
N
m
	​

(A) for the number of side-
2
−
𝑚
2
−m
 dyadic cubes meeting 
𝐴
A,

Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
=
2
−
𝑚
𝑛
𝑁
𝑚
(
𝐴
)
,
Vol(U
m
	​

(A))=2
−mn
N
m
	​

(A),

and therefore

dim
⁡
‾
𝑀
(
𝐴
)
=
lim sup
⁡
𝑚
→
∞
log
⁡
𝑁
𝑚
(
𝐴
)
𝑚
log
⁡
2
=
𝑛
+
lim sup
⁡
𝑚
→
∞
log
⁡
Vol
⁡
(
𝑈
𝑚
(
𝐴
)
)
𝑚
log
⁡
2
.
dim
M
	​

(A)=
m→∞
limsup
	​

mlog2
logN
m
	​

(A)
	​

=n+
m→∞
limsup
	​

mlog2
logVol(U
m
	​

(A))
	​

.

This is the correct notation because a 
lim sup
⁡
limsup is used. Standard references treat the equivalence of ball and cube definitions of box/Minkowski dimension. 
Wiley Online Library
+2
Cambridge University Press & Assessment
+2

Bottom line

The paper contains a few correct elementary observations and one possibly interesting rigidity lemma, but it is not ready for journal publication. The current version lacks the minimum scholarly apparatus, overstates its novelty, and misrepresents the logical dependence of its final section. The right path forward is not cosmetic revision. It is a fundamental reframing around the genuinely nontrivial part, with the rest either demoted to background or connected by a new theorem that is actually used.