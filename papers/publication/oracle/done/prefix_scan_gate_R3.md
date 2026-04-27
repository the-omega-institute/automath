<!-- oracle metadata: {"timestamp": "2026-04-08T06:31:42.914467", "model": "chatgpt-5.4-pro-extended", "response_length": 11909} -->

1. Overall assessment

Reject

The manuscript has a clean central object, the scan error profile, but in its current form I do not think it is publishable. There are two blocker-level mathematical problems: Theorem 5.5 is stronger than what its proof establishes, and the headline golden-mean example is invalid because the event used has measure zero under the paper’s own cylinder estimates, so the claimed nonzero rate cannot hold. Beyond correctness, the remaining main theorems are mostly direct consequences of Proposition 3.1 plus a standard discrete-time Tanaka/convexity identity, and the paper does not clearly distinguish itself from existing dyadic boundary-complexity and tree-approximation literature. 

main

 
Mathematical Institute
+5
Rice Statistics
+5
Machine Learning Group
+5

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 4.1	LOW	Essentially the convexity identity for (
Theorem 5.2	LOW	Immediate from Proposition 3.1 after summing only over mixed cylinders and applying the cylinder-mass upper bound.
Theorem 5.3	LOW	Same argument as Theorem 5.2, with a lower bound added via thickness; structurally very close to existing dyadic boundary-complexity ideas.
Theorem 5.5	LOW	A formal polynomial-distortion variant of Theorem 5.3, and currently overstated as written.

These low ratings are driven by the fact that dyadic boundary-counting classes, boundary/noise assumptions, and tree-approximation viewpoints are already well developed in the dyadic decision-tree and nonlinear approximation literature. Scott and Nowak explicitly define a dyadic box-counting boundary class using the number of partition cells intersecting the boundary, and discuss accompanying noise assumptions; Blanchard et al. develop optimal dyadic decision trees with oracle bounds; Donoho, DeVore, and Cohen et al. provide the broader dyadic CART / nonlinear / tree-approximation context. 
People.math.sc.edu
+5
Rice Statistics
+5
Rice Statistics
+5

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§5.3, Thm. 5.5	BLOCKER	The stated fixed-constant bounds do not follow from 
𝑁
𝑚
(
∂
𝑃
)
=
𝜆
cyl
𝑑
𝑚
+
𝑜
(
𝑚
)
N
m
	​

(∂P)=λ
cyl
dm+o(m)
	​

. The proof only yields a multiplicative 
𝜆
cyl
𝑜
(
𝑚
)
λ
cyl
o(m)
	​

 term.	Weaken the theorem, or strengthen the hypothesis on 
𝑁
𝑚
N
m
	​

.
B2	§6.2, Ex. 6.2	BLOCKER	The event 
𝐸
=
{
𝑥
2
𝑘
=
0
 
∀
𝑘
}
E={x
2k
	​

=0 ∀k} has 
𝜇
(
𝐸
)
=
0
μ(E)=0 under the paper’s own cylinder upper bounds, so 
𝜖
𝑚
(
𝐸
;
𝜇
)
=
0
ϵ
m
	​

(E;μ)=0 for every 
𝑚
m. The claimed 
≍
𝜙
−
𝑚
/
2
≍ϕ
−m/2
 behavior is impossible.	Replace the example completely with a valid positive-measure event and recompute everything.
M1	§6.2	MEDIUM	Boundary cylinders are counted topologically rather than measure-theoretically. The claim 
𝑁
2
𝑘
+
1
(
∂
𝐸
)
=
0
N
2k+1
	​

(∂E)=0 would force 
𝜖
2
𝑘
+
1
=
0
ϵ
2k+1
	​

=0, which contradicts the intended nontrivial infinite-horizon example.	Recompute 
∂
𝑚
𝑃
∂
m
	​

P using the actual definition 
𝜇
(
𝑃
∩
𝐶
)
>
0
μ(P∩C)>0 and 
𝜇
(
𝐶
∖
𝑃
)
>
0
μ(C∖P)>0.
M2	§§1.2, 5, 7	MEDIUM	Related work is missing where it matters most. The boundary-count viewpoint is too close to dyadic box-counting / decision-tree literature for the novelty claim to be credible without a direct comparison.	Add a dedicated related-work subsection and a side-by-side comparison of assumptions, objects, and results.
M3	§4	MEDIUM	Theorem 4.1 is presented as a main contribution, but the proof is basically the discrete Tanaka / convexity identity applied to the posterior martingale. The novelty is interpretive, not theorem-level.	Demote to proposition/corollary, or sharply narrow the novelty claim and cite the discrete-time Tanaka literature.
M4	§§5.3, 7	MEDIUM	The claim that uniform bounds 
𝜇
(
𝐶
)
≍
𝜆
cyl
−
𝑚
μ(C)≍λ
cyl
−m
	​

 hold for Gibbs measures on mixing SFTs is too broad. Standard Gibbs estimates depend on the potential, not just on 
𝑚
m.	Restrict to Parry / measure-of-maximal-entropy cases, or reformulate using potential-dependent Gibbs weights.
M5	§§1.1, 7	MEDIUM	The analogy to Tsybakov’s margin condition is overstated. A fixed thickness constant 
𝜃
θ is not an analogue of the margin exponent 
𝛼
α.	Rewrite this as a heuristic comparison only, and state clearly what is comparable and what is not.
L1	Prop. 2.2	LOW	“Union of length-
𝑚
m cylinders” is not equivalent to “a clopen ball of radius 
2
−
𝑚
2
−m
.” It is a clopen set, or a union of such balls.	Correct the wording.

Rows B1, B2, M1, and L1 arise directly from the manuscript’s statements, proofs, and definitions. In particular, for B2, if 
𝐴
𝑘
:
=
{
𝑥
0
=
𝑥
2
=
⋯
=
𝑥
2
𝑘
=
0
}
A
k
	​

:={x
0
	​

=x
2
	​

=⋯=x
2k
	​

=0}, then 
𝐴
𝑘
A
k
	​

 is a union of at most 
2
𝑘
2
k
 cylinders of length 
2
𝑘
+
1
2k+1, so the paper’s own bound 
𝜇
(
[
𝑎
]
)
≤
𝑐
+
𝜙
−
(
2
𝑘
+
1
)
μ([a])≤c
+
	​

ϕ
−(2k+1)
 gives 
𝜇
(
𝐴
𝑘
)
≤
𝑐
+
2
𝑘
𝜙
−
(
2
𝑘
+
1
)
→
0
μ(A
k
	​

)≤c
+
	​

2
k
ϕ
−(2k+1)
→0, hence 
𝜇
(
𝐸
)
=
0
μ(E)=0. 

main

For rows M2 to M5, the missing or misused context is substantial: Scott and Nowak already work with dyadic box-counting boundary classes and noise conditions; Blanchard et al. give optimal dyadic decision trees and oracle inequalities; discrete-time Tanaka-Meyer formulae are standard; and the Gibbs property on SFTs controls cylinder mass by a potential-dependent weight 
𝑒
𝑆
𝑛
𝜙
−
𝑛
𝑃
(
𝜙
)
e
S
n
	​

ϕ−nP(ϕ)
, not by a universal 
𝜆
−
𝑛
λ
−n
 law unless one is in a special case. 
Springer
+4
Rice Statistics
+4
Rice Statistics
+4

4. Missing references

Scott, C. and Nowak, R. D. (2006), Minimax-Optimal Classification With Dyadic Decision Trees. This is the closest omitted reference. It explicitly introduces a dyadic box-counting boundary class by counting partition cells that intersect the boundary, and studies accompanying noise assumptions and rates. 
Rice Statistics
+1

Blanchard, Schäfer, Rozenholc, and Müller (2007), Optimal Dyadic Decision Trees. Very relevant for the dyadic-tree/oracle viewpoint and for positioning this manuscript against prior exact-search and oracle-bound work. 
Machine Learning Group

Donoho (1997), CART and best-ortho-basis: A connection. Important background if the paper wants to frame its contribution as part of dyadic recursive partition approximation rather than only symbolic dynamics. 
Project Euclid

DeVore (1998), Nonlinear approximation, and Cohen-Dahmen-Daubechies-DeVore (1999/2001), Tree Approximation and Optimal Encoding. These are natural references for any rate theorem phrased through adaptive partitions / tree approximation. 
People.math.sc.edu
+1

Discrete-time Tanaka-Meyer literature, for example Łochowski, Obłój, Prömel, and Siopraes on local times and Tanaka-Meyer formulae for càdlàg paths. If Section 4 remains central, this literature should be acknowledged. 
Mathematical Institute

5. Specific improvements needed to reach acceptance

Fix the correctness issues first. Theorem 5.5 must be restated or reproved, and Example 6.2 must be replaced. Without this, the paper is not reviewable on its intended merits. 

main

Reposition the paper honestly. As written, the manuscript claims theorem-level novelty where there is mostly reformulation or repackaging. The paper needs a narrower and more accurate statement of what is genuinely new.

Add a serious literature comparison. Right now the paper reads as if boundary-counting on dyadic partitions is new, when it is not. The authors need to explain exactly how their oracle scan-error setting differs from Scott-Nowak, Blanchard et al., and the broader tree-approximation literature. 
People.math.sc.edu
+4
Rice Statistics
+4
Machine Learning Group
+4

Restrict the scope claims about measures. The discussion of Gibbs measures should be corrected and narrowed unless the theorems are reformulated in true Gibbs-property form. 
Springer

Strengthen the substantive contribution. Even after fixing B1 and B2, the paper still reads more like a short note built around Proposition 3.1 and a standard convexity identity. For a journal paper, I would want either one genuinely deeper theorem or a significantly more modest presentation.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Theorem 5.5

Replace the current statement by one the proof actually yields, for example

𝜖
𝑚
(
𝑃
;
𝜇
)
=
𝑚
±
𝛼
𝜆
c
y
l
−
(
1
−
𝑑
)
𝑚
+
𝑜
(
𝑚
)
,
ϵ
m
	​

(P;μ)=m
±α
λ
cyl
−(1−d)m+o(m)
	​

,

or more explicitly

𝜃
𝑐
1
𝑚
−
𝛼
𝜆
c
y
l
−
𝑚
𝑁
𝑚
(
∂
𝑃
)
≤
𝜖
𝑚
(
𝑃
;
𝜇
)
≤
𝑐
2
2
𝑚
𝛼
𝜆
c
y
l
−
𝑚
𝑁
𝑚
(
∂
𝑃
)
.
θc
1
	​

m
−α
λ
cyl
−m
	​

N
m
	​

(∂P)≤ϵ
m
	​

(P;μ)≤
2
c
2
	​

	​

m
α
λ
cyl
−m
	​

N
m
	​

(∂P).

If the authors want fixed constants 
𝐶
1
,
𝐶
2
C
1
	​

,C
2
	​

 in front of 
𝜆
c
y
l
−
(
1
−
𝑑
)
𝑚
λ
cyl
−(1−d)m
	​

, they need a stronger hypothesis such as

𝑁
𝑚
(
∂
𝑃
)
=
Θ
(
𝑚
𝛽
𝜆
c
y
l
𝑑
𝑚
)
N
m
	​

(∂P)=Θ(m
β
λ
cyl
dm
	​

)

or at least upper and lower bounds with explicit polynomial factors.

B2. Example 6.2

Delete the example as written. A minimal repair is to replace it with a positive-measure event. One safe option is to move to the full binary shift with fair Bernoulli measure and take an event induced by a dyadic set in 
[
0
,
1
]
[0,1], for example a threshold set or a dyadic fat-Cantor-type set under binary coding, where mixed cylinders can actually be counted. If the authors want a nontrivial exponent 
𝑑
∈
(
0
,
1
)
d∈(0,1), they need to build a set whose dyadic boundary count is tuned to that exponent and then verify both positive measure and thickness.

M1. Measure-theoretic boundary in the example

Recompute 
∂
𝑚
𝑃
∂
m
	​

P using the paper’s actual definition. As an internal consistency check, use Corollary 3.3 / Proposition 3.1 in the form

∂
𝑚
𝑃
=
∅
  
⟹
  
𝜖
𝑚
(
𝑃
;
𝜇
)
=
0
,
∂
m
	​

P=∅⟹ϵ
m
	​

(P;μ)=0,

so any claimed example with infinitely many empty boundary levels but nonzero error is automatically suspect.

M2. Missing comparison to prior dyadic-tree work

Add a dedicated comparison table with columns such as: setting, object approximated, known measure or sampled data, complexity notion, role of noise/margin, and resulting rate. The core papers that must be discussed are Scott-Nowak, Blanchard et al., Donoho, and the tree/nonlinear approximation literature. Without this, the novelty claim remains unconvincing. 
People.math.sc.edu
+4
Rice Statistics
+4
Machine Learning Group
+4

M3. Positioning of Theorem 4.1

Retitle it as something like “A discrete Tanaka identity for the posterior martingale” and present it as a structural observation rather than a main theorem, unless the authors can prove something beyond the standard identity. If they keep the local-time framing, they should cite discrete-time Tanaka-Meyer work explicitly. 
Mathematical Institute

M4. Claims about Gibbs measures

Either restrict the discussion to the Parry measure / measure of maximal entropy, where 
𝜇
(
𝐶
)
≍
𝜆
c
y
l
−
𝑚
μ(C)≍λ
cyl
−m
	​

 is plausible, or rewrite the framework using the actual Gibbs property

𝜇
(
[
𝑥
0
…
𝑥
𝑛
−
1
]
)
≍
𝑒
𝑆
𝑛
𝜙
(
𝑥
)
−
𝑛
𝑃
(
𝜙
)
.
μ([x
0
	​

…x
n−1
	​

])≍e
S
n
	​

ϕ(x)−nP(ϕ)
.

That would require a different weighting in the rate theorems, because cylinder masses are then potential-dependent rather than uniform across all cylinders of the same length. 
Springer

M5. Margin discussion

Rewrite Section 1.1 so that it says only this: thickness is a uniform two-sided nondegeneracy assumption on mixed cylinders, whereas Tsybakov’s condition is a global distributional statement about the regression function near 
1
/
2
1/2. If the authors want a closer statistical-learning comparison, Scott and Nowak’s treatment of box-counting boundary classes together with noise assumptions is the more natural reference point. 
Rice Statistics

My bottom line is that the paper needs more than polishing. It needs a corrected theorem, a new example, narrower claims, and a much stronger literature positioning before it could be reconsidered.