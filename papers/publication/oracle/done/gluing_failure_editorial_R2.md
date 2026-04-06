<!-- oracle metadata: {"timestamp": "2026-04-04T23:29:40.685691", "model": "o3-mini-high", "response_length": 20629} -->

For the manuscript “Elliptic Normalization of a Quartic Transfer Family”, my recommendation is:

1. Overall assessment

Major revision.

The manuscript has a credible algebraic core, but it is not yet publishable in its present form. The most serious problems are not stylistic. They are mathematical and scholarly: the paper does not actually prove the local dominance claim at 
𝑦
=
0
y=0 in Theorem 5.1(1), it does not prove that the branch singled out in Theorem 6.1 is globally dominant for all 
𝑦
>
0
y>0, the bibliography is unusable because the citations remain as unresolved placeholders, and one headline claim is false as stated, namely the repeated assertion of a “double zero” at 
𝑦
=
−
1
y=−1, whereas the paper proves only multiplicity at least two and already gives 
𝑍
3
(
𝑦
)
=
(
𝑦
+
1
)
3
Z
3
	​

(y)=(y+1)
3
. In current form I would not recommend acceptance. 

main

2. Novelty rating for each theorem

These ratings are necessarily provisional, because the manuscript contains no usable bibliography and therefore does not substantiate its priority claims.

Theorem	Rating	One-line justification
Theorem 3.1	LOW	Resultant-based coprimality and minimal recurrence order for a reduced rational generating function are standard.
Theorem 4.4	MEDIUM	The family-specific reduction is neat, but birational reduction of quartic curves to Weierstrass form is classical.
Theorem 5.1	HIGH	The exact dominant versus subdominant classification of all real branch values is the paper’s most distinctive family-specific claim.
Theorem 5.5	MEDIUM	The exact real-root phase diagram is useful and nontrivial, but it is built from standard real-oval geometry of elliptic curves.
Theorem 6.1	LOW	Once the branch is explicit, monotonicity is routine; the genuinely interesting part would be the missing global dominance proof.
Theorem 6.3	LOW	The abstract cosine normal form is a standard local two-branch asymptotic unless the paper documents a sharper novelty claim.
Theorem 6.4	MEDIUM	The explicit constants for the edge-zero quantization in this concrete quartic family are valuable.
Theorem 7.1	LOW	This is an elementary induction on the recurrence once the degree bookkeeping is set up.
3. Issue table

The table below lists the substantive issues that prevent acceptance. 

main

ID	Section	Severity	Description	Suggested fix
B1	§1.1 and throughout	BLOCKER	All references are unresolved placeholders [?], and there is no bibliography. Priority, novelty, and even standard background claims are therefore unverifiable.	Add a full references section, replace every placeholder, and anchor each standard tool to a specific source.
B2	§5, Theorem 5.1(1)	BLOCKER	The proof does not establish that the 
𝑦
=
0
y=0 collision is locally dominant. Direct factorization at 
𝑦
=
0
y=0 is insufficient, since 
𝜆
=
−
1
λ=−1 has the same modulus as the colliding double root there.	Prove dominance for 
𝑦
=
𝑠
2
>
0
y=s
2
>0 small using explicit branch expansions near 
𝑦
=
0
y=0.
B3	§6.1, Theorem 6.1	BLOCKER	The theorem proves monotonicity of the chosen real branch, but not that it is the spectral-radius branch on all of 
𝑦
>
0
y>0.	Add a global modulus comparison with all other roots, separately on 
0
<
𝑦
<
1
0<y<1 and on 
𝑦
>
1
y>1.
M1	§6.3 to §6.4	MEDIUM	The “universal dominant-EP2 normal form” is not stated or proved with enough analytic precision. The substitution 
𝑠
=
𝑖
𝑢
/
𝑚
s=iu/m requires holomorphic control in complex 
𝑠
s, and the zero-location step is only sketched.	Restate with holomorphic hypotheses and prove existence/uniqueness of the 
𝑘
k-th zero by Rouché or the implicit function theorem.
M2	§9.1	MEDIUM	The Beraha-Kahane-Weiss discussion is incomplete: it omits the coefficient-vanishing alternative for a uniquely dominant eigenvalue.	State the theorem correctly and then rule out amplitude zeros on the generic set using formula (56) and Theorem 3.1.
M3	§1.1 and §10	MEDIUM	The manuscript does not clearly separate classical ingredients from the actual family-specific contribution. The novelty claims are therefore overstated.	Rewrite the literature-positioning paragraph so that the standard tools and the genuinely new calculations are distinguished explicitly.
M4	Abstract, §1, §5, §6, §10	MEDIUM	The physical language is stronger than the mathematical evidence, because no microscopic model is given. Terms such as “vacuum boundary” and “edge law” overreach.	Either derive a model, or rewrite in purely spectral language using (r(y)=\max_j
M5	Abstract, §1.2(5), §8, Fig. 1 caption	MEDIUM	The paper repeatedly says “double zero at 
𝑦
=
−
1
y=−1” as if the multiplicity were exactly 
2
2. Proposition 8.1 proves only 
(
𝑦
+
1
)
2
∣
𝑍
𝑚
(
𝑦
)
(y+1)
2
∣Z
m
	​

(y), and 
𝑍
3
(
𝑦
)
=
(
𝑦
+
1
)
3
Z
3
	​

(y)=(y+1)
3
.	Replace “double zero” by “zero of multiplicity at least two”, or analyze the exact multiplicity separately.
L1	§3.1	LOW	The Hankel-rank assertion is standard but uncited and not proved.	Cite a standard source, or add a short proof.
L2	§6.2 and §6.4	LOW	Notation is reused in a confusing way, for example 
𝑌
Y as both Weierstrass coordinate and 
𝑦
1
/
4
y
1/4
, and 
𝜌
ρ for two different logarithmic-slope functions.	Use distinct symbols.
L3	§9.2 and Appendix C	LOW	Reproducibility is asserted, but the script is not supplied with the submission.	Include the script as supplementary material, or record the numerical protocol in the paper itself.
4. Missing references

At minimum, the manuscript should cite the following.

C. N. Yang and T. D. Lee (1952), both Phys. Rev. papers, for the Lee-Yang framework invoked in §1.1 and Remark 5.4.

M. E. Fisher on the Yang-Lee edge singularity, since the paper explicitly distinguishes its 
𝑦
=
0
y=0 phenomenon from the classical edge.

S. Beraha, J. Kahane, N. J. Weiss, Limits of zeroes of recursively defined families of polynomials, for §1.1 and §9.1.

A modern BKW reference, for example work of A. D. Sokal, if the paper wants a contemporary source.

T. Kato, Perturbation Theory for Linear Operators, and preferably a modern exceptional-point reference such as W. D. Heiss, for the EP terminology.

R. A. Horn and C. R. Johnson or F. R. Gantmacher, for companion matrices and cyclicity in Lemma 2.1.

P. Flajolet and R. Sedgewick, Analytic Combinatorics, or H. Wilf, generatingfunctionology, for rational generating functions and linear recurrences.

A standard reference on finite Hankel rank / Kronecker theory, since Theorem 3.1 invokes that fact.

J. H. Silverman, The Arithmetic of Elliptic Curves, and/or R. Miranda or W. Fulton, for Weierstrass models and Riemann-Hurwitz.

A standard Newton-Puiseux reference, such as R. J. Walker, Algebraic Curves, for the local branch expansions.

R. J. Baxter, Exactly Solved Models in Statistical Mechanics, if the transfer-matrix/statistical-mechanics language is to be retained.

5. Specific improvements needed to reach acceptance

First, the paper needs a real bibliography and a credible literature review. In the current version, one cannot evaluate priority or even verify the standard ingredients.

Second, the dominance narrative, which is central to the paper’s abstract and title-level claims, must be repaired rigorously. Theorem 5.1(1) and Theorem 6.1 are presently underproved.

Third, Theorem 6.3 should be formalized as a genuine theorem rather than an asymptotic sketch. The present proof is not adequate for a highlighted general result.

Fourth, the statement about 
𝑦
=
−
1
y=−1 must be corrected everywhere. The current phrasing is mathematically wrong as written.

Fifth, the scope needs tightening. Either the authors add a genuine microscopic model, or they should present the work as a purely algebraic and spectral analysis of a specific quartic recurrence family.

6. Concrete fixes
B1. Missing bibliography and unresolved citations

This is a publication-level blocker. The paper cannot be refereed properly with [?] placeholders.

A workable repair is:

Add a full References section.

Replace every placeholder in §1.1, §2.3, §3.1, §4, §5, and §9 with a specific source.

Narrow the novelty claim. A suitable rewrite of the last paragraph of §1.1 would be:

“The algebraic tools used here are classical: companion matrices, reduced rational generating functions, Weierstrass normalization of quartic curves, Riemann-Hurwitz, Newton-Puiseux expansions, and Beraha-Kahane-Weiss theory. The contribution of this paper is the explicit closed-form analysis of the specific quartic 
Π
(
𝜆
,
𝑦
)
Π(λ,y), including the exact real branch classification, the dominant-versus-subdominant distinction among real branch values, the edge-zero asymptotics, and the degree formulas.”

That single edit would make the novelty claim much more defensible.

B2. Theorem 5.1(1) does not prove local dominance at 
𝑦
=
0
y=0

The current proof says that parts (1) and (2) “follow from direct factorization.” That is false for part (1). Factorization at 
𝑦
=
0
y=0 only gives

Π
(
𝜆
,
0
)
=
𝜆
(
𝜆
+
1
)
(
𝜆
−
1
)
2
,
Π(λ,0)=λ(λ+1)(λ−1)
2
,

and at 
𝑦
=
0
y=0 the simple root 
𝜆
=
−
1
λ=−1 has the same modulus as the colliding double root 
𝜆
=
1
λ=1. So dominance is not a pointwise statement at 
𝑦
=
0
y=0; it is a local statement for 
𝑦
>
0
y>0 small.

A correct fix is to insert the following argument.

Let 
𝑦
=
𝑠
2
y=s
2
 with 
𝑠
>
0
s>0 small. From Appendix D and Proposition 6.2,

𝜆
±
(
𝑠
)
=
1
±
𝑠
2
+
5
8
𝑠
2
+
𝑂
(
𝑠
3
)
.
λ
±
	​

(s)=1±
2
	​

s
	​

+
8
5
	​

s
2
+O(s
3
).

For the remaining two branches, Appendix D gives

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
=
−
1
−
𝑠
2
4
+
𝑂
(
𝑠
4
)
,
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
=
−
𝑠
2
+
𝑂
(
𝑠
4
)
.
λ
−1
	​

(y)=−1−
4
y
	​

+O(y
2
)=−1−
4
s
2
	​

+O(s
4
),λ
0
	​

(y)=−y+O(y
2
)=−s
2
+O(s
4
).

Therefore

∣
𝜆
+
(
𝑠
)
∣
=
1
+
𝑠
2
+
𝑂
(
𝑠
2
)
,
∣λ
+
	​

(s)∣=1+
2
	​

s
	​

+O(s
2
),
∣
𝜆
−
1
(
𝑠
)
∣
=
1
+
𝑠
2
4
+
𝑂
(
𝑠
4
)
,
∣λ
−1
	​

(s)∣=1+
4
s
2
	​

+O(s
4
),
∣
𝜆
−
(
𝑠
)
∣
=
1
−
𝑠
2
+
𝑂
(
𝑠
2
)
,
∣λ
−
	​

(s)∣=1−
2
	​

s
	​

+O(s
2
),
∣
𝜆
0
(
𝑠
)
∣
=
𝑂
(
𝑠
2
)
.
∣λ
0
	​

(s)∣=O(s
2
).

Hence, for all sufficiently small 
𝑠
>
0
s>0,

∣
𝜆
+
(
𝑠
)
∣
>
max
⁡
{
∣
𝜆
−
(
𝑠
)
∣
,
 
∣
𝜆
−
1
(
𝑠
)
∣
,
 
∣
𝜆
0
(
𝑠
)
∣
}
.
∣λ
+
	​

(s)∣>max{∣λ
−
	​

(s)∣, ∣λ
−1
	​

(s)∣, ∣λ
0
	​

(s)∣}.

This proves that the branch issuing from the double root at 
𝜆
=
1
λ=1 contains the unique dominant eigenvalue for 
𝑦
>
0
y>0 small.

The theorem statement should also be corrected. It should not say that 
𝜆
=
1
λ=1 is “the dominant eigenvalue at 
𝑦
=
0
y=0”, because at 
𝑦
=
0
y=0 there is a modulus tie with 
𝜆
=
−
1
λ=−1. A mathematically correct statement is:

“At 
𝑦
=
0
y=0, 
Π
(
𝜆
,
0
)
=
𝜆
(
𝜆
+
1
)
(
𝜆
−
1
)
2
Π(λ,0)=λ(λ+1)(λ−1)
2
. For 
𝑦
>
0
y>0 sufficiently small, the branch issuing from the double root 
𝜆
=
1
λ=1 is uniquely dominant. Thus 
𝑦
=
0
y=0 is the boundary branch point of the dominant spectral branch.”

B3. Theorem 6.1 does not prove global dominance on 
𝑦
>
0
y>0

The proof of Theorem 6.1 establishes only that the branch

𝑦
p
h
y
s
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
𝜆
≥
1
,
y
phys
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

,λ≥1,

is strictly increasing and bijects 
(
1
,
∞
)
(1,∞) onto 
(
0
,
∞
)
(0,∞). That does not prove that this branch is dominant.

A correct repair is to insert a separate proposition:

Proposition. Let 
𝑟
(
𝑦
)
r(y) denote the root corresponding to Theorem 6.1. Then

𝑟
(
𝑦
)
=
max
⁡
𝑗
∣
𝜆
𝑗
(
𝑦
)
∣
(
𝑦
>
0
)
.
r(y)=
j
max
	​

∣λ
j
	​

(y)∣(y>0).

The proof should be split into two regimes.

Case 1: 
0
<
𝑦
<
1
0<y<1

By Theorem 5.5, the four roots are real, and one has

𝑟
1
<
−
1
<
𝑟
2
<
0
<
𝑟
3
<
1
<
𝑟
4
.
r
1
	​

<−1<r
2
	​

<0<r
3
	​

<1<r
4
	​

.

It remains to show 
∣
𝑟
1
∣
<
𝑟
4
∣r
1
	​

∣<r
4
	​

.

For 
𝑥
≥
1
x≥1,

Π
′
(
−
𝑥
,
𝑦
)
=
−
4
𝑥
3
−
3
𝑥
2
+
2
(
2
𝑦
+
1
)
𝑥
+
1
≤
−
4
𝑥
3
−
3
𝑥
2
+
6
𝑥
+
1
=
−
(
𝑥
−
1
)
(
4
𝑥
2
+
7
𝑥
+
1
)
<
0
Π
′
(−x,y)=−4x
3
−3x
2
+2(2y+1)x+1≤−4x
3
−3x
2
+6x+1=−(x−1)(4x
2
+7x+1)<0

for 
𝑥
>
1
x>1. So 
Π
(
𝜆
,
𝑦
)
Π(λ,y) is strictly decreasing on 
(
−
∞
,
−
1
]
(−∞,−1].

Now 
𝑟
4
>
1
r
4
	​

>1 is a root, so

Π
(
−
𝑟
4
,
𝑦
)
−
Π
(
𝑟
4
,
𝑦
)
=
2
𝑟
4
(
𝑟
4
2
−
1
)
>
0.
Π(−r
4
	​

,y)−Π(r
4
	​

,y)=2r
4
	​

(r
4
2
	​

−1)>0.

Since 
Π
(
𝑟
4
,
𝑦
)
=
0
Π(r
4
	​

,y)=0, this gives 
Π
(
−
𝑟
4
,
𝑦
)
>
0
Π(−r
4
	​

,y)>0. Because 
Π
Π is strictly decreasing on 
(
−
∞
,
−
1
]
(−∞,−1] and vanishes at 
𝑟
1
r
1
	​

, it follows that

𝑟
1
>
−
𝑟
4
.
r
1
	​

>−r
4
	​

.

Hence 
∣
𝑟
1
∣
<
𝑟
4
∣r
1
	​

∣<r
4
	​

. Since also 
∣
𝑟
2
∣
<
1
<
𝑟
4
∣r
2
	​

∣<1<r
4
	​

 and 
0
<
𝑟
3
<
𝑟
4
0<r
3
	​

<r
4
	​

, the root 
𝑟
4
r
4
	​

 is dominant.

Case 2: 
𝑦
>
1
y>1

By Theorem 5.5, there are exactly two real roots, both positive, say 
0
<
𝑝
<
𝑟
0<p<r, and the other two roots form a nonreal conjugate pair. Factor

Π
(
𝜆
,
𝑦
)
=
(
𝜆
−
𝑝
)
(
𝜆
−
𝑟
)
(
𝜆
2
+
𝑎
𝜆
+
𝑏
)
.
Π(λ,y)=(λ−p)(λ−r)(λ
2
+aλ+b).

The conjugate pair has modulus 
𝑏
b
	​

, because 
𝑏
=
∣
𝑧
∣
2
b=∣z∣
2
 for roots 
𝑧
,
𝑧
ˉ
z,
z
ˉ
.

Comparing coefficients gives

𝑎
−
(
𝑝
+
𝑟
)
=
−
1
,
so
𝑎
=
𝑝
+
𝑟
−
1.
a−(p+r)=−1,soa=p+r−1.

Comparing the coefficient of 
𝜆
λ,

𝑎
𝑝
𝑟
−
𝑏
(
𝑝
+
𝑟
)
=
1
,
apr−b(p+r)=1,

hence

𝑏
=
(
𝑝
+
𝑟
−
1
)
𝑝
𝑟
−
1
𝑝
+
𝑟
=
𝑝
𝑟
−
𝑝
𝑟
+
1
𝑝
+
𝑟
.
b=
p+r
(p+r−1)pr−1
	​

=pr−
p+r
pr+1
	​

.

Therefore

𝑏
<
𝑝
𝑟
<
𝑟
2
,
b<pr<r
2
,

because 
0
<
𝑝
<
𝑟
0<p<r. So the complex pair has modulus

𝑏
<
𝑟
.
b
	​

<r.

Thus the larger positive root 
𝑟
r is dominant for all 
𝑦
>
1
y>1.

This closes the central gap in the paper’s “dominant sheet” analysis.

M1. Theorem 6.3 needs precise analytic hypotheses and a rigorous zero-counting argument

The theorem as written substitutes 
𝑠
=
𝑖
𝑢
/
𝑚
s=iu/m, but it only states real asymptotic expansions in 
𝑠
s. This is not enough. The theorem should require that 
𝜆
±
(
𝑠
)
λ
±
	​

(s) and 
𝐶
±
(
𝑠
)
C
±
	​

(s) are holomorphic in a complex neighborhood of 
𝑠
=
0
s=0, with expansions valid for complex 
𝑠
s.

A rigorous replacement is:

Assume 
𝜆
±
λ
±
	​

 and 
𝐶
±
C
±
	​

 are holomorphic for 
∣
𝑠
∣
<
𝑠
0
∣s∣<s
0
	​

, with

𝜆
±
(
𝑠
)
=
𝜆
𝑐
exp
⁡
(
±
𝑎
𝑠
+
𝑏
𝑠
2
+
𝑂
(
𝑠
3
)
)
,
𝐶
±
(
𝑠
)
=
𝐶
0
∓
𝑐
𝑠
+
𝑂
(
𝑠
2
)
,
λ
±
	​

(s)=λ
c
	​

exp(±as+bs
2
+O(s
3
)),C
±
	​

(s)=C
0
	​

∓cs+O(s
2
),

uniformly for complex 
𝑠
s near 
0
0, and assume

sup
⁡
𝑢
∈
𝑈
∣
𝑅
𝑚
 ⁣
(
𝑦
𝑐
−
𝑢
2
𝑚
2
)
∣
≤
𝑀
𝑈
𝜆
𝑐
𝑚
𝑚
−
2
u∈U
sup
	​

	​

R
m
	​

(y
c
	​

−
m
2
u
2
	​

)
	​

≤M
U
	​

λ
c
m
	​

m
−2

for every compact 
𝑈
⊂
[
0
,
∞
)
U⊂[0,∞).

Then define

𝐹
𝑚
(
𝑢
)
:
=
𝑒
𝑏
𝑢
2
/
𝑚
2
𝐶
0
𝜆
𝑐
𝑚
𝑍
𝑚
 ⁣
(
𝑦
𝑐
−
𝑢
2
𝑚
2
)
.
F
m
	​

(u):=
2C
0
	​

λ
c
m
	​

e
bu
2
/m
	​

Z
m
	​

(y
c
	​

−
m
2
u
2
	​

).

The correct uniform asymptotic is

𝐹
𝑚
(
𝑢
)
=
cos
⁡
 ⁣
(
𝑎
𝑢
−
𝑐
𝐶
0
𝑢
𝑚
)
+
𝑂
𝑈
(
𝑚
−
2
)
.
F
m
	​

(u)=cos(au−
C
0
	​

c
	​

m
u
	​

)+O
U
	​

(m
−2
).

For the 
𝑘
k-th zero, let

𝑞
𝑘
=
(
2
𝑘
−
1
)
𝜋
2
,
𝑢
𝑘
(
0
)
=
𝑞
𝑘
𝑎
.
q
k
	​

=
2
(2k−1)π
	​

,u
k
(0)
	​

=
a
q
k
	​

	​

.

Choose 
𝜂
>
0
η>0 so small that on the circle 
∣
𝑢
−
𝑢
𝑘
(
0
)
∣
=
𝜂
∣u−u
k
(0)
	​

∣=η,

∣
cos
⁡
 ⁣
(
𝑎
𝑢
−
𝑐
𝐶
0
𝑢
𝑚
)
∣
≥
𝑐
𝑘
,
𝜂
>
0
	​

cos(au−
C
0
	​

c
	​

m
u
	​

)
	​

≥c
k,η
	​

>0

for all large 
𝑚
m. If the 
𝑂
𝑈
(
𝑚
−
2
)
O
U
	​

(m
−2
) term is smaller than 
𝑐
𝑘
,
𝜂
c
k,η
	​

, Rouché’s theorem yields exactly one zero in that disk. Expanding the phase gives

𝑢
𝑚
,
𝑘
=
𝑞
𝑘
𝑎
−
𝑐
𝐶
0
𝑚
+
𝑂
(
𝑚
−
2
)
=
𝑞
𝑘
𝑎
(
1
+
𝑐
𝑎
𝐶
0
𝑚
)
+
𝑂
(
𝑚
−
2
)
,
u
m,k
	​

=
a−
C
0
	​

m
c
	​

q
k
	​

	​

+O(m
−2
)=
a
q
k
	​

	​

(1+
aC
0
	​

m
c
	​

)+O(m
−2
),

and hence

𝑦
𝑚
,
𝑘
=
𝑦
𝑐
−
𝑞
𝑘
2
𝑎
2
𝑚
2
−
2
𝑐
𝑞
𝑘
2
𝑎
3
𝐶
0
𝑚
3
+
𝑂
(
𝑚
−
4
)
.
y
m,k
	​

=y
c
	​

−
a
2
m
2
q
k
2
	​

	​

−
a
3
C
0
	​

m
3
2cq
k
2
	​

	​

+O(m
−4
).

That is the level of rigor required for a theorem of this prominence.

M2. Section 9.1 misstates Beraha-Kahane-Weiss

The paper currently says that zero accumulation is governed by equimodularity of dominant eigenvalues. That is only one half of the theorem.

The correct BKW alternative is:

A limit point of zeros may arise either because two or more eigenvalues of maximal modulus tie, or because a unique dominant eigenvalue exists but its amplitude vanishes.

In the present paper, the second alternative can be ruled out on the generic set. The authors should insert this argument explicitly.

Away from the branch locus and away from 
𝑦
∈
{
−
1
,
0
,
1
}
y∈{−1,0,1}, formula (56) gives

𝐶
𝑗
(
𝑦
)
=
𝜆
𝑗
(
𝑦
)
3
 
𝑁
(
1
/
𝜆
𝑗
(
𝑦
)
,
𝑦
)
∂
𝜆
Π
(
𝜆
𝑗
(
𝑦
)
,
𝑦
)
.
C
j
	​

(y)=
∂
λ
	​

Π(λ
j
	​

(y),y)
λ
j
	​

(y)
3
N(1/λ
j
	​

(y),y)
	​

.

For a simple root, 
∂
𝜆
Π
(
𝜆
𝑗
(
𝑦
)
,
𝑦
)
≠
0
∂
λ
	​

Π(λ
j
	​

(y),y)

=0. If 
𝐶
𝑗
(
𝑦
)
=
0
C
j
	​

(y)=0, then

𝑁
(
1
/
𝜆
𝑗
(
𝑦
)
,
𝑦
)
=
0.
N(1/λ
j
	​

(y),y)=0.

But since 
Π
(
𝜆
𝑗
(
𝑦
)
,
𝑦
)
=
0
Π(λ
j
	​

(y),y)=0, one also has

𝐷
(
1
/
𝜆
𝑗
(
𝑦
)
,
𝑦
)
=
0
,
D(1/λ
j
	​

(y),y)=0,

because 
Π
(
𝜆
,
𝑦
)
=
𝜆
4
𝐷
(
1
/
𝜆
,
𝑦
)
Π(λ,y)=λ
4
D(1/λ,y). Thus 
𝑁
(
⋅
,
𝑦
)
N(⋅,y) and 
𝐷
(
⋅
,
𝑦
)
D(⋅,y) would share a common root, contradicting Theorem 3.1 for 
𝑦
∉
{
−
1
,
0
,
1
}
y∈
/
{−1,0,1}. Therefore the amplitude-vanishing alternative does not occur on the generic set.

So the corrected sentence in §9.1 should be:

“By the Beraha-Kahane-Weiss theorem, zero accumulation may occur either at dominant equimodularity points or at isolated amplitude-vanishing points. In the present family, formula (56) and Theorem 3.1 show that the latter do not occur away from the branch locus and the exceptional parameters 
𝑦
∈
{
−
1
,
0
,
1
}
y∈{−1,0,1}.”

M3. Standard tools and genuine contributions must be separated

The current introduction blurs standard machinery and new content. That should be repaired explicitly.

A suitable rewrite is to organize §1.1 into three paragraphs:

Standard background. Companion matrices, reduced rational generating functions, Weierstrass normalization of quartics, Riemann-Hurwitz, Newton-Puiseux, and BKW theory are classical.

What is new here. For the specific quartic 
Π
(
𝜆
,
𝑦
)
Π(λ,y), the paper obtains the factorization of the ramification equation, the exact real branch-value classification, the proof that only 
𝑦
=
0
y=0 lies on the dominant real boundary, the edge-zero asymptotics (39), and the degree formulas (46)-(48).

Scope. The paper studies an induced quartic transfer family directly, without deriving it from a microscopic model.

That rewrite would make the manuscript much more honest and much easier to assess.

M4. Physical terminology should be either justified or weakened

Since the paper explicitly says that no microscopic model is derived, several physical terms should be replaced by mathematically precise ones.

Concrete replacements:

“vacuum boundary” 
→
→ “boundary branch point at 
𝑦
=
0
y=0”

“positive-real dominant sheet” 
→
→ “the spectral-radius branch over 
𝑦
>
0
y>0”

“edge law” 
→
→ “local zero asymptotics near the dominant square-root branch point”

“partition-function zeros” can be retained only if clearly introduced as terminology for the polynomial family 
𝑍
𝑚
(
𝑦
)
Z
m
	​

(y), not as derived thermodynamic observables.

A precise definition that would resolve much of the ambiguity is:

𝑟
(
𝑦
)
:
=
max
⁡
𝑗
∣
𝜆
𝑗
(
𝑦
)
∣
,
𝑓
d
o
m
(
𝑦
)
:
=
log
⁡
𝑟
(
𝑦
)
.
r(y):=
j
max
	​

∣λ
j
	​

(y)∣,f
dom
	​

(y):=logr(y).

Then state theorems directly in terms of 
𝑟
(
𝑦
)
r(y) and branches of the spectral curve. That makes the paper mathematically self-contained even without a model.

M5. The 
𝑦
=
−
1
y=−1 multiplicity claim must be corrected

Proposition 8.1 proves

(
𝑦
+
1
)
2
∣
𝑍
𝑚
(
𝑦
)
(
𝑚
≥
2
)
,
(y+1)
2
∣Z
m
	​

(y)(m≥2),

which is a zero of multiplicity at least two. It does not prove exact multiplicity 
2
2.

The manuscript’s own initial values already show the problem:

𝑍
3
(
𝑦
)
=
(
𝑦
+
1
)
3
.
Z
3
	​

(y)=(y+1)
3
.

So the phrases “double zero at 
𝑦
=
−
1
y=−1”, “uniform double zero”, and “exact double zero” are wrong as written. 

main

The repair is simple and should be made everywhere:

Abstract: replace “double zero at 
𝑦
=
−
1
y=−1” by “zero of multiplicity at least two at 
𝑦
=
−
1
y=−1”.

§1.2 item 5: replace the headline claim by

(
𝑦
+
1
)
2
∣
𝑍
𝑚
(
𝑦
)
(
𝑚
≥
2
)
.
(y+1)
2
∣Z
m
	​

(y)(m≥2).

Figure 1 caption: replace “exact double zero” by “exact pinned zero with multiplicity at least two”.

If the authors want an exact multiplicity statement, they need a separate analysis of

𝜈
𝑚
:
=
ord
⁡
𝑦
=
−
1
𝑍
𝑚
(
𝑦
)
.
ν
m
	​

:=ord
y=−1
	​

Z
m
	​

(y).

At minimum, exact multiplicity 
2
2 is equivalent to

𝑍
𝑚
(
𝑦
)
(
𝑦
+
1
)
2
∣
𝑦
=
−
1
≠
0
,
(y+1)
2
Z
m
	​

(y)
	​

	​

y=−1
	​


=0,

and that has not been established.

In summary, the paper is potentially salvageable, but only after a serious revision that repairs the dominance proofs, formalizes the edge theorem, supplies a real bibliography, and corrects the false multiplicity language.