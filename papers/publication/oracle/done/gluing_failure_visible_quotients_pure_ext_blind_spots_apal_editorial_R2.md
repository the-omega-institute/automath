<!-- oracle metadata: {"timestamp": "2026-04-05T04:44:40.757715", "model": "o3-mini-high", "response_length": 19787} -->

1. Overall assessment

Major revision.

The manuscript has a potentially publishable algebraic core, especially the balanced-family reduction and the explicit real-branch analysis. However, it is not acceptable in its present form. Two headline spectral claims are not actually proved, namely the local dominance assertion at 
𝑦
=
0
y=0 in Theorem 5.1(1) and the global dominance claim implicit in Theorem 6.1. In addition, the paper contains unresolved citation placeholders and no usable bibliography, Appendix B.3 contains an explicit mathematical error at 
𝑦
=
0
y=0, Section 9.1 states an incomplete version of the Beraha-Kahane-Weiss mechanism, and the repeated claim of a “rigid double zero” at 
𝑦
=
−
1
y=−1 is false as stated because the paper proves only 
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

(y) and already lists 
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
. 

main

2. Novelty rating for each theorem

These ratings are provisional because the manuscript has no bibliography and therefore does not document priority against the relevant literature. 

main

Theorem	Rating	One-line justification
Theorem 3.1	LOW	Coprimality via a resultant, reduced rationality, and minimal recurrence order for a rational generating function are standard.
Theorem 4.4	MEDIUM	The family-specific quartic-to-Weierstrass specialization is elegant, but the normalization itself is classical.
Theorem 5.1	HIGH	The exact dominant-versus-subdominant classification of the real branch values is the paper’s most distinctive family-specific claim.
Theorem 5.5	MEDIUM	The exact real-root phase diagram is useful and nontrivial, but it is built from standard real-elliptic-curve topology once the normalization is available.
Theorem 6.1	LOW	Once the branch formula is explicit, monotonicity is routine. The genuinely interesting part is global dominance, which is not proved.
Theorem 6.3	LOW	As written, this is essentially a standard two-branch cosine normal form, and the proof is only a sketch.
Theorem 6.4	MEDIUM	The explicit 
𝑚
−
2
m
−2
 and 
𝑚
−
3
m
−3
 coefficients in the edge-zero quantization for this specific quartic family are nontrivial and useful.
Theorem 7.1	LOW	The degree law and leading coefficients follow by straightforward induction on the recurrence.
3. Issue table

The issues below arise directly from the introduction, Theorems 5.1, 6.1, 6.3, Section 8, Section 9.1, Figure 1, and Appendix B.3. 

main

ID	Section	Severity	Description	Suggested fix
B1	§1.1 and throughout	BLOCKER	All references remain unresolved placeholders [?], and there is no bibliography. Priority, novelty, and even standard background claims are unverifiable.	Add a complete references section and replace every placeholder with a concrete citation.
B2	Theorem 5.1(1)	BLOCKER	The proof does not show that the 
𝑦
=
0
y=0 collision is locally dominant. Factorization at 
𝑦
=
0
y=0 is insufficient because 
𝜆
=
−
1
λ=−1 has the same modulus as the double root there.	Prove local dominance for 
𝑦
>
0
y>0 small by explicit branch expansions and modulus comparison.
B3	Theorem 6.1	BLOCKER	The theorem proves monotonicity of the chosen branch, but not that it is the spectral-radius branch for all 
𝑦
>
0
y>0.	Add a global modulus comparison with the other three roots, separately on 
0
<
𝑦
<
1
0<y<1 and 
𝑦
>
1
y>1.
M1	Appendix B.3	MEDIUM	The appendix states that at 
𝑦
=
0
y=0 the reduced denominator degree drops from 
4
4 to 
2
2. This is wrong. The reduced degree is 
1
1.	Replace B.3 by the exact factorization 
𝑍
(
𝑡
,
0
)
=
1
/
(
1
−
𝑡
)
Z(t,0)=1/(1−t) and update any downstream comments.
M2	§6.3 to §6.4	MEDIUM	The “universal dominant-EP2 normal form” is under-specified. The proof substitutes 
𝑠
=
𝑖
𝑢
/
𝑚
s=iu/m without stating holomorphic hypotheses in complex 
𝑠
s, and zero existence/uniqueness is only sketched.	Restate the theorem with complex-analytic or explicit real-uniform hypotheses and prove the zero asymptotics rigorously.
M3	§9.1	MEDIUM	The Beraha-Kahane-Weiss discussion omits the amplitude-vanishing alternative for a uniquely dominant eigenvalue.	State BKW correctly and then rule out amplitude zeros on the generic set using formula (56) and Theorem 3.1.
M4	Abstract, §1.2(5), §8, Fig. 1 caption	MEDIUM	The paper repeatedly says “double zero at 
𝑦
=
−
1
y=−1” as if the multiplicity were exactly 
2
2. This is false as written.	Replace by “zero of multiplicity at least two”, or analyze the exact multiplicity pattern separately.
M5	§1.1 and §10	MEDIUM	Classical tools and genuinely family-specific contributions are not cleanly separated, so the novelty claim is overstated.	Rewrite the introduction so standard machinery and new outputs are explicitly distinguished.
M6	Abstract, §1.1, §10	MEDIUM	The physical terminology is stronger than the paper justifies, because no microscopic model is derived.	Rephrase in purely spectral language, or add an actual microscopic transfer-matrix derivation.
L1	§3.1	LOW	The Hankel-rank claim is standard but uncited.	Cite a standard reference on rational generating functions and Hankel rank.
L2	§6	LOW	Notation is reused confusingly, especially 
𝑌
Y as both a Weierstrass coordinate and a large-
𝑦
y scaling variable.	Rename the large-
𝑦
y variable.
L3	§9.2 and Appendix C	LOW	Reproducibility is asserted via an external script, but no script is included with the submission.	Supply the code, or document the numerical protocol fully in the manuscript.
4. Missing references

At minimum, the paper should cite the following.

C. N. Yang and T. D. Lee, both 1952 Phys. Rev. papers, if Lee-Yang language is retained.

M. E. Fisher on the Yang-Lee edge singularity, since the manuscript explicitly contrasts its mechanism with the classical edge.

S. Beraha, J. Kahane, and N. J. Weiss on zeros of recursively defined polynomial families.

A modern BKW reference, such as A. D. Sokal, if a contemporary formulation is intended.

T. Kato, Perturbation Theory for Linear Operators, and preferably W. D. Heiss, for exceptional-point terminology.

Horn and Johnson, or Gantmacher, for companion matrices and cyclicity.

Flajolet and Sedgewick, Wilf, or Stanley, for rational generating functions and linear recurrences.

A standard source for Hankel rank and Kronecker theory.

Silverman, Miranda, Fulton, or Harris, for Weierstrass models, elliptic curves, and Riemann-Hurwitz.

A standard Newton-Puiseux reference, such as Walker or Wall.

Baxter, if the transfer-matrix/statistical-mechanics language is to be kept.

5. Specific improvements needed to reach acceptance

The paper needs five substantive changes before it can be reconsidered.

First, the dominant-sheet narrative must be repaired rigorously. The abstract and introduction overstate what has actually been proved because Theorem 5.1(1) and Theorem 6.1 are incomplete. Second, Theorem 6.3 must be upgraded from a plausible asymptotic sketch to a theorem with precise hypotheses and a genuine zero-counting argument. Third, the 
𝑦
=
−
1
y=−1 statement must be corrected everywhere so that the wording matches the proved divisibility by 
(
𝑦
+
1
)
2
(y+1)
2
. Fourth, Appendix B.3 must be corrected because it contains a concrete error. Fifth, the bibliography and novelty framing must be rebuilt so that the reader can distinguish classical input from the actual contribution of the manuscript. 

main

6. Concrete fixes
B1. Bibliography and unresolved citations

This is a publication-level blocker.

The repair is not merely cosmetic. It changes how the contribution should be framed. Add a References section and replace every placeholder in §1.1, §3.1, §4, §5, and §9. Then rewrite the final paragraph of §1.1 along the following lines:

“The tools used here are classical: companion matrices, reduced rational generating functions, quartic-to-Weierstrass normalization, Riemann-Hurwitz, Newton-Puiseux expansions, and Beraha-Kahane-Weiss theory. The contribution of the present paper is the explicit closed-form analysis of the specific quartic 
Π
(
𝜆
,
𝑦
)
Π(λ,y), including the exact real branch-value classification, the dominant-versus-subdominant distinction among real branch values, the edge-zero asymptotics, and the degree formulas.”

That wording is both accurate and defensible. 

main

B2. Theorem 5.1(1), local dominance at 
𝑦
=
0
y=0

The current proof says that parts (1) and (2) follow from direct factorization. That is not sufficient for part (1). At 
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
,
Π(λ,0)=λ(λ+1)(λ−1)
2
,

so 
𝜆
=
−
1
λ=−1 has the same modulus as the double root 
𝜆
=
1
λ=1. The theorem therefore needs a local dominance proof for 
𝑦
>
0
y>0 small, not a pointwise statement at 
𝑦
=
0
y=0.

A correct repair is:

Set 
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
s>0 small and write 
𝜆
=
1
+
𝜀
λ=1+ε. Expanding gives

Π
(
1
+
𝜀
,
𝑠
2
)
=
𝜀
4
+
3
𝜀
3
+
2
𝜀
2
−
2
𝑠
2
𝜀
2
−
4
𝑠
2
𝜀
+
𝑠
4
−
𝑠
2
.
Π(1+ε,s
2
)=ε
4
+3ε
3
+2ε
2
−2s
2
ε
2
−4s
2
ε+s
4
−s
2
.

The leading balance is 
2
𝜀
2
−
𝑠
2
=
0
2ε
2
−s
2
=0, so the two branches issuing from 
𝜆
=
1
λ=1 satisfy

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
𝑂
(
𝑠
2
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

+O(s
2
).

For the simple roots at 
(
−
1
,
0
)
(−1,0) and 
(
0
,
0
)
(0,0), use the implicit function theorem:

∂
𝜆
Π
(
−
1
,
0
)
=
−
4
,
∂
𝜆
Π
(
0
,
0
)
=
1
,
∂
λ
	​

Π(−1,0)=−4,∂
λ
	​

Π(0,0)=1,
∂
𝑦
Π
(
𝜆
,
𝑦
)
=
−
2
𝜆
2
+
2
𝑦
+
1.
∂
y
	​

Π(λ,y)=−2λ
2
+2y+1.

Hence

𝜆
−
1
′
(
0
)
=
−
∂
𝑦
Π
(
−
1
,
0
)
∂
𝜆
Π
(
−
1
,
0
)
=
−
1
4
,
𝜆
0
′
(
0
)
=
−
∂
𝑦
Π
(
0
,
0
)
∂
𝜆
Π
(
0
,
0
)
=
−
1.
λ
−1
′
	​

(0)=−
∂
λ
	​

Π(−1,0)
∂
y
	​

Π(−1,0)
	​

=−
4
1
	​

,λ
0
′
	​

(0)=−
∂
λ
	​

Π(0,0)
∂
y
	​

Π(0,0)
	​

=−1.

Therefore

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
),λ
0
	​

(y)=−y+O(y
2
).

Substitute 
𝑦
=
𝑠
2
y=s
2
:

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

Thus, for all sufficiently small 
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
λ=1 is uniquely dominant for 
𝑦
>
0
y>0 small. The theorem statement should therefore be changed to:

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
λ=1 is uniquely dominant.”

That is the mathematically correct claim. 

main

B3. Theorem 6.1, global dominance on 
𝑦
>
0
y>0

The present proof shows that

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


is strictly increasing on 
(
1
,
∞
)
(1,∞). It does not prove that this branch is the spectral-radius branch. That missing step is central.

A clean fix is to add the following proposition immediately after Theorem 6.1.

Proposition. Let 
𝑟
(
𝑦
)
r(y) denote the real branch of Theorem 6.1. Then

𝑟
(
𝑦
)
=
max
⁡
1
≤
𝑗
≤
4
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
1≤j≤4
max
	​

∣λ
j
	​

(y)∣(y>0).

Proof on 
0
<
𝑦
<
1
0<y<1. By Theorem 5.5, the four roots are real and ordered

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

It remains only to compare 
∣
𝑟
1
∣
∣r
1
	​

∣ and 
𝑟
4
r
4
	​

. For 
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
x>1. Hence 
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

Since 
𝑟
4
>
1
r
4
	​

>1 is a root,

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

Thus 
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
Π decreases on 
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

, one gets

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

. The other two roots satisfy 
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

, so 
𝑟
4
r
4
	​

 is dominant.

Proof on 
𝑦
>
1
y>1. By Theorem 5.5, there are exactly two real roots, both positive, say 
0
<
𝑝
<
𝑟
0<p<r, and the remaining two roots form a nonreal conjugate pair. Factor

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

If the conjugate pair is 
𝑧
,
𝑧
ˉ
z,
z
ˉ
, then 
𝑏
=
∣
𝑧
∣
2
b=∣z∣
2
. Coefficient comparison gives

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
𝑎
=
𝑝
+
𝑟
−
1
,
a−(p+r)=−1,a=p+r−1,

and from the coefficient of 
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
1.
apr−b(p+r)=1.

Therefore

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

Hence

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

so 
∣
𝑧
∣
=
𝑏
<
𝑟
∣z∣=
b
	​

<r. Thus the larger positive real root 
𝑟
r is dominant for every 
𝑦
>
1
y>1.

With this proposition added, the title “Dominant sheet on 
𝑦
>
0
y>0” becomes justified. 

main

M1. Appendix B.3, the 
𝑦
=
0
y=0 degeneracy

Appendix B.3 currently says that the reduced denominator degree at 
𝑦
=
0
y=0 drops from 
4
4 to 
2
2. That is wrong.

The correct computation is

𝑁
(
𝑡
,
0
)
=
1
−
𝑡
2
=
(
1
−
𝑡
)
(
1
+
𝑡
)
,
N(t,0)=1−t
2
=(1−t)(1+t),
𝐷
(
𝑡
,
0
)
=
1
−
𝑡
−
𝑡
2
+
𝑡
3
=
(
1
−
𝑡
)
2
(
1
+
𝑡
)
.
D(t,0)=1−t−t
2
+t
3
=(1−t)
2
(1+t).

Hence

𝑍
(
𝑡
,
0
)
=
𝑁
(
𝑡
,
0
)
𝐷
(
𝑡
,
0
)
=
1
1
−
𝑡
.
Z(t,0)=
D(t,0)
N(t,0)
	​

=
1−t
1
	​

.

So the reduced denominator degree is 1, not 2, and

𝑍
𝑚
(
0
)
=
1
(
𝑚
≥
0
)
.
Z
m
	​

(0)=1(m≥0).

Appendix B.3 should be replaced by exactly this factorization. Any statement describing the 
𝑦
=
0
y=0 specialization as an order-2 degeneracy should be deleted. 

main

M2. Theorem 6.3 needs a rigorous statement

The theorem currently substitutes 
𝑠
=
𝑖
𝑢
/
𝑚
s=iu/m into a Puiseux expansion stated only for real 
𝑠
s. It also does not prove uniqueness of the 
𝑘
k-th zero.

A rigorous repair is to restate the theorem with holomorphic hypotheses.

Assume that 
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

(s) are holomorphic for 
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
0, and that for every compact 
𝑈
⊂
[
0
,
∞
)
U⊂[0,∞),

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
.
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
.

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

Choose a small disk around 
𝑢
𝑘
(
0
)
u
k
(0)
	​

. On its boundary, the cosine term is bounded below away from 
0
0, while the error is 
𝑂
(
𝑚
−
2
)
O(m
−2
). Rouché’s theorem yields exactly one zero inside that disk. Expanding the phase gives

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

and therefore

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

main

M3. Section 9.1 should state Beraha-Kahane-Weiss correctly

The present text says that zero accumulation is governed by dominant equimodularity. That is only one half of BKW.

The correct statement is:

Limit points of zeros may arise either because two or more dominant eigenvalues tie in modulus, or because a uniquely dominant eigenvalue has vanishing amplitude.

In the present paper, the second alternative can be excluded on the generic set. Using formula (56),

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

Away from the branch locus, 
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

(y),y)=0 and 
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
D(1/λ,y), one also has

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
0.
D(1/λ
j
	​

(y),y)=0.

Thus 
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
{−1,0,1}.

So §9.1 should say that, after excluding amplitude zeros by this argument, the generic zero-accumulation set is controlled by dominant equimodularity. 

main

M4. The 
𝑦
=
−
1
y=−1 multiplicity claim must be corrected

The paper proves only

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
2, and exact multiplicity 
2
2 is already contradicted by the paper’s own initial values:

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

The fix should be made everywhere:

Abstract: replace “rigid double zero at 
𝑦
=
−
1
y=−1” by “uniform zero of multiplicity at least two at 
𝑦
=
−
1
y=−1”.

§1.2(5): state only 
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

(y).

§8 and Figure 1 caption: replace “double zero” by “pinned zero of multiplicity at least two”.

If the authors want an exact multiplicity theorem, they need a separate analysis of

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

At present, the manuscript does not provide that analysis and therefore should not claim it. 

main

M5. Standard tools and actual contribution must be separated

The introduction currently blurs classical machinery and new content. The fix is editorial but precise.

Rewrite §1.1 in three layers.

Classical inputs: companion matrices, reduced rational generating functions, quartic-to-Weierstrass reduction, Riemann-Hurwitz, Newton-Puiseux, and BKW theory.

Family-specific outputs: the balanced-family reduction for this 
Π
Π, the exact real branch-value classification, the proof that only 
𝑦
=
0
y=0 lies on the dominant real boundary, the explicit 
𝑚
−
2
m
−2
 and 
𝑚
−
3
m
−3
 coefficients in the edge law, and the degree formulas.

Scope: the paper analyzes a fixed quartic recurrence family, not a derived microscopic model.

Without that separation, the novelty claim is not credible.

M6. Tone down or justify the physical language

Because no microscopic model is derived, the safest repair is to define

𝑟
(
𝑦
)
:
=
max
⁡
1
≤
𝑗
≤
4
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
,
r(y):=
1≤j≤4
max
	​

∣λ
j
	​

(y)∣,f
dom
	​

(y):=logr(y),

and then rewrite the paper in purely spectral language:

“dominant sheet” = the connected component on which 
∣
𝜆
∣
=
𝑟
(
𝑦
)
∣λ∣=r(y),

“vacuum boundary” = the square-root boundary branch point at 
𝑦
=
0
y=0,

“edge zeros” = zeros governed by that dominant square-root branch point.

If the authors want to retain stronger Lee-Yang or thermodynamic language, they need to add a genuine microscopic transfer-matrix derivation and explain what physical fugacity 
𝑦
y represents. 

main

In its current form, the manuscript is promising but not yet publishable. The algebraic heart is worth preserving, but the dominance proofs, the 
𝑦
=
−
1
y=−1 claim, the 
𝑦
=
0
y=0 appendix, and the bibliography all need substantial revision before the paper can be fairly reassessed.