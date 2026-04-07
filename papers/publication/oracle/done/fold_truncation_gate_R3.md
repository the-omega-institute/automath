<!-- oracle metadata: {"timestamp": "2026-04-07T07:20:41.691129", "model": "o3-mini-high", "response_length": 16087} -->

Referee report on the attached manuscript. 

main

1. Overall assessment

Decision: Reject

The deterministic core is mostly correct, but it is too slight for a journal article in its present form. The central result, Theorem 4.1, is essentially a formal telescoping identity once the local and global defects have been defined, and Sections 4 to 6 derive only immediate consequences of that identity. The manuscript itself also states that Section 7 is only a conditional criterion and is not verified for the Fold tower, while the introduction and related-work discussion still contain unresolved placeholder citations. In current form, the paper does not meet the standards of novelty, completeness, or scholarly readiness required for publication. 

main

I did not find a major gap in Proposition 2.1 or in the proof of Theorem 4.1. The main problems are different: the core contribution is near-definitional, the literature positioning is not yet credible, and the probabilistic section is neither instantiated for the actual model nor fully cleanly stated.

2. Novelty rating by result
Result	Novelty	One-line justification
Proposition 2.1	MEDIUM	This is the one genuinely Fold-specific lemma, isolating dependence on the residue mod 
𝐹
𝑚
+
2
F
m+2
	​

.
Lemma 2.2	LOW	Pure functoriality of prefix maps and xor-homomorphism.
Theorem 4.1	LOW	A formal coboundary/telescoping identity once 
𝐷
𝑛
→
𝑚
D
n→m
	​

 and 
𝜅
𝑚
+
1
→
𝑚
κ
m+1→m
	​

 are defined.
Corollary 4.4	LOW	Standard coupling plus union bound.
Corollary 5.1	LOW	Standard Lipschitz/Hamming estimate from the same coupling.
Proposition 5.2	LOW	Immediate decomposition of the telescoping sum at an intermediate scale.
Proposition 6.1	LOW	Finite sum of nonnegative integers implies eventual vanishing, then inverse-limit compatibility is routine.
Theorem 7.1	LOW	Standard Fourier/twisted-matrix criterion for finite-state additive Markov models, and not proved for Fold here.
Corollary 7.4	LOW	Immediate character-theoretic corollary of Theorem 7.1.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	1, 1.1, 4.2, 7	BLOCKER	Bibliography is unresolved. Placeholder citations appear throughout, so novelty claims and background assertions are unverifiable.	Replace every placeholder with complete references and moderate unsupported claims of novelty.
B2	4 to 6	BLOCKER	The main deterministic contribution is formal. The paper lacks a nontrivial Fold-specific theorem or quantitative estimate.	Add a genuinely arithmetic theorem about the Fold defects, not just a telescoping identity.
B3	7	BLOCKER	Section 7 is generic and explicitly not established for the Fold tower. As written, it does not deliver a new theorem about the actual process studied in the paper.	Either instantiate the finite-state additive model for Fold and verify the spectral condition, or move Section 7 to an appendix / separate note.
M1	7.1	MEDIUM	Theorem 7.1 should explicitly restrict to 
𝜈
𝑚
ν
m
	​

-reachable states, or redefine 
𝐻
𝑚
H
m
	​

, so that 
𝑃
𝑚
,
𝜒
(
𝑎
,
𝑏
)
=
𝑝
𝑎
𝑏
𝜒
(
Γ
𝑚
(
𝑎
,
𝑏
)
)
P
m,χ
	​

(a,b)=p
ab
	​

χ(Γ
m
	​

(a,b)) is well-defined on the relevant state space.	Replace 
𝑆
𝑚
S
m
	​

 by its reachable subset and define 
𝐻
𝑚
H
m
	​

 from reachable-edge increments.
M2	2.1	MEDIUM	
𝑍
(
𝑁
)
Z(N) and the index convention are not defined precisely enough. The paper relies on position 
𝑘
k corresponding to 
𝐹
𝑘
+
1
F
k+1
	​

, but this is implicit.	Give an explicit formal definition of 
𝑍
(
𝑁
)
Z(N) as an infinite legal sequence.
M3	4.2	MEDIUM	Corollary 4.4 is stated in a weaker, nonstandard form. The natural statement is a total-variation coupling bound.	State 
𝑑
T
V
≤
𝑃
[
𝐷
𝑛
→
𝑚
≠
0
]
d
TV
	​

≤P[D
n→m
	​


=0] first, then derive the test-function inequality by duality.
M4	6.1	MEDIUM	Proposition 6.1 is tautological as stated, because (\sum_m	\delta_m
L1	1, 4.1, 8	LOW	Informal language, “auditable”, “Stokes”, “larger manuscript”, “gauge-anomaly”, is not matched by corresponding mathematical content.	Replace with standard terminology and remove project-internal language.
L2	1.1	LOW	The claim that the observable “appears absent from the literature” is unsupported.	Either justify this through a real literature review or soften the claim.
4. Missing references

At minimum, the manuscript needs the foundational Fibonacci and Zeckendorf references: Lekkerkerker, Representation of natural numbers as a sum of Fibonacci numbers, Simon Stevin 29 (1952), 190-195; Zeckendorf, Représentation des nombres naturels par une somme de nombres de Fibonacci ou de nombres de Lucas, Bull. Soc. Roy. Sci. Liège 41 (1972), 179-182. 
cambridge.org
+1

For numeration systems and automata, the omissions are serious: Carlitz, Fibonacci representations, Fibonacci Quarterly 6 (1968), 193-220; Carlitz, Scoville, and Hoggatt, Fibonacci representations, Fibonacci Quarterly 10 (1972), 1-28; Frougny, Fibonacci representations and finite automata, IEEE Trans. Inform. Theory 37 (1991), 393-399; Frougny, Representations of numbers and finite automata, Math. Systems Theory 25 (1992), 37-60; and Frougny-Sakarovitch, Number representation and finite automata (2010 book chapter). 
cambridge.org
+4
Springer Link
+4
cambridge.org
+4

For symbolic dynamics and factor-code background, standard references such as Lind and Marcus, An Introduction to Symbolic Dynamics and Coding, and Kitchens, Symbolic Dynamics, should be cited. 
cambridge.org
+2
Cambridge Assets
+2

For Section 7, the standard harmonic-analysis background should be cited directly, at least Diaconis, Group Representations in Probability and Statistics, and Levin, Peres, and Wilmer, Markov Chains and Mixing Times. 
Project Euclid
+2
AMS Bookstore
+2

If the author wants to claim current awareness of Fibonacci transducer work, recent papers such as Labbé and Lepšová (2023) and Marques and Trojovský (2025) should also be acknowledged. 
Rairo Ita
+1

5. Specific improvements needed to reach acceptance

First, the paper needs a complete bibliography and a defensible literature-positioning section.

Second, the paper needs at least one substantive Fold-specific theorem beyond the formal telescoping identity. Proposition 2.1 points in the right direction. The paper should build on that arithmetic content.

Third, Section 7 must either be made concrete for the actual Fold tower, or removed from the main text. A conditional theorem that is not instantiated for the object of study does not materially strengthen the manuscript.

Fourth, the presentation should be rebalanced. Theorem 4.1 should be stated honestly as a general telescoping lemma or coboundary identity, while the real effort should go into analyzing the arithmetic structure of the adjacent defects.

6. Concrete fixes
B1. Replace the placeholder bibliography and repair the literature claims

This is not a cosmetic change. The introduction currently makes claims about background, contribution, and absence from the literature without a usable bibliography. The fix is to insert actual references at the precise places where the manuscript now has placeholders, and to cite any “core folding paper” or “larger manuscript” explicitly if those documents are public. If they are not public, those phrases should be removed. The minimum bibliography is the set listed above. 
AMS Bookstore
+7
cambridge.org
+7
cambridge.org
+7

A suitable rewrite of the end of Section 1.1 would be along the lines:

“The telescoping identity of Section 4 is formal once the defects are defined. The Fold-specific arithmetic input enters through Proposition 2.1 and the adjacent-defect analysis of Section 3. To the best of my knowledge, I am not aware of a prior paper isolating exactly this xor-valued defect observable.”

That wording is much safer than the current broad novelty claim.

B2. Add a genuinely Fold-specific theorem

The paper urgently needs an arithmetic result about the actual defect process. The following proposition is a natural and provable upgrade, using the manuscript’s own Proposition 2.1. 

main

Proposed Proposition. Let 
𝜂
=
𝛼
𝑏
∈
Ω
𝑚
+
1
η=αb∈Ω
m+1
	​

 with 
𝛼
∈
Ω
𝑚
α∈Ω
m
	​

, 
𝑏
∈
{
0
,
1
}
b∈{0,1}, and 
𝑎
:
=
𝑁
(
𝛼
)
a:=N(α). Then

𝐾
𝑚
+
1
→
𝑚
(
𝜂
)
=
𝑏
 
1
{
𝑎
≥
𝐹
𝑚
+
1
}
.
K
m+1→m
	​

(η)=b1
{a≥F
m+1
	​

}
	​

.

More precisely,

𝜅
𝑚
+
1
→
𝑚
(
𝛼
0
)
=
0
,
κ
m+1→m
	​

(α0)=0,

and

𝜅
𝑚
+
1
→
𝑚
(
𝛼
1
)
=
{
0
,
	
𝑎
<
𝐹
𝑚
+
1
,


𝜋
∞
→
𝑚
𝑍
(
𝑎
 
m
o
d
 
𝐹
𝑚
+
2
)
 
⊕
 
𝜋
∞
→
𝑚
𝑍
(
𝑎
−
𝐹
𝑚
+
1
)
,
	
𝑎
≥
𝐹
𝑚
+
1
.
κ
m+1→m
	​

(α1)=
⎩
⎨
⎧
	​

0,
π
∞→m
	​

Z(amodF
m+2
	​

) ⊕ π
∞→m
	​

Z(a−F
m+1
	​

),
	​

a<F
m+1
	​

,
a≥F
m+1
	​

.
	​


Proof sketch.
If 
𝑏
=
0
b=0, both routes use the same value 
𝑎
a, so both outputs reduce to 
𝜋
∞
→
𝑚
𝑍
(
𝑎
 
m
o
d
 
𝐹
𝑚
+
2
)
π
∞→m
	​

Z(amodF
m+2
	​

).
If 
𝑏
=
1
b=1 and 
𝑎
<
𝐹
𝑚
+
1
a<F
m+1
	​

, then 
𝑎
+
𝐹
𝑚
+
2
<
𝐹
𝑚
+
3
a+F
m+2
	​

<F
m+3
	​

, and 
𝑍
(
𝑎
+
𝐹
𝑚
+
2
)
Z(a+F
m+2
	​

) is obtained by placing a 
1
1 at position 
𝑚
+
1
m+1 on top of 
𝑍
(
𝑎
)
Z(a), so the first 
𝑚
m digits do not change.
If 
𝑏
=
1
b=1 and 
𝑎
≥
𝐹
𝑚
+
1
a≥F
m+1
	​

, then

𝑎
+
𝐹
𝑚
+
2
=
𝐹
𝑚
+
3
+
(
𝑎
−
𝐹
𝑚
+
1
)
,
0
≤
𝑎
−
𝐹
𝑚
+
1
<
𝐹
𝑚
+
2
,
a+F
m+2
	​

=F
m+3
	​

+(a−F
m+1
	​

),0≤a−F
m+1
	​

<F
m+2
	​

,

so the high-resolution route has prefix 
𝜋
∞
→
𝑚
𝑍
(
𝑎
−
𝐹
𝑚
+
1
)
π
∞→m
	​

Z(a−F
m+1
	​

), whereas the low-resolution route is 
𝜋
∞
→
𝑚
𝑍
(
𝑎
 
m
o
d
 
𝐹
𝑚
+
2
)
π
∞→m
	​

Z(amodF
m+2
	​

). These represent distinct numbers in 
[
0
,
𝐹
𝑚
+
2
)
[0,F
m+2
	​

), hence distinct words in 
𝑋
𝑚
X
m
	​

.

This proposition immediately yields the explicit global event bound

{
𝐷
𝑛
→
𝑚
≠
0
}
⊆
⋃
𝑗
=
𝑚
𝑛
−
1
{
𝜔
𝑗
+
1
=
1
,
 
𝑁
(
𝑟
𝑛
→
𝑗
𝜔
)
≥
𝐹
𝑗
+
1
}
,
{D
n→m
	​


=0}⊆
j=m
⋃
n−1
	​

{ω
j+1
	​

=1, N(r
n→j
	​

ω)≥F
j+1
	​

},

which is materially more informative than the present union bound in terms of the abstract indicators 
𝐾
𝑗
+
1
→
𝑗
K
j+1→j
	​

.

You can push this one step further under uniform input. Let

𝐴
𝑚
:
=
#
{
𝛼
∈
Ω
𝑚
:
𝑁
(
𝛼
)
<
𝐹
𝑚
+
1
}
.
A
m
	​

:=#{α∈Ω
m
	​

:N(α)<F
m+1
	​

}.

Then

𝐴
1
=
1
,
𝐴
2
=
2
,
𝐴
𝑚
=
2
𝑚
−
2
+
𝐴
𝑚
−
2
(
𝑚
≥
3
)
,
A
1
	​

=1,A
2
	​

=2,A
m
	​

=2
m−2
+A
m−2
	​

(m≥3),

because necessarily the last bit is 
0
0; if the penultimate bit is 
0
0, any first 
𝑚
−
2
m−2 bits are allowed, while if the penultimate bit is 
1
1, the first 
𝑚
−
2
m−2 bits must contribute 
<
𝐹
𝑚
−
1
<F
m−1
	​

. Solving gives

𝐴
2
𝑟
=
2
2
𝑟
+
2
3
,
𝐴
2
𝑟
+
1
=
2
2
𝑟
+
1
+
1
3
.
A
2r
	​

=
3
2
2r
+2
	​

,A
2r+1
	​

=
3
2
2r+1
+1
	​

.

Hence, for the uniform measure on 
Ω
𝑚
+
1
Ω
m+1
	​

,

𝑃
 ⁣
(
𝐾
𝑚
+
1
→
𝑚
=
1
)
=
2
𝑚
−
𝐴
𝑚
2
𝑚
+
1
=
⌊
2
𝑚
+
1
/
3
⌋
2
𝑚
+
1
.
P(K
m+1→m
	​

=1)=
2
m+1
2
m
−A
m
	​

	​

=
2
m+1
⌊2
m+1
/3⌋
	​

.

Then the global coupling bound becomes

𝑃
(
𝐷
𝑛
→
𝑚
≠
0
)
≤
∑
𝑗
=
𝑚
𝑛
−
1
⌊
2
𝑗
+
1
/
3
⌋
2
𝑗
+
1
.
P(D
n→m
	​


=0)≤
j=m
∑
n−1
	​

2
j+1
⌊2
j+1
/3⌋
	​

.

This is the type of Fold-specific quantitative theorem the current submission needs.

B3. Either instantiate Section 7 for Fold, or remove it from the main text

Right now Section 7 is a generic theorem about finite-state additive models, and the paper openly says it is not proved for Fold. That is not enough for a research article centered on Fold defects. 

main

There are only two viable fixes.

One route is deletion or demotion. Move Section 7 to an appendix titled “A general Fourier criterion for future use”, and make clear that it is external background rather than a main result of the paper.

The stronger route is to build the actual finite-state model. A plausible strategy is to use the finite-state normalization machinery available for Fibonacci numeration. For each fixed 
𝑚
m, let 
𝑄
Q be the state set of a normalization transducer, and enlarge the state to 
𝑆
𝑚
=
𝑄
×
(
𝑍
/
2
𝑍
)
𝑚
S
m
	​

=Q×(Z/2Z)
m
, where the second component stores the current 
𝑚
m-bit projected defect. Then define 
Γ
𝑚
Γ
m
	​

 as the transition increment in the defect coordinate. This would prove assumption (i) instead of postulating it. The existence of the required finite-state normalization framework is precisely why the omitted Frougny references matter here. 
Springer Link
+1

Without such a construction, Section 7 should not remain in the main line of argument.

M1. Repair Theorem 7.1 so the twisted matrices are cleanly defined

A clean corrected statement is:

𝑅
𝑚
:
=
{
𝑎
∈
𝑆
𝑚
:
 there exists a path from 
supp
⁡
𝜈
𝑚
 to 
𝑎
 with positive probability
}
.
R
m
	​

:={a∈S
m
	​

: there exists a path from suppν
m
	​

 to a with positive probability}.

Replace 
𝑆
𝑚
S
m
	​

 by 
𝑅
𝑚
R
m
	​

, and define

𝐻
𝑚
:
=
⟨
Γ
𝑚
(
𝑎
,
𝑏
)
:
𝑎
,
𝑏
∈
𝑅
𝑚
,
 
𝑝
𝑎
𝑏
>
0
⟩
≤
(
𝑍
/
2
𝑍
)
𝑚
.
H
m
	​

:=⟨Γ
m
	​

(a,b):a,b∈R
m
	​

, p
ab
	​

>0⟩≤(Z/2Z)
m
.

Then for 
𝜒
∈
𝐻
^
𝑚
χ∈
H
m
	​

,

𝑃
𝑚
,
𝜒
(
𝑎
,
𝑏
)
:
=
𝑝
𝑎
𝑏
𝜒
(
Γ
𝑚
(
𝑎
,
𝑏
)
)
,
𝑎
,
𝑏
∈
𝑅
𝑚
,
P
m,χ
	​

(a,b):=p
ab
	​

χ(Γ
m
	​

(a,b)),a,b∈R
m
	​

,

is unambiguously defined, and the proof goes through verbatim.

This is the minimal statement-level repair. It prevents irrelevant unreachable states from contaminating the theorem.

M2. Define 
𝑍
(
𝑁
)
Z(N) and the indexing convention precisely

Insert a formal definition in Section 2.1, for example:

“For 
𝑁
≥
0
N≥0, let 
𝑍
(
𝑁
)
=
(
𝑧
𝑘
)
𝑘
≥
1
∈
{
0
,
1
}
𝑁
Z(N)=(z
k
	​

)
k≥1
	​

∈{0,1}
N
 denote the unique finitely supported sequence such that

𝑁
=
∑
𝑘
≥
1
𝑧
𝑘
𝐹
𝑘
+
1
,
𝑧
𝑘
𝑧
𝑘
+
1
=
0
 for all 
𝑘
.
N=
k≥1
∑
	​

z
k
	​

F
k+1
	​

,z
k
	​

z
k+1
	​

=0 for all k.

Thus digit position 
𝑘
k corresponds to the Fibonacci weight 
𝐹
𝑘
+
1
F
k+1
	​

. For 
𝑥
∈
𝑋
𝑚
x∈X
m
	​

, we identify 
𝑥
x with 
(
𝑥
1
,
…
,
𝑥
𝑚
,
0
,
0
,
…
 
)
(x
1
	​

,…,x
m
	​

,0,0,…).”

With that definition in place, Proposition 2.1 and Example 2.3 become completely transparent.

M3. Strengthen Corollary 4.4 to the natural total-variation statement

The more natural and stronger statement is:

𝑑
T
V
 ⁣
(
\Law
(
𝐹
𝑜
𝑙
𝑑
𝑚
(
𝑟
𝑛
→
𝑚
𝜔
)
)
,
\Law
(
𝜋
𝑛
→
𝑚
(
𝐹
𝑜
𝑙
𝑑
𝑛
𝜔
)
)
)
≤
𝑃
𝜇
(
𝐷
𝑛
→
𝑚
≠
0
)
.
d
TV
	​

(\Law(Fold
m
	​

(r
n→m
	​

ω)),\Law(π
n→m
	​

(Fold
n
	​

ω)))≤P
μ
	​

(D
n→m
	​


=0).

Proof. Put

𝑋
:
=
𝐹
𝑜
𝑙
𝑑
𝑚
(
𝑟
𝑛
→
𝑚
𝜔
)
,
𝑌
:
=
𝜋
𝑛
→
𝑚
(
𝐹
𝑜
𝑙
𝑑
𝑛
𝜔
)
,
X:=Fold
m
	​

(r
n→m
	​

ω),Y:=π
n→m
	​

(Fold
n
	​

ω),

on the common probability space 
(
Ω
𝑛
,
𝜇
)
(Ω
n
	​

,μ). By the coupling characterization of total variation,

𝑑
T
V
(
\Law
(
𝑋
)
,
\Law
(
𝑌
)
)
≤
𝑃
(
𝑋
≠
𝑌
)
=
𝑃
(
𝐷
𝑛
→
𝑚
≠
0
)
.
d
TV
	​

(\Law(X),\Law(Y))≤P(X

=Y)=P(D
n→m
	​


=0).

Then Theorem 4.1 gives

𝑃
(
𝐷
𝑛
→
𝑚
≠
0
)
≤
∑
𝑗
=
𝑚
𝑛
−
1
𝑃
(
𝐾
𝑗
+
1
→
𝑗
(
𝑟
𝑛
→
𝑗
+
1
𝜔
)
=
1
)
.
P(D
n→m
	​


=0)≤
j=m
∑
n−1
	​

P(K
j+1→j
	​

(r
n→j+1
	​

ω)=1).

The current bounded-test-function estimate follows immediately from

∣
𝐸
𝑓
(
𝑋
)
−
𝐸
𝑓
(
𝑌
)
∣
≤
2
∥
𝑓
∥
∞
 
𝑑
T
V
(
\Law
(
𝑋
)
,
\Law
(
𝑌
)
)
.
∣Ef(X)−Ef(Y)∣≤2∥f∥
∞
	​

d
TV
	​

(\Law(X),\Law(Y)).

This reformulation is mathematically cleaner.

M4. Recast Proposition 6.1 as an equivalence, and make it Fold-specific

As written, the proposition is a dressed-up statement that a summable sequence of nonnegative integers is eventually zero. It should be replaced by:

∑
𝑚
≥
1
∣
𝛿
𝑚
∣
0
<
∞
  
⟺
  
𝛿
𝑚
=
0
 for all sufficiently large 
𝑚
.
m≥1
∑
	​

∣δ
m
	​

∣
0
	​

<∞⟺δ
m
	​

=0 for all sufficiently large m.

After adding the explicit local criterion above, you can strengthen this to:

𝛿
𝑚
=
0
  
⟺
  
𝜔
𝑚
+
1
=
0
 or 
𝑁
(
𝑟
∞
→
𝑚
𝜔
∞
)
<
𝐹
𝑚
+
1
.
δ
m
	​

=0⟺ω
m+1
	​

=0 or N(r
∞→m
	​

ω
∞
)<F
m+1
	​

.

Hence the proposition becomes:

There exists 
𝑀
M such that 
𝜋
𝑚
+
1
→
𝑚
(
𝑥
𝑚
+
1
)
=
𝑥
𝑚
π
m+1→m
	​

(x
m+1
	​

)=x
m
	​

 for all 
𝑚
≥
𝑀
m≥M if and only if for all 
𝑚
≥
𝑀
m≥M,

𝜔
𝑚
+
1
=
0
or
𝑁
(
𝑟
∞
→
𝑚
𝜔
∞
)
<
𝐹
𝑚
+
1
.
ω
m+1
	​

=0orN(r
∞→m
	​

ω
∞
)<F
m+1
	​

.

That version actually tells the reader what eventual compatibility means in the Fold model.

Final recommendation

The submission is not journal-ready. The main deterministic statements are essentially correct, but too formal and too slight. The paper needs a complete bibliography, a more honest novelty claim, a substantial Fold-specific theorem, and either a real finite-state realization for Section 7 or excision of that section. Without those changes, I recommend rejection.