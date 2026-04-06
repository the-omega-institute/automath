<!-- oracle metadata: {"timestamp": "2026-04-06T20:28:41.670984", "model": "o3-mini-high", "response_length": 15133} -->

Referee report
1. Overall assessment

Major revision

The manuscript contains a potentially publishable core, especially in the explicit entropy-coefficient analysis and the defect identities in Section 5. I did not find a contradiction in the displayed coefficient formulas of Theorems 5.10 to 5.12, and the computational core appears salvageable. However, the paper is not acceptable in its current form because there is one serious proof gap in Theorem 6.3, one hypothesis mismatch in Theorem 5.13, one incorrect domination estimate in Theorem 6.4, and a persistent mismatch between the novelty claims and the manuscript’s own positioning of Section 7 as largely classical machinery with explicit formulas as the added contribution. 

main

The paper itself explicitly describes Theorem 6.4 as a structural corollary and states that Theorems 7.4 and 7.5 are standard consequences of the shift-invariant-space framework, with the genuine contribution in Section 7 concentrated in the closed-form symbol, cardinal kernel, and norm formula. The abstract, introduction, and theorem packaging should reflect that more honestly. 

main

2. Novelty rating for each theorem

I rate theorem-level novelty only, not propositions or corollaries.

Theorem	Rating	One-line justification
4.2	LOW	Elegant formulation, but the proof is essentially an elementary pullback-density ODE/integration argument.
5.1	LOW	Standard differential-entropy change-of-variables identity in Cayley coordinates.
5.6	MEDIUM	The explicit Chebyshev/trigonometric mode formulas are useful and specialized, though derived from a standard generating function.
5.9	MEDIUM	The even-order vanishing principle is a clean structural observation and seems genuinely nontrivial in this Poisson-shift setting.
5.10	MEDIUM	The explicit eighth-order entropy coefficient is substantial and likely new, but it is primarily a careful coefficient extraction.
5.11	HIGH	The nonnegative defect decomposition of 
𝐶
8
C
8
	​

 and the sharp extremal characterization appear to be the strongest new structural result.
5.12	HIGH	The explicit amplification inequality 
Δ
8
≥
(
13
𝜎
2
/
8
)
Δ
6
Δ
8
	​

≥(13σ
2
/8)Δ
6
	​

 is sharp, conceptual, and stronger than the raw expansion itself.
5.13	MEDIUM	Useful rigidity consequence, but methodologically downstream of Theorems 5.11 and 5.12 and based on relatively elementary coupling estimates.
6.1	MEDIUM	The exact Gram kernel is a neat closed formula, although the residue computation is straightforward once the family is identified.
6.3	LOW	Natural density/unitary-completion statement once 6.1 is known, and the current proof is not yet rigorous.
6.4	LOW	Essentially a reformulation of classical Laplace uniqueness plus characteristic-function inversion, as the manuscript itself largely acknowledges.
6.7	LOW	Interesting structural packaging, but mainly a corollary of the earlier identities and the unitary map.
7.4	LOW	The paper itself states that the abstract Riesz/sampling mechanism is standard in principal shift-invariant-space theory.
7.5	MEDIUM	The abstract reconstruction theorem is standard, but the explicit Poisson-strip formulas for the symbol, norm, and cardinal kernel add nontrivial value.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§6.1, Theorem 6.3	BLOCKER	The proof passes from 
𝑇
1
𝑓
=
0
T
1
	​

f=0 to (e^{-	\xi
M1	§5.5, Theorem 5.13	MEDIUM	Theorem 5.13 assumes only a finite centred fourth moment, but its proof explicitly invokes Theorem 5.12, which assumes a finite centred seventh absolute moment.	Insert a separate fourth-moment lemma proving the formula for 
Δ
6
Δ
6
	​

, or reproduce the short algebra directly in the proof of Theorem 5.13.
M2	§6.2, Theorem 6.4	MEDIUM	The dominated-convergence estimate used to differentiate under the integral is incorrect as written: (\frac{2t	x-\gamma
M3	Abstract, Introduction, §7	MEDIUM	The novelty claims for Section 7 are overstated relative to the manuscript’s own admission that the structural sampling statements are standard consequences of known theory.	Recast Section 7 as an explicit specialization of classical sampling theory, and isolate the genuinely new closed-form formulas as the contribution.
M4	Introduction, §6.2, Remark 6.8	MEDIUM	Theorem 6.4 is presented with more theorem-level novelty than warranted. In substance it is classical Laplace/Cauchy-transform uniqueness plus characteristic-function inversion.	Demote the uniqueness portion to a structural proposition/corollary, and state clearly that the real contribution is the observation-channel identification used in Theorem 6.7.
M5	§5.5, Theorem 5.10	MEDIUM	The coefficient extraction for the 
𝑡
−
8
t
−8
 term is too compressed. A reader cannot easily audit which terms come from 
𝛿
𝑡
2
δ
t
2
	​

, 
𝛿
𝑡
3
δ
t
3
	​

, and 
𝛿
𝑡
4
δ
t
4
	​

.	Add an intermediate coefficient-bookkeeping lemma or a short table listing the exact 
𝑡
−
4
t
−4
, 
𝑡
−
6
t
−6
, and 
𝑡
−
8
t
−8
 contributions before invoking Appendix A.
L1	§5.4, Proposition 5.7	LOW	The boundedness of 
𝑣
𝑁
v
N
	​

 is asserted from a degree comparison that is too compressed to be fully convincing in the 
(
𝑦
,
𝜀
)
(y,ε) variables actually used.	Give a direct uniform bound for 
𝑣
𝑁
v
N
	​

, or make the rational-function degree comparison explicit after rewriting in 
𝑦
y.
L2	Global exposition	LOW	The paper does not clearly separate standard material, repackaging, and genuinely new results on a theorem-by-theorem basis.	Add a contribution map at the end of the introduction.
L3	§5.5, Theorem 5.11	LOW	The manuscript says that (5.21) recovers the classical Pearson moment relation, but no direct Pearson reference is given.	Add a citation for Pearson’s skewness-kurtosis inequality, or a standard modern source.
4. Missing references

The only definite omission I would insist on is the following:

A direct citation for Pearson’s inequality 
𝛽
4
≥
𝛽
3
2
+
1
β
4
	​

≥β
3
2
	​

+1, since Theorem 5.11 explicitly says that (5.21) recovers the classical Pearson moment relation.

Two further additions are not strictly mandatory, but would materially improve the scholarly positioning:

A direct reference on uniqueness/inversion for the Cauchy transform or Stieltjes transform of a finite measure on 
𝑅
R, since Remark 6.8 frames Theorem 6.4 in precisely that language.

If the authors wish to keep strong novelty language in Section 7, the bibliography should include a more historically representative reference for explicit Cauchy/Lorentz cardinal interpolation, not only the recent Kiselev-Minin-Novikov line.

5. Specific improvements needed to reach acceptance

Repair Section 6 rigorously. Theorem 6.3 must be reproved without the current invalid Fourier-distribution step. Because Section 7 depends on it, this is the main acceptance barrier.

Make hypotheses consistent. Theorem 5.13 must be proved under its stated fourth-moment assumption, without importing the seventh-moment hypotheses of Theorem 5.12.

Correct all proof-level analytic estimates. In particular, the differentiation step in Theorem 6.4 must use a correct dominating function.

Make Theorem 5.10 auditable. The coefficient extraction needs an intermediate lemma or table. At present, too much algebra is hidden in the prose.

Repackage the contribution honestly. The title, abstract, and introduction should concentrate novelty on Theorems 5.10 to 5.12, the exact Gram kernel, and the explicit Section 7 formulas. They should not present the standard sampling mechanism itself as if it were new.

Add a theorem-by-theorem contribution map and the missing Pearson citation.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Rigorous replacement for Theorem 6.3

A clean fix is available that avoids the illegitimate 
𝑆
′
S
′
 multiplier argument.

Define the unitary map

(
𝐽
𝑓
)
(
𝜃
)
:
=
𝑓
(
tan
⁡
𝜃
)
,
𝜃
∈
(
−
𝜋
/
2
,
𝜋
/
2
)
,
(Jf)(θ):=f(tanθ),θ∈(−π/2,π/2),

from 
𝐿
0
2
(
𝜔
)
L
0
2
	​

(ω) onto the zero-mean space 
𝐿
0
2
(
(
−
𝜋
/
2
,
𝜋
/
2
)
,
𝑑
𝜃
/
𝜋
)
L
0
2
	​

((−π/2,π/2),dθ/π), since

𝜔
(
𝑑
𝑦
)
=
𝑑
𝑦
𝜋
(
1
+
𝑦
2
)
=
𝑑
𝜃
𝜋
.
ω(dy)=
π(1+y
2
)
dy
	​

=
π
dθ
	​

.

Now use Theorem 5.6. For each 
𝑚
≥
1
m≥1,

𝐽
𝑢
2
𝑚
(
𝜃
)
=
∑
𝑗
=
1
𝑚
𝑎
𝑚
,
𝑗
cos
⁡
(
2
𝑗
𝜃
)
,
𝑎
𝑚
,
𝑚
≠
0
,
Ju
2m
	​

(θ)=
j=1
∑
m
	​

a
m,j
	​

cos(2jθ),a
m,m
	​


=0,

and

𝐽
𝑢
2
𝑚
+
1
(
𝜃
)
=
∑
𝑗
=
1
𝑚
+
1
𝑏
𝑚
,
𝑗
sin
⁡
(
2
𝑗
𝜃
)
,
𝑏
𝑚
,
𝑚
+
1
≠
0.
Ju
2m+1
	​

(θ)=
j=1
∑
m+1
	​

b
m,j
	​

sin(2jθ),b
m,m+1
	​


=0.

This is immediate from the finite Fourier formulas (5.14) and (5.15): the expansions are triangular in frequency with nonzero top coefficient.

Therefore, by downward induction on frequency, the span of 
{
𝐽
𝑢
𝑛
:
𝑛
≥
1
}
{Ju
n
	​

:n≥1} contains every 
cos
⁡
(
2
𝑘
𝜃
)
cos(2kθ) and 
sin
⁡
(
2
𝑘
𝜃
)
sin(2kθ), 
𝑘
≥
1
k≥1. But

{
cos
⁡
(
2
𝑘
𝜃
)
,
sin
⁡
(
2
𝑘
𝜃
)
}
𝑘
≥
1
{cos(2kθ),sin(2kθ)}
k≥1
	​


is a complete orthogonal basis of the zero-mean 
𝐿
2
L
2
-space on 
(
−
𝜋
/
2
,
𝜋
/
2
)
(−π/2,π/2). Hence

span
⁡
‾
{
𝑢
𝑛
:
𝑛
≥
1
}
=
𝐿
0
2
(
𝜔
)
.
span
	​

{u
n
	​

:n≥1}=L
0
2
	​

(ω).

Finally, Corollary 6.2 gives the 
𝐿
2
(
𝜔
)
L
2
(ω)-expansion

Ψ
𝜀
=
∑
𝑛
≥
1
𝑢
𝑛
𝜀
𝑛
−
1
,
∣
𝜀
∣
 small
.
Ψ
ε
	​

=
n≥1
∑
	​

u
n
	​

ε
n−1
,∣ε∣ small.

Thus each 
𝑢
𝑛
u
n
	​

 belongs to 
span
⁡
‾
{
Ψ
𝜀
:
𝜀
∈
𝑅
}
span
	​

{Ψ
ε
	​

:ε∈R}. Therefore

span
⁡
‾
{
Ψ
𝜀
:
𝜀
∈
𝑅
}
=
𝐿
0
2
(
𝜔
)
.
span
	​

{Ψ
ε
	​

:ε∈R}=L
0
2
	​

(ω).

This yields the density statement rigorously, and the isometric extension to 
𝑈
:
𝐿
0
2
(
𝜔
)
→
𝐻
𝐾
U:L
0
2
	​

(ω)→H
K
	​

 then follows by completion.

This fix also restores the foundations of Theorems 6.7, 7.4, and 7.5.

M1. Repair Theorem 5.13 under the stated fourth-moment hypothesis

The proof should not cite Theorem 5.12. Instead, insert the following lemma immediately before Theorem 5.13.

Let

𝑋
=
𝛾
−
𝛾
ˉ
𝜎
,
𝛽
3
=
𝐸
[
𝑋
3
]
,
𝜅
=
𝐸
[
(
𝑋
2
−
1
−
𝛽
3
𝑋
)
2
]
.
X=
σ
γ−
γ
ˉ
	​

	​

,β
3
	​

=E[X
3
],κ=E[(X
2
−1−β
3
	​

X)
2
].

Since 
𝜇
3
=
𝜎
3
𝛽
3
μ
3
	​

=σ
3
β
3
	​

 and 
𝜇
4
=
𝜎
4
𝛽
4
μ
4
	​

=σ
4
β
4
	​

,

𝐶
6
=
𝜎
6
+
6
𝜇
3
2
−
8
𝜎
2
𝜇
4
64
=
𝜎
6
(
1
+
6
𝛽
3
2
−
8
𝛽
4
)
64
.
C
6
	​

=
64
σ
6
+6μ
3
2
	​

−8σ
2
μ
4
	​

	​

=
64
σ
6
(1+6β
3
2
	​

−8β
4
	​

)
	​

.

Also

𝜅
=
𝛽
4
−
1
−
𝛽
3
2
.
κ=β
4
	​

−1−β
3
2
	​

.

Hence

Δ
6
(
𝜈
)
=
−
7
64
𝜎
6
−
𝐶
6
=
𝜎
6
64
(
8
𝛽
4
−
8
−
6
𝛽
3
2
)
=
𝜎
6
8
𝜅
+
𝜎
6
32
𝛽
3
2
.
Δ
6
	​

(ν)=−
64
7
	​

σ
6
−C
6
	​

=
64
σ
6
	​

(8β
4
	​

−8−6β
3
2
	​

)=
8
σ
6
	​

κ+
32
σ
6
	​

β
3
2
	​

.

This identity uses only fourth moments.

Then the proof of Theorem 5.13 becomes valid as written, because

𝐸
[
(
𝑋
−
𝑌
)
2
]
≤
2
𝛽
3
2
+
2
𝜅
≤
2
𝛽
3
2
+
8
𝜅
=
64
𝜎
6
Δ
6
(
𝜈
)
.
E[(X−Y)
2
]≤2β
3
2
	​

+2κ≤2β
3
2
	​

+8κ=
σ
6
64
	​

Δ
6
	​

(ν).
M2. Correct the differentiation step in Theorem 6.4

The displayed estimate

2
𝑡
∣
𝑥
−
𝛾
∣
(
(
𝑥
−
𝛾
)
2
+
𝑡
2
)
2
≤
1
2
𝑡
((x−γ)
2
+t
2
)
2
2t∣x−γ∣
	​

≤
2t
1
	​


is false.

A correct bound is obtained by writing 
𝑢
=
𝑥
−
𝛾
u=x−γ and scaling:

2
𝑡
∣
𝑢
∣
(
𝑢
2
+
𝑡
2
)
2
=
𝑡
−
2
2
∣
𝑢
/
𝑡
∣
(
1
+
(
𝑢
/
𝑡
)
2
)
2
≤
𝑡
−
2
,
(u
2
+t
2
)
2
2t∣u∣
	​

=t
−2
(1+(u/t)
2
)
2
2∣u/t∣
	​

≤t
−2
,

because 
sup
⁡
𝑣
∈
𝑅
2
∣
𝑣
∣
(
1
+
𝑣
2
)
2
<
1
sup
v∈R
	​

(1+v
2
)
2
2∣v∣
	​

<1. The exact maximum is

sup
⁡
𝑢
∈
𝑅
2
𝑡
∣
𝑢
∣
(
𝑢
2
+
𝑡
2
)
2
=
9
8
3
 
𝑡
−
2
.
u∈R
sup
	​

(u
2
+t
2
)
2
2t∣u∣
	​

=
8
3
	​

9
	​

t
−2
.

Thus one may justify differentiation under the integral using

∣
∂
𝑥
𝑃
𝑡
(
𝑥
−
𝛾
)
∣
=
1
𝜋
2
𝑡
∣
𝑥
−
𝛾
∣
(
(
𝑥
−
𝛾
)
2
+
𝑡
2
)
2
≤
1
𝜋
𝑡
2
,
∣∂
x
	​

P
t
	​

(x−γ)∣=
π
1
	​

((x−γ)
2
+t
2
)
2
2t∣x−γ∣
	​

≤
πt
2
1
	​

,

which is integrable against the probability measure 
𝜈
ν for fixed 
𝑡
>
0
t>0.

The remainder of the proof can then proceed unchanged.

M3. Repackage Section 7 so that the novelty claim matches the mathematics

The clean solution is to split the current Section 7 payload into two layers.

First, state a standard sampling corollary:

From the symbol bounds

𝐴
𝑍
≤
𝜎
(
𝜃
)
≤
𝐵
𝑍
,
A
Z
	​

≤σ(θ)≤B
Z
	​

,

one gets the Riesz basis and stable sampling conclusions by the classical principal shift-invariant-space machinery already cited in [3,10,14,21].

Second, isolate the explicit Poisson-strip formulas as the actual new theorem:

Explicit symbol:

𝜎
(
𝜃
)
=
𝜋
cosh
⁡
(
2
(
𝜋
−
∣
𝜃
∣
)
)
sinh
⁡
(
2
𝜋
)
.
σ(θ)=
sinh(2π)
πcosh(2(π−∣θ∣))
	​

.

Exact interpolation norm:

∥
𝐹
𝛼
∥
𝐻
𝐾
2
=
1
2
𝜋
∫
−
𝜋
𝜋
∣
𝛼
^
(
𝜃
)
∣
2
𝜎
(
𝜃
)
 
𝑑
𝜃
.
∥F
α
	​

∥
H
K
	​

2
	​

=
2π
1
	​

∫
−π
π
	​

σ(θ)
∣
α
(θ)∣
2
	​

dθ.

Explicit Fourier formula for the cardinal kernel:

𝐿
^
(
𝜃
+
2
𝜋
𝑚
)
=
𝜋
𝑒
−
2
∣
𝜃
+
2
𝜋
𝑚
∣
𝜎
(
𝜃
)
.
L
(θ+2πm)=
σ(θ)
πe
−2∣θ+2πm∣
	​

.

Then rewrite the abstract accordingly. Instead of “we prove a lattice-sampling theorem and a cardinal reconstruction formula”, say that the paper specializes classical lattice-sampling theory to the Poisson-strip kernel and derives explicit closed formulas.

That would accurately represent the mathematics.

M4. Reframe Theorem 6.4 as classical uniqueness plus a new observation-channel interpretation

The mathematically clean packaging is:

First prove the exact transform identities

𝐴
(
𝑡
)
=
𝐿
(
ℜ
𝜑
𝜈
𝑐
)
(
𝑡
)
,
𝐻
(
𝑡
)
=
𝐿
(
ℑ
𝜑
𝜈
𝑐
)
(
𝑡
)
.
A(t)=L(ℜφ
ν
c
	​

	​

)(t),H(t)=L(ℑφ
ν
c
	​

	​

)(t).

Then state, as a corollary, that 
(
𝐴
,
𝐵
)
(A,B) determines 
𝜈
𝑐
ν
c
	​

 by classical Laplace uniqueness and Lévy inversion.

Keep the theorem-level emphasis on Theorem 6.7, where the genuinely paper-specific content appears:

𝛿
~
𝑡
∈
𝐿
0
2
(
𝜔
)
,
(
𝑈
𝛿
~
𝑡
)
(
𝑎
)
=
1
𝑡
∫
Δ
 
𝐾
(
𝑎
,
Δ
/
𝑡
)
 
𝑑
𝜈
(
𝛾
)
,
δ
t
	​

∈L
0
2
	​

(ω),(U
δ
t
	​

)(a)=
t
1
	​

∫ΔK(a,Δ/t)dν(γ),

and in particular

𝛿
~
𝑡
(
0
)
=
𝑡
𝐴
(
𝑡
)
−
1
,
(
𝑈
𝛿
~
𝑡
)
(
0
)
=
2
𝑡
𝐻
(
2
𝑡
)
.
δ
t
	​

(0)=tA(t)−1,(U
δ
t
	​

)(0)=2tH(2t).

This preserves the mathematics while presenting the novelty more accurately.

M5. Make Theorem 5.10 verifiable by adding a coefficient-bookkeeping lemma

Introduce a short lemma before the proof of Theorem 5.10.

Write

𝛿
𝑡
=
𝑡
−
2
𝑎
2
+
𝑡
−
3
𝑎
3
+
𝑡
−
4
𝑎
4
+
𝑡
−
5
𝑎
5
+
𝑡
−
6
𝑎
6
+
𝑂
(
𝑡
−
7
)
,
δ
t
	​

=t
−2
a
2
	​

+t
−3
a
3
	​

+t
−4
a
4
	​

+t
−5
a
5
	​

+t
−6
a
6
	​

+O(t
−7
),

with 
𝑎
𝑗
a
j
	​

 as in the paper. Then record explicitly:

[
𝑡
−
4
]
 
Φ
(
𝛿
𝑡
)
=
1
2
𝑎
2
2
,
[t
−4
]Φ(δ
t
	​

)=
2
1
	​

a
2
2
	​

,
[
𝑡
−
6
]
 
Φ
(
𝛿
𝑡
)
=
𝑎
2
𝑎
4
+
1
2
𝑎
3
2
−
1
6
𝑎
2
3
,
[t
−6
]Φ(δ
t
	​

)=a
2
	​

a
4
	​

+
2
1
	​

a
3
2
	​

−
6
1
	​

a
2
3
	​

,
[
𝑡
−
8
]
 
Φ
(
𝛿
𝑡
)
=
𝑎
2
𝑎
6
+
𝑎
3
𝑎
5
+
1
2
𝑎
4
2
−
1
2
𝑎
2
2
𝑎
4
−
1
2
𝑎
2
𝑎
3
2
+
1
12
𝑎
2
4
.
[t
−8
]Φ(δ
t
	​

)=a
2
	​

a
6
	​

+a
3
	​

a
5
	​

+
2
1
	​

a
4
2
	​

−
2
1
	​

a
2
2
	​

a
4
	​

−
2
1
	​

a
2
	​

a
3
2
	​

+
12
1
	​

a
2
4
	​

.

Now the proof of Theorem 5.10 reduces to evaluating exactly six weighted integrals from Appendix A. This would make the argument transparent and independently checkable.

I would also strongly recommend displaying the full 
𝑡
−
8
t
−8
 coefficient in the theorem statement as a single combined numerator over 
256
𝑡
8
256t
8
, rather than as two separate fractions split across lines.

In summary, I see a paper with a real core contribution, but not one that is yet ready for acceptance. The decisive step is to make Section 6 rigorous and to align the novelty narrative with the actual mathematics.