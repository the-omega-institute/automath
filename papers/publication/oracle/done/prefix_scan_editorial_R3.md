<!-- oracle metadata: {"timestamp": "2026-04-07T00:46:41.692432", "model": "o3-mini-high", "response_length": 17741} -->

My assessment is based on the uploaded manuscript. Under the literal hypotheses, I do not see a deep hidden proof error in Sections 3 to 5. The main problems are different: the submission is bibliographically incomplete, its novelty is substantially overstated, and its rate theorems are nearly immediate once Proposition 3.2 is in place. The discussion also misstates the reach of Shannon-McMillan-Breiman and generic Gibbs cylinder estimates. 

main

1. Overall assessment

Reject

This is not a recommendation for rejection because the algebra is wrong. It is a recommendation for rejection because the paper, in its current form, is not a publishable journal contribution. The submission has no usable bibliography, contains unresolved citation placeholders, and the advertised new theorems are too elementary for a full article. Theorem 4.1 is essentially a discrete Tanaka identity applied to the posterior martingale 
𝑝
𝑚
=
𝜇
(
𝑃
∣
𝐹
𝑚
)
p
m
	​

=μ(P∣F
m
	​

). Theorems 5.2 and 5.3 are direct consequences of Proposition 3.2 plus the stated cylinder-mass assumptions. 

main

2. Novelty rating for each theorem
Theorem	Novelty	Justification
Theorem 4.1	LOW	This is a direct application of the discrete Tanaka identity to (
Theorem 5.2	LOW	This is an immediate corollary of Proposition 3.2 and the uniform bound 
𝜇
(
𝐶
)
≤
𝐾
𝜆
c
y
l
−
𝑚
μ(C)≤Kλ
cyl
−m
	​

.
Theorem 5.3	LOW	This is the same decomposition with the trivial bounds 
𝜃
≤
min
⁡
{
𝜇
(
𝑃
∣
𝐶
)
,
1
−
𝜇
(
𝑃
∣
𝐶
)
}
≤
1
2
θ≤min{μ(P∣C),1−μ(P∣C)}≤
2
1
	​

 and 
𝑐
−
𝜆
−
𝑚
≤
𝜇
(
𝐶
)
≤
𝑐
+
𝜆
−
𝑚
c
−
	​

λ
−m
≤μ(C)≤c
+
	​

λ
−m
.
3. Issue table

All section references below are to the uploaded manuscript. 

main

ID	Section	Severity	Description	Suggested fix
B1	Global	BLOCKER	No bibliography is present, and several citations remain unresolved as [?]. This prevents verification of claims of classicality, novelty, and applicability.	Supply a complete bibliography and resolve every placeholder.
B2	Introduction, Sections 4 to 5	BLOCKER	The central “new” results are too elementary for journal publication. Theorem 4.1 is a direct convex-martingale identity. Theorems 5.2 and 5.3 are one-step consequences of Proposition 3.2.	Either reposition the work as a short note with much reduced claims, or add a genuine structural theorem deriving boundary growth or boundary mass from intrinsic dynamics.
B3	Related work, Discussion	BLOCKER	The scope claims are mathematically false or overstated. Shannon-McMillan-Breiman does not give the uniform cylinder bounds used in Section 5, and generic Gibbs measures do not satisfy the same-base two-sided comparability assumed in Theorem 5.3.	Restrict claims to settings that really satisfy the hypotheses, or reformulate the rate theory so that only typical-cylinder estimates are needed.
M1	Introduction, Sections 2 to 5	MEDIUM	The dynamical-system setup is largely decorative. The proofs use only an increasing finite filtration. Also, Section 5 does not depend on Section 4 despite the announced theorem chain.	State the results first for a general finite filtration, then specialize to prefix partitions. Split the logical structure into two branches from Proposition 3.2.
M2	Definition 5.1	MEDIUM	
dim
⁡
𝐵
(
∂
𝑃
)
dim
B
	​

(∂P) uses 
log
⁡
𝑁
𝑚
(
∂
𝑃
)
logN
m
	​

(∂P), but 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P) may be 
0
0, including in the finite-horizon regime of Example 6.1.	Adopt a convention for 
𝑁
𝑚
=
0
N
m
	​

=0, for example 
log
⁡
0
=
−
∞
log0=−∞, or replace 
log
⁡
𝑁
𝑚
logN
m
	​

 by 
log
⁡
max
⁡
{
1
,
𝑁
𝑚
}
logmax{1,N
m
	​

}.
M3	Example 6.2	MEDIUM	Example 6.2 is not a worked example. It does not specify an event 
𝑃
P, compute 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P), verify thickness, or calculate 
𝜀
𝑚
ε
m
	​

. It merely restates the theorem under the theorem’s own assumptions.	Add a fully explicit event and carry out the boundary, conditional-probability, and error calculations.
M4	Section 5	MEDIUM	
𝜆
c
y
l
λ
cyl
	​

 is used both as a complexity base and as a cylinder-mass decay base. These are different objects in general. The exponent 
1
−
𝑑
1−d is meaningful only in the special case where the two bases coincide.	Introduce separate parameters for complexity growth and mass decay, and restate the exponent in terms of both.
M5	Theorem 5.3, Discussion	MEDIUM	The thickness hypothesis is ad hoc and disconnected from the classification literature. It is really a cylinder-level low-noise or margin condition.	Recast the assumption in terms of atomwise margin (\gamma_C:=
M6	Section 5	MEDIUM	The natural quantity controlling the risk is weighted boundary mass, not boundary cardinality. The present formulation obscures the exact mechanism.	Make weighted boundary mass the main object and derive the cardinality bounds as corollaries.
L1	Section 2	LOW	
𝑇
T-invariance of 
𝜇
μ is assumed but never used.	Remove it or explain its later role.
L2	Theorem 4.1	LOW	The final assumption “if 
1
𝑃
1
P
	​

 is measurable with respect to 
⋁
𝑚
𝐹
𝑚
⋁
m
	​

F
m
	​

” is redundant because 
𝑃
∈
𝐹
∞
P∈F
∞
	​

 by definition.	Simplify the statement.
L3	Theorem 5.2 proof	LOW	The upper bound loses a factor 
1
/
2
1/2, since 
min
⁡
{
𝑎
,
𝑏
}
≤
(
𝑎
+
𝑏
)
/
2
min{a,b}≤(a+b)/2.	Replace 
𝐾
K by 
𝐾
/
2
K/2.
L4	Related work	LOW	Barron-Györfi-van der Meulen is not the right reference for the uniform cylinder hypotheses actually used in Section 5.	Replace with references on Parry, quasi-Bernoulli, or Gibbs cylinder estimates.
4. Missing references

The omissions below are not exhaustive, because the manuscript currently has no usable bibliography. These are the most important missing items.

William Parry, “Intrinsic Markov Chains”, for the Parry measure on shifts of finite type. 
jstor.org

Rufus Bowen, Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms, for Gibbs measures and cylinder asymptotics. 
Springer

Enno Mammen and Alexandre B. Tsybakov, “Smooth discrimination analysis”, because the paper’s thickness assumption is a cylinder-level low-noise condition. 
projecteuclid.org

Alexandre B. Tsybakov, “Optimal aggregation of classifiers in statistical learning”, for the standard margin-dependent classification-rate framework. 
projecteuclid.org

5. Specific improvements needed to reach acceptance

Replace the bibliographic apparatus completely. The paper needs a full reference list, resolved placeholders, and accurate attributions of what is classical and what is new.

Reposition the contribution mathematically. Either present it honestly as a short filtration note, or add a genuinely nontrivial theorem that computes boundary growth or boundary mass from intrinsic symbolic or probabilistic data.

Correct the scope claims in Section 7. The current entropy discussion is not valid for the uniform assumptions actually used in Section 5.

Add at least one fully explicit, nontrivial example. The current golden-mean “example” does not instantiate the theory.

Reformulate Section 5 around weighted boundary mass and margin. That is the exact object appearing in Proposition 3.2, and it leads to a cleaner and more informative theory.

Clarify the logical structure. At present the paper suggests a chain “Tanaka representation implies rate laws”, but the rate laws do not use Section 4 at all.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Missing bibliography and unresolved citations

Add a complete bibliography and tie each classical statement to a precise source. At minimum, the manuscript should explicitly source:

𝜀
𝑚
(
𝑃
;
𝜇
)
=
∑
𝐶
∈
𝐶
𝑚
min
⁡
{
𝜇
(
𝑃
∩
𝐶
)
,
𝜇
(
𝐶
∖
𝑃
)
}
,
𝜀
𝑚
=
𝐸
[
min
⁡
(
𝑝
𝑚
,
1
−
𝑝
𝑚
)
]
,
ε
m
	​

(P;μ)=
C∈C
m
	​

∑
	​

min{μ(P∩C),μ(C∖P)},ε
m
	​

=E[min(p
m
	​

,1−p
m
	​

)],

the threshold optimality of 
𝑝
𝑚
≥
1
2
p
m
	​

≥
2
1
	​

, Doob or Lévy upward convergence, the discrete Tanaka or convex-martingale identity used in Section 4, and the symbolic references used in Example 6.2. Without this, the reader cannot evaluate whether the paper’s core is new or merely repackaged. The missing symbolic and classification references listed above should be added explicitly. 
projecteuclid.org
+3
jstor.org
+3
Springer
+3

B2. The core results need real mathematical strengthening

A viable route to acceptability is to add one theorem that computes boundary growth from intrinsic structure instead of assuming it.

For example, let 
𝑋
X be a mixing one-step SFT with Parry measure, and let 
𝑃
P be recognized by a deterministic finite automaton with absorbing accept and reject states. Build a product automaton that tracks:

the current SFT state,

the automaton state for 
𝑃
P,

whether the event has been forced true, forced false, or remains ambiguous.

Let 
𝐵
B be the adjacency matrix of the ambiguous subgraph. Then the boundary cylinders at depth 
𝑚
m correspond to length-
𝑚
m ambiguous paths, so one should prove

𝑁
𝑚
(
∂
𝑃
)
=
𝑢
⊤
𝐵
𝑚
𝑣
,
N
m
	​

(∂P)=u
⊤
B
m
v,

for suitable vectors 
𝑢
,
𝑣
u,v, and under Parry measure obtain

∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
≍
𝜌
(
𝐵
)
𝑚
 
𝜆
P
a
r
r
y
−
𝑚
.
C∈∂
m
	​

P
∑
	​

μ(C)≍ρ(B)
m
λ
Parry
−m
	​

.

Under a uniform margin bound on ambiguous product states, Proposition 3.2 would then give

𝜀
𝑚
(
𝑃
;
𝜇
)
≍
𝜌
(
𝐵
)
𝑚
 
𝜆
P
a
r
r
y
−
𝑚
.
ε
m
	​

(P;μ)≍ρ(B)
m
λ
Parry
−m
	​

.

That would be a genuine symbolic-dynamics theorem. The present Section 5 does not do this. It assumes the decisive asymptotic input instead of deriving it.

B3. Correct the entropy and Gibbs discussion

The discussion must be rewritten because Shannon-McMillan-Breiman does not imply the hypotheses of Theorems 5.2 and 5.3.

A clean counterexample is the Bernoulli measure 
𝜇
𝑝
μ
p
	​

 on the full two-shift with 
𝑝
≠
1
2
p

=
2
1
	​

. SMB says that for 
𝜇
𝑝
μ
p
	​

-typical cylinders,

−
1
𝑚
log
⁡
𝜇
𝑝
(
𝐶
𝑚
(
𝑥
)
)
→
ℎ
(
𝑝
)
,
−
m
1
	​

logμ
p
	​

(C
m
	​

(x))→h(p),

but the specific cylinders 
[
1
𝑚
]
[1
m
] and 
[
0
𝑚
]
[0
m
] have masses 
𝑝
𝑚
p
m
 and 
(
1
−
𝑝
)
𝑚
(1−p)
m
. Hence there is generally no single base 
𝜆
λ and constants 
𝑐
±
c
±
	​

 such that

𝑐
−
𝜆
−
𝑚
≤
𝜇
𝑝
(
𝐶
)
≤
𝑐
+
𝜆
−
𝑚
c
−
	​

λ
−m
≤μ
p
	​

(C)≤c
+
	​

λ
−m

for every 
𝑚
m-cylinder 
𝐶
C. So the current claim of “standard applicability” is false.

There are two mathematically correct repair options.

First, restrict the discussion to measures that genuinely satisfy uniform estimates, for example Parry-type or quasi-Bernoulli settings. The references that should anchor this discussion are Parry and Bowen. 
jstor.org
+1

Second, if the author wants a true SMB-based result, separate typical and atypical cylinders. If 
𝐴
𝑚
,
𝛿
A
m,δ
	​

 is the union of atypical cylinders and every typical boundary cylinder satisfies 
𝜇
(
𝐶
)
≤
𝑒
−
𝑚
(
ℎ
−
𝛿
)
μ(C)≤e
−m(h−δ)
, then

𝜀
𝑚
(
𝑃
;
𝜇
)
≤
1
2
 
𝜇
(
𝐴
𝑚
,
𝛿
)
+
𝑒
−
𝑚
(
ℎ
−
𝛿
)
 
𝑁
𝑚
 ⁣
(
∂
𝑚
𝑃
∖
𝐴
𝑚
,
𝛿
)
.
ε
m
	​

(P;μ)≤
2
1
	​

μ(A
m,δ
	​

)+e
−m(h−δ)
N
m
	​

(∂
m
	​

P∖A
m,δ
	​

).

That would produce a theorem genuinely connected to SMB.

M1. Recast the paper as a filtration theorem, then specialize

The correct abstract framework is not “measurable dynamical system plus binary readout”. It is:

Let 
(
Ω
,
𝐹
,
𝜇
)
(Ω,F,μ) be a probability space, let 
(
𝐹
𝑚
)
(F
m
	​

) be an increasing sequence of finite sub-
𝜎
σ-algebras, let 
𝑃
∈
⋁
𝑚
𝐹
𝑚
P∈⋁
m
	​

F
m
	​

, and define

𝑝
𝑚
:
=
𝐸
[
1
𝑃
∣
𝐹
𝑚
]
,
𝜀
𝑚
(
𝑃
)
:
=
inf
⁡
𝑄
∈
𝐹
𝑚
𝜇
(
𝑃
△
𝑄
)
.
p
m
	​

:=E[1
P
	​

∣F
m
	​

],ε
m
	​

(P):=
Q∈F
m
	​

inf
	​

μ(P△Q).

Then Propositions 3.2 and 3.3 and Theorem 4.1 hold verbatim.

Only after proving this should the manuscript specialize to the prefix filtration induced by a binary readout. This would make the scope honest and remove the false impression that the dynamical system is doing substantial work in Sections 3 to 5.

Also, the theorem map should be redrawn as two independent branches from Proposition 3.2:

Branch A:

𝜀
𝑚
=
1
2
−
𝐸
∣
𝑝
𝑚
−
1
2
∣
⟹
Tanaka identity.
ε
m
	​

=
2
1
	​

−E
	​

p
m
	​

−
2
1
	​

	​

⟹Tanaka identity.

Branch B:

𝜀
𝑚
=
∑
𝐶
∈
𝐶
𝑚
𝜇
(
𝐶
)
min
⁡
{
𝑝
𝐶
,
1
−
𝑝
𝐶
}
⟹
boundary bounds.
ε
m
	​

=
C∈C
m
	​

∑
	​

μ(C)min{p
C
	​

,1−p
C
	​

}⟹boundary bounds.

At present, the introduction suggests a causal chain that the proofs do not use.

M2. Repair Definition 5.1

A mathematically clean repair is:

dim
⁡
𝐵
(
∂
𝑃
)
:
=
lim sup
⁡
𝑚
→
∞
log
⁡
max
⁡
{
1
,
𝑁
𝑚
(
∂
𝑃
)
}
𝑚
log
⁡
𝜆
c
y
l
,
dim
B
	​

(∂P):=
m→∞
limsup
	​

mlogλ
cyl
	​

logmax{1,N
m
	​

(∂P)}
	​

,

together with the convention that if 
𝑁
𝑚
(
∂
𝑃
)
=
0
N
m
	​

(∂P)=0 for all sufficiently large 
𝑚
m, then 
dim
⁡
𝐵
(
∂
𝑃
)
=
−
∞
dim
B
	​

(∂P)=−∞.

This fixes the current defect that finite-horizon events, including Example 6.1, make 
log
⁡
𝑁
𝑚
(
∂
𝑃
)
logN
m
	​

(∂P) ill-defined. It also gives the correct interpretation: eventual emptiness of the boundary corresponds to finite-depth decidability.

M3. Add a genuine worked example

The paper needs one explicit event 
𝑃
P for which the boundary cylinders, conditional probabilities, and error profile can actually be computed.

A direct repair of Example 6.2 is available on the one-sided golden-mean shift with Parry measure. Take

𝑃
:
=
{
the first occurrence of 
1
 is at an even index
}
.
P:={the first occurrence of 1 is at an even index}.

Then:

the only ambiguous cylinder at depth 
𝑚
m is 
[
0
𝑚
]
[0
m
], so

∂
𝑚
𝑃
=
{
[
0
𝑚
]
}
,
𝑁
𝑚
(
∂
𝑃
)
=
1
;
∂
m
	​

P={[0
m
]},N
m
	​

(∂P)=1;

conditioned on 
[
0
𝑚
]
[0
m
], the waiting time 
𝑅
R until the first 
1
1 has

Pr
⁡
(
𝑅
=
𝑟
)
=
𝜙
−
(
𝑟
+
2
)
,
𝑟
≥
0
,
Pr(R=r)=ϕ
−(r+2)
,r≥0,

because after a 
0
0, the Parry transition probabilities are 
0
→
0
0→0 with probability 
𝜙
−
1
ϕ
−1
 and 
0
→
1
0→1 with probability 
𝜙
−
2
ϕ
−2
;

therefore

𝜇
(
𝑃
∣
[
0
𝑚
]
)
=
{
∑
𝑟
 even
𝜙
−
(
𝑟
+
2
)
=
𝜙
−
1
,
	
𝑚
 even
,


∑
𝑟
 odd
𝜙
−
(
𝑟
+
2
)
=
𝜙
−
2
,
	
𝑚
 odd
,
μ(P∣[0
m
])={
∑
r even
	​

ϕ
−(r+2)
=ϕ
−1
,
∑
r odd
	​

ϕ
−(r+2)
=ϕ
−2
,
	​

m even,
m odd,
	​


so the boundary thickness is uniform with 
𝜃
=
𝜙
−
2
θ=ϕ
−2
;

since 
𝜇
(
[
0
𝑚
]
)
≍
𝜙
−
𝑚
μ([0
m
])≍ϕ
−m
, one obtains

𝜀
𝑚
(
𝑃
;
𝜇
)
=
𝜇
(
[
0
𝑚
]
)
min
⁡
{
𝜇
(
𝑃
∣
[
0
𝑚
]
)
,
1
−
𝜇
(
𝑃
∣
[
0
𝑚
]
)
}
=
𝜙
−
2
𝜇
(
[
0
𝑚
]
)
≍
𝜙
−
𝑚
.
ε
m
	​

(P;μ)=μ([0
m
])min{μ(P∣[0
m
]),1−μ(P∣[0
m
])}=ϕ
−2
μ([0
m
])≍ϕ
−m
.

This is the kind of example the paper presently lacks.

M4. Separate complexity growth from cylinder-mass decay

Section 5 should not use a single 
𝜆
c
y
l
λ
cyl
	​

 for two distinct phenomena. Introduce:

𝛼
>
1
α>1 for cylinder-mass decay:

𝜇
(
𝐶
)
≤
𝐾
𝛼
−
𝑚
;
μ(C)≤Kα
−m
;

𝜅
>
1
κ>1 for cylinder-count growth:

𝑁
𝑚
(
∂
𝑃
)
≤
𝜅
𝑑
𝑚
+
𝑜
(
𝑚
)
.
N
m
	​

(∂P)≤κ
dm+o(m)
.

Then the correct upper-rate statement is

𝜀
𝑚
(
𝑃
;
𝜇
)
≤
𝐾
exp
⁡
 ⁣
(
−
𝑚
(
log
⁡
𝛼
−
𝑑
log
⁡
𝜅
)
+
𝑜
(
𝑚
)
)
.
ε
m
	​

(P;μ)≤Kexp(−m(logα−dlogκ)+o(m)).

Under two-sided mass bounds 
𝑐
−
𝛼
−
𝑚
≤
𝜇
(
𝐶
)
≤
𝑐
+
𝛼
−
𝑚
c
−
	​

α
−m
≤μ(C)≤c
+
	​

α
−m
, exact boundary growth 
𝑁
𝑚
(
∂
𝑃
)
=
𝜅
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

(∂P)=κ
dm+o(m)
, and a thickness condition, one gets

lim
⁡
𝑚
→
∞
−
1
𝑚
log
⁡
𝜀
𝑚
(
𝑃
;
𝜇
)
=
log
⁡
𝛼
−
𝑑
log
⁡
𝜅
.
m→∞
lim
	​

−
m
1
	​

logε
m
	​

(P;μ)=logα−dlogκ.

Only in the special case 
𝛼
=
𝜅
α=κ does this reduce to the paper’s 
1
−
𝑑
1−d exponent.

M5. Replace “thickness” by a margin formulation

Define on each atom 
𝐶
∈
𝐶
𝑚
C∈C
m
	​

:

𝑝
𝐶
:
=
𝜇
(
𝑃
∣
𝐶
)
,
𝛾
𝐶
:
=
∣
2
𝑝
𝐶
−
1
∣
.
p
C
	​

:=μ(P∣C),γ
C
	​

:=∣2p
C
	​

−1∣.

Then

min
⁡
{
𝑝
𝐶
,
1
−
𝑝
𝐶
}
=
1
−
𝛾
𝐶
2
.
min{p
C
	​

,1−p
C
	​

}=
2
1−γ
C
	​

	​

.

So Proposition 3.2 can be rewritten exactly as

𝜀
𝑚
(
𝑃
;
𝜇
)
=
1
2
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
(
1
−
𝛾
𝐶
)
.
ε
m
	​

(P;μ)=
2
1
	​

C∈∂
m
	​

P
∑
	​

μ(C)(1−γ
C
	​

).

This is the precise cylinder-level analogue of a low-noise or margin condition. The manuscript should define the weighted average margin

𝛾
ˉ
𝑚
:
=
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
𝛾
𝐶
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
γ
ˉ
	​

m
	​

:=
∑
C∈∂
m
	​

P
	​

μ(C)
∑
C∈∂
m
	​

P
	​

μ(C)γ
C
	​

	​


whenever the denominator is nonzero. Then

𝜀
𝑚
(
𝑃
;
𝜇
)
=
1
−
𝛾
ˉ
𝑚
2
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
.
ε
m
	​

(P;μ)=
2
1−
γ
ˉ
	​

m
	​

	​

C∈∂
m
	​

P
∑
	​

μ(C).

This yields an exact average-thickness theorem. If 
𝛾
ˉ
𝑚
≤
1
−
2
𝜃
γ
ˉ
	​

m
	​

≤1−2θ eventually, then

𝜃
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
≤
𝜀
𝑚
(
𝑃
;
𝜇
)
≤
1
2
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
.
θ
C∈∂
m
	​

P
∑
	​

μ(C)≤ε
m
	​

(P;μ)≤
2
1
	​

C∈∂
m
	​

P
∑
	​

μ(C).

This is cleaner, stronger, and much easier to compare with the classical margin literature. 
projecteuclid.org
+1

M6. Make weighted boundary mass the main object

The exact structural quantity is not the count 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P), but the weighted boundary mass

𝐵
𝑚
(
𝑃
)
:
=
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
.
B
m
	​

(P):=
C∈∂
m
	​

P
∑
	​

μ(C).

Then Proposition 3.2 immediately gives

0
≤
𝜀
𝑚
(
𝑃
;
𝜇
)
≤
1
2
 
𝐵
𝑚
(
𝑃
)
,
0≤ε
m
	​

(P;μ)≤
2
1
	​

B
m
	​

(P),

and the average-thickness identity above gives

𝜀
𝑚
(
𝑃
;
𝜇
)
=
𝜃
ˉ
𝑚
 
𝐵
𝑚
(
𝑃
)
,
𝜃
ˉ
𝑚
:
=
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
min
⁡
{
𝑝
𝐶
,
1
−
𝑝
𝐶
}
∑
𝐶
∈
∂
𝑚
𝑃
𝜇
(
𝐶
)
.
ε
m
	​

(P;μ)=
θ
ˉ
m
	​

B
m
	​

(P),
θ
ˉ
m
	​

:=
∑
C∈∂
m
	​

P
	​

μ(C)
∑
C∈∂
m
	​

P
	​

μ(C)min{p
C
	​

,1−p
C
	​

}
	​

.

So the natural theorem is:

𝜃
ˉ
𝑚
𝐵
𝑚
(
𝑃
)
≤
𝜀
𝑚
(
𝑃
;
𝜇
)
≤
1
2
𝐵
𝑚
(
𝑃
)
,
θ
ˉ
m
	​

B
m
	​

(P)≤ε
m
	​

(P;μ)≤
2
1
	​

B
m
	​

(P),

with equality in the left factor if 
𝜃
ˉ
𝑚
θ
ˉ
m
	​

 is defined exactly as above. The current cardinality statements then become corollaries via

𝐵
𝑚
(
𝑃
)
≤
sup
⁡
𝐶
∈
𝐶
𝑚
𝜇
(
𝐶
)
 
𝑁
𝑚
(
∂
𝑃
)
.
B
m
	​

(P)≤
C∈C
m
	​

sup
	​

μ(C)N
m
	​

(∂P).

This would make Section 5 conceptually correct, sharpen Theorem 5.2, and clarify that the real mechanism is weighted ambiguity, not merely combinatorial counting.

Overall, the paper is closer to a neat observation than to a publishable journal article. To reach acceptance, it needs corrected scope, complete scholarship, and at least one genuinely derived structural theorem or one fully worked symbolic example with nontrivial calculations.