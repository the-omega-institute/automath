<!-- oracle metadata: {"timestamp": "2026-04-02T10:09:16.790401", "model": "o3-mini-high", "prompt_length": 922, "response_length": 18296, "pdf": "papers\\publication\\2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta\\main.pdf"} -->

Overall assessment: REJECT. The manuscript is competently written at a formal level, but the present version does not meet the novelty threshold of a research journal. The paper itself states that the Fredholm-Witt bridge is a direct consequence of classical determinant identities, that Proposition 4.3 is standard, and that the note’s novelty lies mainly in “the systematic separation” of known ingredients rather than in a new symbolic model or a new operator theorem. In its current form, Theorem 3.1 is classical, Theorem 3.7 is essentially a reformulation of the canonical zero set description of trace-class Fredholm determinants, and the perturbative applications are either standard or too briefly justified to count as new contributions. 

main

 

main

 

main

 

main

The one component with some claim to originality is the cyclic-block converse realization in Theorem 3.3, but as presented it is a short constructive observation. That alone is not enough to carry the paper unless the authors either: (a) sharpen it into a genuinely new characterization theorem with a necessity statement or optimality theorem beyond the chosen model, or (b) substantially deepen the symbolic-dynamical applications so that the operator-theoretic packaging yields new consequences not already routine from finite-dimensional perturbation theory. At present, neither direction is realized. 

main

Novelty rating by theorem

Theorem 1.1(i) / Theorem 3.1 (Fredholm-Witt bridge): LOW. The paper explicitly presents this as a direct consequence of the classical Fredholm determinant identity and Möbius inversion. 

main

Theorem 1.1(ii) / Theorem 3.3 (cyclic-block realization): MEDIUM-LOW. The explicit block construction is neat and clean, but it is elementary once one writes down 
𝐶
(
𝑛
,
𝛼
)
C(n,α) and uses multiplicativity of determinants on direct sums. 

main

Theorem 1.1(iii) / Theorem 3.7 (spectral rigidity): LOW. This is essentially extracted from the classical canonical product description of trace-class Fredholm determinants, which the paper itself cites as the underlying input. 

main

 

main

Theorem 1.2 / Theorem 4.1 (gradient formula for 
log
⁡
𝐶
logC): MEDIUM-LOW. The formula is useful, but in finite dimension it is a straightforward reduced-determinant derivative identity once the simple Perron eigenspace is isolated. 

main

Theorem 4.2 (holomorphic variation of 
log
⁡
𝑀
logM): LOW. This is a termwise differentiation consequence of Theorem 2.4 plus finite-dimensional analyticity. 

main

Proposition 1.3 / Proposition 4.3 (CLT and off-origin characteristic-function decay): LOW. The paper itself labels this as a standard consequence of the Nagaev-Guivarc’h method. 

main

Issue table
ID	Section	Severity	Description	Suggested fix
B1	1.2, 3.1, 3.3, 3.7, 4.2	BLOCKER	Insufficient novelty for a research paper. Most central statements are classical, standard, or short corollaries of standard tools, and the manuscript does not clearly isolate a genuinely new theorem of independent significance.	Reframe around one genuinely new result. Either strengthen Theorem 3.3 into a characterization/optimality theorem, or replace Section 4 by genuinely new perturbative consequences not already standard.
B2	4.2 / Proposition 4.3	BLOCKER	The CLT and exponential characteristic-function decay are only sketched. The proof omits the precise Banach/finite-dimensional space, the exact analytic perturbation setup, and the key strict spectral-radius bound for twisted operators on compact 
𝐾
⊂
𝑅
∖
{
0
}
K⊂R∖{0}.	Give a complete finite-dimensional proof on a higher-block presentation, or downgrade to a remark/corollary and cite a precise theorem from the literature.
B3	3.2 / Remark 3.4	BLOCKER	The remark states that weaker summability may still allow trace-class realizability through other operator models, but no theorem, example, or citation is provided. As written, this is speculative and mathematically unsupported.	Remove the claim, or replace it by a theorem/example/citation. If kept, formulate as an open question.
M1	1.1 / Theorem 1.2 statement	MEDIUM	The statement “obtained by adding the absolutely convergent higher-order Fredholm corrections” is too vague for a theorem statement.	State the exact formula already given later in Theorem 4.2.
M2	4.1 / Theorem 4.1 proof	MEDIUM	The identity 
𝐶
(
𝐴
𝜃
)
=
det
⁡
′
(
𝐵
𝜃
)
−
1
C(A
θ
	​

)=det
′
(B
θ
	​

)
−1
 is used as obvious from (6), but the reduced determinant 
det
⁡
′
det
′
 is not defined explicitly and the identification is not spelled out.	Define 
det
⁡
′
(
𝐵
𝜃
)
:
=
∏
𝜇
∈
s
p
e
c
(
𝐴
𝜃
)
∖
{
𝜆
(
𝜃
)
}
(
1
−
𝜇
/
𝜆
(
𝜃
)
)
det
′
(B
θ
	​

):=∏
μ∈spec(A
θ
	​

)∖{λ(θ)}
	​

(1−μ/λ(θ)), then show 
𝐶
(
𝐴
𝜃
)
=
det
⁡
′
(
𝐵
𝜃
)
−
1
C(A
θ
	​

)=det
′
(B
θ
	​

)
−1
.
M3	4.2 / Theorem 4.2 proof	MEDIUM	“Write 
log
⁡
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
=
−
T
r
log
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
logdet(I−zA
θ
	​

)
−1
=−Trlog(I−zA
θ
	​

) and differentiate inside the trace” is not justified as written. One must specify the branch of logarithm and justify differentiation.	Use Jacobi’s formula directly in finite dimension: 
∂
𝜃
log
⁡
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
=
T
r
(
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
𝑧
 
∂
𝜃
𝐴
𝜃
)
∂
θ
	​

logdet(I−zA
θ
	​

)
−1
=Tr((I−zA
θ
	​

)
−1
z∂
θ
	​

A
θ
	​

).
M4	2.2 / Theorem 2.4	MEDIUM	The proof’s “elementary identity” paragraph is garbled and not publication-ready. The displayed explanation of the identity is syntactically broken and obscures the logic.	Replace with a clean Möbius inversion derivation, or prove by comparing coefficients after differentiating both sides.
M5	3.2 / Theorem 3.3	MEDIUM	The phrase “if 
𝑟
𝐷
<
∞
r
D
	​

<∞” is unnecessary under the summability hypothesis, since 
ℓ
1
ℓ
1
-summability of (m_j n_j	\beta_j
M6	5 / Further remarks	MEDIUM	The extension claims to nuclear Banach-space operators and Axiom A flows are plausible but unproved and stronger than what is established.	Shorten to clearly labeled conjectural remarks, or add precise hypotheses and citations showing the extension is already known.
L1	2.1 / Lemma 2.2	LOW	The error term is standard but the constant dependence is not made fully explicit.	State that the implied constant depends only on the Jordan data of the non-Perron spectrum, or just on 
𝐴
A.
L2	2.2 / Definition 2.3	LOW	The existence of 
log
⁡
𝑀
(
𝐴
)
logM(A) is said to follow from 
𝑝
𝑛
(
𝐴
)
𝜆
−
𝑛
=
1
/
𝑛
+
𝑂
(
𝜗
𝑛
/
𝑛
)
p
n
	​

(A)λ
−n
=1/n+O(ϑ
n
/n), but the deduction is compressed.	Add one sentence comparing with 
∑
𝑟
𝑛
/
𝑛
=
−
log
⁡
(
1
−
𝑟
)
∑r
n
/n=−log(1−r) and using absolute convergence of 
∑
𝜗
𝑛
𝑟
𝑛
/
𝑛
∑ϑ
n
r
n
/n.
L3	Throughout	LOW	Several statements are advertised as “the novelty” but then immediately identified as classical or standard in the body, which weakens the positioning.	Rewrite the introduction to separate original contributions from repackaging.
L4	References	LOW	Bibliography is serviceable but thin for the standard probabilistic and spectral claims in Section 4.	Add more precise references for CLT / local limit / spectral perturbation in subshifts and transfer operators.
Missing references

The bibliography is adequate for a short note, but for a paper making Section 4 part of its contribution it is missing some standard references that would either support or undercut novelty claims:

David Ruelle, Statistical Mechanics: Rigorous Results (1969) or equivalent early perturbation/pressure reference for analytic dependence of the leading eigenvalue and cumulants.

Hennion-Hervé, Limit Theorems for Markov Chains and Stochastic Properties of Dynamical Systems by Quasi-Compactness (2001) for spectral-method CLT and characteristic-function estimates.

Keller-Liverani (1999) on stability of transfer-operator spectra, if the authors want to situate perturbative arguments more broadly.

A precise reference for Livšic-type coboundary criteria in subshifts, if “not a coboundary modulo constants” is to be the operative non-arithmetic assumption behind strict variance positivity and off-origin decay.

If the authors want to promote Theorem 3.7 as a theorem rather than a corollary of Simon, then a more explicit reference to the exact zero-eigenvalue correspondence for trace-class determinants should be given, not just “Theorem 3.7” of Simon in passing. 

main

 

main

Specific improvements needed to reach acceptance

The manuscript would need substantial restructuring.

First, the contribution must be narrowed and sharpened. The present title, abstract, and introduction suggest a substantial new theory, but the body establishes one classical bridge, one short constructive realization, one rigidity corollary from classical Fredholm determinant theory, and two standard perturbative applications. That mismatch is fatal at editorial stage. The paper needs one central theorem that is unmistakably new. The most promising candidate is Theorem 3.3, but then the manuscript must develop it materially further: for example, by proving an if-and-only-if criterion for realizability within a specified operator class, by classifying minimal trace norm or minimal rank realizations, by identifying uniqueness or moduli of realizations up to similarity/unitary equivalence, or by relating realizability constraints to arithmetic positivity/integrality obstructions from symbolic dynamics. In its current state, Theorem 3.3 is too short and too elementary to support the paper alone. 

main

Second, if Section 4 is retained, it must either become genuinely new or be demoted. Right now Theorem 4.1 and Theorem 4.2 are finite-dimensional perturbation formulas, and Proposition 4.3 is explicitly standard. These can remain only as brief corollaries or examples, not as co-equal main results. Otherwise the paper reads as a polished expository note rather than a research article. 

main

 

main

Third, speculative remarks must be removed or converted into precise open problems. Remark 3.4 in particular is not acceptable as written. It says weaker summability may suffice for trace-class realizability via other models, but gives neither proof nor citation. That kind of unsupported assertion is especially problematic because it touches the sharpness and scope of the only potentially novel theorem. 

main

Fourth, the exposition should be tightened so that all theorem statements are exact and self-contained. Theorem 1.2 is too vague. Theorem 4.2 uses an informal differentiation step that should be replaced by a precise determinant derivative formula. The proof of Theorem 2.4 contains a garbled identity explanation that must be rewritten. 

main

 

main

 

main

Concrete fixes
B1. Insufficient novelty

Problem. The manuscript’s main theorems are mostly classical or straightforward.

Actionable solution A: strengthen Theorem 3.3 into a real theorem. One way is to prove a minimality statement for the cyclic-block realization.

A concrete direction:

For an Euler product

𝐷
(
𝑧
)
−
1
=
∏
𝑗
(
1
−
𝛽
𝑗
𝑧
𝑛
𝑗
)
−
𝑚
𝑗
,
D(z)
−1
=
j
∏
	​

(1−β
j
	​

z
n
j
	​

)
−m
j
	​

,

define

𝑁
(
𝐷
)
:
=
inf
⁡
{
∥
𝑇
∥
1
:
𝑇
∈
𝑆
1
,
 
det
⁡
(
𝐼
−
𝑧
𝑇
)
−
1
=
𝐷
(
𝑧
)
−
1
}
.
N(D):=inf{∥T∥
1
	​

:T∈S
1
	​

, det(I−zT)
−1
=D(z)
−1
}.

Show first that the constructed block model 
𝐿
𝐷
L
D
	​

 satisfies

∥
𝐿
𝐷
∥
1
=
∑
𝑗
𝑚
𝑗
𝑛
𝑗
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
.
∥L
D
	​

∥
1
	​

=
j
∑
	​

m
j
	​

n
j
	​

∣β
j
	​

∣
1/n
j
	​

.

Then attempt to prove a lower bound

∥
𝑇
∥
1
≥
∑
𝑗
𝑚
𝑗
𝑛
𝑗
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
∥T∥
1
	​

≥
j
∑
	​

m
j
	​

n
j
	​

∣β
j
	​

∣
1/n
j
	​


for every normal trace-class realization 
𝑇
T with spectrum partitioned into 
𝑛
𝑗
n
j
	​

-cycles over the roots of 
𝛽
𝑗
β
j
	​

. This would yield optimality inside a natural class.

Even a partial theorem of the form “
𝐿
𝐷
L
D
	​

 is trace-norm minimal among block-cyclic normal realizations” would materially improve novelty.

Actionable solution B: alternatively, recast as an expository note. If no stronger theorem is available, then the paper should be submitted as a short survey/expository note, not as a research article. In that case:

rename Theorem 3.1 and 3.7 as propositions or classical facts,

state explicitly that Theorem 3.3 is the only original observation,

shorten Section 4 to two corollaries.

B2. Proposition 4.3 proof is too incomplete

Problem. The proof does not establish the uniform off-origin decay rigorously.

Concrete replacement proof sketch.
Let 
𝑓
f depend on the first 
𝑚
m coordinates. Pass to the 
(
𝑚
−
1
)
(m−1)-block presentation, so the system becomes a primitive finite-state Markov shift on alphabet 
𝐴
𝑚
A
m
	​

, and 
𝑓
f becomes a one-step observable 
𝑔
(
𝑖
→
𝑗
)
g(i→j). Define the weighted matrix

𝑀
𝑡
(
𝑖
,
𝑗
)
=
𝐴
𝑖
𝑗
(
𝑚
−
1
)
𝑒
𝑖
𝑡
𝑔
(
𝑖
,
𝑗
)
.
M
t
	​

(i,j)=A
ij
(m−1)
	​

e
itg(i,j)
.

Then

∫
𝑒
𝑖
𝑡
𝑆
𝑛
𝑓
 
𝑑
𝜇
∫e
itS
n
	​

f
dμ

can be written as

𝑢
⊤
𝑀
𝑡
𝑛
𝑣
𝑢
⊤
𝑀
0
𝑛
𝑣
u
⊤
M
0
n
	​

v
u
⊤
M
t
n
	​

v
	​


for suitable positive left/right Perron vectors 
𝑢
,
𝑣
u,v of 
𝑀
0
M
0
	​

.

Now prove:

𝑀
𝜃
M
θ
	​

 depends analytically on 
𝜃
θ near 
0
0.

Since 
𝑀
0
M
0
	​

 is primitive, it has a simple Perron eigenvalue 
𝜆
(
0
)
λ(0), and analytic perturbation gives a simple eigenvalue 
𝜆
(
𝜃
)
λ(θ) near 
0
0.

Centering gives 
𝜆
′
(
0
)
=
0
λ
′
(0)=0.

Non-coboundary modulo constants implies 
𝜆
′
′
(
0
)
/
𝜆
(
0
)
=
𝜎
𝑓
2
>
0
λ
′′
(0)/λ(0)=σ
f
2
	​

>0.

For each compact 
𝐾
⋐
𝑅
∖
{
0
}
K⋐R∖{0}, show

sup
⁡
𝑡
∈
𝐾
𝜌
(
𝑀
𝑡
)
≤
(
𝜆
(
0
)
−
𝜂
𝐾
)
<
𝜆
(
0
)
.
t∈K
sup
	​

ρ(M
t
	​

)≤(λ(0)−η
K
	​

)<λ(0).

The key point is that if 
𝜌
(
𝑀
𝑡
)
=
𝜆
(
0
)
ρ(M
t
	​

)=λ(0) for some real 
𝑡
≠
0
t

=0, then by equality in the Perron-Frobenius comparison one gets

𝑒
𝑖
𝑡
𝑔
(
𝑖
,
𝑗
)
=
𝜔
ℎ
(
𝑖
)
ℎ
(
𝑗
)
e
itg(i,j)
=ω
h(j)
h(i)
	​


on every allowed edge, which is equivalent to 
𝑓
f being a coboundary modulo constants. Contradiction.

Compactness of 
𝐾
K upgrades pointwise 
𝜂
𝑡
>
0
η
t
	​

>0 to uniform 
𝜂
𝐾
>
0
η
K
	​

>0.

Then Jordan decomposition yields

∥
𝑀
𝑡
𝑛
∥
≤
𝐶
𝐾
(
𝜆
(
0
)
−
𝜂
𝐾
)
𝑛
,
∥M
t
n
	​

∥≤C
K
	​

(λ(0)−η
K
	​

)
n
,

hence

sup
⁡
𝑡
∈
𝐾
∣
∫
𝑒
𝑖
𝑡
𝑆
𝑛
𝑓
ˉ
 
𝑑
𝜇
∣
≤
𝐶
𝐾
′
𝜗
𝐾
𝑛
.
t∈K
sup
	​

	​

∫e
itS
n
	​

f
ˉ
	​

dμ
	​

≤C
K
′
	​

ϑ
K
n
	​

.

This is the level of detail required if Proposition 4.3 remains in theorem status.

B3. Unsupported Remark 3.4

Problem. The remark makes an unproved existence assertion.

Concrete fix.
Replace the current last sentence by:

“The summability condition is sharp for the specific cyclic-block construction above. Whether the same Euler product can admit a trace-class realization under strictly weaker hypotheses in a different operator model is left open.”

That converts speculation into a legitimate open problem. 

main

M1. Vague statement of Theorem 1.2

Concrete fix. Replace the theorem statement by the exact formula:

𝑑
𝑑
𝜃
log
⁡
𝑀
(
𝐴
𝜃
)
=
Tr
⁡
 ⁣
(
𝑅
𝜃
(
∂
𝜃
𝐴
𝜃
𝜆
(
𝜃
)
−
∂
𝜃
𝜆
(
𝜃
)
𝜆
(
𝜃
)
2
𝐴
𝜃
)
)
+
∑
𝑘
≥
2
𝜇
(
𝑘
)
𝑘
𝑑
𝑑
𝜃
log
⁡
det
⁡
(
𝐼
−
𝜆
(
𝜃
)
−
𝑘
𝐴
𝜃
)
−
1
.
dθ
d
	​

logM(A
θ
	​

)=Tr(R
θ
	​

(
λ(θ)
∂
θ
	​

A
θ
	​

	​

−
λ(θ)
2
∂
θ
	​

λ(θ)
	​

A
θ
	​

))+
k≥2
∑
	​

k
μ(k)
	​

dθ
d
	​

logdet(I−λ(θ)
−k
A
θ
	​

)
−1
.

Then add a sentence:

“The series converges normally in 
𝜃
θ on a neighborhood of 
𝜃
0
θ
0
	​

.”

This makes the abstract and introduction mathematically precise. 

main

 

main

M2. Define the reduced determinant used in Theorem 4.1

Concrete fix. Insert before Theorem 4.1:

det
⁡
′
(
𝐵
𝜃
)
:
=
∏
𝜈
∈
spec
⁡
(
𝐵
𝜃
)
∖
{
0
}
𝜈
=
∏
𝜇
∈
spec
⁡
(
𝐴
𝜃
)
∖
{
𝜆
(
𝜃
)
}
(
1
−
𝜇
𝜆
(
𝜃
)
)
.
det
′
(B
θ
	​

):=
ν∈spec(B
θ
	​

)∖{0}
∏
	​

ν=
μ∈spec(A
θ
	​

)∖{λ(θ)}
∏
	​

(1−
λ(θ)
μ
	​

).

Then from (5)-(6),

𝐶
(
𝐴
𝜃
)
−
1
=
∏
𝜇
∈
spec
⁡
(
𝐴
𝜃
)
∖
{
𝜆
(
𝜃
)
}
(
1
−
𝜇
𝜆
(
𝜃
)
)
=
det
⁡
′
(
𝐵
𝜃
)
.
C(A
θ
	​

)
−1
=
μ∈spec(A
θ
	​

)∖{λ(θ)}
∏
	​

(1−
λ(θ)
μ
	​

)=
det
′
(B
θ
	​

).

Hence

𝐶
(
𝐴
𝜃
)
=
det
⁡
′
(
𝐵
𝜃
)
−
1
.
C(A
θ
	​

)=
det
′
(B
θ
	​

)
−1
.

This removes an implicit step in the proof. 

main

 

main

M3. Repair Theorem 4.2 derivative justification

Concrete fix. Replace the final sentence of the proof by:

∂
𝜃
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
=
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
 
Tr
⁡
 ⁣
(
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
(
−
𝑧
∂
𝜃
𝐴
𝜃
)
)
∂
θ
	​

det(I−zA
θ
	​

)=det(I−zA
θ
	​

)Tr((I−zA
θ
	​

)
−1
(−z∂
θ
	​

A
θ
	​

))

by Jacobi’s formula. Therefore

∂
𝜃
log
⁡
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
=
−
∂
𝜃
log
⁡
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
=
Tr
⁡
 ⁣
(
(
𝐼
−
𝑧
𝐴
𝜃
)
−
1
𝑧
∂
𝜃
𝐴
𝜃
)
.
∂
θ
	​

logdet(I−zA
θ
	​

)
−1
=−∂
θ
	​

logdet(I−zA
θ
	​

)=Tr((I−zA
θ
	​

)
−1
z∂
θ
	​

A
θ
	​

).

No branch of matrix logarithm is needed. 

main

M4. Rewrite the “elementary identity” in Theorem 2.4

Concrete fix. Instead of the current paragraph, write:

−
∑
𝑘
≥
1
𝜇
(
𝑘
)
𝑘
log
⁡
(
1
−
𝑥
𝑘
)
=
∑
𝑘
≥
1
𝜇
(
𝑘
)
𝑘
∑
𝑟
≥
1
𝑥
𝑘
𝑟
𝑟
=
∑
𝑛
≥
1
𝑥
𝑛
𝑛
∑
𝑘
∣
𝑛
𝜇
(
𝑘
)
=
𝑥
,
∣
𝑥
∣
<
1.
−
k≥1
∑
	​

k
μ(k)
	​

log(1−x
k
)=
k≥1
∑
	​

k
μ(k)
	​

r≥1
∑
	​

r
x
kr
	​

=
n≥1
∑
	​

n
x
n
	​

k∣n
∑
	​

μ(k)=x,∣x∣<1.

Hence

∑
𝑘
≥
1
𝜇
(
𝑘
)
𝑘
log
⁡
(
1
−
𝑥
𝑘
)
=
−
𝑥
.
k≥1
∑
	​

k
μ(k)
	​

log(1−x
k
)=−x.

This is short, exact, and coefficientwise transparent. 

main

M5. Clean up Theorem 3.3 radius statement

Concrete fix. Replace:

“In particular, if 
𝑟
𝐷
:
=
sup
⁡
𝑗
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
<
∞
r
D
	​

:=sup
j
	​

∣β
j
	​

∣
1/n
j
	​

<∞, then…”

by:

“Since 
∑
𝑗
𝑚
𝑗
𝑛
𝑗
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
<
∞
∑
j
	​

m
j
	​

n
j
	​

∣β
j
	​

∣
1/n
j
	​

<∞ and 
𝑚
𝑗
𝑛
𝑗
≥
1
m
j
	​

n
j
	​

≥1, the sequence 
(
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
)
𝑗
(∣β
j
	​

∣
1/n
j
	​

)
j
	​

 is bounded; writing 
𝑟
𝐷
:
=
sup
⁡
𝑗
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
<
∞
r
D
	​

:=sup
j
	​

∣β
j
	​

∣
1/n
j
	​

<∞, the identity holds for 
∣
𝑧
∣
<
𝑟
𝐷
−
1
∣z∣<r
D
−1
	​

.”

This removes a logically unnecessary conditional. 

main

M6. Moderate the extension claims in Section 5

Concrete fix. Rewrite the first extension paragraph as:

“The cyclic-block construction itself extends formally to direct sums in broader settings. Extending the spectral-rigidity statement beyond the Hilbert-space trace-class case would require a precise determinant theory and a corresponding canonical zero description; this lies beyond the scope of the present paper.”

That keeps the perspective but removes overreach. 

main

In editorial terms, the paper is not close to acceptance in its current form. The cleanest path forward is to either turn it into a short expository note centered on Theorem 3.3, or to produce one substantially stronger original theorem that goes beyond explicit block construction and classical determinant rigidity.