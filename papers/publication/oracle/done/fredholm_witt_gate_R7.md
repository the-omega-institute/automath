<!-- oracle metadata: {"timestamp": "2026-04-07T02:47:41.875188", "model": "o3-mini-high", "response_length": 16395} -->

Overall assessment: Major revision

The manuscript contains one potentially publishable structural observation, namely the normal trace-class cyclic-block classification in Section 3. However, the current version is not ready for acceptance. The principal difficulty is not Theorem 3.3 itself, which appears essentially correct, but Section 4: several perturbative statements are formulated with 
𝜆
(
𝜃
)
=
𝜌
(
𝐴
𝜃
)
λ(θ)=ρ(A
θ
	​

) as though the spectral radius were holomorphic, and the quantities 
𝐶
(
𝐴
𝜃
)
C(A
θ
	​

) and 
log
⁡
𝑀
(
𝐴
𝜃
)
logM(A
θ
	​

) are used outside the category in which they were defined. In addition, Proposition 3.1 is stated on too large a domain, Theorem 3.3 needs a proper trace-norm continuity argument for countable direct sums, and the bibliography still contains unresolved placeholders. As a result, the paper presently mixes a short note’s worth of new content with a substantial amount of classical material that is not yet stated at publication level. 

main

1. Novelty rating for each theorem
Theorem	Novelty	Justification
Theorem 1.2	MEDIUM	This is the paper’s main structural claim, but it is largely a neat packaging of classical ingredients: determinant rigidity, the spectral theorem for normal compact operators, and Fourier diagonalization of cyclic permutation blocks.
Theorem 2.4	LOW	This is a direct Möbius inversion and Euler-product rearrangement from Proposition 2.1, not a genuinely new structural theorem.
Theorem 3.3	MEDIUM	Same substance as Theorem 1.2. The exact if-and-only-if formulation and support count are clean, but the proof is short and mostly assembled from standard facts.

No theorem in the current manuscript rises to HIGH novelty.

2. Issue table

The table below lists the substantive issues that must be addressed. 

main

ID	Section	Severity	Description	Suggested fix
B1	§4.1-§4.3	BLOCKER	The paper repeatedly writes 
𝜆
(
𝜃
)
:
=
𝜌
(
𝐴
𝜃
)
λ(θ):=ρ(A
θ
	​

) for a holomorphic family 
𝐴
𝜃
A
θ
	​

 and then differentiates in 
𝜃
θ. The spectral radius is not holomorphic in complex parameters in general.	Replace 
𝜌
(
𝐴
𝜃
)
ρ(A
θ
	​

) by the analytic continuation of a simple isolated eigenvalue branch 
𝜆
(
𝜃
)
λ(θ), with a uniform spectral gap from the remaining spectrum.
B2	§4.1-§4.3	BLOCKER	The quantities 
𝐶
(
𝐴
𝜃
)
C(A
θ
	​

) and 
log
⁡
𝑀
(
𝐴
𝜃
)
logM(A
θ
	​

) are used for general holomorphic matrix families, but they were defined earlier only for primitive symbolic matrices via orbit counts and a pole of 
𝜁
𝐴
ζ
A
	​

.	Introduce algebraic versions 
𝐶
(
𝐴
,
𝜆
)
C(A,λ) and 
𝐹
(
𝐴
,
𝜆
)
F(A,λ) for an arbitrary matrix with a distinguished simple eigenvalue 
𝜆
λ, then recover the symbolic quantity by specialization on the real primitive slice.
M1	§3.1	MEDIUM	Proposition 3.1 states the Witt/Euler product on (	z
M2	§3.2	MEDIUM	Theorem 3.3 does not justify the passage from finite direct sums to the countable direct sum determinant identity.	Use finite-rank truncations 
𝐿
𝐷
(
𝑁
)
L
D
(N)
	​

, prove 
𝐿
𝐷
(
𝑁
)
→
𝐿
𝐷
L
D
(N)
	​

→L
D
	​

 in trace norm, and invoke continuity of the Fredholm determinant in 
𝑆
1
S
1
	​

.
M3	§4.1	MEDIUM	The logarithms 
log
⁡
det
⁡
𝐺
𝑘
(
𝜃
)
−
1
logdetG
k
	​

(θ)
−1
 and 
log
⁡
𝐶
(
𝐴
𝜃
)
logC(A
θ
	​

) are used without fixing branches on a simply connected zero-free domain.	Shrink to a simply connected neighborhood 
𝑈
U where all relevant determinants avoid 
0
0, define branches there, and record the derivative formula for those branches.
M4	§4.2	MEDIUM	Proposition 4.7(ii) does not rigorously identify the dominant eigenvalue germs. Equality of spectral multisets for each fixed 
𝑡
t is not by itself enough unless one isolates a spectral disc around the leading eigenvalue.	Add a local spectral-separation lemma using Riesz projections and conclude uniqueness of the eigenvalue branch in that disc.
M5	§4.3	MEDIUM	Proposition 4.10 assumes existence of 
𝜂
𝐾
η
K
	​

 but does not supply the continuity argument needed to produce it.	Insert the argument that 
𝑢
↦
𝜌
(
𝑀
𝑢
𝑓
)
u↦ρ(M
u
f
	​

) is continuous and equals 
𝜆
λ exactly on 
Λ
𝑓
Λ
f
	​

, hence is uniformly 
<
𝜆
<λ on compact 
𝐾
⊂
𝑅
∖
Λ
𝑓
K⊂R∖Λ
f
	​

.
M6	§1.2 and references	MEDIUM	The manuscript contains unresolved citations “[?]”, so several claims cannot presently be checked.	Replace all placeholders with exact bibliographic entries. At minimum add the standard sources listed below.
L1	Introduction, §5	LOW	The novelty positioning is too aggressive. Most of Section 4 is classical, and Theorem 3.3 is conceptually neat but technically short.	Recast the paper as a short note centered on Section 3, with Section 4 explicitly labeled as standard applications or moved to an appendix.
L2	Throughout	LOW	“Primitive matrix” is used in several incompatible senses: symbolic adjacency matrix, primitive nonnegative matrix, and complex holomorphic family.	Separate the categories explicitly: symbolic/nonnegative in Sections 2 and 4 on the real slice, abstract matrix/eigenvalue-branch formalism for the perturbative complex arguments.
L3	Abstract, §3	LOW	The support-optimality language is slightly too absolute. It is true relative to a chosen factorization 
𝐷
=
{
(
𝑛
𝑗
,
𝛽
𝑗
,
𝑚
𝑗
)
}
D={(n
j
	​

,β
j
	​

,m
j
	​

)}, but the same determinant may admit different equivalent factorizations.	Add one sentence clarifying that the dimension count is attached to the chosen Euler data 
𝐷
D, although equivalent factorizations produce unitarily equivalent normal models.
3. Missing references

At minimum, the unresolved placeholders should be replaced by the following standard sources. Hennion-Hervé fits the cited “Chapters I and IV” material on quasi-compact perturbation and limit theorems. Keller-Liverani fits the cited “Theorem 1 and Corollary 1” on spectral stability. Parry fits the cited cocycle criterion. 
Springer
+2
Numdam
+2

A notable additional omission is Keller’s 1989 paper on Markov extensions, zeta functions, and Fredholm theory, which is directly relevant to the paper’s Fredholm-determinant framing of symbolic zeta functions. If the manuscript keeps its determinant-regularity discussion as more than a purely finite-dimensional remark, Jézéquel’s work on parameter regularity of dynamical determinants should also be acknowledged. 
AMS
+1

Concretely, I would add:

H. Hennion and L. Hervé, Limit Theorems for Markov Chains and Stochastic Properties of Dynamical Systems by Quasi-Compactness, LNM 1766, Springer, 2001. 
Springer

G. Keller and C. Liverani, Stability of the spectrum for transfer operators, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 28 (1999), 141-152. 
Numdam

W. Parry, A cocycle equation for shifts, in Symbolic Dynamics and its Applications, Contemp. Math. 135, AMS, 1992, pp. 327-333. 
AMS
+1

G. Keller, Markov extensions, zeta functions, and Fredholm theory for piecewise invertible dynamical systems, Trans. Amer. Math. Soc. 314 (1989), 433-497. 
AMS

M. Jézéquel, Parameter regularity of dynamical determinants of expanding maps of the circle and an application to linear response, arXiv:1708.01055. 
arXiv

4. Specific improvements needed to reach acceptance

First, Section 4 must be reformulated correctly. As written, it is not enough to say “holomorphic family of primitive matrices” and then differentiate 
𝜌
(
𝐴
𝜃
)
ρ(A
θ
	​

). The section must instead be written for a holomorphic family together with a holomorphic simple eigenvalue branch separated from the rest of the spectrum, and the finite-part quantity must be redefined algebraically in that setting. Only after that should the paper specialize back to primitive symbolic matrices on the real slice. 

main

Second, the connective determinant statements in Section 3 need sharper analytic bookkeeping. Proposition 3.1 should be weakened to a local statement near 
𝑧
=
0
z=0, or its branch choices should be made explicit, and Theorem 3.3 should include a trace-norm truncation argument for the countable direct sum. These are fixable, but they should not be left implicit in the main theorem of the paper. 

main

Third, the literature review needs to be completed and made credible. The unresolved placeholders are not cosmetic. They prevent the reader from checking exactly which standard results are being imported into Section 4. The paper also needs a clearer boundary between what is genuinely new and what is classical packaging. 

main

Fourth, the manuscript should probably be shortened. In its current form, Section 4 dilutes the only original result. A stronger version would be a shorter note centered on Theorem 3.3, with only the cleanest corrected application retained in the main text and the remainder moved to an appendix. 

main

5. Concrete fixes for every BLOCKER and MEDIUM issue
B1. Replace 
𝜆
(
𝜃
)
=
𝜌
(
𝐴
𝜃
)
λ(θ)=ρ(A
θ
	​

) by an analytic eigenvalue branch

Use the following hypothesis everywhere in Section 4:

Let 
𝜃
↦
𝐴
(
𝜃
)
θ↦A(θ) be holomorphic near 
𝜃
0
θ
0
	​

. Assume 
𝐴
(
𝜃
0
)
A(θ
0
	​

) has a simple eigenvalue 
𝜆
0
≠
0
λ
0
	​


=0 such that

∣
𝜇
∣
<
∣
𝜆
0
∣
for every 
𝜇
∈
spec
⁡
(
𝐴
(
𝜃
0
)
)
∖
{
𝜆
0
}
.
∣μ∣<∣λ
0
	​

∣for every μ∈spec(A(θ
0
	​

))∖{λ
0
	​

}.

Then, after shrinking to a simply connected neighborhood 
𝑈
U, there exist holomorphic maps 
𝜃
↦
𝜆
(
𝜃
)
θ↦λ(θ) and 
𝜃
↦
𝑃
(
𝜃
)
θ↦P(θ) with

𝑃
(
𝜃
)
=
1
2
𝜋
𝑖
∫
∣
𝑧
−
𝜆
0
∣
=
𝛿
(
𝑧
𝐼
−
𝐴
(
𝜃
)
)
−
1
 
𝑑
𝑧
,
P(θ)=
2πi
1
	​

∫
∣z−λ
0
	​

∣=δ
	​

(zI−A(θ))
−1
dz,
𝐴
(
𝜃
)
𝑃
(
𝜃
)
=
𝜆
(
𝜃
)
𝑃
(
𝜃
)
,
sup
⁡
𝜃
∈
𝑈
𝜌
 ⁣
(
𝐴
(
𝜃
)
∣
(
𝐼
−
𝑃
(
𝜃
)
)
𝐶
𝑑
)
∣
𝜆
(
𝜃
)
∣
<
𝑞
<
1.
A(θ)P(θ)=λ(θ)P(θ),
θ∈U
sup
	​

∣λ(θ)∣
ρ(A(θ)∣
(I−P(θ))C
d
	​

)
	​

<q<1.

Then rewrite every proposition with this 
𝜆
(
𝜃
)
λ(θ). This is not cosmetic. Example 4.14 already shows why the present notation is wrong: for

𝑀
𝑡
=
(
1
	
𝑒
𝑡


1
	
𝑒
𝑡
)
,
M
t
	​

=(
1
1
	​

e
t
e
t
	​

),

the analytic leading eigenvalue is 
1
+
𝑒
𝑡
1+e
t
, whereas 
𝜌
(
𝑀
𝑡
)
=
∣
1
+
𝑒
𝑡
∣
ρ(M
t
	​

)=∣1+e
t
∣ for complex 
𝑡
t, which is not holomorphic.

B2. Introduce an algebraic finite-part functional for general matrix families

Define, for a matrix 
𝐴
A with distinguished simple eigenvalue 
𝜆
λ and 
∣
𝜇
∣
<
∣
𝜆
∣
∣μ∣<∣λ∣ for all other eigenvalues,

𝐶
(
𝐴
,
𝜆
)
:
=
det
⁡
′
 ⁣
(
𝐼
−
𝐴
𝜆
)
−
1
,
C(A,λ):=det
′
(I−
λ
A
	​

)
−1
,
𝐹
(
𝐴
,
𝜆
)
:
=
log
⁡
𝐶
(
𝐴
,
𝜆
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
log
⁡
det
⁡
 ⁣
(
𝐼
−
𝜆
−
𝑘
𝐴
)
−
1
.
F(A,λ):=logC(A,λ)+
k≥2
∑
	​

k
μ(k)
	​

logdet(I−λ
−k
A)
−1
.

Then state the perturbative section for 
𝐶
C and 
𝐹
F, not for 
𝐶
(
𝐴
𝜃
)
C(A
θ
	​

) and 
log
⁡
𝑀
(
𝐴
𝜃
)
logM(A
θ
	​

). The corrected analogue of Proposition 4.4 is:

∂
𝜃
𝐹
(
𝐴
𝜃
,
𝜆
(
𝜃
)
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
∂
𝜃
log
⁡
det
⁡
 ⁣
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
,
∂
θ
	​

F(A
θ
	​

,λ(θ))=Tr(R
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

∂
θ
	​

logdet(I−λ(θ)
−k
A
θ
	​

)
−1
,

where 
𝑅
𝜃
=
(
𝐼
−
𝐴
𝜃
/
𝜆
(
𝜃
)
)
#
R
θ
	​

=(I−A
θ
	​

/λ(θ))
#
.

Only after this should you specialize to a real primitive symbolic matrix 
𝐴
A, where Theorem 2.4 gives

𝐹
(
𝐴
,
𝜆
)
=
log
⁡
𝑀
(
𝐴
)
.
F(A,λ)=logM(A).
M1. Correct Proposition 3.1 by restricting the analytic domain

The clean fix is to replace the current statement by:

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
exp
⁡
 ⁣
(
∑
𝑛
≥
1
𝑎
𝑛
(
𝑇
)
𝑛
𝑧
𝑛
)
=
exp
⁡
 ⁣
(
−
∑
𝑚
≥
1
𝑝
𝑚
(
𝑇
)
\Log
(
1
−
𝑧
𝑚
)
)
det(I−zT)
−1
=exp(
n≥1
∑
	​

n
a
n
	​

(T)
	​

z
n
)=exp(−
m≥1
∑
	​

p
m
	​

(T)\Log(1−z
m
))

for 
∣
𝑧
∣
<
min
⁡
(
1
,
∥
𝑇
∥
−
1
)
∣z∣<min(1,∥T∥
−1
), where 
\Log
\Log is the principal branch on the unit disc.

If you want the Witt form, say explicitly that the “Euler product” is an identity of holomorphic germs at 
0
0, or of formal power series, rather than a globally single-valued analytic identity on 
∣
𝑧
∣
<
∥
𝑇
∥
−
1
∣z∣<∥T∥
−1
. This is necessary because the exponents 
𝑝
𝑚
(
𝑇
)
p
m
	​

(T) need not be integers.

M2. Add the missing countable-direct-sum determinant argument in Theorem 3.3

Let

𝐿
𝐷
(
𝑁
)
:
=
⨁
𝑗
≤
𝑁
(
𝐶
(
𝑛
𝑗
,
𝛼
𝑗
)
⊗
𝐼
𝑚
𝑗
)
.
L
D
(N)
	​

:=
j≤N
⨁
	​

(C(n
j
	​

,α
j
	​

)⊗I
m
j
	​

	​

).

Then

∥
𝐿
𝐷
−
𝐿
𝐷
(
𝑁
)
∥
1
=
∑
𝑗
>
𝑁
𝑚
𝑗
𝑛
𝑗
∣
𝛼
𝑗
∣
→
0.
∥L
D
	​

−L
D
(N)
	​

∥
1
	​

=
j>N
∑
	​

m
j
	​

n
j
	​

∣α
j
	​

∣→0.

Use trace-norm continuity of the Fredholm determinant, for example

∣
det
⁡
(
𝐼
+
𝐾
)
−
det
⁡
(
𝐼
+
𝐿
)
∣
≤
∥
𝐾
−
𝐿
∥
1
 
exp
⁡
 ⁣
(
1
+
∥
𝐾
∥
1
+
∥
𝐿
∥
1
)
,
∣det(I+K)−det(I+L)∣≤∥K−L∥
1
	​

exp(1+∥K∥
1
	​

+∥L∥
1
	​

),

to conclude that, locally uniformly in 
𝑧
z,

det
⁡
(
𝐼
−
𝑧
𝐿
𝐷
)
=
lim
⁡
𝑁
→
∞
det
⁡
(
𝐼
−
𝑧
𝐿
𝐷
(
𝑁
)
)
.
det(I−zL
D
	​

)=
N→∞
lim
	​

det(I−zL
D
(N)
	​

).

Since each finite truncation satisfies

det
⁡
(
𝐼
−
𝑧
𝐿
𝐷
(
𝑁
)
)
−
1
=
∏
𝑗
≤
𝑁
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
det(I−zL
D
(N)
	​

)
−1
=
j≤N
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

passing to the limit gives the infinite product identity. This is the missing justification.

M3. Fix the logarithm branches in Section 4

Shrink to a simply connected neighborhood 
𝑈
U on which every 
𝐺
𝑘
(
𝜃
)
=
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
G
k
	​

(θ)=I−λ(θ)
−k
A
θ
	​

 is invertible for 
𝑘
≥
2
k≥2. Define 
Φ
𝑘
Φ
k
	​

 by choosing one base point 
𝜃
0
∈
𝑈
θ
0
	​

∈U and setting

Φ
𝑘
(
𝜃
0
)
:
=
log
⁡
det
⁡
𝐺
𝑘
(
𝜃
0
)
−
1
,
Φ
k
	​

(θ
0
	​

):=logdetG
k
	​

(θ
0
	​

)
−1
,
Φ
𝑘
(
𝜃
)
:
=
Φ
𝑘
(
𝜃
0
)
−
∫
𝜃
0
𝜃
Tr
⁡
 ⁣
(
𝐺
𝑘
(
𝜉
)
−
1
∂
𝜉
𝐺
𝑘
(
𝜉
)
)
 
𝑑
𝜉
.
Φ
k
	​

(θ):=Φ
k
	​

(θ
0
	​

)−∫
θ
0
	​

θ
	​

Tr(G
k
	​

(ξ)
−1
∂
ξ
	​

G
k
	​

(ξ))dξ.

Because 
𝑈
U is simply connected and 
det
⁡
𝐺
𝑘
≠
0
detG
k
	​


=0 on 
𝑈
U, this defines a single-valued holomorphic branch with

∂
𝜃
Φ
𝑘
(
𝜃
)
=
−
Tr
⁡
 ⁣
(
𝐺
𝑘
(
𝜃
)
−
1
∂
𝜃
𝐺
𝑘
(
𝜃
)
)
.
∂
θ
	​

Φ
k
	​

(θ)=−Tr(G
k
	​

(θ)
−1
∂
θ
	​

G
k
	​

(θ)).

Do the same for 
log
⁡
𝐶
(
𝐴
𝜃
,
𝜆
(
𝜃
)
)
logC(A
θ
	​

,λ(θ)).

M4. Make Proposition 4.7(ii) rigorous via a local spectral disc

Let 
𝜆
0
=
𝜆
𝑓
(
0
)
=
𝜆
𝑔
(
0
)
λ
0
	​

=λ
f
	​

(0)=λ
g
	​

(0) be the common simple Perron eigenvalue at 
𝑡
=
0
t=0. Choose 
𝜀
>
0
ε>0 so that the circle 
∣
𝑧
−
𝜆
0
∣
=
𝜀
∣z−λ
0
	​

∣=ε contains no other eigenvalues of 
𝑀
0
(
𝑓
)
M
0
(f)
	​

 or 
𝑀
0
(
𝑔
)
M
0
(g)
	​

. By continuity of eigenvalues, after shrinking to 
∣
𝑡
∣
<
𝛿
∣t∣<δ, each matrix family has exactly one eigenvalue inside this circle. Define

𝑃
𝑓
(
𝑡
)
=
1
2
𝜋
𝑖
∫
∣
𝑧
−
𝜆
0
∣
=
𝜀
(
𝑧
𝐼
−
𝑀
𝑡
(
𝑓
)
)
−
1
 
𝑑
𝑧
,
P
f
	​

(t)=
2πi
1
	​

∫
∣z−λ
0
	​

∣=ε
	​

(zI−M
t
(f)
	​

)
−1
dz,

and similarly 
𝑃
𝑔
(
𝑡
)
P
g
	​

(t). Then 
rank
⁡
𝑃
𝑓
(
𝑡
)
=
rank
⁡
𝑃
𝑔
(
𝑡
)
=
1
rankP
f
	​

(t)=rankP
g
	​

(t)=1, and the corresponding eigenvalues are the unique analytic branches 
𝜆
𝑓
(
𝑡
)
λ
f
	​

(t), 
𝜆
𝑔
(
𝑡
)
λ
g
	​

(t) near 
𝜆
0
λ
0
	​

.

Now apply spectral rigidity for each fixed 
𝑡
t: equality of determinants gives equality of spectral multisets, hence the unique eigenvalue inside 
∣
𝑧
−
𝜆
0
∣
<
𝜀
∣z−λ
0
	​

∣<ε must agree. Therefore

𝜆
𝑓
(
𝑡
)
=
𝜆
𝑔
(
𝑡
)
(
∣
𝑡
∣
<
𝛿
)
.
λ
f
	​

(t)=λ
g
	​

(t)(∣t∣<δ).
M5. Supply the missing existence proof for 
𝜂
𝐾
η
K
	​

 in Proposition 4.10

Before the proposition, insert:

𝑢
↦
𝑀
𝑢
𝑓
is continuous in 
𝑢
,
u↦M
u
f
	​

is continuous in u,

hence 
𝑢
↦
𝜌
(
𝑀
𝑢
𝑓
)
u↦ρ(M
u
f
	​

) is continuous because spectral radius is continuous on finite matrices. By Parry’s cocycle criterion,

𝜌
(
𝑀
𝑢
𝑓
)
=
𝜆
  
⟺
  
𝑢
∈
Λ
𝑓
.
ρ(M
u
f
	​

)=λ⟺u∈Λ
f
	​

.

Therefore, if 
𝐾
⊂
⊂
𝑅
∖
Λ
𝑓
K⊂⊂R∖Λ
f
	​

 is compact,

𝜅
𝐾
:
=
sup
⁡
𝑢
∈
𝐾
𝜌
(
𝑀
𝑢
𝑓
)
𝜆
<
1.
κ
K
	​

:=
u∈K
sup
	​

λ
ρ(M
u
f
	​

)
	​

<1.

Then one may choose explicitly

𝜂
𝐾
:
=
1
+
𝜅
𝐾
2
∈
(
𝜅
𝐾
,
1
)
.
η
K
	​

:=
2
1+κ
K
	​

	​

∈(κ
K
	​

,1).

This gives the missing constant used in the resolvent estimate.

M6. Repair the bibliography and replace every placeholder

This needs to be done explicitly in the source. The minimum repair is:

replace “[?, Chapters I and IV]” by Hennion-Hervé;

replace “[?, Theorem 1 and Corollary 1]” by Keller-Liverani;

replace “[?, Theorem 1]” in the arithmetic obstruction discussion by Parry;

add Keller 1989 to the historical paragraph on Fredholm determinants and symbolic zeta functions;

if determinant regularity remains emphasized, add Jézéquel. 
arXiv
+4
Springer
+4
Numdam
+4

6. Bottom line

The paper is salvageable, but only if it is rewritten much more tightly. My recommendation is to center the paper on the cyclic-block theorem, repair Section 3 carefully, and either substantially reformulate Section 4 along the lines above or move most of it out of the main text. In its present form I would not recommend acceptance.