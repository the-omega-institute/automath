<!-- oracle metadata: {"timestamp": "2026-04-06T13:11:45.055084", "model": "o3-mini-high", "response_length": 15786} -->

For the current uploaded manuscript “Fredholm Determinants, Cyclic-Block Realisations, and Spectral Rigidity for Symbolic 
𝜁
ζ-Functions”, my recommendation is:

1. Overall assessment

Major revision.

The paper has a genuine publishable core. The cyclic-block characterization in the normal trace-class category is the mathematically substantive contribution, and the manuscript itself identifies that theorem as the main novelty. By contrast, the Fredholm–Witt bridge and spectral rigidity are connective classical material, and the symbolic-dynamical part is presented by the paper itself as an application package built from standard perturbative and spectral-gap machinery. In its present form, however, the manuscript is not referee-ready. The two main reasons are: first, the scholarly apparatus is incomplete, with unresolved placeholders still present in the literature review and proof scaffolding; second, the theorem hierarchy is inflated, especially in Section 4, where several distinct standard consequences are bundled together at headline level rather than separated by hypothesis and proof burden. 

main

 

main

 

main

2. Novelty rating for each theorem

I rate the theorem-level claims that are explicitly identifiable in the current draft.

Result	Novelty	One-line justification
Proposition 1.1 / Fredholm–Witt bridge	LOW	This is classical trace-class determinant technology, included as connective background.
Theorem 3.3 / Cyclic-block characterization and optimality	HIGH	This is the paper’s genuine new core: an exact normal trace-class realizability criterion with forced cyclic geometry.
Theorem 3.5 / Trace-norm rigidity and support optimality	MEDIUM	Valuable sharpening inside the normal category, but conceptually it is a close corollary of the cyclic-block realization theorem.
Theorem 3.9 / Spectral rigidity of Fredholm determinants	LOW	This is a standard consequence of the classical zero set description of trace-class Fredholm determinants.
Theorem 4.2 / Holomorphic variation of the Abel finite part	LOW	Useful and explicit, but essentially an application of standard analytic perturbation plus determinant calculus.
Section 4 CLT / off-origin decay application package	LOW	The manuscript itself treats this as standard spectral-gap machinery reorganized by the determinant formalism, not as further structural novelty.

These ratings follow the manuscript’s own novelty framing, which singles out the strengthened cyclic-block theorem and treats the symbolic section as application rather than a second source of new theory. 

main

 

main

 

main

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§1.2 and throughout	BLOCKER	The bibliography is incomplete: unresolved placeholder citations remain in core background and proof-signposting, including the transfer-operator stability reference, the missing finite-dimensional perturbation source, and the citation for Parry’s cocycle theorem.	Replace every placeholder with a full bibliographic item and theorem-level pinpoint citation.
B2	§4 and Theorem 1.4 / 4.2	BLOCKER	The Section 4 application package is over-bundled. Holomorphic variation of 
𝐶
(
𝐴
𝜃
)
C(A
θ
	​

) and 
𝑀
(
𝐴
𝜃
)
M(A
θ
	​

), periodic-orbit moment recovery, cumulants, CLT, and off-origin characteristic-function decay are logically distinct statements with different hypotheses, but they are advertised together at headline level.	Split Section 4 into separate propositions/theorems, each with explicit hypotheses and proof boundaries.
M1	Introduction and §5	MEDIUM	The novelty framing is too broad relative to the manuscript’s own later caveat that the symbolic section is only an application of standard perturbative and spectral-gap methods.	Rewrite the introduction around three layers: classical bridge, new cyclic-block theorem, standard symbolic applications.
M2	§3	MEDIUM	The theorem hierarchy is poorly calibrated. Theorem 3.5 is essentially a consequence of Theorem 3.3, and Theorem 3.9 is classical background. Presenting them on the same level obscures the paper’s true contribution.	Demote Theorem 3.5 to a corollary and Theorem 3.9 to a proposition/background theorem.
M3	§4.2–§4.4	MEDIUM	The off-origin decay statement is not presented in the sharp operator form actually used. The non-lattice / non-coboundary hypothesis and the spectral-radius gap on twisted matrices should be stated explicitly.	State the decay result as a spectral-radius inequality for 
𝑀
𝑖
𝑢
M
iu
	​

 on compact sets away from the lattice obstruction.
M4	§4.1–§4.4	MEDIUM	The proof architecture for the Abel finite-part variation is too diffuse. The normal-convergence and truncation estimates are mathematically important but are not isolated early enough as a reusable lemma.	Insert a standalone normal-convergence/truncation proposition before the main derivative formula.
L1	§4.5	LOW	The comparison with classical finite-dimensional perturbation theory is rhetorically extended beyond its mathematical necessity.	Compress it substantially or move part of it to the discussion.
L2	§4 examples	LOW	The golden-mean and full two-shift computations are helpful but underused. They illustrate formulas but do not clarify the limitations of the theory.	Add a sentence explaining exactly what these examples validate and what they do not.

The placeholders and the paper’s own internal novelty caveat are both visible in the current draft. 

main

 

main

 

main

4. Missing references

The most urgent missing references are the ones the manuscript already signals but does not complete.

A precise source replacing the placeholder after “Ruelle and Baladi” for transfer-operator spectral stability.

A precise source replacing the placeholder in the phrase “the standard finite-dimensional framework described in [Rue78, Bal00, ?, Kat95]”.

A precise citation, with theorem number, for the finite-state Livšic / cocycle criterion currently referred to as “Parry’s cocycle theorem [?]”.

If the author wants the off-origin decay result to be read as standard, a specific reference for the non-lattice criterion in the finite-state symbolic setting should be inserted exactly where it is used. 

main

 

main

I do not see a need for a large expansion of the bibliography beyond this. The core classical references, such as Bowen–Lanford, Manning, Grothendieck, Simon, Kato, Ruelle, Pollicott, Nagaev, and Guivarc’h–Hardy, are already part of the intended framework. The problem is that several crucial items are still missing in the actual draft. 

main

5. Specific improvements needed to reach acceptance

Five changes are needed.

First, complete the bibliography and eliminate every placeholder.

Second, restructure the theorem hierarchy so that Theorem 3.3 is unmistakably the central new result, while the classical bridge, spectral rigidity, and Section 4 applications are presented with their proper logical status.

Third, split Section 4 into mathematically separate results. In the current form, the reader has to reconstruct which assumptions yield which conclusion.

Fourth, state the off-origin decay theorem in exact operator terms, not just as prose about a “standard finite-state aperiodicity hypothesis”.

Fifth, rewrite the introduction so that it no longer overstates the novelty of the symbolic-dynamical package. The manuscript itself already says the Section 4 material is application-level. The introduction should match that. 

main

 

main

6. Concrete fixes
B1. Complete the bibliography and remove all placeholders

This is mandatory.

A minimally acceptable repair is:

replace every ? in §1.2 by a real citation;

add theorem-level pinpoints for the external tools that are actually invoked;

keep the bibliography aligned with the actual claims rather than broadening it indiscriminately.

The following edits are needed.

Replace

“Ruelle and Baladi [?, Rue78, Bal00]”
“Ruelle and Baladi [?, Rue78, Bal00]”

by a concrete stability reference if spectral stability beyond the basic perturbative framework is being used.

Replace

“[Rue78, Bal00, ?, Kat95]”
“[Rue78, Bal00, ?, Kat95]”

by a complete finite-dimensional perturbation or symbolic spectral-gap reference.

Replace

“Parry’s cocycle theorem [?]”
“Parry’s cocycle theorem [?]”

by an exact Livšic-type theorem in the finite-state symbolic setting, with theorem number.

Where Simon’s theorem is used for spectral rigidity, cite the exact theorem number already mentioned in the prose. That part is already basically in place; it just needs consistency throughout. 

main

 

main

B2. Split Section 4 into separate theorem blocks with explicit mathematics

The current Section 4 can be repaired by replacing the broad application theorem with three precise statements.

Proposed replacement theorem structure

Proposition 4.2A.
Let 
𝜃
↦
𝐴
𝜃
θ↦A
θ
	​

 be holomorphic near 
𝜃
0
θ
0
	​

, with simple Perron root 
𝜆
(
𝜃
)
λ(θ), and define

𝐺
𝑘
(
𝜃
)
:
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
,
𝑘
≥
2.
G
k
	​

(θ):=I−λ(θ)
−k
A
θ
	​

,k≥2.

Then on a neighborhood 
𝑈
U of 
𝜃
0
θ
0
	​

 there exist constants 
𝐶
𝑈
>
0
C
U
	​

>0 and 
𝑞
𝑈
∈
(
0
,
1
)
q
U
	​

∈(0,1) such that

sup
⁡
𝜃
∈
𝑈
∣
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
∣
+
sup
⁡
𝜃
∈
𝑈
∣
∂
𝜃
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
∣
≤
𝐶
𝑈
 
𝑘
 
𝑞
𝑈
𝑘
.
θ∈U
sup
	​

	​

logdetG
k
	​

(θ)
−1
	​

+
θ∈U
sup
	​

	​

∂
θ
	​

logdetG
k
	​

(θ)
−1
	​

≤C
U
	​

kq
U
k
	​

.

Hence

log
⁡
𝑀
(
𝐴
𝜃
)
=
log
⁡
𝐶
(
𝐴
𝜃
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
𝐺
𝑘
(
𝜃
)
−
1
logM(A
θ
	​

)=logC(A
θ
	​

)+
k≥2
∑
	​

k
μ(k)
	​

logdetG
k
	​

(θ)
−1

converges normally, and termwise differentiation is justified. This is the estimate already underlying the truncation scheme. 

main

Actionable proof sketch.
Choose 
𝑈
U so that 
𝜆
(
𝜃
)
λ(θ) stays simple and

sup
⁡
𝜃
∈
𝑈
𝜌
 ⁣
(
𝜆
(
𝜃
)
−
1
𝐴
𝜃
∣
(
𝐼
−
𝑃
𝜃
)
𝐶
𝑑
)
≤
𝑞
𝑈
<
1.
θ∈U
sup
	​

ρ(λ(θ)
−1
A
θ
	​

	​

(I−P
θ
	​

)C
d
	​

)≤q
U
	​

<1.

Then 
𝐺
𝑘
(
𝜃
)
G
k
	​

(θ) is invertible for 
𝑘
≥
2
k≥2, and the Neumann series gives

sup
⁡
𝜃
∈
𝑈
∥
𝐺
𝑘
(
𝜃
)
−
1
∥
≤
1
1
−
𝑞
𝑈
2
.
θ∈U
sup
	​

∥G
k
	​

(θ)
−1
∥≤
1−q
U
2
	​

1
	​

.

From

log
⁡
det
⁡
(
𝐼
−
𝑋
)
−
1
=
∑
𝑚
≥
1
Tr
⁡
(
𝑋
𝑚
)
𝑚
logdet(I−X)
−1
=
m≥1
∑
	​

m
Tr(X
m
)
	​


for 
∥
𝑋
∥
<
1
∥X∥<1, one obtains the geometric bound on 
Φ
𝑘
(
𝜃
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
)
−
1
Φ
k
	​

(θ):=logdetG
k
	​

(θ)
−1
, and Jacobi’s formula yields the derivative estimate.

Proposition 4.2B.
For a locally constant observable 
𝑓
f with twisted matrices 
𝑀
𝑡
M
t
	​

,

log
⁡
det
⁡
(
𝐼
−
𝑧
𝑀
𝑡
)
−
1
=
∑
𝑛
≥
1
𝑧
𝑛
𝑛
Tr
⁡
(
𝑀
𝑡
𝑛
)
,
logdet(I−zM
t
	​

)
−1
=
n≥1
∑
	​

n
z
n
	​

Tr(M
t
n
	​

),

and differentiation at 
𝑡
=
0
t=0 gives

∂
𝑡
𝑟
Tr
⁡
(
𝑀
𝑡
𝑛
)
∣
𝑡
=
0
=
∑
𝑥
∈
F
i
x
(
𝜎
𝑛
)
(
𝑆
𝑛
𝑓
(
𝑥
)
)
𝑟
.
∂
t
r
	​

Tr(M
t
n
	​

)
	​

t=0
	​

=
x∈Fix(σ
n
)
∑
	​

(S
n
	​

f(x))
r
.

Thus the twisted determinant determines every periodic-orbit moment sum.

Proposition 4.2C.
If 
𝑓
ˉ
=
𝑓
−
∫
𝑓
 
𝑑
𝜇
f
ˉ
	​

=f−∫fdμ is not a coboundary modulo constants and

𝜂
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
𝑖
𝑢
)
𝜆
(
0
)
<
1
η
K
	​

:=
u∈K
sup
	​

λ(0)
ρ(M
iu
	​

)
	​

<1

for a compact set 
𝐾
⊂
𝑅
∖
Λ
𝑓
K⊂R∖Λ
f
	​

, where 
Λ
𝑓
Λ
f
	​

 is the arithmetic lattice obstruction, then

sup
⁡
𝑢
∈
𝐾
∣
∫
𝑒
𝑖
𝑢
∑
𝑗
=
0
𝑛
−
1
𝑓
ˉ
∘
𝜎
𝑗
 
𝑑
𝜇
∣
≤
𝐶
𝐾
𝜂
𝐾
𝑛
.
u∈K
sup
	​

	​

∫e
iu∑
j=0
n−1
	​

f
ˉ
	​

∘σ
j
dμ
	​

≤C
K
	​

η
K
n
	​

.

This is the exact form of the claimed off-origin decay. It should be stated explicitly. The arithmetic example in the full two-shift already illustrates the lattice obstruction at 
2
𝜋
𝑍
2πZ. 

main

This three-step structure would make Section 4 verifiable and would align the claims with the proofs.

M1. Rewrite the introduction so the contribution is not overstated

The introduction should explicitly separate:

the classical Fredholm–Witt bridge;

the genuinely new cyclic-block realization theorem;

the standard symbolic-dynamical application package.

A mathematically accurate replacement paragraph would be:

“The paper contains one genuinely new structural theorem: the exact normal trace-class realizability and support-optimality criterion for Euler products of cyclic-block type. The Fredholm–Witt bridge and spectral rigidity are classical connective results included for completeness, and the symbolic-dynamical formulas in Section 4 are determinant-level reorganizations of standard perturbative and spectral-gap consequences.”

That wording matches the manuscript’s own statement that the Section 4 material is application-level rather than additional structural novelty. 

main

 

main

M2. Recalibrate the theorem hierarchy around Theorem 3.3

Theorem 3.5 should be demoted to a corollary, because it follows immediately once the realization in Theorem 3.3 has been identified.

The proof is simply:

dim
⁡
ran
⁡
(
𝐿
)
=
∑
𝑗
∈
𝐽
𝑚
𝑗
𝑛
𝑗
,
∥
𝐿
∥
1
=
∑
𝑗
∈
𝐽
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
,
dimran(L)=
j∈J
∑
	​

m
j
	​

n
j
	​

,∥L∥
1
	​

=
j∈J
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

,

since each block 
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
C(n
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

 contributes the singular value 
∣
𝛼
𝑗
∣
=
∣
𝛽
𝑗
∣
1
/
𝑛
𝑗
∣α
j
	​

∣=∣β
j
	​

∣
1/n
j
	​

 with multiplicity 
𝑚
𝑗
𝑛
𝑗
m
j
	​

n
j
	​

. This is a corollary-sized consequence of the block model, not an independent theorem. 

main

Likewise, spectral rigidity should be labeled as classical background. Its content is important, but it is not a new theorem of the paper. 

main

M3. State the off-origin decay criterion in exact spectral terms

The current prose relies on an unstated exact criterion. The paper should insert the following proposition.

Proposition. Let 
𝑓
f be locally constant on a mixing SFT, let 
𝑀
𝑡
M
t
	​

 be the twisted matrix family, and let 
𝐾
⋐
𝑅
∖
Λ
𝑓
K⋐R∖Λ
f
	​

, where 
Λ
𝑓
Λ
f
	​

 is the arithmetic lattice of 
𝑓
f. If

𝜂
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
𝑖
𝑢
)
𝜆
(
0
)
<
1
,
η
K
	​

:=
u∈K
sup
	​

λ(0)
ρ(M
iu
	​

)
	​

<1,

then

sup
⁡
𝑢
∈
𝐾
∣
∫
𝑒
𝑖
𝑢
∑
𝑗
=
0
𝑛
−
1
𝑓
ˉ
∘
𝜎
𝑗
 
𝑑
𝜇
∣
≤
𝐶
𝐾
𝜂
𝐾
𝑛
.
u∈K
sup
	​

	​

∫e
iu∑
j=0
n−1
	​

f
ˉ
	​

∘σ
j
dμ
	​

≤C
K
	​

η
K
n
	​

.

Proof sketch.
Write the centered characteristic function in the Parry measure as

𝜆
(
0
)
−
𝑛
 
ℓ
0
𝑇
𝑀
𝑖
𝑢
𝑛
𝑟
0
,
λ(0)
−n
ℓ
0
T
	​

M
iu
n
	​

r
0
	​

,

up to uniformly bounded spectral projectors. Quasi-compactness and the strict spectral-radius gap on 
𝐾
K give

∥
𝑀
𝑖
𝑢
𝑛
∥
≤
𝐶
𝐾
(
𝜂
𝐾
𝜆
(
0
)
)
𝑛
,
∥M
iu
n
	​

∥≤C
K
	​

(η
K
	​

λ(0))
n
,

uniformly in 
𝑢
∈
𝐾
u∈K. Dividing by 
𝜆
(
0
)
𝑛
λ(0)
n
 yields the bound.

That is the operator-theoretic statement the prose is presently gesturing toward. It should appear explicitly.

M4. Isolate the truncation scheme as a proposition, not just a passing estimate

The manuscript already contains the ingredients for a useful numerical proposition:

log
⁡
𝑀
𝑁
(
𝐴
𝜃
)
=
log
⁡
𝐶
(
𝐴
𝜃
)
+
∑
2
≤
𝑘
≤
𝑁
𝜇
(
𝑘
)
𝑘
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
logM
N
	​

(A
θ
	​

)=logC(A
θ
	​

)+
2≤k≤N
∑
	​

k
μ(k)
	​

logdet(I−λ(θ)
−k
A
θ
	​

)
−1
.

A clear proposition should state that

sup
⁡
𝜃
∈
𝑈
∣
log
⁡
𝑀
(
𝐴
𝜃
)
−
log
⁡
𝑀
𝑁
(
𝐴
𝜃
)
∣
≤
𝐶
𝑈
𝑞
𝑈
𝑁
+
1
,
θ∈U
sup
	​

∣logM(A
θ
	​

)−logM
N
	​

(A
θ
	​

)∣≤C
U
	​

q
U
N+1
	​

,

and the same after one 
𝜃
θ-derivative. This is already present mathematically, but it should be promoted and highlighted as a standalone numerical consequence. 

main

That change would make the computational content of the paper sharper and easier to cite.

In summary, I would not recommend acceptance in the present form, but I would encourage revision. The manuscript has one strong and potentially publishable new theorem. What it lacks is editorial and expository discipline: the references are incomplete, the theorem hierarchy is inflated, and the Section 4 application package is not yet written in a referee-efficient way. Once those issues are repaired, the paper’s actual contribution should be much easier to assess and, in my view, substantially stronger.