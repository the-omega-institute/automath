<!-- oracle metadata: {"timestamp": "2026-04-07T00:01:41.672209", "model": "o3-mini-high", "response_length": 14961} -->

Overall assessment: Major revision

The paper contains a genuinely interesting combinatorial core, centered on the affine transfer and partition-difference identity, and that core looks potentially publishable. However, the submission is not yet journal-ready. The proof of the finite-state spectral realization is incomplete at a crucial point, and the entire arithmetic window in Section 7 rests on computational certificates that are not reproduced in a form that permits independent verification from the manuscript itself. In its present form, I would not recommend acceptance. I would encourage resubmission after a substantial rewrite, or alternatively after splitting the paper into a rigorous core paper and a separate computational companion. 

main

For the novelty ratings below, I am treating the automaton and Perron-Frobenius realization claims conservatively, because Sanna already gives an automata-theoretic proof of the existence of the constants 
𝜆
𝑝
λ
p
	​

, an effective algorithm to compute them, a strongly connected accessible automaton whose transition matrix has Perron root 
𝜆
𝑝
λ
p
	​

, and even a minimized automaton with 
2
𝑝
+
1
2p+1 states. 
arXiv
+2
arXiv
+2

Novelty rating for each theorem
Theorem	Rating	One-line justification
3.1	LOW	This is essentially the residue characterization already encoded in the definition of 
F
o
l
d
𝑚
Fold
m
	​

.
3.2	LOW	Standard root-of-unity filtering and orthogonality.
3.6	HIGH	The explicit affine permutation linking finite-window fibers to ordinary Fibonacci subset sums is the first genuinely distinctive structural step.
3.9	HIGH	This is the paper’s main new identity, and it is the real mathematical bridge to the classical partition function.
4.2	LOW	Immediate repackaging of 3.9 at the level of moments.
4.3	MEDIUM	The Fibonacci-window sandwich is a clean and useful consequence that seems new in this form.
4.4	MEDIUM	The transfer of 
𝜆
𝑞
λ
q
	​

 from partition moments to fold moments is useful, but mostly formal once 4.3 and Sanna are available.
4.9	MEDIUM	The explicit cubic recurrence for the quadratic fold energy is concrete and worthwhile.
4.11	MEDIUM	The alternating second-order term is a nice explicit spectral refinement.
5.2	LOW	A finite automaton/Perron realization of 
𝜆
𝑞
λ
q
	​

 is largely anticipated by Sanna’s automata-theoretic construction.
5.3	LOW	Symmetry compression is natural, and not stronger than the linear-size minimization already noted by Sanna.
5.7	LOW	Discrete convexity from Hölder is standard.
5.11	MEDIUM	The “canonical band” interpretation is appealing, though the proof is a short exponential-tilting estimate.
5.12	MEDIUM	Useful quantitative corollary of 5.11, but not conceptually deep beyond it.
5.14	MEDIUM	The largest-fiber growth law appears new for this fold model.
5.15	MEDIUM	New diagonal high-moment asymptotic, albeit a short consequence of 5.14.
5.16	MEDIUM	New endpoint concentration statement, but largely formal from 5.14 and 5.15.
6.3	LOW	Rényi entropy rates follow routinely once 
𝑆
𝑞
(
𝑚
)
S
q
	​

(m) is known exponentially.
7.2	MEDIUM	Interesting arithmetic statement, but presently computational rather than conceptually developed.
7.7	MEDIUM	Full symmetric Galois groups in the window 
𝑞
=
9
,
…
,
17
q=9,…,17 would be new if fully certified.
7.10	MEDIUM	Linear disjointness and product Chebotarev densities in the four-parameter window are new if rigorously certified.
Issue table
ID	Section	Severity	Description	Suggested fix
I1	5.1, Thm. 5.2	BLOCKER	The passage from 
𝑆
𝑞
(
𝑚
)
=
𝑢
𝑞
𝑇
𝐴
𝑞
𝑚
𝑣
𝑞
S
q
	​

(m)=u
q
T
	​

A
q
m
	​

v
q
	​

 to 
lim
⁡
𝑚
−
1
log
⁡
𝑆
𝑞
(
𝑚
)
=
log
⁡
𝜌
(
𝐴
𝑞
)
limm
−1
logS
q
	​

(m)=logρ(A
q
	​

) is not justified. Perron-Frobenius does not give this for an arbitrary nonnegative matrix with boundary vectors unless one trims to the relevant SCCs, or proves strong connectivity/accessibility.	Replace 
𝐴
𝑞
A
q
	​

 by a trimmed accessible/coaccessible matrix, or prove the trimmed automaton is strongly connected and aperiodic.
I2	7.1, Thm. 7.2	BLOCKER	The claim 
r
a
n
k
 
𝐻
𝑞
=
𝑑
𝑞
rankH
q
	​

=d
q
	​

 is asserted, not proved. “The chosen range is one in which this rank is already attained” is a computational assertion masquerading as proof.	Give an explicit nonzero 
𝑑
𝑞
×
𝑑
𝑞
d
q
	​

×d
q
	​

 minor, or provide a rigorous exact-rank certificate for each 
𝑞
q.
I3	7 and App. B	BLOCKER	The arithmetic results depend on private computational certificates. Table 4 records only the Smith normal form diagonals, not the matrices whose SNF is being used.	Publish full supplementary data, exact matrices, and verifiable code, or remove Section 7 from the formal theorem chain.
I4	7.1	MEDIUM	The notation 
𝑃
𝑞
P
q
	​

 is overloaded: earlier it denotes pressure 
log
⁡
𝜆
𝑞
logλ
q
	​

, later it denotes a recurrence polynomial. Definition 7.1 is also conceptually muddy.	Use distinct symbols, e.g. 
𝑃
𝑞
P
q
	​

 for pressure and 
𝑀
𝑞
(
𝑋
)
M
q
	​

(X) for the recurrence polynomial, and define 
𝑀
𝑞
M
q
	​

 as the minimal recurrence polynomial of 
𝑆
𝑞
(
𝑚
)
S
q
	​

(m).
I5	App. A	MEDIUM	Proposition A.5 is too sketchy. The invariant relating committed blocks, residual suffixes, and final output equality is not formalized.	Add a precise inductive state invariant and explicit update map proving accepted synchronized runs are exactly common-fold tuples.
I6	Intro, 5.1	MEDIUM	Theorem C is presented with insufficient attribution. Its automaton/Perron aspect overlaps substantially with Sanna’s prior automata-theoretic realization.	Reframe the claim as an alternative fold-side realization and cite the prior automata literature explicitly.
I7	7.2, 7.3	MEDIUM	The Frobenius-cycle arguments rely on unramified primes, but the proof does not explicitly say 
𝑝
∤
D
i
s
c
(
𝑀
𝑞
)
p∤Disc(M
q
	​

). The linear-disjointness proof also skips one subgroup-theoretic implication.	State the unramified condition explicitly, and explain why 
𝐿
𝑞
⊆
𝑀
𝑞
L
q
	​

⊆M
q
	​

 would force the discriminant quadratic subfield into 
𝑀
𝑞
M
q
	​

.
I8	7, Table 3	MEDIUM	The recurrence polynomials are not written explicitly, only their recurrence coefficients. This obstructs independent checking of irreducibility, discriminants, and mod-
𝑝
p factorization.	Write 
𝑀
𝑞
(
𝑋
)
=
𝑋
𝑑
𝑞
−
∑
𝑖
=
1
𝑑
𝑞
𝑐
𝑞
,
𝑖
𝑋
𝑑
𝑞
−
𝑖
M
q
	​

(X)=X
d
q
	​

−∑
i=1
d
q
	​

	​

c
q,i
	​

X
d
q
	​

−i
 explicitly for each 
𝑞
q.
I9	2.2	LOW	The split-epimorphism/reﬂector formalism is not used later and distracts from the theorem chain.	Remove it, or connect it directly to the entropy section.
I10	Throughout	LOW	The paper overuses thermodynamic and arithmetic rhetoric for results that are often straightforward moment inequalities or computational certificates.	Simplify terminology and compress corollaries into a tighter theorem chain.
Missing references

Several important references are absent and should be added.

First, the classical Fibonacci-partition literature is under-cited. In particular, the foundational papers of Klarner, and the classical Carlitz paper, are standard background for any paper that positions itself as a structural advance on 
𝑅
(
𝑛
)
R(n). Chow and Slattery themselves cite Hoggatt-Basin (1963), Klarner (1966, 1968), and Carlitz (1968) as part of that lineage. 
wrap.warwick.ac.uk
+2
wrap.warwick.ac.uk
+2

Second, the automata-theoretic background is incomplete. Berstel’s “An exercise on Fibonacci representations” is directly relevant to normalization/counting in Fibonacci numeration, and Shallit’s “Robbins and Ardila meet Berstel” is specifically about automata methods for Fibonacci partitions. 
eudml.org
+1

Third, for the transducer machinery, Frougny’s 1988 paper on linear numeration systems of order two, and Ahlbach-Usatine-Pippenger on efficient Zeckendorf arithmetic, are relevant context beyond the two Frougny citations already present. 
ScienceDirect
+1

Fourth, Kempton’s recent dynamical study of the Fibonacci partition function is clearly relevant to the paper’s “discrete thermodynamics” framing and to its discussion of partition-function irregularity. 
arXiv

Specific improvements needed to reach acceptance

The paper would move much closer to acceptance if the authors do five things.

Repair Theorem 5.2 rigorously, by trimming the automaton to the relevant SCCs or proving the trimmed graph is strongly connected.

Rebuild Section 7 so that every arithmetic claim is independently verifiable from the manuscript and its supplement, rather than from undocumented internal scripts.

Reposition Theorem C relative to Sanna’s prior automaton construction, and explicitly isolate what is genuinely new here.

Clean up notation and structure, especially the 
𝑃
𝑞
P
q
	​

 overloading and the ad hoc entry to Section 7.

Either motivate the categorical material in Section 2.2 by later use, or remove it.

Concrete fixes for each BLOCKER and MEDIUM issue

I1. Fix to Theorem 5.2.
Let 
𝐺
𝑞
G
q
	​

 be the digraph of the automaton from Proposition A.5. Delete every state not reachable from the initial synchronized state, and every state from which no accepting terminal state can be reached. Call the resulting adjacency matrix 
𝐴
𝑞
t
r
A
q
tr
	​

. Then

𝑆
𝑞
(
𝑚
)
=
𝑢
𝑞
𝑇
(
𝐴
𝑞
t
r
)
𝑚
𝑣
𝑞
.
S
q
	​

(m)=u
q
T
	​

(A
q
tr
	​

)
m
v
q
	​

.

Put 
𝐴
𝑞
t
r
A
q
tr
	​

 into Frobenius normal form. If 
𝐶
C is the set of SCCs lying on some path from 
supp
⁡
(
𝑢
𝑞
)
supp(u
q
	​

) to 
supp
⁡
(
𝑣
𝑞
)
supp(v
q
	​

), then standard path decomposition gives

lim
⁡
𝑚
→
∞
1
𝑚
log
⁡
𝑆
𝑞
(
𝑚
)
=
log
⁡
(
max
⁡
𝐶
∈
𝐶
𝜌
(
𝐶
)
)
.
m→∞
lim
	​

m
1
	​

logS
q
	​

(m)=log(
C∈C
max
	​

ρ(C)).

If the authors can show the trimmed graph is strongly connected, this simplifies to 
log
⁡
𝜌
(
𝐴
𝑞
t
r
)
logρ(A
q
tr
	​

). If not, they should define 
𝑟
𝑞
r
q
	​

 as the maximum SCC spectral radius and use that consistently. This also aligns the proof strategy with Sanna’s accessible strongly connected automata. 

main

 
arXiv
+1

I2. Fix to the Hankel-rank assertion in Theorem 7.2.
Write the minimal recurrence polynomial as

𝑀
𝑞
(
𝑋
)
=
𝑋
𝑑
𝑞
−
∑
𝑖
=
1
𝑑
𝑞
𝑐
𝑞
,
𝑖
𝑋
𝑑
𝑞
−
𝑖
.
M
q
	​

(X)=X
d
q
	​

−
i=1
∑
d
q
	​

	​

c
q,i
	​

X
d
q
	​

−i
.

Then every Hankel row 
𝑟
𝑛
=
(
𝑆
𝑞
(
𝑛
+
𝑗
+
2
)
)
0
≤
𝑗
<
𝑛
𝑞
r
n
	​

=(S
q
	​

(n+j+2))
0≤j<n
q
	​

	​

 satisfies

𝑟
𝑛
+
𝑑
𝑞
=
∑
𝑖
=
1
𝑑
𝑞
𝑐
𝑞
,
𝑖
 
𝑟
𝑛
+
𝑑
𝑞
−
𝑖
,
r
n+d
q
	​

	​

=
i=1
∑
d
q
	​

	​

c
q,i
	​

r
n+d
q
	​

−i
	​

,

so 
rank
⁡
𝐻
𝑞
≤
𝑑
𝑞
rankH
q
	​

≤d
q
	​

. To prove equality, it is enough to exhibit one exact 
𝑑
𝑞
×
𝑑
𝑞
d
q
	​

×d
q
	​

 minor of 
𝐻
𝑞
H
q
	​

 with nonzero determinant. This can be done either by printing the minor and its determinant, or by giving a certified exact LU decomposition over 
𝑍
Z. Until that is supplied, the theorem is not proved. 

main

I3. Fix to the computational certification architecture.
For each 
𝑞
=
9
,
…
,
17
q=9,…,17, the supplement should contain: the exact initial segment of 
𝑆
𝑞
(
𝑚
)
S
q
	​

(m) used to infer the recurrence, the explicit polynomial 
𝑀
𝑞
(
𝑋
)
M
q
	​

(X), the Hankel matrix 
𝐻
𝑞
H
q
	​

, a 
𝑍
Z-basis matrix 
𝑁
𝑞
N
q
	​

 for 
N
u
l
l
M
o
d
e
s
(
𝑞
)
NullModes(q), the truncated-multiple matrix 
𝐵
𝑞
B
q
	​

, and an explicit unimodular matrix 
𝑈
𝑞
∈
G
L
𝜅
𝑞
(
𝑍
)
U
q
	​

∈GL
κ
q
	​

	​

(Z) such that 
𝑁
𝑞
𝑈
𝑞
=
𝐵
𝑞
N
q
	​

U
q
	​

=B
q
	​

, or equivalently a full SNF decomposition of the change-of-basis matrix. For Tables 1 and 2, the supplement should also include discriminants and exact mod-
𝑝
p factorization output. Without such data, the arithmetic section is not reproducible. 

main

I4. Fix to the notation and definition in Section 7.
Rename the pressure sequence as 
𝑃
𝑞
:
=
log
⁡
𝜆
𝑞
P
q
	​

:=logλ
q
	​

 throughout Section 5, and reserve 
𝑀
𝑞
(
𝑋
)
M
q
	​

(X) for the minimal recurrence polynomial in Section 7. Then Definition 7.1 should read: “
𝑀
𝑞
(
𝑋
)
M
q
	​

(X) is the unique monic polynomial of least degree such that 
𝑀
𝑞
(
𝐸
)
𝑆
𝑞
(
𝑚
)
=
0
M
q
	​

(E)S
q
	​

(m)=0 for all sufficiently large 
𝑚
m.” This removes the present ambiguity between pressure and polynomial, and avoids the unclear phrase “minimal polynomial of the companion matrix of the linear recurrence.” 

main

I5. Fix to Proposition A.5.
The appendix needs one additional invariant lemma. For each processed prefix 
𝑢
u, there should be a uniquely determined state triple 
(
𝑠
(
𝑢
)
,
𝑟
(
𝑢
)
,
𝑒
(
𝑢
)
)
(s(u),r(u),e(u)) and committed word 
𝑐
(
𝑢
)
c(u) such that

v
i
s
(
Λ
(
𝑢
𝑤
)
)
=
𝑐
(
𝑢
)
 
Ξ
𝑠
(
𝑢
)
,
𝑟
(
𝑢
)
,
𝑒
(
𝑢
)
(
𝑤
)
vis(Λ(uw))=c(u)Ξ
s(u),r(u),e(u)
	​

(w)

for every continuation 
𝑤
w, with 
∣
𝑟
(
𝑢
)
∣
≤
𝐿
+
1
∣r(u)∣≤L+1. One then proves inductively that the update

(
𝑠
,
𝑟
,
𝑒
,
𝑎
)
↦
(
𝑠
′
,
𝑟
′
,
𝑒
′
,
𝑐
′
)
(s,r,e,a)↦(s
′
,r
′
,e
′
,c
′
)

has the property that 
𝑐
(
𝑢
𝑎
)
=
𝑐
(
𝑢
)
𝑐
′
c(ua)=c(u)c
′
, and that equality of full outputs for 
𝑞
q copies is equivalent to equality of all committed blocks 
𝑐
′
c
′
 at every step plus equality of the terminal residuals. At present, the proposition only sketches this. 

main

I6. Fix to the novelty/attribution of Theorem C.
The introduction should say explicitly that Sanna already supplied an automata-theoretic construction of 
𝜆
𝑝
λ
p
	​

, proved strong connectivity and aperiodicity for the accessible automaton, identified 
𝜆
𝑝
λ
p
	​

 as its Perron root, and noted a minimized automaton with 
2
𝑝
+
1
2p+1 states. The present contribution should then be phrased more modestly, for example: “We give an alternative fold-side realization of the same constants, and an explicit symmetry-compressed quotient.” As written, the paper implies a first algebraicity result that the literature already essentially contains. 
arXiv
+2
arXiv
+2

I7. Fix to the Frobenius and disjointness arguments in Section 7.
For each prime in Table 1, the authors should state explicitly that 
𝑝
∤
D
i
s
c
(
𝑀
𝑞
)
p∤Disc(M
q
	​

), so that the factorization type of 
𝑀
𝑞
 
m
o
d
 
𝑝
M
q
	​

modp is the Frobenius cycle type. In Theorem 7.10, add the sentence: “If 
𝐿
𝑞
⊆
𝑀
𝑞
L
q
	​

⊆M
q
	​

, then its unique quadratic subfield 
𝑄
(
D
i
s
c
(
𝑀
𝑞
)
)
Q(
Disc(M
q
	​

)
	​

) is also contained in 
𝑀
𝑞
M
q
	​

, contradicting the squareclass independence of Table 2.” This makes the subgroup-theoretic logic complete. 

main

I8. Fix to Table 3 / explicit polynomials.
The paper should print the actual recurrence polynomials, not only recurrence coefficients. A sentence of the form

𝑀
𝑞
(
𝑋
)
=
𝑋
𝑑
𝑞
−
𝑐
𝑞
,
1
𝑋
𝑑
𝑞
−
1
−
⋯
−
𝑐
𝑞
,
𝑑
𝑞
M
q
	​

(X)=X
d
q
	​

−c
q,1
	​

X
d
q
	​

−1
−⋯−c
q,d
q
	​

	​


should appear once, and each row of Table 3 should be readable as an explicit 
𝑀
𝑞
(
𝑋
)
M
q
	​

(X). Then an interested reader can verify the mod-
𝑝
p irreducibility, discriminant squareclass, and Galois-group computations from the paper alone. 

main

In summary, my recommendation is Major revision. The paper has a promising core, but the spectral/arithmetic superstructure needs a substantially more rigorous and more transparent presentation before it can be accepted.