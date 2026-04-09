<!-- oracle metadata: {"timestamp": "2026-04-07T04:19:41.660455", "model": "o3-mini-high", "response_length": 14064} -->

I have reviewed the attached manuscript. 

main

1. Overall assessment

Major revision.

The paper is not publishable in its current form. There is one theorem-level statement/proof mismatch in Proposition 4.3 and Theorem 1.5(ii), a repeated sign error in the core identity of Theorem 4.1, an unhandled edge case and a logical gap in Theorem 3.1, and the literature review omits direct antecedents. The note may become publishable after substantial correction and reframing, but not as it stands. The originality profile is also limited. Primes versus automata goes back at least to Hartmanis and Shank, and the Zeckendorf non-regularity corollary is subsumed by the abstract numeration systems result that primes are never 
𝑆
S-recognizable. 
MIT CSAIL
+2
arXiv
+2

My editorial view is therefore as follows. As a short note whose contribution is an elementary synthesis plus a few quantitative corollaries, the manuscript could perhaps be rehabilitated. As a research article claiming substantial theorem-level novelty, it is presently too weak.

2. Novelty rating for each theorem
Result	Novelty	One-line justification
Theorem 2.2 / Theorem 1.1	LOW	This is a standard Perron-Frobenius / finite Markov chain decomposition for complete DFAs, specialized to normalized word counts.
Theorem 3.1 / Theorem 1.4	LOW	The proof is a routine transfer-matrix and Jordan-form argument for a regular language inside a regular numeration syntax.
Theorem 3.7	MEDIUM	The residue-class obstruction to eventual sofic realization of the prime Zeckendorf slices is the cleanest genuinely note-worthy synthesis in the paper.
Theorem 4.1 / Theorem 1.5(i)	LOW	This is a special case of the classical Pólya-Carlson / Estermann natural-boundary mechanism.
Proposition 4.3 / Theorem 1.5(ii)	LOW	The periodicity after 
𝑧
=
𝑒
−
𝑠
z=e
−s
 is elementary, and the current statement is in fact incorrect as written.

Corollaries 2.3, 2.4, and 3.4 are not rated separately because they are immediate applications. In particular, Corollary 3.4 should not be presented as new. It is a Zeckendorf-specialized instance of the general abstract numeration systems non-recognizability of primes. 
arXiv
+1

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	§4, Proposition 4.3 / Theorem 1.5(ii)	BLOCKER	The statement assumes the first nonzero Dirichlet coefficient occurs at 
𝑛
0
>
1
n
0
	​

>1, but then concludes “in particular” non-agreement with 
𝜁
(
𝑠
)
ζ(s). This is invalid because 
𝜁
(
𝑠
)
ζ(s) has 
𝑎
1
=
1
a
1
	​

=1. The proof explicitly violates its own hypothesis by applying the proposition to 
𝜁
ζ.	Restate the proposition in terms of the least index 
𝑛
1
≥
2
n
1
	​

≥2 with 
𝑎
𝑛
1
≠
0
a
n
1
	​

	​


=0, or equivalently say “some coefficient with 
𝑛
≥
2
n≥2 is nonzero.” Then 
𝜁
ζ is covered.
M1	§4, Theorem 4.1	MEDIUM	The logarithmic derivative identity has the wrong sign. The manuscript writes 
−
𝑧
𝑍
𝑏
′
(
𝑧
)
/
𝑍
𝑏
(
𝑧
)
=
∑
𝑛
𝑏
𝑛
𝑧
𝑛
/
(
1
−
𝑧
𝑛
)
−zZ
b
′
	​

(z)/Z
b
	​

(z)=∑nb
n
	​

z
n
/(1−z
n
), which is false.	Replace it by 
𝑧
𝑍
𝑏
′
(
𝑧
)
/
𝑍
𝑏
(
𝑧
)
=
∑
𝑛
𝑏
𝑛
𝑧
𝑛
/
(
1
−
𝑧
𝑛
)
zZ
b
′
	​

(z)/Z
b
	​

(z)=∑nb
n
	​

z
n
/(1−z
n
), or redefine the coefficient sequence with the minus sign consistently.
M2	§3, Theorem 3.1	MEDIUM	The deduction 
𝜌
≤
𝜑
ρ≤φ is asserted before the lower-bound argument that would justify it. As written, the logic is incomplete.	Deduce 
𝜌
≤
𝜑
ρ≤φ only after constructing exponentially many accepted words from a reachable/co-reachable SCC of spectral radius 
𝜌
ρ.
M3	§3, Theorem 3.1	MEDIUM	The empty-language case is not handled. After trimming, there may be no strongly connected component, so 
𝜌
ρ is undefined, and 
𝑁
𝐿
(
𝑇
)
=
𝑇
𝛼
+
𝑜
(
1
)
N
L
	​

(T)=T
α+o(1)
 is false for 
𝐿
=
∅
L=∅.	Add “assume 
𝐿
≠
∅
L

=∅” or split off the trivial case 
𝐿
=
∅
L=∅.
M4	§1.2 and §3	MEDIUM	The literature review omits direct antecedents. This materially distorts the novelty of the automata/primes discussion and especially of Corollary 3.4.	Cite Hartmanis-Shank and the abstract numeration systems literature, and explicitly state that the Zeckendorf non-regularity corollary is not new in that general framework.
M5	§4, Theorem 4.1	MEDIUM	Two analytic steps are too compressed for publication: integrality of Taylor coefficients, and justification of termwise logarithmic differentiation / rearrangement.	Add a finite-truncation coefficient argument and a summability estimate based on 
−
log
⁡
(
1
−
𝑥
)
≥
𝑥
−log(1−x)≥x.
L1	§2	LOW	Proof labeling is confusing. Proposition 2.5 is inserted between Corollary 2.4 and its proof, and the next “Proof.” is visually easy to misread.	Label “Proof of Proposition 2.5” and “Proof of Corollary 2.4” explicitly.
L2	§3, Proposition 3.5	LOW	The proof conflates a regular block language with a right-resolving presentation. Labeled-path counts in a sofic presentation are not automatically distinct-word counts.	Invoke a DFA for the regular language 
𝐵
(
𝑋
)
B(X), not merely a labeled graph presentation.
L3	Throughout	LOW	There are several editorial inaccuracies: lowercase cross-references, ambiguous parenthesization in the symmetric-difference statements, and imprecise wording such as “half-plane of holomorphy” for the determinant model.	Perform a careful copy-edit and standardize notation and references.
4. Missing references

At minimum, the following should be cited.

J. Hartmanis and H. Shank, On the Recognition of Primes by Automata, J. ACM 15(3) (1968), 382 to 389. This is the classical direct antecedent for primes versus automata. 
MIT CSAIL

M. Rigo, Generalization of automatic sequences for numeration systems on a regular language. This paper explicitly states that for any numeration system 
𝑆
S, the set of primes is never 
𝑆
S-recognizable. That substantially subsumes the manuscript’s Corollary 3.4. 
arXiv

M. Rigo and A. Maes, More on generalized automatic sequences, J. Automata, Languages and Combinatorics 7(3) (2002). Relevant for the 
𝑆
S-automatic / morphic framework behind the general non-recognizability statement. 
JALC

M. Rigo, Construction of regular languages and recognizability of polynomials, Discrete Math. 254 (2002), 485 to 496. Relevant for the broader abstract numeration systems context, and it explicitly remarks on the non-recognizability of primes. 
arXiv
+1

É. Charlier, An introduction to numeration systems: Cobham-like theorems, first-order logic and regular sequences. This is a useful modern survey for situating the manuscript in the ANS literature and states the “primes are never 
𝑆
S-recognizable” fact in that framework. 
Oxford CS

5. Specific improvements needed to reach acceptance

First, all theorem-level flaws in Sections 3 and 4 must be repaired. The paper is not in a state where a reader can rely on the statements as written.

Second, the paper must be reframed honestly. The main contribution is not the bare non-regularity of prime Zeckendorf representations. That point is already known in much greater generality. The paper’s real contribution, if any, is the elementary synthesis of three obstruction mechanisms, plus the fixed-DFA precision/recall corollaries and the sofic slice obstruction. 
arXiv
+1

Third, the proofs need to be tightened to published standards. Several steps are mathematically correct in spirit but too compressed in print. This is especially true in Theorem 3.1 and Theorem 4.1.

Fourth, the exposition should be cleaned up so that it reads as a rigorous short note rather than as a draft. Right now there are enough structural and copy-editing blemishes that they undermine confidence in the mathematics.

Fifth, the target venue should be reconsidered. After correction, this looks more like a concise note or synthesis paper than a paper with multiple high-novelty theorem statements.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Correct Proposition 4.3 / Theorem 1.5(ii)

A correct theorem-level statement is the following.

𝐺
𝐴
(
𝑠
)
:
=
det
⁡
(
𝐼
−
𝑒
−
𝑠
𝐴
)
−
1
G
A
	​

(s):=det(I−e
−s
A)
−1

is 
2
𝜋
𝑖
2πi-periodic wherever it is holomorphic. Now let

𝐹
(
𝑠
)
=
∑
𝑛
≥
1
𝑎
𝑛
𝑛
−
𝑠
F(s)=
n≥1
∑
	​

a
n
	​

n
−s

have abscissa of convergence 
𝜎
𝑐
σ
c
	​

, and assume there exists at least one index 
𝑛
≥
2
n≥2 with 
𝑎
𝑛
≠
0
a
n
	​


=0. Let

𝑛
1
:
=
min
⁡
{
𝑛
≥
2
:
𝑎
𝑛
≠
0
}
.
n
1
	​

:=min{n≥2:a
n
	​


=0}.

Then for real 
𝜎
→
+
∞
σ→+∞,

𝐹
(
𝜎
+
2
𝜋
𝑖
)
−
𝐹
(
𝜎
)
=
∑
𝑛
≥
2
𝑎
𝑛
𝑛
−
𝜎
(
𝑒
−
2
𝜋
𝑖
log
⁡
𝑛
−
1
)
F(σ+2πi)−F(σ)=
n≥2
∑
	​

a
n
	​

n
−σ
(e
−2πilogn
−1)

and therefore

𝐹
(
𝜎
+
2
𝜋
𝑖
)
−
𝐹
(
𝜎
)
=
𝑎
𝑛
1
𝑛
1
−
𝜎
(
𝑒
−
2
𝜋
𝑖
log
⁡
𝑛
1
−
1
)
+
𝑂
 ⁣
(
(
𝑛
1
+
1
)
−
𝜎
)
.
F(σ+2πi)−F(σ)=a
n
1
	​

	​

n
1
−σ
	​

(e
−2πilogn
1
	​

−1)+O((n
1
	​

+1)
−σ
).

Since 
log
⁡
𝑛
1
∉
𝑍
logn
1
	​

∈
/
Z, the coefficient 
𝑒
−
2
𝜋
𝑖
log
⁡
𝑛
1
−
1
e
−2πilogn
1
	​

−1 is nonzero. Hence the difference is nonzero for all sufficiently large 
𝜎
σ, so 
𝐹
F is not 
2
𝜋
𝑖
2πi-periodic on any right half-plane of holomorphy.

This immediately yields the zeta case, because 
𝜁
(
𝑠
)
ζ(s) has nonzero coefficients for all 
𝑛
≥
2
n≥2. In fact,

𝜁
(
𝜎
+
2
𝜋
𝑖
)
−
𝜁
(
𝜎
)
=
2
−
𝜎
(
𝑒
−
2
𝜋
𝑖
log
⁡
2
−
1
)
+
𝑂
(
3
−
𝜎
)
≠
0
ζ(σ+2πi)−ζ(σ)=2
−σ
(e
−2πilog2
−1)+O(3
−σ
)

=0

for all sufficiently large 
𝜎
σ.

The current “first nonzero term occurs at 
𝑛
0
>
1
n
0
	​

>1” hypothesis should therefore be replaced by “there exists some 
𝑛
≥
2
n≥2 with 
𝑎
𝑛
≠
0
a
n
	​


=0.”

M1. Fix the sign in Theorem 4.1

The correct identity is

log
⁡
𝑍
𝑏
(
𝑧
)
=
−
∑
𝑛
≥
1
𝑏
𝑛
log
⁡
(
1
−
𝑧
𝑛
)
,
logZ
b
	​

(z)=−
n≥1
∑
	​

b
n
	​

log(1−z
n
),

hence

𝑧
𝑍
𝑏
′
(
𝑧
)
𝑍
𝑏
(
𝑧
)
=
∑
𝑛
≥
1
𝑛
𝑏
𝑛
𝑧
𝑛
1
−
𝑧
𝑛
=
∑
𝑚
≥
1
𝑐
𝑚
𝑧
𝑚
,
𝑐
𝑚
:
=
∑
𝑛
∣
𝑚
𝑛
𝑏
𝑛
∈
𝑍
≥
0
.
Z
b
	​

(z)
zZ
b
′
	​

(z)
	​

=
n≥1
∑
	​

1−z
n
nb
n
	​

z
n
	​

=
m≥1
∑
	​

c
m
	​

z
m
,c
m
	​

:=
n∣m
∑
	​

nb
n
	​

∈Z
≥0
	​

.

So everywhere in the proof one should write

𝑅
(
𝑧
)
:
=
𝑧
𝑍
𝑏
′
(
𝑧
)
𝑍
𝑏
(
𝑧
)
,
R(z):=
Z
b
	​

(z)
zZ
b
′
	​

(z)
	​

,

not

𝑅
(
𝑧
)
:
=
−
𝑧
𝑍
𝑏
′
(
𝑧
)
𝑍
𝑏
(
𝑧
)
.
R(z):=−
Z
b
	​

(z)
zZ
b
′
	​

(z)
	​

.

With this correction, the later identity

𝑐
𝑝
=
𝑐
1
+
𝑝
𝑏
𝑝
c
p
	​

=c
1
	​

+pb
p
	​


for prime 
𝑝
p is correct.

M2. Repair the 
𝜌
≤
𝜑
ρ≤φ step in Theorem 3.1

The sentence “Since 
∣
𝑍
∩
{
0
,
1
}
𝑚
∣
=
𝐹
𝑚
+
1
=
𝜑
𝑚
+
𝑜
(
𝑚
)
∣Z∩{0,1}
m
∣=F
m+1
	​

=φ
m+o(m)
, one has 
𝜌
≤
𝜑
ρ≤φ” is not justified at that point.

A correct insertion is:

Choose a reachable, co-reachable SCC 
𝐶
C with spectral radius 
𝜌
ρ.

By Perron-Frobenius, there exist 
𝑖
,
𝑗
∈
𝐶
i,j∈C, a residue 
𝑟
r, and 
𝑐
>
0
c>0 such that

(
𝐵
𝐶
 
𝑟
+
𝑘
𝑑
𝐶
)
𝑖
𝑗
≥
𝑐
 
𝜌
 
𝑟
+
𝑘
𝑑
𝐶
(B
C
r+kd
C
	​

	​

)
ij
	​

≥cρ
r+kd
C
	​


for all large 
𝑘
k.

After appending fixed entry and exit paths of lengths 
ℓ
1
,
ℓ
2
ℓ
1
	​

,ℓ
2
	​

, obtain

𝑎
ℓ
1
+
ℓ
2
+
𝑟
+
𝑘
𝑑
𝐶
≥
𝑐
 
𝜌
 
𝑟
+
𝑘
𝑑
𝐶
.
a
ℓ
1
	​

+ℓ
2
	​

+r+kd
C
	​

	​

≥cρ
r+kd
C
	​

.

Therefore

lim sup
⁡
𝑚
→
∞
𝑎
𝑚
1
/
𝑚
≥
𝜌
.
m→∞
limsup
	​

a
m
1/m
	​

≥ρ.

But 
𝑎
𝑚
≤
∣
𝑍
∩
{
0
,
1
}
𝑚
∣
=
𝐹
𝑚
+
1
=
𝜑
𝑚
+
𝑜
(
𝑚
)
a
m
	​

≤∣Z∩{0,1}
m
∣=F
m+1
	​

=φ
m+o(m)
, so

lim sup
⁡
𝑚
→
∞
𝑎
𝑚
1
/
𝑚
≤
𝜑
.
m→∞
limsup
	​

a
m
1/m
	​

≤φ.

Hence 
𝜌
≤
𝜑
ρ≤φ.

That is the logically correct place to deduce the spectral bound.

M3. Handle the empty-language case in Theorem 3.1

As written, the theorem fails for 
𝐿
=
∅
L=∅. The cleanest fix is to split off the trivial case:

If 
𝐿
=
∅
L=∅, then 
𝑁
𝐿
(
𝑇
)
=
0
N
L
	​

(T)=0 for all 
𝑇
T, and there is nothing to prove. Assume henceforth that 
𝐿
≠
∅
L

=∅.

Then the trimmed automaton has at least one path to an accepting state, and the definition of 
𝜌
ρ is meaningful.

If the author wants a uniform statement, one may instead declare the convention 
𝜌
=
0
ρ=0 when the trimmed automaton has no SCC, and then write the theorem as a case distinction. But the split formulation is clearer.

M4. Rewrite the prior-work discussion and novelty claim

The introduction should say explicitly that Corollary 3.4 is not new in the abstract numeration systems setting. A concrete replacement paragraph would be:

The impossibility of recognizing primes by finite automata in classical settings is old, beginning with Hartmanis and Shank. In the broader framework of abstract numeration systems, Rigo proved that for any numeration system 
𝑆
S, the set of primes is never 
𝑆
S-recognizable. Accordingly, Corollary 3.4 is included here only as a Zeckendorf-specialized derivation from the transfer-matrix argument, not as a new non-recognizability theorem. The distinctive points of the present note are instead the fixed-DFA density/recall-precision obstruction and the elementary sofic-slice obstruction. 
MIT CSAIL
+2
arXiv
+2

Without such a paragraph, the paper materially overstates what is new.

M5. Justify integrality and termwise differentiation in Theorem 4.1

Two explicit insertions are needed.

For the coefficient integrality, write:

For each 
𝑚
m, the coefficient of 
𝑧
𝑚
z
m
 in 
𝑍
𝑏
(
𝑧
)
Z
b
	​

(z) depends only on the finite product 
∏
𝑛
≤
𝑚
(
1
−
𝑧
𝑛
)
−
𝑏
𝑛
∏
n≤m
	​

(1−z
n
)
−b
n
	​

. Each such finite product has coefficients in 
𝑍
≥
0
Z
≥0
	​

. Hence the Taylor coefficients of 
𝑍
𝑏
Z
b
	​

 lie in 
𝑍
≥
0
Z
≥0
	​

.

For termwise differentiation, write:

Fix 
0
<
𝑟
<
1
0<r<1. Since the Euler product converges at 
𝑟
1
/
2
r
1/2
,

∑
𝑛
≥
1
𝑏
𝑛
(
−
log
⁡
(
1
−
𝑟
𝑛
/
2
)
)
<
∞
.
n≥1
∑
	​

b
n
	​

(−log(1−r
n/2
))<∞.

Because 
−
log
⁡
(
1
−
𝑥
)
≥
𝑥
−log(1−x)≥x for 
0
<
𝑥
<
1
0<x<1, this implies

∑
𝑛
≥
1
𝑏
𝑛
𝑟
𝑛
/
2
<
∞
.
n≥1
∑
	​

b
n
	​

r
n/2
<∞.

Also 
sup
⁡
𝑛
≥
1
𝑛
𝑟
𝑛
/
2
<
∞
sup
n≥1
	​

nr
n/2
<∞, so

∑
𝑛
≥
1
𝑛
𝑏
𝑛
𝑟
𝑛
≤
(
sup
⁡
𝑛
≥
1
𝑛
𝑟
𝑛
/
2
)
∑
𝑛
≥
1
𝑏
𝑛
𝑟
𝑛
/
2
<
∞
.
n≥1
∑
	​

nb
n
	​

r
n
≤(
n≥1
sup
	​

nr
n/2
)
n≥1
∑
	​

b
n
	​

r
n/2
<∞.

Therefore

∑
𝑛
≥
1
𝑛
𝑏
𝑛
𝑧
𝑛
1
−
𝑧
𝑛
n≥1
∑
	​

1−z
n
nb
n
	​

z
n
	​


converges absolutely and uniformly on 
∣
𝑧
∣
≤
𝑟
∣z∣≤r, which justifies termwise logarithmic differentiation and rearrangement of the divisor sums.

That is enough to make the proof publishable.

In summary, the manuscript has a viable core, but it needs genuine mathematical correction and a substantial reduction in claimed novelty before it should be considered for acceptance.