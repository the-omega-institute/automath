<!-- oracle metadata: {"timestamp": "2026-04-12T04:59:45.734884", "model": "chatgpt-5.4-pro-extended", "response_length": 11904} -->

1. Overall assessment

Major revision

The manuscript has a plausible publishable core, but not in its present form. The strongest part is the base-
𝑏
b quantitative obstruction, especially the recall/precision and symmetric-difference consequences. However, the current draft has central proof problems in Section 2.1 and Lemma 3.4, and its novelty discussion does not adequately engage with prior work on conditional and relative density of regular languages. I would not recommend acceptance until those issues are fixed and the contribution is repositioned more modestly and precisely. 

main

 
DROPS
+3
ACM Digital Library
+3
Sage Journals
+3

2. Novelty rating for each numbered formal result

I rate the substantive numbered results in Sections 2 and 3, since Section 1 mostly restates them. 

main

Result	Rating	One-line justification
Theorem 2.2	LOW	Classical Perron-Frobenius / Markov-chain asymptotics for regular-language densities, repackaged for the fixed-base DFA setting.
Proposition 2.4	LOW	Essentially an algebraic unpacking of the definitions of recall and precision plus (
Corollary 2.5	MEDIUM	The quantitative symmetric-difference lower bound for prime slices seems new in this exact formulation, though it is an immediate corollary of classical density dichotomy plus PNT.
Corollary 2.7	MEDIUM	The recall/precision obstruction is a useful and seemingly new framing, but mathematically it is a short consequence of Theorem 2.2.
Lemma 2.8	LOW	Standard periodic Perron-Frobenius growth for an irreducible nonnegative matrix.
Theorem 2.9	LOW	Natural product-automaton / relative-density extension; novelty is currently under-argued and close prior literature is not discussed.
Proposition 3.1	LOW	Known Zeckendorf / S-recognizable growth law.
Lemma 3.4	LOW	Straightforward prime-counting in Fibonacci intervals.
Corollary 3.5	LOW	Direct application of Theorem 2.9 and Lemma 3.4.
Corollary 3.6	LOW	Same.
Corollary 3.7	LOW	Already known from Rigo-type non-recognizability, and also follows quickly from PNT plus Proposition 3.1.
3. Issue table

The issues below target correctness, novelty, and scope. The most serious ones are in Lemma 2.8, Theorem 2.9, and Lemma 3.4. 

main

ID	Section	Severity	Description	Suggested fix
B1	2.1, Lemma 2.8	BLOCKER	The proof identifies residue-class coefficients with single peripheral spectral projectors and claims 
𝑢
𝑁
𝑇
𝐸
ℓ
𝑣
𝑁
≥
0
u
N
T
	​

E
ℓ
	​

v
N
	​

≥0. That is generally false. These coefficients can be complex before residue-class regrouping.	Rewrite the lemma exactly as in Theorem 2.2: first group all peripheral terms by 
𝑚
 
m
o
d
 
𝑑
𝑁
mmodd
N
	​

, then define nonnegative residue coefficients 
𝑑
𝑟
d
r
	​

 from the grouped matrices.
B2	2.1, Theorem 2.9	BLOCKER	The argument “
𝜌
(
𝐵
)
≤
𝜆
ρ(B)≤λ because 
𝐿
(
𝐴
)
∩
𝑁
⊆
𝐿
(
𝑁
)
L(A)∩N⊆L(N)” is not a valid proof. Also, 
𝜌
(
𝐵
)
=
𝜆
ρ(B)=λ does not imply a positive leading coefficient for 
𝑢
𝑇
𝐵
𝑚
𝑣
u
T
B
m
v unless the product automaton is trimmed to relevant SCCs.	Trim the product automaton to reachable and co-reachable states, prove 
𝜌
(
𝐵
′
)
≤
𝜆
ρ(B
′
)≤λ by path-count comparison or matrix domination, and extract asymptotics only from 
𝜆
λ-maximal relevant SCCs.
B3	3, Lemma 3.4	BLOCKER	The displayed crude bounds 
𝑥
/
(
2
log
⁡
𝑥
)
≤
𝜋
(
𝑥
)
≤
2
𝑥
/
log
⁡
𝑥
x/(2logx)≤π(x)≤2x/logx do not yield the claimed lower bound for 
𝜋
(
𝐹
𝑚
+
2
)
−
𝜋
(
𝐹
𝑚
+
1
)
π(F
m+2
	​

)−π(F
m+1
	​

). As written, the lower-bound proof does not go through.	Use the full prime number theorem asymptotic, or an explicit interval estimate for 
[
𝑐
𝑥
,
𝑥
]
[cx,x] with fixed 
0
<
𝑐
<
1
0<c<1.
B4	1.2, 2.1, 3	BLOCKER	Novelty is overstated or at least under-documented. The paper omits closely related prior work on conditional and relative densities of regular languages, so the contribution of Theorem 2.9 is not properly situated.	Add the missing literature and sharply separate what is classical, what is a specialized reproof, and what is genuinely new.
M1	Abstract, Introduction, Remark 2.10	MEDIUM	The scope is broader than the theorem proved. The main extension is only for trim deterministic presentations with strongly connected underlying graph and 
𝜆
>
1
λ>1, not for arbitrary regular numeration systems.	Either narrow the claims everywhere, or generalize the theorem to the non-strongly-connected case by isolating dominant accessible/co-accessible SCCs.
M2	Section 3	MEDIUM	The known Zeckendorf material occupies too much of the paper relative to the new base-
𝑏
b contribution.	Compress Section 3 heavily, or move the known growth-law proof to an appendix.
M3	Notation throughout	MEDIUM	Notation such as 
𝐿
𝑚
(
𝐴
,
𝑁
)
L
m
	​

(A,N) and 
𝐿
𝑚
(
𝑍
)
(
𝐴
)
L
m
(Z)
	​

(A) denotes counts, but visually suggests languages. This makes proofs harder to read.	Use 
𝑎
𝑚
(
𝐴
,
𝑁
)
a
m
	​

(A,N), 
𝑛
𝑚
(
𝐴
)
n
m
	​

(A), or similar for counts, and reserve 
𝐿
(
⋅
)
L(⋅) for languages.
M4	Abstract and conclusions	MEDIUM	The word “explicit” is stronger than what is actually provided. The constants are existential asymptotic constants, not effectively computed from automaton data.	Either make the constants genuinely effective, or weaken the wording to “uniform asymptotic” or similar.
L1	Section 1 vs Sections 2-3	LOW	There is substantial duplication between the Introduction and the body.	Shorten Section 1 or move some repeated statements into a concise roadmap paragraph.
L2	Exposition	LOW	The switch between MSD-first base-
𝑏
b and LSD-first Zeckendorf is handled, but still cognitively heavy.	Add one explicit worked example in each convention.
4. Missing references

The following omissions are important enough that they should be discussed, not just added to the bibliography:

Jakub Kozik, Conditional Densities of Regular Languages (2005). This is the closest prior reference for the relative-density viewpoint in regular languages, and it matters directly for how Theorem 2.9 is positioned. 
ACM Digital Library

Toshihiro Koga, On the Density of Regular Languages (2019). Relevant recent refinement on asymptotic density for regular languages. 
Sage Journals

Georges Hansel and Dominique Perrin, Rational probability measures (1989). Classical background for density/probability viewpoints on rational languages. 
ScienceDirect

Émilie Charlier, Narad Rampersad, Michel Rigo, Laurent Waxweiler, The Minimal Automaton Recognizing 
𝑚
𝑁
mN in a Linear Numeration System (2010). Relevant because it explicitly studies when automata for numeration languages have more than one strongly connected component, which bears directly on the manuscript’s strong-connectivity hypothesis. 
ResearchGate

Valérie Berthé, Herman Goulet-Ouellet, Dominique Perrin, Density of Rational Languages Under Shift Invariant Measures (ICALP 2025). Recent nearby work on density of rational languages that should at least be acknowledged in the density discussion. 
DROPS
+1

J. Andres Montoya, Relative Densities of Formal Languages (DCFS 2025). Recent adjacent work on asymptotic and relative densities of formal languages. 
Springer

5. Specific improvements needed to reach acceptance

Repair the core proof package in Section 2.1. As written, Theorem 2.9 is not established rigorously enough for publication.

Fix Lemma 3.4 and re-check every Zeckendorf corollary that depends on it. The current lower-bound argument is not valid.

Reposition the novelty carefully. The manuscript should present Theorem 2.2 as classical, Theorem 2.9 as at best a specialized refinement or repackaging unless a sharper comparison is given, and Corollaries 2.5 and 2.7 as the clearest genuinely new contributions. 
DROPS
+3
ACM Digital Library
+3
Sage Journals
+3

Narrow or generalize the numeration-system claim. There is real prior evidence that automata for numeration languages may have more than one SCC, so strong connectivity is not a harmless technicality. 
ResearchGate

Streamline the paper into a sharper note. If the authors cannot fully stabilize the regular-numeration extension, a shorter paper focused on the base-
𝑏
b prime obstructions would be stronger and more convincing.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Lemma 2.8

Replace the current coefficient definition by a residue-class decomposition. Write

𝐵
𝑁
𝑚
=
𝜆
𝑚
(
∑
𝑗
=
0
𝑑
𝑁
−
1
𝜔
𝑗
𝑚
𝐸
𝑗
+
𝑅
𝑚
)
,
B
N
m
	​

=λ
m
(
j=0
∑
d
N
	​

−1
	​

ω
jm
E
j
	​

+R
m
	​

),

then group by 
𝑚
 
m
o
d
 
𝑑
𝑁
mmodd
N
	​

 to obtain matrices 
𝑆
0
,
…
,
𝑆
𝑑
𝑁
−
1
S
0
	​

,…,S
d
N
	​

−1
	​

 such that

𝐵
𝑁
𝑚
=
𝜆
𝑚
(
𝑆
𝑚
 
m
o
d
 
𝑑
𝑁
+
𝐸
𝑚
)
,
∥
𝐸
𝑚
∥
≤
𝐶
𝜃
𝑚
.
B
N
m
	​

=λ
m
(S
mmodd
N
	​

	​

+E
m
	​

),∥E
m
	​

∥≤Cθ
m
.

Only after that should one define

𝑑
𝑟
:
=
𝑢
𝑁
𝑇
𝑆
𝑟
𝑣
𝑁
≥
0.
d
r
	​

:=u
N
T
	​

S
r
	​

v
N
	​

≥0.

Do not identify 
𝑑
𝑟
d
r
	​

 with a single 
𝑢
𝑁
𝑇
𝐸
𝑟
𝑣
𝑁
u
N
T
	​

E
r
	​

v
N
	​

.

B2. Theorem 2.9

Introduce the trimmed product automaton 
𝐵
′
B
′
, keeping only states reachable from the initial pair and from which an accepting pair is reachable. Then:

prove 
𝜌
(
𝐵
′
)
≤
𝜆
ρ(B
′
)≤λ by comparing path counts in 
𝐵
′
B
′
 with those in 
𝑁
N, or by matrix domination after summing over the 
𝐴
A-coordinate;

replace the case split by one on 
𝜌
(
𝐵
′
)
ρ(B
′
), not 
𝜌
(
𝐵
)
ρ(B);

in the 
𝜌
(
𝐵
′
)
=
𝜆
ρ(B
′
)=λ case, sum only over 
𝜆
λ-maximal SCCs that actually contribute to 
𝑢
𝑇
(
𝐵
′
)
𝑚
𝑣
u
T
(B
′
)
m
v;

set the final period 
𝑝
p to absorb both numerator and denominator periodicity.

As a sanity check, test the proof against an automaton 
𝐴
A with an unreachable full-shift SCC. In the current proof, that SCC can force 
𝜌
(
𝐵
)
=
𝜆
ρ(B)=λ even when the intersection language is empty.

B3. Lemma 3.4

Replace the current proof by a true asymptotic argument:

𝜋
(
𝐹
𝑚
+
2
)
−
𝜋
(
𝐹
𝑚
+
1
)
=
𝐹
𝑚
+
2
log
⁡
𝐹
𝑚
+
2
−
𝐹
𝑚
+
1
log
⁡
𝐹
𝑚
+
1
+
𝑜
 ⁣
(
𝜙
𝑚
𝑚
)
.
π(F
m+2
	​

)−π(F
m+1
	​

)=
logF
m+2
	​

F
m+2
	​

	​

−
logF
m+1
	​

F
m+1
	​

	​

+o(
m
ϕ
m
	​

).

Since 
𝐹
𝑚
+
1
/
𝐹
𝑚
+
2
→
𝜙
−
1
<
1
F
m+1
	​

/F
m+2
	​

→ϕ
−1
<1, the main term is a positive constant times 
𝜙
𝑚
/
𝑚
ϕ
m
/m. This immediately gives positive 
𝐴
𝑍
,
𝐵
𝑍
A
Z
	​

,B
Z
	​

. The current crude inequalities are not enough.

B4. Literature and novelty

Add a dedicated paragraph titled something like “Relation to conditional-density literature.” Explicitly discuss Kozik 2005, Koga 2019, Montoya 2025, and Berthé-Goulet-Ouellet-Perrin 2025. Then rewrite the novelty map as follows:

Theorem 2.2: classical.

Lemma 2.8 / Proposition 3.1: classical.

Theorem 2.9: specialized refinement / packaging, unless a precise distinction from prior work is demonstrated.

Corollaries 2.5 and 2.7: main new contributions.

M1. Scope mismatch

Either change the abstract and introduction to say “for strongly connected trim deterministic presentations” everywhere, or prove the natural generalization to arbitrary trim deterministic presentations by reducing to dominant accessible/co-accessible SCCs.

M2. Overlong known material

Move Proposition 3.1 and most of its proof to an appendix, or cite it and give only a two- or three-sentence sketch. Keep the main text focused on the new obstruction statements.

M3. Notation

Rename all counting functions so that notation distinguishes clearly between a language and its size. For example:

𝑎
𝑚
(
𝐴
)
:
=
∣
𝐿
(
𝐴
)
∩
Σ
𝑏
𝑚
∣
a
m
	​

(A):=∣L(A)∩Σ
b
m
	​

∣,

𝑎
𝑚
(
𝐴
,
𝑁
)
:
=
∣
𝐿
(
𝐴
)
∩
𝑁
𝑚
∣
a
m
	​

(A,N):=∣L(A)∩N
m
	​

∣,

𝑎
𝑚
(
𝑍
)
(
𝐴
)
:
=
∣
𝐿
(
𝐴
)
∩
𝑍
𝑚
∣
a
m
(Z)
	​

(A):=∣L(A)∩Z
m
	​

∣.

M4. “Explicit” constants

Either provide an actual recipe for 
𝑐
𝐴
,
𝑏
c
A,b
	​

, 
𝐶
𝐴
,
𝑏
C
A,b
	​

, and 
𝑐
𝐴
,
𝜙
c
A,ϕ
	​

 in terms of the DFA’s periodic decomposition and chosen prime-counting constants, or weaken the wording from “explicit” to “uniform asymptotic lower bound” or similar.

My editorial view is that this is not far from a publishable note, but it needs a mathematically corrected Section 2.1 and a more honest novelty framing before it gets there.