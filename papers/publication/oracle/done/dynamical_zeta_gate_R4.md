<!-- oracle metadata: {"timestamp": "2026-04-06T12:00:41.824568", "model": "o3-mini-high", "response_length": 16376} -->

1. Overall assessment: MAJOR REVISION.

The manuscript has a genuine research core and should not be dismissed as a routine repackaging of standard symbolic-dynamical facts. The strongest contributions are the closed formula for the finite-part constant at the Perron pole, the cyclic reconstruction mechanism for the reduced spectrum, and the Adams–Möbius primitive determinant calculus for finite-group extensions. The distinction between the abelian shadow and the genuinely non-abelian primitive defect is also conceptually strong. 

main

However, the paper is not yet at acceptance standard. The main issues are not superficial. Several central statements are stronger or more polished than the proofs currently support. The introduction advertises exact non-abelian Fourier reconstruction and sharp class Mertens constants, but the derivation of the needed twisted spectral-radius bounds is too compressed, the use of the twisted spectral-gap hypothesis is not modularized enough, and some algebraic claims in the cyclic reconstruction section rely on steps that should be isolated and proved more carefully. In addition, the paper still has noticeable expository strain: some proofs fold several independent arguments into one block, several constants or growth claims are not localized enough, and the S
3
3
	​

 model, while very useful, is still more computational than conceptual. 

main

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 1.1 / 3.1	HIGH	The closed primitive-orbit formula for the finite part 
𝐹
𝑃
(
𝐴
)
FP(A) in terms of 
𝐶
(
𝐴
)
C(A) and determinant corrections is the clearest original result in the paper. 

main


Theorem 1.2 / 3.7–3.8	MEDIUM-HIGH	Cyclic-lift constants reconstructing the reduced spectrum is strong and useful, though once the multiple-sum expansion and Newton identities are available, much of the mechanism becomes algebraic. 

main


Theorem 1.3(i) / 4.3–4.8	HIGH	Adams–Möbius inversion for primitive Peter–Weyl channels is conceptually distinctive and the main non-abelian innovation of the paper. 

main


Theorem 1.3(ii) / 4.11–4.13	MEDIUM-HIGH	The class Mertens constants and non-abelian Fourier reconstruction are strong consequences, but they depend heavily on the twisted spectral-gap hypothesis and on some proofs that are still too compressed. 

main


Theorem 1.3(iii) / 5.2–5.5	MEDIUM-HIGH	The quotient-functoriality and abelian-shadow boundary are conceptually important and well aligned with the paper’s theme. 

main


Theorem A.1 / A.2 / A.3	MEDIUM	Useful technical appendices, but they support rather than drive the main novelty. 

main


Theorem B.1 / B.5 / B.7 / B.10 / B.11	MEDIUM	Interesting arithmetic consequences, especially character inversion and boundary-multiplicity averages, but they feel secondary to the main determinant calculus. 

main


Theorem C.2	LOW-MEDIUM	A reasonable rigidity consequence, but mostly an asymptotic application of earlier bounds. 

main

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	4.11	BLOCKER	The proof of the class Mertens theorem uses the claim that 
𝜌
(
𝐴
𝜎
)
≤
𝜆
ρ(A
σ
	​

)≤λ for every irreducible 
𝜎
σ, justified only parenthetically via Proposition 4.2 and entropy of the skew product. This is too compressed for a load-bearing estimate.	Isolate and prove this as a standalone proposition, with a precise argument linking eigenvalues of 
𝐴
𝜎
A
σ
	​

 to the spectrum of 
𝐴
𝑒
A
e
	​

 and then to 
𝜌
(
𝐴
𝑒
)
=
𝜆
ρ(A
e
	​

)=λ.
B2	4.11	BLOCKER	The passage from the Peter–Weyl expansion to the asymptotic formula for 
𝑝
𝑛
,
𝐶
p
n,C
	​

 bundles together several estimates, including the nontrivial-channel bound and the divisor tail, without enough separation of cases.	Split the theorem into lemmas: nontrivial channel estimate, conjugacy-class decomposition, Perron contribution, and tail summation.
B3	4.13	BLOCKER	The “non-abelian Fourier reconstruction” theorem is correct in form, but the proof relies on orthogonality after inserting constants 
Δ
𝐶
(
𝐴
)
Δ
C
	​

(A) whose convergence and classwise definition depend on Theorem 4.11. The logical dependency should be made explicit and cleaner.	Reorder the section so Theorem 4.11 yields a separate proposition defining 
Δ
𝐶
(
𝐴
)
Δ
C
	​

(A) rigorously before Fourier inversion is stated.
B4	5.5	BLOCKER	Theorem 5.5 identifies cyclic quotients with the exact abelian shadow. This is plausible and likely correct, but the proof uses “one-dimensional characters of 
𝐺
G” and “cyclic quotients” interchangeably too quickly. The finite-group argument should be tightened.	Add a lemma stating explicitly that every one-dimensional complex character factors through a finite cyclic quotient, and conversely every cyclic quotient character pulls back to a one-dimensional character.
B5	5.8–5.10	BLOCKER	The 
𝑆
3
S
3
	​

 example is central to the claim that primitive bias can survive vanishing periodic traces, yet many of its calculations are presented as “direct substitution” or “direct calculation.” Given its importance, the example needs a more explicit and auditable derivation.	Expand the example into a self-contained computation with the twisted matrices, characteristic polynomials, Adams decompositions, primitive coefficients, and class constants all displayed cleanly.
M1	3.1	MEDIUM	Theorem 3.1 uses the identity 
∑
𝑘
≥
1
𝜇
(
𝑘
)
log
⁡
(
1
−
𝑥
𝑘
)
/
𝑘
=
−
𝑥
∑
k≥1
	​

μ(k)log(1−x
k
)/k=−x without proof.	Add a short coefficientwise proof by expanding 
log
⁡
(
1
−
𝑥
𝑘
)
log(1−x
k
) and using 
∑
𝑑
∣
𝑛
𝜇
(
𝑑
)
∑
d∣n
	​

μ(d).
M2	3.2	MEDIUM	Proposition 3.5 gives 
Ψ
𝑞
(
𝐴
)
=
𝑢
𝑞
(
𝐴
)
+
𝑂
(
Λ
r
e
l
(
𝐴
)
2
𝑞
)
Ψ
q
	​

(A)=u
q
	​

(A)+O(Λ
rel
	​

(A)
2q
), but the implied constant is not stated and later growth arguments depend on this estimate.	State the dependence of the constant explicitly in terms of 
𝑑
d and 
Λ
r
e
l
(
𝐴
)
Λ
rel
	​

(A).
M3	3.2 / 3.7	MEDIUM	The proof that the exponential growth rate of 
Ψ
𝑞
(
𝐴
)
Ψ
q
	​

(A) equals 
Λ
r
e
l
(
𝐴
)
Λ
rel
	​

(A) uses the phrase “finite linear combination of exponentials” without isolating the required limsup lemma.	Add a lemma on exponential sums showing that the limsup equals the maximum modulus of the frequencies.
M4	4.1	MEDIUM	The determinant linearisation theorem is good, but the exchange of sums in the proof should state absolute convergence more quantitatively.	Insert an explicit bound using 
∥
𝜑
∥
∞
Tr
⁡
(
𝐴
𝑛
)
∥φ∥
∞
	​

Tr(A
n
).
M5	4.2	MEDIUM	Lemma 4.5 gives a rough bound (	a^{(m)}_{\varrho,\sigma}
M6	4.11	MEDIUM	The error term 
𝑂
(
(
Λ
∗
/
𝜆
)
𝑁
/
𝑁
)
O((Λ
∗
	​

/λ)
N
/N) is asserted without clearly distinguishing whether 
Λ
∗
=
max
⁡
{
Λ
(
𝐴
)
,
𝜂
,
𝜆
1
/
2
}
Λ
∗
	​

=max{Λ(A),η,λ
1/2
} is strict enough to make the tail geometric.	Add a short lemma that controls the partial sums of 
𝑂
(
Λ
∗
𝑛
/
𝑛
)
O(Λ
∗
n
	​

/n) after division by 
𝜆
𝑛
λ
n
.
M7	5.4	MEDIUM	Proposition 5.8 and Proposition 5.9 are computationally correct-looking, but the representation matrices are not displayed before use.	Write the standard 
2
×
2
2×2 matrices for the standard representation explicitly before forming 
𝐴
𝜌
A
ρ
	​

.
M8	Appendix A.2	MEDIUM	The proof of Theorem A.2 differentiates 
−
Tr
⁡
log
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
−Trlog(I−zA
θ
	​

) inside the trace. This is standard in finite dimensions, but Jacobi’s formula would be cleaner and avoid any unnecessary analytic ambiguity.	Replace the derivative step by Jacobi’s formula for 
det
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
det(I−zA
θ
	​

).
M9	Appendix B.7	MEDIUM	The Cesàro boundary-multiplicity theorem is interesting, but the error term from replacing 
𝑢
𝑞
(
𝐴
)
u
q
	​

(A) by 
Ψ
𝑞
(
𝐴
)
Ψ
q
	​

(A) is treated too quickly.	Spell out the estimate coming from Proposition 3.5 before passing to Cesàro averages.
L1	Introduction	LOW	The introduction is mathematically informed, but it tries to do too much at once. The table is useful but gives the paper a slightly inflated scope.	Streamline the introduction around the three core contributions and move some comparison material to remarks.
L2	1.2	LOW	The plan of the paper advertises appendices B and C as more central than they are.	Mark them explicitly as secondary consequences.
L3	6.2	LOW	The open problems are reasonable, but the first one is so central that it would be better framed earlier as a limitation of the current paper.	Note already in Section 4 that the twisted spectral gap is an assumption, not a derived criterion.
4. Missing references

The bibliography is substantially better than in earlier drafts and no longer contains placeholder citations. That said, a few load-bearing citations should be sharpened.

The introduction and Section 4 would benefit from a more precise theorem-level citation for the Chebotarev-type theory for finite-group extensions, not just general references to Parry–Pollicott and successors. 

main

The Adams-operations part should cite a standard source on Adams operations / character rings of finite groups, since this is central to Section 4 but currently only used implicitly. 

main

Appendix B.3 and Theorem B.10 would benefit from an explicit source for finite Fourier inversion on residue classes / Dirichlet characters, though the arguments are elementary. 

main

The rigidity appendix would benefit from a more direct citation for Perron–Frobenius perturbation in asymptotic matrix families, unless the author wants to keep Appendix C fully self-contained. 

main

5. Specific improvements needed to reach acceptance

The paper should be revised so that the main theorem chain is unmistakably primary and the appendices are clearly secondary.

The strongest path through the paper is:

finite part at the Perron pole,

cyclic-lift reduced spectral reconstruction,

Adams–Möbius primitive inversion,

class Mertens constants under twisted spectral gap,

quotient functoriality and the abelian-shadow boundary,

the 
𝑆
3
S
3
	​

 model.

That already makes a strong paper.

What currently weakens it is that some important technical dependencies are hidden inside proofs instead of promoted to lemmas. The most important example is the twisted spectral-radius bound behind Theorem 4.11. That estimate is structurally as important as the theorem itself and should not appear as a parenthetical remark.

The second needed improvement is proof modularity. Theorem 4.11, Theorem 4.13, and Theorem 5.5 are all easier to trust once decomposed into intermediate statements. Right now the mathematics is plausible, but the presentation asks the reader to accept too many steps at once.

The third needed improvement is the 
𝑆
3
S
3
	​

 example. It is one of the paper’s selling points and should be made more transparent, not less. Right now it still reads slightly like a supporting computation rather than a flagship example.

6. Concrete fixes
B1. Add a standalone twisted spectral-radius proposition before Theorem 4.11

Insert a proposition of the following form:

Proposition. For every irreducible unitary representation 
𝜎
σ of 
𝐺
G, one has

𝜌
(
𝐴
𝜎
)
≤
𝜌
(
𝐴
𝑒
)
=
𝜆
.
ρ(A
σ
	​

)≤ρ(A
e
	​

)=λ.

A clean proof route is:

By Proposition 4.2,

det
⁡
(
𝐼
−
𝑧
𝐴
𝑒
)
=
∏
𝜚
∈
I
r
r
(
𝐺
)
det
⁡
(
𝐼
−
𝑧
𝐴
𝜚
)
dim
⁡
𝜚
.
det(I−zA
e
	​

)=
ϱ∈Irr(G)
∏
	​

det(I−zA
ϱ
	​

)
dimϱ
.

Hence every eigenvalue of every 
𝐴
𝜎
A
σ
	​

 is also an eigenvalue of 
𝐴
𝑒
A
e
	​

.

The skew-product extension over a finite group has the same topological entropy as the base mixing SFT, so 
𝜌
(
𝐴
𝑒
)
=
𝜆
ρ(A
e
	​

)=λ.

Therefore 
𝜌
(
𝐴
𝜎
)
≤
𝜆
ρ(A
σ
	​

)≤λ.

This is the precise argument currently compressed into one sentence in Theorem 4.11. Once isolated, the later estimates become much more transparent. 

main

B2. Break Theorem 4.11 into four lemmas

A cleaner structure is:

Lemma (nontrivial channel bound).
For 
𝜚
≠
1
ϱ

=1,

𝜋
𝑛
,
𝜚
(
𝐴
)
=
𝑂
 ⁣
(
max
⁡
{
𝜂
𝑛
,
𝜆
𝑛
/
2
}
𝑛
)
.
π
n,ϱ
	​

(A)=O(
n
max{η
n
,λ
n/2
}
	​

).

Lemma (class decomposition).

𝑝
𝑛
,
𝐶
=
∣
𝐶
∣
∣
𝐺
∣
𝑝
𝑛
(
𝐴
)
+
∣
𝐶
∣
∣
𝐺
∣
∑
𝜚
≠
1
𝜒
𝜚
(
𝐶
−
1
)
𝜋
𝑛
,
𝜚
(
𝐴
)
.
p
n,C
	​

=
∣G∣
∣C∣
	​

p
n
	​

(A)+
∣G∣
∣C∣
	​

ϱ

=1
∑
	​

χ
ϱ
	​

(C
−1
)π
n,ϱ
	​

(A).

Lemma (absolute convergence at the Perron point).
Under 
𝜂
<
𝜆
η<λ,

Π
𝜚
(
𝜆
−
1
)
=
∑
𝑛
≥
1
𝜋
𝑛
,
𝜚
(
𝐴
)
𝜆
−
𝑛
Π
ϱ
	​

(λ
−1
)=
n≥1
∑
	​

π
n,ϱ
	​

(A)λ
−n

converges absolutely for every nontrivial 
𝜚
ϱ.

Theorem (class Mertens asymptotic).
Combine the preceding lemmas with Corollary 3.3 to obtain

∑
𝑛
≤
𝑁
𝑝
𝑛
,
𝐶
𝜆
𝑛
=
∣
𝐶
∣
∣
𝐺
∣
log
⁡
𝑁
+
𝑀
𝐶
(
𝐴
)
+
𝑂
(
𝑁
−
1
)
.
n≤N
∑
	​

λ
n
p
n,C
	​

	​

=
∣G∣
∣C∣
	​

logN+M
C
	​

(A)+O(N
−1
).

This would make the central asymptotic theorem much easier to verify line by line. 

main

B4. Strengthen Theorem 5.5 by inserting a lemma on one-dimensional characters

Add:

Lemma. A class function on 
𝐺
G lies in the span of pullbacks from cyclic quotients if and only if it lies in the span of the one-dimensional irreducible characters of 
𝐺
G.

Proof sketch.

If 
𝑞
:
𝐺
↠
𝑍
/
𝑚
𝑍
q:G↠Z/mZ and 
𝑓
f is a class function on the cyclic quotient, then 
𝑓
f is a linear combination of characters of 
𝑍
/
𝑚
𝑍
^
Z/mZ
	​

, and each pullback is one-dimensional on 
𝐺
G.

Conversely, if 
𝜒
:
𝐺
→
𝐶
×
χ:G→C
×
 is one-dimensional, then 
𝜒
(
𝐺
)
χ(G) is a finite subgroup of 
𝐶
×
C
×
, hence cyclic; thus 
𝜒
χ factors through a finite cyclic quotient.

Once this is stated explicitly, Theorem 5.5 becomes immediate and fully transparent. 

main

B5. Expand the 
𝑆
3
S
3
	​

 example into a fully auditable subsection

The example should explicitly display the standard representation matrices for the generators used in the edge labels. For instance, in the chosen basis,

𝜌
(
(
12
)
)
,
𝜌
(
(
23
)
)
,
𝜌
(
(
123
)
)
ρ((12)),ρ((23)),ρ((123))

should be written down before forming 
𝐴
𝜌
A
ρ
	​

. Then:

compute 
𝐴
𝜀
A
ε
	​

 and show 
𝐴
𝜀
2
=
0
A
ε
2
	​

=0,

compute 
𝐴
𝜌
A
ρ
	​

 and its characteristic polynomial 
𝑡
3
(
𝑡
+
1
)
t
3
(t+1),

derive 
𝐿
𝜀
(
𝑧
)
=
0
L
ε
	​

(z)=0 and 
𝐿
𝜌
(
𝑧
)
=
−
log
⁡
(
1
+
𝑧
)
L
ρ
	​

(z)=−log(1+z),

list the Adams decompositions 
𝜓
𝑚
𝜌
ψ
m
ρ,

extract 
𝜋
𝑛
,
𝜀
(
𝐴
)
π
n,ε
	​

(A) and 
𝜋
𝑛
,
𝜌
(
𝐴
)
π
n,ρ
	​

(A),

compute 
Δ
𝑒
,
Δ
𝑇
,
Δ
𝐾
Δ
e
	​

,Δ
T
	​

,Δ
K
	​

.

This would convert the example from a persuasive computation into a decisive one. 

main

M1. Insert a short proof of the Möbius-log identity in Theorem 3.1

The proof can be made self-contained by adding:

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
−
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
−
𝑥
,
k≥1
∑
	​

k
μ(k)
	​

log(1−x
k
)=−
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

=−
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

μ(k)=−x,

for 
∣
𝑥
∣
<
1
∣x∣<1, since 
∑
𝑘
∣
𝑛
𝜇
(
𝑘
)
=
0
∑
k∣n
	​

μ(k)=0 unless 
𝑛
=
1
n=1. This removes one hidden standard step. 

main

M3. Add an exponential-sum limsup lemma in Section 3

Before Theorem 3.7, add:

Lemma. If

𝑓
𝑞
=
∑
𝑗
=
1
𝑟
𝑐
𝑗
𝛼
𝑗
𝑞
f
q
	​

=
j=1
∑
r
	​

c
j
	​

α
j
q
	​


with 
𝑐
𝑗
≠
0
c
j
	​


=0 and 
𝛼
𝑗
∈
𝐶
α
j
	​

∈C, then

lim sup
⁡
𝑞
→
∞
∣
𝑓
𝑞
∣
1
/
𝑞
=
max
⁡
𝑗
∣
𝛼
𝑗
∣
.
q→∞
limsup
	​

∣f
q
	​

∣
1/q
=
j
max
	​

∣α
j
	​

∣.

Apply this to 
𝑢
𝑞
(
𝐴
)
u
q
	​

(A) and then use Proposition 3.5 to transfer the result to 
Ψ
𝑞
(
𝐴
)
Ψ
q
	​

(A). This would make the proof of Theorem 3.7 formally complete rather than heuristic. 

main

M8. Replace the proof step in Theorem A.2 by Jacobi’s formula

Instead of differentiating 
−
Tr
⁡
log
⁡
(
𝐼
−
𝑧
𝐴
𝜃
)
−Trlog(I−zA
θ
	​

), write directly:

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
𝑧
𝐴
𝜃
)
−
1
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
,
dθ
d
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

),

which is Jacobi’s formula in finite dimensions. This is cleaner and removes any unnecessary analytic subtlety about the matrix logarithm. 

main

Final recommendation

The correct editorial decision is major revision.

This is not a reject-level manuscript. It has a real mathematical core and several distinctive ideas, especially the finite-part formula and the Adams–Möbius primitive determinant calculus. But the paper is not yet fully convincing at the level of proof architecture expected for publication. It needs:

a standalone proof of the twisted spectral-radius bound,

a more modular build-up to the class Mertens theorem,

a tighter proof of the cyclic-detection boundary,

and a fully explicit 
𝑆
3
S
3
	​

 example.

With those revisions, the paper could become a strong specialist contribution in symbolic dynamics and finite-group extensions.