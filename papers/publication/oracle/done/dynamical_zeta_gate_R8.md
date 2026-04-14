<!-- oracle metadata: {"timestamp": "2026-04-08T05:50:42.856974", "model": "chatgpt-5.4-pro-extended", "response_length": 12198} -->

I reviewed the attached manuscript on finite parts of dynamical zeta functions and finite-group extensions. 

main

1. Overall assessment

Major revision

The paper is technically ambitious, and on a first-pass reading I do not see an obvious fatal algebraic error in the main line of Sections 3 to 5. The main problem is not basic correctness. It is publication positioning. The manuscript currently presents the explicit finite-part/Mertens formula and the finite-group extension package as if both were clearly new at theorem level, but the novelty case is not yet convincing enough. Explicit dynamical Mertens constants of essentially the same shape already occur in the Sharp/Pollicott line, and Chebotarev asymptotics for finite homogeneous extensions of shifts of finite type already appear in Noorani-Parry. In addition, the bibliography omits several central precursors for twisted Perron-Frobenius/dynamical L-functions and covering-zeta theory. 
ScienceDirect
+5
arXiv
+5
arXiv
+5

My editorial view is that there is probably a publishable core here, but it is narrower than the current presentation suggests. The strongest candidate for genuine novelty is the primitive Peter-Weyl / Adams-Möbius packaging, especially Corollaries 4.5 and 4.8, not the whole present theorem architecture.

2. Novelty rating for each theorem

I am rating the body theorems, not the introductory restatements Theorems 1.1 to 1.3.

Main text
Theorem	Rating	One-line justification
Theorem 3.1	LOW	Neat finite-state rewrite, but very close in substance to existing explicit dynamical Mertens constant formulas.
Theorem 3.4	LOW	Straight determinant/spectrum computation for cyclic lifts.
Theorem 3.8	LOW	Largely Möbius inversion on multiples plus Newton identities.
Theorem 3.9	LOW	Essentially discrete Fourier interpolation of a degree 
<
𝑞
<q polynomial from root-of-unity samples.
Theorem 4.4	MEDIUM	Useful packaging of twisted determinant linearization in this finite-state class-function language, though conceptually close to standard dynamical L-function formalisms.
Theorem 4.11	LOW	Direct conjugacy-class Fourier inversion from character theory.
Theorem 4.18	MEDIUM	The leading Chebotarev asymptotic is known, but the class-constant packaging and Perron-point primitive-channel formulation are useful additions.
Theorem 4.21	MEDIUM	Conceptually nice reconstruction of primitive twisted values from class constants, though driven mainly by standard character orthogonality.
Theorem 5.2	LOW	Formal functoriality under quotient pullback.
Theorem 5.4	LOW	Orthogonal splitting into one-dimensional and higher-dimensional sectors is essentially formal once the Fourier expansion is set up.
Theorem 5.6	LOW	Follows formally from the previous orthogonal decomposition and the identification of cyclic quotients with one-dimensional characters.
Appendices
Theorem	Rating	One-line justification
Theorem A.1	LOW	Standard perturbation/group-inverse differentiation formula.
Theorem A.2	LOW	Routine holomorphic differentiation of determinant identities.
Theorem A.3	LOW	Elementary truncation estimate.
Theorem B.1	LOW	Parseval plus finite aliasing.
Theorem B.5	LOW	Standard finite-character inversion.
Theorem B.7	LOW	Nice observation, but technically elementary Cesàro averaging of exponential sums.
Theorem B.10	LOW	Mostly a restatement once the reconstruction result is available.
Theorem B.11	LOW	Pleasant generating-series reformulation, but elementary polylog expansion.
Theorem C.2	LOW	Straight consequence of previous determinant bounds and the square-root hypothesis.
3. Issue table

Two external benchmarks drive the table below. First, prior dynamical Mertens work already gives an explicit constant of the same structural form as Theorem 3.1. Second, prior work already covers Chebotarev asymptotics for finite homogeneous SFT extensions, and older twisted L-function / covering-zeta frameworks are directly relevant to Sections 4 and 5. 
ScienceDirect
+5
arXiv
+5
arXiv
+5

ID	Section	Severity	Description	Suggested fix
B1	Intro, §3	BLOCKER	Theorem 3.1 is presented as a main new contribution, but the paper does not clearly distinguish it from prior explicit dynamical Mertens constant formulas.	Recast Theorem 3.1 as a specialization/refinement of prior Mertens formulas, or prove a sharper increment that is genuinely new.
B2	Intro, refs, §4	BLOCKER	The bibliography is missing core predecessors for twisted Perron-Frobenius/dynamical L-functions and covering-zeta theory. That makes the Section 4 novelty claim incomplete.	Add the missing references and include a theorem-by-theorem comparison paragraph in the introduction or beginning of §4.
B3	Whole paper	BLOCKER	The theorem architecture inflates many formal or elementary consequences into headline results, which obscures the actual contribution.	Restructure the paper around the real new core, likely the Adams-Möbius primitive-channel formalism, and demote elementary consequences to propositions/remarks.
M1	§3.2	MEDIUM	
𝐶
(
𝐴
)
C(A) is defined for primitive matrices, but then used for cyclic lifts 
𝐴
⟨
𝑞
⟩
=
𝐴
⊗
𝑃
𝑞
A
⟨q⟩
=A⊗P
q
	​

, which are imprimitive for 
𝑞
>
1
q>1.	Extend the definition of the residue constant/reduced determinant to any matrix with a simple eigenvalue at the relevant pole, and state this explicitly before Theorem 3.4.
M2	Theorem 3.8	MEDIUM	The proof says 
𝐹
𝐴
F
A
	​

 has “known degree 
𝑑
−
1
d−1,” but the statement sounds like the cyclic data alone determine 
𝐹
𝐴
F
A
	​

.	Either include 
𝑑
d as part of the input, or prove degree recovery from the power-sum sequence, for example via minimal recurrence or Hankel rank.
M3	§4	MEDIUM	Theorems 4.4, 4.18, and 4.21 are not compared precisely enough with older dynamical 
𝐿
L-function frameworks.	Add a short “comparison with classical twisted 
𝐿
L-functions” subsection translating the present notation into standard literature terms and stating the exact increment.
M4	§4.3 to §4.4	MEDIUM	Theorem 4.18 mixes a known leading asymptotic with newer constant-term packaging, and the conditional role of 
𝜂
<
𝜆
η<λ is not emphasized strongly enough.	Split clearly between known asymptotic input and new consequences, and mark the Perron-point results as conditional already in the abstract and intro.
M5	Appendices	MEDIUM	The appendices are too long relative to the real contribution, and many results are routine consequences.	Trim aggressively, or move much of Appendices B and C to a supplementary note.
L1	§3.3, §5	LOW	Several results are mathematically correct but too elementary to be theorem-level in a research paper.	Demote some of them to propositions or remarks.
L2	Examples	LOW	The worked examples are too small to support the breadth of the claims.	Add at least one nontrivial computational example beyond the Fibonacci toy model and the single 
𝑆
3
S
3
	​

 example.
L3	References, exposition	LOW	The bibliography and exposition need a full consistency audit.	Check citation completeness, theorem labels, and relevance of every listed reference.
4. Missing references

The following are the most important omissions I noticed.

T. Adachi and T. Sunada, “Twisted Perron-Frobenius theorem and L-functions,” J. Funct. Anal. 71 (1987), 1 to 47. This is a foundational precursor for the twisted determinant / twisted 
𝐿
L-function viewpoint that Section 4 is very close to. 
ScienceDirect
+1

T. Sunada, “Dynamical 
𝐿
L-functions and homology of closed orbits,” Bull. Amer. Math. Soc. 20 (1989), 73 to 77. This is a natural conceptual precursor for the paper’s non-abelian / homological / Fourier-decomposition framing. 
ResearchGate
+1

H. M. Stark and A. A. Terras, “Zeta Functions of Finite Graphs and Coverings,” Adv. Math. 121 (1996), 124 to 165. This is important for the covering-graph / Artin-type determinant side of the story. 
ScienceDirect

Graph-theoretic Mertens literature, especially work contextualizing explicit Mertens constants and prime-zeta expansions. This is less central than the items above, but it would help position Theorem 3.1 more honestly. 
arXiv
+1

5. Specific improvements needed to reach acceptance

First, the paper needs a full novelty rewrite. The introduction should separate clearly between:

known background being specialized,

formal consequences,

genuinely new contributions.

Second, Section 4 should become the center of the paper. Right now the likely publishable increment, namely the primitive Adams-Möbius / Peter-Weyl packaging, is buried among many lower-novelty statements.

Third, the paper needs a serious prior-work comparison subsection. Not a broad bibliography paragraph. A theorem-by-theorem comparison.

Fourth, the statements in Section 3 need tightening. In particular, the use of 
𝐶
(
𝐴
⟨
𝑞
⟩
)
C(A
⟨q⟩
) and the “known degree” input in Theorem 3.8 should be made logically precise.

Fifth, the appendices should be shortened. The current manuscript reads like several papers’ worth of corollaries attached to one core note.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1

Add a subsection before Theorem 3.1 titled something like “Relation with classical dynamical Mertens constants.” State explicitly whether Theorem 3.1 is:

a specialization of the Sharp/Pollicott formula to primitive SFT matrices,

a simplification of the constant into reduced-determinant language,

or a genuinely stronger statement.

If it is only a specialization plus repackaging, say so plainly and lower the claim.

B2

Expand the bibliography and insert a direct comparison paragraph for Section 4. For each of Theorems 4.4, 4.18, and 4.21, add three sentences:

what was already known,

what overlaps,

what is new here.

Without that, the referee cannot fairly assess novelty.

B3

Rebuild the theorem structure around the likely new core. My recommendation:

promote the Adams-Möbius primitive inversion mechanism to the main theorem,

keep the class-constant Fourier reconstruction as a second-tier consequence,

demote Theorems 3.9, 5.2, 5.4, and 5.6 to propositions/remarks unless the author can justify why they deserve theorem status.

M1

Before Theorem 3.4, define for a general finite matrix 
𝑀
M with a simple eigenvalue 
𝜆
λ:

𝐶
𝜆
(
𝑀
)
:
=
lim
⁡
𝑧
→
𝜆
−
1
(
1
−
𝜆
𝑧
)
det
⁡
(
𝐼
−
𝑧
𝑀
)
−
1
.
C
λ
	​

(M):=
z→λ
−1
lim
	​

(1−λz)det(I−zM)
−1
.

Then restate Proposition 3.2 in this generality and use that notation for cyclic lifts. That removes the current primitive/imprimitive ambiguity.

M2

Either:

restate Theorem 3.8 as “given 
𝑑
d and 
{
Ψ
𝑞
(
𝐴
)
}
𝑞
≥
1
{Ψ
q
	​

(A)}
q≥1
	​

, one recovers 
𝐹
𝐴
F
A
	​

,” or

add a proof that the degree can itself be reconstructed from the recovered power sums 
𝑢
𝑛
u
n
	​

, for example through the minimal linear recurrence or finite Hankel rank of the sequence.

The current proof uses extra input not visible in the statement.

M3

Add a short subsection in §4 called “Dictionary with classical twisted 
𝐿
L-functions.” Translate:

𝐿
𝜑
(
𝑧
)
L
φ
	​

(z) into twisted logarithmic determinant language,

Π
𝜑
(
𝑧
)
Π
φ
	​

(z) into primitive-orbit channels,

the Adams operation into the passage from periodic to primitive data.

Then cite the older twisted 
𝐿
L-function papers explicitly and state the delta.

M4

Split Theorem 4.18 conceptually into:

the known-type Chebotarev asymptotic input,

the new explicit constant-term and Fourier-reconstruction consequences.

Also, flag in the abstract and introduction that the Perron-point class constants depend on the assumed twisted spectral gap 
𝜂
<
𝜆
η<λ. At minimum, add one more nontrivial worked example where this hypothesis is checked.

M5

Trim the appendices to what the main paper actually uses. My suggestion:

keep A.1 to A.3 only if analytic perturbation is part of the paper’s core message,

keep only one or two arithmetic corollaries in Appendix B,

move the rest to supplementary material.

In the current form, the appendices dilute the contribution rather than strengthen it.

My bottom line is: there may be a solid paper here, but it is not yet in accept-ready form. The author needs to narrow the claim, repair the literature positioning, and reorganize the manuscript so that the genuinely new finite-group primitive-channel calculus is unmistakably the center.