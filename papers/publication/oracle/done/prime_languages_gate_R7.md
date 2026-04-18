<!-- oracle metadata: {"timestamp": "2026-04-08T07:00:42.888099", "model": "chatgpt-5.4-pro-extended", "response_length": 8480} -->

I reviewed the manuscript. 

main

1. Overall assessment

Reject

The paper is readable and mostly technically straightforward, but one of its two advertised new contributions, the eventual sofic realization obstruction for prime Zeckendorf slices, is not genuinely new as stated. If 
𝐵
𝑚
(
𝑋
)
=
𝑃
𝑚
(
𝑍
)
B
m
	​

(X)=P
m
(Z)
	​

 for all sufficiently large 
𝑚
m, then the block language 
𝐵
(
𝑋
)
B(X) differs from the prime Zeckendorf language 
𝑃
𝑍
P
Z
	​

 by only finitely many words. Since block languages of sofic shifts are regular, Corollary 3.4 already excludes this. After that correction, the manuscript is left mainly with the Section 2 recall/precision observation, which is neat but quite short and derived from a standard density dichotomy. The manuscript itself also presents Theorem 1.1, the regular Zeckendorf growth law, and the analytic section as known or classical context. 

main

2. Novelty rating

The manuscript itself says that the real new content is Corollaries 1.2 and 1.3 plus the sofic-slice obstruction, while the other theorem-level statements are known/classical background. 

main

Result	Rating	One-line justification
Theorem 1.1 / 2.2 (density dichotomy for DFA languages)	LOW	Standard Perron-Frobenius / rational-series asymptotics specialized to complete binary DFAs.
Corollary 1.2 / 2.4 (symmetric-difference lower bound)	MEDIUM	Clean quantitative formulation, but it is a short consequence of Theorem 1.1 plus the prime number theorem.
Corollary 1.3 / 2.5 (no simultaneous recall and precision)	MEDIUM	Same as above, nice formulation but conceptually immediate once the density dichotomy is in place.
Theorem 1.4 / 3.1, first part (regular Zeckendorf growth law)	LOW	Known growth behavior for regular or 
𝑆
S-recognizable sets in numeration systems, presented here in a specialized proof.
Theorem 1.4, second part / Theorem 3.7 (prime Zeckendorf slices are not sofic)	LOW	As stated, this follows immediately from Corollary 3.4 plus regularity of sofic block languages and finite modification closure.
Theorem 1.5(i) / 4.1 (natural boundary for prime-supported Euler products)	LOW	Classical Pólya-Carlson-Estermann type material.
Theorem 1.5(ii) / Proposition 4.3 (periodicity of determinant models after 
𝑧
=
𝑒
−
𝑠
z=e
−s
)	LOW	Elementary observation once one writes 
det
⁡
(
𝐼
−
𝑒
−
𝑠
𝑀
)
−
1
det(I−e
−s
M)
−1
.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Sections 1, 3	BLOCKER	Theorem 3.7 is not genuinely new as stated. Eventual slice equality with a sofic block language differs from 
𝑃
𝑍
P
Z
	​

 only by finitely many words, so Corollary 3.4 already rules it out.	Remove Theorem 3.7 as a headline result, or strengthen it to a statement that is not implied by nonregularity.
B2	Whole paper	BLOCKER	Once B1 is corrected, the manuscript is left with one modest new observation in Section 2, while much of the paper is acknowledged background. This is not enough for a research journal in current form.	Either recast as a very short note focused on Section 2, or add substantially stronger new results.
M1	Section 2, Corollary 2.4	MEDIUM	The proof of the global bound (	L_m \triangle P_m^{(2)}
M2	Sections 1 and 3	MEDIUM	Theorem 1.4 mixes a known growth theorem with the claimed new sofic obstruction, which obscures novelty and logical dependence.	Split Theorem 1.4 into separate statements and label known material explicitly.
M3	Section 4	MEDIUM	The analytic section is classical and not used to prove the main finite-state claims. In a short paper it reads as padding.	Delete Section 4, or move it to a brief appendix/remark.
M4	Introduction / prior work	MEDIUM	The literature positioning is incomplete around density and growth of regular languages and numeration-system regular sets.	Add more direct references on polynomial densities and regular-set growth, and explain exactly what is new beyond them.
L1	Section 5	LOW	The remark that Section 2 uses “completeness and determinism in an essential way” is inaccurate for completeness. Any DFA can be completed by adding a sink.	Say that determinism is essential, while completeness is just a convenient normalization.
L2	Abstract / Introduction / Summary	LOW	The paper repeatedly advertises “two new obstructions,” which becomes misleading once B1 is fixed.	Rewrite the front matter after revising scope.
4. Missing references

No catastrophic bibliography gap, but I would add a few more direct sources that are closer to the actual arguments than some of the current broad citations:

Szilard, Yu, Zhang, Shallit (1992) on regular languages with polynomial densities. This is directly relevant to the Section 2 theme that regular languages cannot realize 
2
𝑚
/
𝑚
2
m
/m-type slice counts.

Shallit (1994), Numeration Systems, Linear Recurrences, and Regular Sets. This fits the Section 3 numeration/growth viewpoint very closely.

For standard background, Sakarovitch, Elements of Automata Theory and Perrin-Pin, Infinite Words would be good direct sources for automata/rational-series and sofic-shift background. 
Elsevier Shop
+3
Springer
+3
ScienceDirect
+3

5. Specific improvements needed to reach acceptance

First, Theorem 3.7 has to be either removed or replaced by a statement that is genuinely stronger than nonregularity up to finite modification.

Second, Section 2 needs to become the real mathematical core. At present the new content there is too slight. Either strengthen it substantially, for example to NFAs, weighted automata, or sharper approximation lower bounds, or recast the paper as a short note rather than a multi-section research article.

Third, repair the proof of Corollary 2.4 and do a full consistency pass on every statement that is supposed to hold for all sufficiently large lengths, not just on one residue class.

Fourth, cut the classical background materially. Section 4 should almost certainly go, and Proposition 3.5 plus Lemma 3.6 should stay only if they support a stronger replacement for Theorem 3.7.

6. Concrete fixes

B1. Theorem 3.7 is redundant.
Actionable fix: after Corollary 3.4, insert the one-paragraph argument that if 
𝐵
𝑚
(
𝑋
)
=
𝑃
𝑚
(
𝑍
)
B
m
	​

(X)=P
m
(Z)
	​

 for all 
𝑚
≥
𝑁
m≥N, then 
𝐵
(
𝑋
)
△
𝑃
𝑍
⊆
{
0
,
1
}
<
𝑁
B(X)△P
Z
	​

⊆{0,1}
<N
, hence 
𝑃
𝑍
P
Z
	​

 would be regular because 
𝐵
(
𝑋
)
B(X) is regular. Then either delete Theorem 3.7 entirely, or replace it with a genuinely stronger theorem, for example a quantitative asymptotic non-approximation statement for any language with eventually exponential-polynomial slice counts.

B2. Remaining novelty is too thin.
Actionable fix: choose one of two paths.
Path A: shorten the manuscript drastically and submit it as a brief note centered on Section 2.
Path B: add a substantial new theorem, for example extending the recall/precision obstruction beyond fixed DFAs, or proving optimal lower bounds for approximation by broader finite-state models.

M1. Corollary 2.4 proof gap.
Actionable fix: rewrite the proof residue class by residue class. For each 
𝑟
 
m
o
d
 
𝑝
rmodp, Theorem 2.2 gives

∣
𝐿
𝑝
𝑘
+
𝑟
∣
/
2
𝑝
𝑘
+
𝑟
=
𝑐
𝑟
+
𝑂
(
𝜃
𝑘
)
.
∣L
pk+r
	​

∣/2
pk+r
=c
r
	​

+O(θ
k
).

If 
𝑐
𝑟
=
0
c
r
	​

=0, then 
∣
𝐿
𝑝
𝑘
+
𝑟
∣
∣L
pk+r
	​

∣ is exponentially smaller than 
∣
𝑃
𝑝
𝑘
+
𝑟
(
2
)
∣
∣P
pk+r
(2)
	​

∣, so the symmetric difference is 
≫
2
𝑚
/
𝑚
≫2
m
/m. If 
𝑐
𝑟
>
0
c
r
	​

>0, then 
∣
𝐿
𝑝
𝑘
+
𝑟
∣
≫
2
𝑚
∣L
pk+r
	​

∣≫2
m
, so the symmetric difference is 
≫
2
𝑚
≫2
m
. Taking the minimum over residues yields the claimed uniform bound.

M2. Mixed theorem statement in 1.4.
Actionable fix: split into:

Theorem 3.1. Known regular Zeckendorf growth law.

Corollary 3.4. Prime Zeckendorf language is not regular.

Separate theorem only if there is a genuinely new stronger sofic statement.

M3. Classical Section 4.
Actionable fix: remove it from the main text. If the authors want to keep it, reduce it to a short appendix titled “Classical analytic remarks not used elsewhere.”

M4. Prior work discussion.
Actionable fix: add a short paragraph in the introduction saying exactly how the paper differs from classical density/growth results for regular languages and 
𝑆
S-recognizable sets, with direct citations to the density and numeration-system literature. Do not present Section 3 as a second new obstruction unless it truly is one after revision.

My bottom line is that the paper needs a substantial reframing. In its current form, the main claim of novelty is too strong, and one headline theorem is effectively redundant.