<!-- oracle metadata: {"timestamp": "2026-04-08T11:15:42.901553", "model": "chatgpt-5.4-pro-extended", "response_length": 10074} -->

1. Overall assessment

Major revision

The manuscript is a coherent and technically ambitious case study of one quartic spectral family, and much of the algebra in Sections 3 to 5 and 7 to 8 appears internally consistent. However, I would not recommend acceptance in the current form for two reasons. First, the journal-level contribution is not yet convincingly established beyond a specialized worked example. Second, Section 6 contains incorrect general statements about spectral-radius analyticity and modulus crossings, so one of the headline parts of the paper is not rigorously supported as written. 

main

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 3.1	LOW	Standard coprimeness/resultant reasoning gives minimal recurrence order and Hankel rank.
Theorem 4.4	MEDIUM	The explicit elliptic normalization and exact branch-value extraction for this specific quartic are neat and likely original for this family, but the method is classical.
Theorem 5.2	MEDIUM	The dominant versus subdominant classification of the real branch points is nontrivial and specific to the family, though still essentially a careful case analysis.
Theorem 5.6	MEDIUM	The complete real-root phase diagram from the real ovals of the elliptic normalization is explicit and useful, but specialized.
Theorem 6.3	LOW	This is mainly an explicit parameterization and monotonicity computation for one branch.
Theorem 6.9	MEDIUM	This is the strongest original-looking part: it extracts finite-size zero asymptotics from local branch geometry, but remains family-specific and uses standard local tools.
Theorem 7.1	LOW	Degree growth and leading coefficients follow by straightforward induction on the recurrence.
3. Issue table

Based on the submitted manuscript, especially Sections 1, 5, 6, 9 and Appendix D. 

main

ID	Section	Severity	Description	Suggested fix
B1	Global	BLOCKER	The paper does not yet make a convincing case for journal-level significance. Most results are explicit computations for one hand-picked quartic, while the broader balanced-family observation is not developed far enough to carry the paper.	Either generalize to a nontrivial theorem for the full balanced family, or connect the quartic to a substantive external model/problem. Otherwise reposition as a short note and scale down claims.
B2	§6.1, Prop. 6.5, Rem. 6.2	BLOCKER	Section 6 uses false general claims. Simplicity of eigenvalue branches does not imply analyticity of the spectral radius, and equal modulus of two simple roots does not force discriminant zero. The current “no modulus crossing without collision” logic is invalid.	Rewrite Section 6 so that global dominance is proved directly by explicit inequalities, not by discriminant-based branch-crossing arguments.
M1	Lemma 5.1	MEDIUM	The proof contains a reversed inequality relative to assumption (25). The displayed chain uses (	\mu_*
M2	§6	MEDIUM	Internal references are broken. The text refers to Lemmas 6.12 and 6.13, which do not exist in the submitted version. Also, “the largest-modulus root 
𝑟
(
𝑦
)
r(y)” is malformed, since 
𝑟
(
𝑦
)
r(y) is a modulus, not a root.	Fix numbering and rewrite the statements precisely.
M3	§1.1, References	MEDIUM	The literature review omits closely related work on four-term recurrences, hyperbolicity, and rational-generating-function zero loci.	Add the missing references and state explicitly what is new relative to them.
M4	Abstract, §1.2, §10	MEDIUM	The novelty language is stronger than the evidence currently provided. Several claims read like “first/exact/foundational” statements without a sufficiently complete comparison to prior work.	Tone down novelty claims or support them with precise comparisons.
M5	Appendix D / notation	MEDIUM	Notation is overloaded. 
𝐶
0
C
0
	​

 is both a constant in the local cosine law and, later, a branch amplitude associated with the small root. This creates avoidable ambiguity.	Rename constants and branch amplitudes systematically.
M6	§9, App. C	MEDIUM	The numerical section is not fully reproducible. Pseudo-code is given, but not the actual scripts, precision settings beyond standard double precision, or certified checks near modulus ties.	Provide a supplementary code archive and include higher-precision or certified checks near 
𝑦
=
0
,
1
,
𝑦
s
u
b
y=0,1,y
sub
	​

.
L1	Throughout	LOW	Some terminology is unnecessarily physical or misleading for a purely algebraic paper, e.g. “Perron simplicity” and “vacuum-edge quantization.”	Use strictly mathematical terminology unless a physical model is actually supplied.
L2	Abstract, Intro	LOW	The exposition is verbose and somewhat repetitive.	Compress routine parts and move more calculations to appendices.
4. Missing references

The most important omissions, in my view, are these:

Beraha, Kahane, Weiss, Limits of zeroes of recursively defined families of polynomials (1978). The paper cites the 1975 PNAS note, but the fuller 1978 treatment is the standard detailed reference for the theorem actually being used. 
Contributions to Discrete Mathematics

Biggs, Equimodular curves (2002). This is relevant to the geometry of dominant-equimodular sets, which is central to the manuscript’s interpretation of the zero-attractor picture. 
ScienceDirect

Forgács and Tran, Zeros of polynomials generated by a rational function with a hyperbolic-type denominator (Constructive Approximation, 2017). This is a direct continuation of the rational-generating-function zero literature already cited by the manuscript. 
arXiv

Forgács and Tran, Hyperbolic polynomials and linear-type generating functions (JMAA 488(2), 2020). This broadens the real-zero / generating-function framework and should be discussed if the paper wants to claim novelty in that direction. 
ScienceDirect

Tran and Zumba, Zeros of polynomials with four-term recurrence and Zeros of polynomials with four-term recurrence and linear coefficients. Both are directly relevant because the present paper is built around a four-term recurrence and real-zero structure. 
arXiv
+1

Adams, On hyperbolic polynomials with four-term recurrence and linear coefficients (Calcolo, 2020). Also relevant to the four-term-recurrence side of the story. 
Springer

5. Specific improvements needed to reach acceptance

Repair Section 6 completely. The dominant-sheet argument must be rewritten without the false claim that modulus crossings require repeated roots.

Clarify what the actual contribution is. Right now the paper reads as a very detailed worked example. For acceptance in a standard research journal, it needs either broader generalization or sharper justification for why this quartic is intrinsically important.

Strengthen the literature comparison. The introduction should explain, theorem by theorem, what is new relative to the existing rational-generating-function and four-term-recurrence literature.

Tighten the exposition. There is a solid paper hidden here, but it needs a cleaner separation between classical background, routine algebra, and the genuinely new parts.

Improve reproducibility. The numerical section should be a supporting supplement, not a black box.

6. Concrete fixes for each BLOCKER and MEDIUM issue
ID	Concrete fix
B1	Add one substantial general theorem beyond the current specialization. The natural route is to develop the balanced family 
𝑃
𝑎
,
𝑐
,
𝑑
,
𝑔
P
a,c,d,g
	​

 further: for example, give criteria for the number of real branch values, the topology of the real locus, or conditions under which the real 
𝑦
y-projection is one interval versus two. If that is not done, then explicitly recast the paper as a short case-study note and moderate the claims accordingly.
B2	Replace Lemma 6.1 by a corrected local statement: simple roots vary analytically locally, and strict dominance persists locally by continuity. Remove all claims that the spectral radius is analytic before uniqueness is proved, and delete the assertion that equal modulus forces discriminant zero. In Proposition 6.5, keep the direct pointwise arguments from Case 1 and Case 2, which already nearly prove the result, and delete Step 3 or replace it by a legitimate continuity argument using an explicit modulus gap.
M1	Rewrite Lemma 5.1 so the inequalities match assumption (25). A short proof is enough: bound non-bifurcating roots by (
M2	Run a full cross-reference audit after recompilation. Fix the nonexistent references to 6.12 and 6.13, and rewrite phrases like “largest-modulus root 
𝑟
(
𝑦
)
r(y)” as “a root of modulus 
𝑟
(
𝑦
)
r(y)” or, after dominance is proved, “the dominant root 
𝜆
d
o
m
(
𝑦
)
λ
dom
	​

(y).”
M3	Expand §1.1 by one focused paragraph comparing the paper to: full BKW, equimodular-curve literature, rational generating functions with hyperbolicity, and four-term recurrence papers. State explicitly: what those papers already do, what they do not do, and where this manuscript adds something different.
M4	Remove or soften phrases such as “first negative zeros” unless the author can document that priority claim precisely. Replace broad novelty language by narrower claims, e.g. “for this quartic family we obtain an explicit elliptic normalization and endpoint zero asymptotics.”
M5	Rename the local-cosine-law constant 
𝐶
0
C
0
	​

 to something like 
𝐴
∗
A
∗
	​

, and rename the amplitude of the 
𝜆
≈
0
λ≈0 branch to 
𝐶
s
m
a
l
l
(
𝑦
)
C
small
	​

(y). Similar cleanup should be applied to any notation that visually clashes with 
𝑦
0
y
0
	​

, 
𝜆
0
λ
0
	​

, or branch labels.
M6	Supply the exact scripts used to generate Figure 1 and the numerical checks, preferably as supplementary material. Use at least one higher-precision check near 
𝑦
=
0
y=0, 
𝑦
=
1
y=1, and 
𝑦
s
u
b
y
sub
	​

, where ordering by modulus is delicate. Also state clearly whether repeated roots are factored out before rootfinding.

My bottom line is that this is not an accept in its present state, but it is also not far from a potentially publishable paper if the author fixes Section 6, improves the positioning, and either broadens the general theory or reframes the manuscript more modestly.