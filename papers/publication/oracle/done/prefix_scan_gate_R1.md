<!-- oracle metadata: {"timestamp": "2026-04-07T11:42:41.646709", "model": "o3-mini-high", "response_length": 8695} -->

1. Overall assessment

Reject.

The manuscript is readable and the displayed proofs appear mostly algebraically correct, but in its current form it does not meet the bar for a journal research article. The main reasons are: the central “new” theorems are extremely close to tautological consequences of the exact Bayes-risk decomposition and a standard discrete Tanaka identity; the submission is not bibliographically complete because unresolved citations remain and no reference list is printed; and the scope discussion overstates how broadly the rate assumptions are justified. 

main

I do not see a fatal proof gap in the formal identities themselves. The problem is mainly one of novelty, positioning, and journal readiness.

2. Novelty rating for each theorem

I rate only the theorem-labeled statements. Propositions 2.1, 3.2, 3.3 and Corollary 3.4 are classical, as the paper itself indicates.

Theorem	Novelty	One-line justification
Theorem 4.1	LOW	This is essentially the classical identity (\varepsilon_m=\tfrac12-\mathbb E
Theorem 5.2	LOW	The bound is an immediate counting estimate from Proposition 3.2 after restricting to boundary cylinders and bounding each summand by 
𝜇
(
𝐶
)
μ(C).
Theorem 5.3	LOW	The two-sided law follows directly from Proposition 3.2 once uniform cylinder-mass bounds and a uniform lower bound on 
min
⁡
{
𝑝
𝐶
,
1
−
𝑝
𝐶
}
min{p
C
	​

,1−p
C
	​

} are assumed.
3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Global / References	BLOCKER	The PDF contains unresolved citations such as “Parry [?]” and “Bowen [?]”, and no bibliography is printed. This makes the submission not formally reviewable.	Rebuild the bibliography, fix all citation keys, and include a complete reference list.
B2	4-5 / Overall contribution	BLOCKER	The main theorem chain is too elementary for journal publication. Theorems 4.1, 5.2, and 5.3 are very short corollaries of already stated classical formulas.	Either recast as a short expository note with much more modest claims, or add a genuinely stronger result.
M1	1, 7 / Literature positioning	MEDIUM	The manuscript does not compare its “uniform thickness” condition to the classical classification margin/noise literature, which is the obvious comparison point.	Add a literature subsection explaining the relation to margin assumptions and cite the foundational papers.
M2	7 / Entropy discussion	MEDIUM	The discussion overstates the role of Shannon-McMillan-Breiman. The theorem gives almost-sure asymptotics for the cylinder containing 
𝑥
x, not the uniform all-cylinder bounds assumed in Theorems 5.2 and 5.3.	Rewrite the discussion so uniform cylinder bounds are stated as separate hypotheses, or restrict claims to classes where they are known.
M3	2-7 / Framework	MEDIUM	The dynamical-systems framing is largely ornamental. 
𝑇
T-invariance and the dynamics are not used in the proofs. The results are really filtration statements.	Either formulate the paper on a general filtered probability space, or add results that use dynamics in an essential way.
M4	5 / Definitions	MEDIUM	Definition 5.1 is not fully precise. “Relevant cylinder complexity grows like 
𝜆
c
y
l
𝑚
λ
cyl
m
	​

” is undefined, and the boundary dimension depends on the chosen normalization.	Define the growth scale precisely and explain what is invariant and what is normalization-dependent.
M5	6 / Examples	MEDIUM	Example 6.2 is only schematic. It does not analyze a concrete event 
𝑃
P or compute 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P).	Replace it with at least one fully worked nontrivial example.
L1	4	LOW	The limit clause in Theorem 4.1 is stated under a condition that is already part of the standing setup 
𝑃
∈
𝐹
∞
P∈F
∞
	​

.	Remove the redundancy and streamline the statement.
L2	2-3	LOW	Notation is overloaded. 
𝑃
P denotes a subset of 
Ω
∞
Ω
∞
 in Proposition 2.1 and an event in 
𝑋
X elsewhere.	Separate symbolic-space and phase-space notation.

The bibliography problem and unresolved Parry/Bowen placeholders are visible in the submission itself. The SMB issue matters because the manuscript uses that discussion to motivate the uniform cylinder hypotheses, whereas SMB is an almost-sure statement about the cylinder containing the sample point. 

main

 
Faculty of Mathematics
+2
American Mathematical Society
+2

4. Missing references

At minimum, the following need to be added or properly resolved.

Enno Mammen and Alexandre B. Tsybakov, “Smooth discrimination analysis,” Annals of Statistics 27(6), 1999. This is a foundational reference for boundary/margin-based fast classification rates and is the natural comparison point for the paper’s thickness hypothesis. 
Project Euclid
+1

Alexandre B. Tsybakov, “Optimal aggregation of classifiers in statistical learning,” Annals of Statistics 32(1), 2004. This is a key general reference for margin/noise conditions and classification-rate theory. 
Project Euclid
+1

William Parry, “Intrinsic Markov chains,” Transactions of the AMS 112, 1964. The manuscript explicitly invokes Parry measure but leaves the citation unresolved. 
American Mathematical Society
+1

Rufus Bowen, “Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms,” Lecture Notes in Mathematics 470, 1975. The manuscript explicitly invokes Bowen for Gibbs/SFT cylinder asymptotics but leaves the citation unresolved. 
Springer
+1

5. Specific improvements needed to reach acceptance

The paper needs a complete and correct bibliography, with all unresolved citations fixed.

The contribution must be strengthened substantially. As written, the main results are too immediate to justify journal publication.

The scope must be narrowed or justified properly. In particular, entropy-theoretic discussion should not be used to suggest uniform cylinder bounds unless those implications are actually proved or cited for the relevant class.

The manuscript needs a real application or worked symbolic example where the boundary growth is computed for an explicit event.

The framing must be clarified. Either this is a general filtered-probability note, or it is a genuinely dynamical paper. At present it sits awkwardly between the two.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Recompile the manuscript with a functioning bibliography. Add a printed References section. Resolve every “[?]”. Check that every numbered citation appears in the bibliography and every bibliography item is cited in the text.

B2. Add at least one theorem that is not an immediate corollary of Proposition 3.2 plus a standard convexity identity. Plausible ways to do that:

replace the uniform thickness hypothesis with a genuine Tsybakov-style margin condition and derive a nontrivial rate;

handle nonuniform cylinder-mass profiles rather than assuming 
𝜇
(
𝐶
)
≍
𝜆
−
𝑚
μ(C)≍λ
−m
;

prove boundary-growth estimates for a concrete class of symbolic events;

or derive a computational/statistical consequence that is not already contained in the exact decomposition.

M1. Insert a subsection titled something like “Relation to margin assumptions in classification.” State explicitly whether your thickness condition is stronger than, equivalent to, or incomparable with standard margin/noise assumptions. Cite Mammen-Tsybakov 1999 and Tsybakov 2004 and explain the overlap.

M2. Rewrite the entropy paragraph. State SMB correctly as an almost-sure statement for the cylinder containing 
𝑥
x. Then separate that from the uniform all-cylinder bounds required by Theorems 5.2 and 5.3. If you want a standard regime where those bounds hold, state it explicitly for mixing SFTs with Parry/Gibbs measures and cite the appropriate sources.

M3. Decide the mathematical setting. If the dynamics are not used, rewrite the setup in terms of a filtered probability space and finite partitions. If you want to keep the dynamical framing, add a theorem where invariance, coding, or symbolic structure is actually used.

M4. Replace the informal phrase “relevant cylinder complexity grows like 
𝜆
c
y
l
𝑚
λ
cyl
m
	​

” with a precise definition. For example, define 
𝜆
c
y
l
λ
cyl
	​

 from the growth of the number of nonempty 
𝑚
m-cylinders in a fixed subshift, or avoid the “dimension” terminology and simply state all bounds in terms of 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P).

M5. Replace Example 6.2 with a fully worked example. Pick an explicit event 
𝑃
P in the golden-mean shift or another SFT, compute or sharply bound 
𝑁
𝑚
(
∂
𝑃
)
N
m
	​

(∂P), verify the thickness assumption, and then derive the resulting 
𝜀
𝑚
ε
m
	​

 asymptotics.

My bottom line is that this reads more like a short observation note than a research article. To become journal-ready, it needs both a stronger theorem and a much more careful scholarly rewrite.