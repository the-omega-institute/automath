<!-- oracle metadata: {"timestamp": "2026-04-13T18:06:45.876752", "model": "chatgpt-5.4-pro-extended", "response_length": 12617} -->

Overall assessment: Major revision

There is a potentially publishable finite-state core here, especially the exact killed-matrix formula for the Bayes error and the residue-dependent quasistationary amplitude. But the manuscript is not ready in its current form. The main reasons are: the observation model is not consistently defined across the paper, one theorem is overstated as written, one auxiliary proposition is incorrectly formulated, and too much of the framework is left at sketch level rather than proved cleanly. My recommendation is Major revision, not rejection, because these problems look repairable if the paper is substantially refocused around Section 6. 

main

Novelty rating for each theorem

I rate distinct theorem content only. Theorem 1.1 = Theorem 6.1, and Theorem 1.2 = Theorem 6.10. 

main

Theorem 5.4 (Tanaka identity). LOW. Classical martingale/Tanaka machinery used as background, not a new contribution.

Theorem 5.7 (Upper boundary estimate). LOW. Standard boundary counting estimate in spirit, and currently not correctly stated at the level of the final asymptotic claim.

Theorem 5.8 (Weighted boundary transfer). MEDIUM. Useful packaging of weighted boundary mass via automata and Perron-Frobenius theory, but conceptually close to standard weighted automaton/path-sum methods.

Theorem 1.1 / 6.1 (First-entry residue events and escape rates). MEDIUM. The novelty is the observable and its interpretation, not a new escape-rate mechanism. The proof is largely a clean Markov/Perron-Frobenius repackaging.

Theorem 1.2 / 6.10 (Quasistationary ambiguity amplitudes). MEDIUM. This is the strongest genuinely new refinement in the paper, but once the path-sum formula is established the ratio asymptotic is a fairly natural Perron-Frobenius consequence.

Issue table

The table below refers to the current manuscript. 

main

ID	Section	Severity	Description	Suggested fix
B1	§§2-6	BLOCKER	The observation model is inconsistent. Early sections define Bayes error via a binary readout sigma-algebra, while Section 6 computes Bayes error by conditioning on full symbolic cylinders over the SFT alphabet. As written, the main theorem is not transparently a specialization of the earlier framework.	Rewrite the preliminaries for finite-alphabet observation, or explicitly redefine the observation sigma-algebra before Theorem 6.1. If binary observation is intended, derive the hidden-state filtered version instead.
B2	Theorem 5.7	BLOCKER	The last sentence claims an asymptotic equality from a one-sided upper bound. That does not follow and is generally false without matching lower estimates.	Replace the equality by an upper bound, or add lower cylinder-mass and nondegenerate boundary-weight hypotheses and prove the lower bound.
B3	Theorem 5.8 / §5	BLOCKER	A structurally central theorem is only sketched. Definitions such as boundary language, nondegenerate boundary weights, and the pressure term are not developed at publication level.	Either provide a full proof with precise hypotheses, or delete the general framework and keep only the self-contained finite-state theory needed for Section 6.
B4	Proposition 6.2 / Remark 6.3	BLOCKER	The proposition is incorrectly formulated for transient states. An SCC cannot both contain a transient state 
𝑖
i and intersect 
𝑆
∞
S
∞
	​

. The proof mixes transient and recurrent behavior.	Split the statement into cases 
𝑖
∈
𝑆
∞
i∈S
∞
	​

 and 
𝑖
∈
𝑇
i∈T, or remove the proposition and replace it with a direct finite graph reachability test modulo 
𝑞
q.
M1	Abstract / Introduction	MEDIUM	The novelty framing is broader than the actual proof content. Phrases like “cyclotomic resonance structure” suggest more than the paper proves, since the resolvent result is pole containment plus a genuine dominant pole.	Narrow the claims. State plainly that the new part is the Bayes-error observable and residue amplitude, while the escape-rate and PF ingredients are standard.
M2	Front matter / Introduction	MEDIUM	The manuscript contains process-oriented text that should not appear in a journal paper, such as comments about ETDS targeting and “the main editorial change relative to the first submission.”	Remove all journal-targeting and resubmission language. Keep only mathematics and literature positioning.
M3	§§2-4	MEDIUM	The binary-readout preliminaries and recursive re-coding material are much broader than what the paper actually proves, and they blur the finite-state symbolic core.	Compress these sections heavily or move them to an appendix. Start the paper directly in the symbolic Markov setting.
M4	§6.3 / Remark 6.12	MEDIUM	The conjectural Hölder extension is too long and too theorem-like for material that is not proved.	Reduce it to a short concluding remark, or remove it entirely.
M5	§7	MEDIUM	The Rényi/Poisson consequences are secondary and currently occupy too much space relative to the main contribution.	Compress Section 7 into one short corollary subsection, or move the Chen-Stein details to an appendix.
M6	References / positioning	MEDIUM	The positioning around quasistationary distributions and holes is incomplete.	Add the missing references listed below and use them to sharpen the introduction.
L1	Throughout	LOW	The theorem statements are very long and notation-heavy.	Move common setup into a notation subsection and shorten the statements.
L2	Bibliography	LOW	Bibliographic formatting is uneven, with a mix of complete journal entries and incomplete preprint-style entries.	Standardize the bibliography and update incomplete entries.
L3	Examples	LOW	The examples are useful, but a genuinely multi-state non-Bernoulli example would better display the new effect.	Add one asymmetric 2- or 3-state Markov example with visibly different residue amplitudes.

Missing references

At minimum, I would add the following.

Darroch and Seneta (1965), “On quasi-stationary distributions in absorbing discrete-time finite Markov chains.” This is the classical finite-state reference for the quasistationary-distribution viewpoint that the paper uses in Theorem 6.10. 
Cambridge University Press & Assessment
+1

Collet, Martínez, and San Martín, Quasi-Stationary Distributions: Markov Chains, Diffusions and Dynamical Systems (Springer, 2013). This would strengthen the quasistationary positioning and connect the finite-state result to the broader dynamical-systems QSD literature. 
Springer
+1

Collet, Martínez, and Schmitt (1996), “Quasi-Stationary Distribution and Gibbs Measure of Expanding Systems.” This is directly relevant if the authors want to emphasize the Gibbs/QSD connection. 
Springer

Haritha and Agarwal (2019), “Product of expansive Markov maps with hole.” Since the introduction already discusses recent Agarwal/Cheriyath work, this earlier related paper should also be acknowledged. 
AIMS

Bandtlow and Jenkinson (2014), “Eigenvalues of Transfer Operators for Dynamical Systems with Holes.” This is relevant to the spectral/resolvent discussion around Corollary 6.11. 
Springer
+1

Bonanno, Cristadoro, and Lenci (2022), “Maximal escape rate for shifts.” This is not central to the Bayes-error viewpoint, but it is relevant recent shift-with-holes background if the authors want broader SFT positioning. 
AIMS
+1

Specific improvements needed to reach acceptance

Recast the paper as a focused finite-state symbolic dynamics paper, centered on Theorem 6.1, Theorem 6.10, Corollary 6.11, and a much shorter consequence section. 

main

Fix or remove the mathematically problematic statements. In particular, Theorem 5.7 cannot stay as written, and Proposition 6.2 needs a genuine correction, not cosmetic rephrasing. 

main

Unify the observation model. The reader must know exactly what information is available at depth 
𝑚
m, and that model must be the same one used in the proofs. 

main

Provide complete proofs for all retained nontrivial statements. ETDS will not accept a paper whose central framework is still at the “proof sketch” stage unless those results are explicitly cited from the literature. 

main

Rewrite the introduction to remove meta-editorial language and state the contribution more precisely. The current version still reads partly like a response to prior review rather than a finished journal article. 

main

Compress or remove the conjectural Hölder extension. The present manuscript is strongest when it stays finite-state and exact. 

main

Concrete fixes

B1. Observation model mismatch.
Introduce a single preliminary definition: for an observed process with alphabet 
𝐴
o
b
s
A
obs
	​

, let 
𝐹
𝑚
=
𝜎
(
𝑦
0
,
…
,
𝑦
𝑚
−
1
)
F
m
	​

=σ(y
0
	​

,…,y
m−1
	​

). Then state explicitly that in the main symbolic theorem 
𝐴
o
b
s
=
𝐴
A
obs
	​

=A, or the 
ℓ
ℓ-block alphabet after recoding. Remove the earlier binary 
𝑊
W-readout framework unless it is only a one-paragraph motivation. If the authors truly want binary observation as the main model, then Section 6 must be recomputed using filtered terminal-state distributions rather than full cylinder conditioning. 

main

B2. False or overstated Theorem 5.7.
Change the theorem to a correct one-sided statement:

𝜀
𝑚
(
𝑃
;
𝜇
)
≤
𝐶
 
𝜆
c
y
l
−
(
1
−
𝑑
+
𝑜
(
1
)
)
𝑚
.
ε
m
	​

(P;μ)≤Cλ
cyl
−(1−d+o(1))m
	​

.

If the authors want a two-sided asymptotic, they need extra assumptions such as comparable cylinder masses on boundary cylinders and a uniform lower bound on the Bayes weights 
𝛽
𝑃
(
𝑎
)
β
P
	​

(a). Then they should prove both the lower and upper bounds explicitly. If that is not needed later, the cleanest repair is simply to delete the asymptotic equality claim. 

main

B3. Incomplete Theorem 5.8.
There are two viable routes. Route A: give the full proof. That means defining the regular boundary language precisely, proving the bijection between accepted words and product-graph paths, deriving the matrix formula, then applying Perron-Frobenius and the pressure conjugacy carefully. Route B: remove Section 5.2 entirely and keep only the self-contained Section 6 proof, which already carries the paper’s real content. For this manuscript, Route B may actually produce the stronger paper. 

main

B4. Incorrect Proposition 6.2.
Rewrite it as two statements. For 
𝑖
∈
𝑇
i∈T, the safe subgraph on 
𝑇
T is acyclic, so 
𝐿
𝑖
L
i
	​

 is finite and 
𝐷
𝑖
D
i
	​

 is just a finite set of residues. For 
𝑖
∈
𝑆
∞
i∈S
∞
	​

, use the unique primitive survivor component to obtain eventual periodicity, which under mixing should in fact reduce to period 
1
1 on the survivor component. If the proposition is not used later, the best fix is to remove it and keep only Lemma 6.4 plus an algorithmic remark based on breadth-first search modulo 
𝑞
q. 

main

M1. Overstated novelty language.
Replace broad claims like “cyclotomic resonance structure” with the exact proved statement: the error generating function is a scalar resolvent coefficient whose poles are contained in the reciprocal cyclotomic lift of the killed spectrum, and whose dominant real pole is genuine. Also state more plainly that the new ingredient is the Bayes-error observable, while the escape-rate formula and PF asymptotics are standard. 

main

M2. Meta-editorial text.
Delete text about ETDS focus, “the main editorial change relative to the first submission,” and similar process comments. Replace it with one clean paragraph explaining the mathematical hierarchy of results. 

main

M3. Overlong preliminaries.
Cut Sections 2-4 to a few pages at most, or move them to an appendix. The paper can begin almost immediately with: setup, Bayes error on symbolic prefixes, killed matrix, main theorem. That would make the contribution much easier to see. 

main

M4. Conjectural Hölder roadmap.
Reduce Remark 6.12 to a short final remark saying that a Hölder/cylinder-hole extension is expected after block recoding but is not proved here. The current multi-part formal roadmap reads too much like an unproved theorem. 

main

M5. Secondary corollaries.
Compress Section 7. One concise corollary for survivor Rényi pressure, followed by a brief statement about the Poisson birthday threshold, is enough. The detailed Chen-Stein setup is standard and should not dominate the paper’s narrative. 

main

M6. Literature positioning.
Add the missing quasistationary and open-hole references above, and revise the introduction so that the paper is positioned as a finite-state observation-theoretic refinement of standard open-system machinery, not as a broad new escape-rate theory. 

main

My bottom line is this: the paper has a workable core, but it needs a substantial mathematical and editorial tightening before it is close to acceptance.