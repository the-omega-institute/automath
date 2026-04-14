<!-- oracle metadata: {"timestamp": "2026-04-08T18:01:42.867797", "model": "chatgpt-5.4-pro-extended", "response_length": 10462} -->

1. Overall assessment

Major revision

The core idea is potentially interesting: using depth-
𝑚
m Bayes error for first-entry residue events as an observable that detects open-system escape data. But the current manuscript is not close to publishable form. The draft contains a false lemma, an unproved numbered theorem presented as part of the results, broken internal references and citation placeholders, inconsistent examples, and an incomplete literature comparison. I would not recommend acceptance until those issues are fixed and the paper is substantially tightened. 

main

2. Novelty rating for each theorem

Grouped where the introduction theorem is duplicated later in the paper.

Theorem(s)	Rating	One-line justification
1.1 / 6.6	MEDIUM	The residue-dependent quasistationary amplitude looks like the most distinctive refinement, but it is still a direct Perron-Frobenius consequence once the killed-matrix formula is in place.
1.2 / 7.1	LOW	This is essentially the same transfer-matrix computation with power weights.
1.3 / 6.7	LOW	The cyclotomic lift is an algebraic residue-state augmentation, not a new dynamical mechanism.
4.2	LOW	Sliding-block collapse of recursive codings is standard factor theory.
5.4	LOW	This is a classical discrete Tanaka identity applied to the conditional-probability martingale.
5.8	LOW	Standard boundary-counting estimate once the cylinder mass bound is assumed.
5.9	MEDIUM	The weighted-boundary automaton packaging is neat and potentially useful, but it is still standard finite-state transfer machinery in spirit.
6.1	MEDIUM	This is the paper’s best claim: the Bayes-error observable is interesting, but the proof itself is a straightforward killed-Markov calculation.
6.8	LOW	As written it is only a conditional proof outline, so it should not receive theorem-level novelty credit yet.
7.3	LOW	Standard Chen-Stein occupancy/Poisson threshold material.
A.1	LOW	Elementary entropy bookkeeping.
A.2	LOW	Elementary convexity and injectivity observation.

My overall novelty read is: the observable is the new part, not most of the machinery around it.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	1, 6, 8	BLOCKER	Broken cross-references and placeholders remain: Section ??, Appendix ??, Lemma ??, ? ], and proofs pointing to nonexistent Theorems 6.3, 6.4, 6.5.	Complete bibliography and renumbering, then do a full reference audit before resubmission.
B2	6.3	BLOCKER	Theorem 6.8 is not proved. It is explicitly conditional, contains only a proof outline, and lists unverified assumptions.	Either supply a complete proof, or demote it to a remark/conjectural framework and remove it from the theorem list and result claims.
B3	6.1	BLOCKER	Lemma 6.2 is false as stated. Two first-hit lengths with different residues mod 
𝑞
q do not imply residue nondegeneracy for an arbitrary nonempty proper 
𝑅
⊂
𝑍
/
𝑞
𝑍
R⊂Z/qZ.	Replace it with a correct criterion based on the full set of attainable first-hit residues, or restrict the lemma to a case where the parity argument is actually valid.
B4	1	BLOCKER	The literature comparison is incomplete and currently unusable because of placeholder citations. The manuscript does not yet distinguish clearly between what is genuinely new and what is standard escape-rate / transfer-matrix / Chen-Stein machinery.	Add the missing references and rewrite the comparison paragraph to isolate the true contribution.
M1	1, 6, 8	MEDIUM	Result hierarchy is inconsistent. The introduction says the main theorem is 1.1/6.1, but 1.1 is the amplitude statement, while later “Proof of Theorem 1.1” points to nonexistent 6.3.	Rebuild the theorem architecture and make one clean hierarchy: main theorem, refinement, algebraic corollary, secondary consequences.
M2	6.1 examples	MEDIUM	Examples 6.3 and 6.4 are internally inconsistent. Example 6.3 calls 
𝐻
=
[
11
]
H=[11] a symbol hole. Example 6.4 cannot simultaneously have full adjacency and only allow transitions into 2 from 0.	Rewrite the examples with correct graphs or with explicit block recoding.
M3	2-4, A	MEDIUM	Large portions of the manuscript are tangential to the title and main claim. Sections 2-4 and Appendix A dilute the dynamical contribution.	Compress heavily, move to supplementary material, or split off into a separate note.
M4	5-6	MEDIUM	Section 5 develops a general weighted-boundary formalism, but Section 6 proves the main theorem again from scratch. The structural role of 5.9 is unclear.	Either derive 6.1 explicitly from 5.9, or streamline 5.9 and focus on the killed-matrix case only.
M5	7	MEDIUM	The survivor Rényi spectrum and Poisson threshold are over-emphasized relative to their derivational status. They read as corollaries, not co-equal main results.	Demote them rhetorically to corollaries and shorten the exposition.
M6	Overall	MEDIUM	For an ETDS-level submission, the significance of the one-step finite-state result alone is not yet convincingly established.	Either complete the broader Hölder/cylinder-hole theorem, or refocus the paper as a shorter finite-state note with much sharper claims.
L1	3	LOW	The Sturmian remark feels disconnected from the rest of the paper.	Remove unless it is used later.
L2	Throughout	LOW	Terminology is unstable, especially around “symbol hole” versus higher-cylinder hole after block recoding.	Standardize the terminology and state recoding conventions explicitly.
4. Missing references

At minimum, the placeholder paragraph on “subsystems and escape statistics” should cite the following.

J.-R. Chazottes, Z. Coelho, P. Collet, Poisson processes for subsystems of finite type in symbolic dynamics. This is the obvious reference for prior Poisson-process limits and pressure-scale asymptotics for subsystems of finite type. 
arXiv
+1

J.-R. Chazottes, Z. Coelho, P. Collet, On the asymptotic measure of periodic subsystems of finite type in symbolic dynamics. This is the natural companion reference for asymptotic measure / pressure-difference behavior of periodic subsystems. The web surfaced the arXiv companion record. If there is a final journal version, that should be cited instead. 
arXiv
+1

H. Bruin, M. F. Demers, M. Todd, Hitting and escaping statistics: mixing, targets and holes, Adv. Math. 328 (2018), 1263-1298. This is the natural citation for the manuscript’s claim about the relationship between hitting and escape statistics. 
University of St Andrews Research Portal
+1

N. Haydn, F. Yang, Local escape rates for 
𝜙
ϕ-mixing dynamical systems, ETDS 40(10) (2020), 2854-2880. This is the natural citation for local escape-rate asymptotics beyond the finite-state setting. 
Cambridge University Press & Assessment
+1

A. C. M. Freitas, J. M. Freitas, M. Todd, Speed of convergence for laws of rare events and escape rates, Stochastic Processes and their Applications 125(4) (2015), 1653-1687. This fits the manuscript’s placeholder claim about convergence-rate questions. 
ScienceDirect
+1

5. Specific improvements needed to reach acceptance

Remove the gap between claim and proof. Theorem 6.8 cannot stay as a theorem unless it is fully proved.

Correct false and inconsistent statements. Lemma 6.2 must be repaired or removed, and Examples 6.3-6.4 must be rewritten.

Stabilize the manuscript structure. Fix theorem numbering, proof pointers, bibliography, and all unresolved placeholders.

Sharpen the contribution. State plainly that the new part is the Bayes-error observable, while escape-rate recovery, PF asymptotics, and Chen-Stein consequences are largely corollary-level.

Tighten the scope. For this journal level, either prove a broader Hölder/cylinder-hole extension, or substantially shorten the paper and present the finite-state result as a focused note.

6. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Cross-references and placeholders.
Run a full source cleanup and do not resubmit until the compiled PDF contains no ??, no [?], and no references to nonexistent theorem numbers. Then manually verify every “Proof of Theorem X” pointer.

B2. Theorem 6.8.
Choose one of two routes.
(a) Prove it on a clearly specified Hölder Banach space, with full spectral-gap, duality, and regularity arguments.
(b) Rename it as a conjectural extension / formal framework, move it out of the numbered theorem list, and remove any suggestion that it is established.

B3. Lemma 6.2.
Define, for each safe state 
𝑖
i, the set 
𝐷
𝑖
⊂
𝑍
/
𝑞
𝑍
D
i
	​

⊂Z/qZ of attainable first-hit residues. Then state the nondegeneracy criterion directly in terms of 
𝐷
𝑖
D
i
	​

: for every 
𝑟
r, 
𝐷
𝑖
D
i
	​

 must meet both 
𝑅
−
𝑟
R−r and its complement. If you want a simple sufficient condition, use a genuinely sufficient one, for example 
𝐷
𝑖
=
𝑍
/
𝑞
𝑍
D
i
	​

=Z/qZ, or restrict the easy parity version to 
𝑞
=
2
q=2.

B4. Literature comparison.
Replace the current placeholder paragraph by a precise comparison with cited works. One clean formulation would be: “New here is the Bayes-error observable and its residue-dependent ambiguity amplitude. Standard ingredients are the pressure-gap escape formula, PF asymptotics for the killed matrix, and Chen-Stein Poisson approximation.”

M1. Result hierarchy.
Reorganize the paper so that:

Theorem 6.1 is the main theorem.

Theorem 6.6 is the amplitude refinement.

Theorem 6.7 is the algebraic corollary.

Theorem 7.1 and Theorem 7.3 are secondary corollaries.

Theorem 6.8 is either removed or demoted.

M2. Examples.
Rewrite Example 6.3 using explicit 2-block recoding if 
𝐻
=
[
11
]
H=[11]. Rewrite Example 6.4 on an actual non-full graph where all first-hit paths have even length. Then verify that the stated conclusion really matches the graph.

M3. Scope drift.
Cut Sections 2-4 to the minimum needed for Sections 5-7. Unless Appendix A is used in the main proofs, remove it or save it for a separate note.

M4. Role of Section 5.
Either instantiate Theorem 5.9 for first-entry residue events and derive Theorem 6.1 from it, or delete the general weighted-boundary formalism and keep only the killed-matrix argument actually used.

M5. Secondary consequences.
Shorten Section 7 and present it explicitly as “Consequences of the same matrix formula.” That will make the paper more honest and more focused.

M6. Journal fit.
If the target is ETDS, I would strongly advise one of two strategies: complete the Hölder/cylinder-hole extension in a fully rigorous way, or recast the paper as a shorter finite-state contribution with narrower claims and a sharper novelty statement.