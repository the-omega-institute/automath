<!-- oracle metadata: {"timestamp": "2026-04-10T07:44:44.218727", "model": "chatgpt-5.4-pro-extended", "response_length": 12809} -->

I reviewed the attached manuscript, Finite Parts of Dynamical ζ-Functions for Shifts of Finite Type. 

main

1. Overall assessment

Major revision

The manuscript contains one potentially publishable core idea, namely the class-function level Adams–Möbius inversion that expresses primitive Peter–Weyl channels directly in terms of twisted determinant data. But in its current form the paper does not separate that core from classical input and routine consequences sharply enough. The paper itself acknowledges that Theorem A is not a new prime-orbit theorem, that Theorem 4.4 is classical, that the leading term in Theorem 4.19 is known, and that the appendices are routine secondary consequences. In addition, there is at least one substantive conceptual error in the discussion of the twisted spectral-gap hypothesis in §6.2(1). On editorial grounds, this is not ready for acceptance as a full research article in its present form. 

main

I did not find an obvious fatal gap in the main determinant manipulations or in the worked S3 calculations. My recommendation is driven mainly by novelty positioning, theorem hierarchy, and one real conceptual misstatement, not by a collapse of the whole argument. 

main

2. Novelty rating by main theorem chain
Theorem / claim	Rating	One-line justification
Theorem 1.1 / Theorem A / Theorem 3.1	LOW	The paper itself presents this as a finite-state reduced-determinant packaging of classical dynamical Mertens asymptotics, not a new prime-orbit theorem. 

main


Theorem 1.2 / Theorem B / Props. 3.8–3.9 + Cor. 3.10	LOW	Once the cyclic-lift determinant identity is written down, the reconstruction is essentially discrete Fourier inversion plus Newton identities; the manuscript does not make a strong case that this is a substantial new theorem. 

main


Theorem 4.4 (class-function determinant linearisation)	LOW	The manuscript explicitly says this is identical to the classical Adachi–Sunada-type result and is included mainly for notation and consistency. 

main


Cor. 4.5 and Cor. 4.8. Adams–Möbius primitive inversion / irreducible-channel determinant formula	MEDIUM	This is the strongest candidate for genuine novelty, but the paper still needs a sharper demonstration that it is more than a clean repackaging of known determinant factorisation plus trace-level Möbius inversion. 

main


Theorem 4.19. Class Mertens theorem under twisted spectral gap	MEDIUM	The leading Chebotarev term is acknowledged as known; the new part is the constant-term packaging under the extra hypothesis η < λ, which is interesting but incremental. 

main


Theorem 4.23. Non-abelian Fourier reconstruction	MEDIUM	Once the class constants are defined, the reconstruction is a natural orthogonality argument, so the novelty is mainly in the packaging, not in the inversion step itself. 

main


Theorem C(iii) / Section 5 quotient functoriality, abelian shadow, cyclic detection	LOW	These are mostly formal character-theoretic consequences of the Peter–Weyl decomposition and quotient pullback, with limited independent depth. 

main

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Title, Abstract, Introduction, theorem hierarchy	BLOCKER	The manuscript overstates novelty. It promotes several results as main contributions even though it also says Theorem A is not new, Theorem 4.4 is classical, the leading term of Theorem 4.19 is known, and the appendices are routine. 

main

	Rebuild the paper around the genuinely new theorem chain only. Demote classical/supporting material to propositions, remarks, or appendices.
B2	§4.2–§4.3	BLOCKER	The central novelty claim, namely Adams–Möbius primitive inversion, is asserted rather than convincingly established against the literature. I am not saying it is already known, but the manuscript does not yet prove that it is new at a publishable standard. 

main

	Add a precise prior-art comparison showing exactly what follows from standard twisted determinant factorisation plus ordinary Möbius inversion, and exactly what does not.
M1	§6.2(1)	MEDIUM	As written, the sentence claiming that the abelian, cyclic-lift case reduces to strict Perron dominance and “holds by primitivity” is false or at least seriously misleading. In Remark 4.9 the canonical cyclic lift has A_{χ_j} = ω_q^j A, so nontrivial twists have spectral radius λ, not < λ. 

main

	Correct or remove the sentence. Distinguish general abelian cocycles from canonical cyclic lifts, and explicitly state that the Perron-point machinery of §4 does not apply to canonical cyclic lifts.
M2	§4, §6	MEDIUM	The hypothesis η < λ is central to the main asymptotic consequences, but the paper gives too little structural discussion of when it holds, when equality can occur, and how this interacts with the paper’s own abelian examples. 

main

	Add a focused subsection on the status of η < λ, including equality cases, known criteria, and explicit examples where the hypothesis fails.
M3	§3	MEDIUM	The cyclic reconstruction material is over-promoted. It reads as useful supporting infrastructure, but not as a major theorem branch of the same weight as the Adams–Möbius part. 

main

	Compress §3 substantially, or move most of it to a short appendix unless the authors can document stronger novelty.
M4	§5	MEDIUM	The quotient-functoriality and abelian-shadow results are clean, but largely formal. A full section and theorem-level prominence feel disproportionate to the depth of the claims. 

main

	Shorten §5 and keep only the strongest consequence plus one worked example.
M5	Appendices A–C	MEDIUM	The paper is too long relative to its likely core contribution. The appendices are explicitly described as routine consequences, yet materially enlarge the submission. 

main

	Move most appendix material to supplementary notes or remove it.
L1	§2.1	LOW	The symbol A is used for both the alphabet and the adjacency matrix, which is avoidably confusing. 

main

	Use \mathcal A for the alphabet, or any other distinct notation.
L2	Bibliography	LOW	The bibliography appears insufficiently curated. In particular, reference [35] is a Zeckendorf paper unrelated to the subject of this manuscript and appears to be a carryover entry. 

main

	Audit the bibliography carefully. Remove irrelevant and uncited entries.
L3	Global style	LOW	The paper introduces a fair amount of branding language, such as “spectral fingerprint”, “abelian shadow”, and “genuine non-abelian defect”, for material that is often fairly formal.	Reduce terminology unless it carries real technical load later.
4. Missing references

These are the omissions I would regard as most worth fixing, especially if the current graph-covering and group-extension comparisons remain in the paper.

Kotani and Sunada, Zeta Functions of Finite Graphs (2000). This is a standard graph-zeta reference and should be cited if the paper keeps its graph-theoretic determinant discussion. 
University of Tokyo Medical Sciences

Stark and Terras, Zeta Functions of Finite Graphs and Coverings, Part II (2000). This is directly relevant because it develops Artin L-functions and factorisation formulas for Galois graph coverings, which is very close to the comparison the manuscript wants to make. 
ScienceDirect

Terras and Stark, Zeta Functions of Finite Graphs and Coverings, III (2007). If the paper invokes the graph-covering Artin-L program, omitting the later continuation looks incomplete. 
ScienceDirect

Richard Sharp, Convergence of zeta functions for amenable group extensions of shifts (2019). This is relevant background for the broader dynamical setting of group extensions of shifts and should at least be acknowledged in the discussion/open-problem section. 
University of Warwick

Manuel Stadlbauer, An extension of Kesten’s criterion for amenability to topological Markov chains (2013), and On conformal measures and harmonic functions for group extensions (2019). These are relevant to the pressure and Perron–Frobenius theory of group extensions, which is exactly the neighborhood of the paper’s η < λ discussion. 
arXiv
+1

5. Specific improvements needed to reach acceptance

First, the paper needs a much sharper statement of what is actually new. The current submission reads like two different papers combined. One is a supporting finite-state note on Perron finite parts and cyclic reconstruction. The other is a more interesting paper on primitive determinant calculus for finite-group extensions. Only the second has a plausible claim to significant originality. 

main

Second, the title, abstract, and introduction should be rewritten so that the Adams–Möbius primitive inversion, not the classical finite-part packaging, is clearly the center of gravity. The present abstract distributes attention too evenly across claims of very different originality. 

main

Third, the paper must correct the spectral-gap discussion. The incorrect or misleading cyclic-lift sentence in §6.2(1) is not a cosmetic problem. It directly affects the reader’s understanding of where the main asymptotic results do and do not apply. 

main

Fourth, the paper needs substantial shortening. In its current state, too much routine material is theoremized. A shorter, more focused paper would read much better and make the genuine contribution easier to assess.

Fifth, the literature review should be more exact and less declarative. When the manuscript says “this does not appear in [1,22,27,25,21]”, that is not yet enough. A referee needs a line-by-line explanation of why the existing frameworks stop short of Corollary 4.5 and Corollary 4.8.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Overstated novelty and poor theorem hierarchy

Actionable fix

Rewrite the abstract so that only the Adams–Möbius primitive inversion and its best nontrivial consequence are presented as primary new results.

Demote Theorem 3.1 to a proposition or a short preliminary theorem.

Demote most of the cyclic reconstruction material to supporting results unless the authors can document a genuine inverse-spectral advance.

State explicitly, in a boxed paragraph near the end of the introduction, which results are classical input, which are formal consequences, and which are claimed new.

B2. Central novelty not yet convincingly separated from prior work

Actionable fix

Expand §4.2 into a true comparison section, not just a narrative one.

For each relevant predecessor, state: “Known input gives X. Our contribution is Y. The missing step is Z.”

Add one proposition or remark proving that the standard periodic determinant factorisation plus direct trace-level Möbius inversion yields a weaker statement than Cor. 4.5, if that is indeed the case.

If the result is “new in this explicit class-function form” rather than “new in substance”, say so honestly.

M1. Incorrect or misleading cyclic-lift claim in §6.2(1)

Actionable fix

Replace the current sentence by something mathematically correct, for example:
“For canonical cyclic lifts, the nontrivial twisted matrices are scalar multiples ω_q^j A, so their spectral radii equal λ; thus the strict inequality η < λ is not automatic in that model, and the Perron-point results of §4 do not specialize directly to §3.”

Add a cross-reference back to Remark 4.9.

Clarify that §3 and §4 treat different mechanisms.

M2. Central hypothesis η < λ is underexplained

Actionable fix

Add a subsection titled something like “When can one expect η < λ?”

Include at least: one explicit equality case, one explicit strict case, one cohomological obstruction, and one literature reference for pressure/amenability in group extensions.

Cite Boyle–Schmieding, Sharp, and Stadlbauer here. 
University of Warwick
+2
arXiv
+2

M3. Section 3 is over-promoted

Actionable fix

Compress the cyclic reconstruction results to one theorem plus one corollary.

Move “spectral fingerprint” terminology and arithmetic corollaries to an appendix or remove them.

Keep only what is needed later in §4.

M4. Section 5 is formal and too long

Actionable fix

Reduce §5 to the minimal formal package needed to interpret the S3 example.

Keep one main proposition on cyclic detection and one worked example.

Move the rest to supplementary material.

M5. Appendices are routine and should not dominate the submission

Actionable fix

Remove Appendices B and C unless the authors can show that they are used later in an essential way.

Keep Appendix A only if the journal values explicit perturbation formulas; otherwise move it out as supplementary notes.

Target a noticeably shorter manuscript.

My editorial bottom line is this: there may be a publishable paper here, but it is not yet this paper. The authors should recast it as a shorter, sharper article centered on the Adams–Möbius primitive inversion and its strongest genuinely nonclassical consequences.