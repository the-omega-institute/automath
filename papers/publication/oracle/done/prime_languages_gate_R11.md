<!-- oracle metadata: {"timestamp": "2026-04-13T14:59:45.747827", "model": "chatgpt-5.4-pro-extended", "response_length": 10779} -->

Overall assessment

Major revision

There is a potentially publishable short note inside this manuscript, but the current submission is not yet journal-ready. The genuinely new content seems to be the quantitative prime-approximation consequences, especially the symmetric-difference and recall/precision corollaries. By contrast, the density dichotomies, the Zeckendorf growth statement, and the analytic remarks are classical or are presented by the authors themselves as repackaged background. More seriously, the draft is incomplete, with unresolved placeholders such as [?], ??, and ????, and the generalization in Theorem 2.9 is not proved rigorously in its present form. 

main

My recommendation is therefore not acceptance in current form, but a substantial rewrite that narrows the scope, repairs the proof of Theorem 2.9 or replaces it with a precise citation-based corollary, and accurately repositions the novelty relative to the existing density literature on rational/automatic languages. 
ResearchGate
+2
Journal de Théorie des Nombres
+2

Novelty rating for each theorem

Theorem 1.1 / Theorem 2.2: LOW. This is a classical transfer-matrix or Markov-chain density dichotomy for regular languages, and the manuscript itself describes it as a specialized reproof. 

main

 
Journal de Théorie des Nombres
+2
ScienceDirect
+2

Theorem 2.9: LOW. As stated, it looks like a packaging of existing conditional-density ideas for regular languages inside a regular numeration system, close to Kozik’s conditional densities and later relative-density work. 

main

 
ResearchGate
+2
Springer
+2

Theorem 1.4 / Proposition 3.1: LOW. This is known growth theory for regular or S-recognizable sets, and the manuscript itself labels it as “known, specialized derivation.” 

main

Sofic-slice exclusion attached to Theorem 1.4 / Remark 3.8: LOW. In the submitted version this is not a new asymptotic theorem. It follows immediately from regularity of sofic block languages plus non-regularity of the prime Zeckendorf language, exactly as Remark 3.8 argues. 

main

Theorem 1.5: LOW. Entirely background, and currently unsupported by precise citations or proofs in the body. 

main

 
Oxford Research Archive
+1

The actual novel points are the quantitative prime-approximation corollaries, namely Corollaries 1.2, 1.3, 2.5, 2.7, 3.5, and 3.6. I would rate those MEDIUM. They are technically short, but the explicit symmetric-difference and recall/precision formulation is useful and reasonably distinctive. 

main

Issue table

Main issues are summarized below. 

main

ID	Section	Severity	Description	Suggested fix
I1	Abstract, §1.2, §1.3	BLOCKER	The manuscript is still an incomplete draft. It contains unresolved placeholders [?], ??, ????, and a promised section for Theorem 1.5 that does not actually appear.	Submit only a clean, fully compiled version with all citations and cross-references resolved, and every announced theorem either proved or removed.
I2	§2.1, Theorem 2.9	BLOCKER	The proof does not justify the claimed pure λ^m periodic asymptotic for the product automaton. The step “summing over λ-maximal components” does not exclude polynomial prefactors from chains of maximal SCCs.	Replace the argument with a rigorous Perron-Frobenius normalization to a substochastic matrix, or cite a precise conditional-density theorem and present 2.9 as a corollary.
I3	Abstract, §1.1-1.2, §3	BLOCKER	Novelty is overstated. The “sofic-slice obstruction” is not proved as a genuinely new asymptotic statement and, as written, is an easy corollary of Remark 3.8 plus Corollary 3.7.	Reframe the paper around the genuinely new quantitative corollaries, and either strengthen the sofic result quantitatively or downgrade it to an easy corollary.
I4	Theorem 1.4, Proposition 3.1, Remark 3.8	MEDIUM	The introduction promises a self-contained Perron-Frobenius proof and later residue-class asymptotics, but the body gives only a proof sketch and then uses a different argument for the sofic claim.	Make the narrative consistent. Either give the full promised proof, or cite the known theorem precisely and simplify the section.
I5	Theorem 1.5, §1.3	MEDIUM	Theorem 1.5 is announced as a main theorem but is neither proved nor integrated into the body.	Delete it, or add a short background section with exact references and short proofs.
I6	Cor. 1.2, 2.5, 3.5	MEDIUM	The symmetric-difference notation is ambiguous because parentheses are missing.	Write `
I7	§1.2, References	MEDIUM	The density and relative-density literature is incomplete and partly placeholder-based, which makes the novelty claim hard to evaluate.	Add the missing references listed below and explain exactly what 2.9 adds beyond them.
I8	Whole paper	LOW	Too much classical background relative to the modest genuinely new contribution.	Compress the paper into a focused note.
I9	Numbering and organization	LOW	Intro theorem numbering and body propositions/remarks are not aligned cleanly.	Synchronize numbering and theorem status throughout.
Missing references

Most important missing items:

Hansel and Perrin, Rational Probability Measures (1989). This is foundational for rational or sofic measures and belongs in the density discussion. 
ScienceDirect

Kozik, Conditional Densities of Regular Languages (2005). This is the closest precursor to the relative-density flavor of Theorem 2.9. 
ResearchGate

Koga, On the Density of Regular Languages (2019). This is directly relevant to the Sin’ya density-zero discussion that is currently left with a placeholder. 
Sage Journals

Montoya, Relative Densities of Formal Languages (2025). This is relevant modern context for how relative density is currently framed. 
Springer

Berthé, Goulet-Ouellet, Perrin, Density of Rational Languages Under Shift Invariant Measures (2025). This is the broad modern density theorem for rational languages and should be acknowledged if the paper wants to claim a general density package. 
DROPS
+1

If Theorem 1.5 remains: add Estermann (1928) for the natural-boundary claim and Bowen-Lanford (1970) for the determinant or zeta-function formula. 
Oxford Research Archive
+1

Also, Bell, The upper density of an automatic set is rational (2020) is already in the bibliography but should be cited in the discussion around Theorem 1.1, and the same is true for Berstel 1973 and Bodirsky et al. 2004. Right now several relevant references are present in the bibliography but are not actually used in the text. 

main

 
Journal de Théorie des Nombres
+1

Specific improvements needed to reach acceptance

First, the paper should be recast as a short note centered on the genuinely new quantitative claims, namely the symmetric-difference and recall/precision obstructions for primes, together with the Zeckendorf analogues. The classical density dichotomies and growth laws should be clearly labeled as background and either shortened drastically or cited instead of reproved in full. 

main

Second, Theorem 2.9 needs either a correct proof or a precise citation to the established conditional-density literature. In the current version, it is the main technical bridge to the Zeckendorf section, and that bridge is not yet solid. 

main

Third, the front matter must be made consistent with the body. Remove all unresolved placeholders, synchronize theorem numbering, and either integrate Theorem 1.5 properly or delete it. As submitted, the paper still reads like a draft rather than a finished journal manuscript. 

main

Fourth, the Zeckendorf and sofic discussion should either be strengthened or modestly restated. At present the eventual-sofic exclusion is too weak to be advertised as a second major new theorem. A more convincing version would be a quantitative corollary for sofic shifts, or else a toned-down statement that this is an easy consequence of regularity plus non-regularity of the prime Zeckendorf language. 

main

Concrete fixes for each BLOCKER and MEDIUM issue

I1. Incomplete draft.
Run a full compile and remove every [?], ??, and ????. Make sure §1.3 matches the actual section structure. Every theorem announced in the introduction should either appear later with proof, or be deleted from the theorem list.

I2. Theorem 2.9 proof gap.
Do not keep the present “sum over λ-maximal SCCs” proof. A clean repair is to normalize by a positive Perron-Frobenius right eigenvector h of B_N. Let D = diag(h) and form
P_N = λ^{-1} D^{-1} B_N D, which is stochastic, and similarly for the trimmed product matrix B', form
P' = λ^{-1} \widetilde D^{-1} B' \widetilde D, which is substochastic. Then apply the same transient/recurrent decomposition used in Theorem 2.2 to P'. Because substochastic matrices are power-bounded, you avoid the polynomial-prefactor problem and recover the required periodic-plus-exponential asymptotic. If the authors do not want to reprove this, the alternative is to cite Kozik or a later relative-density theorem and restate 2.9 explicitly as a corollary. 
ResearchGate
+2
Springer
+2

I3. Overstated novelty.
Rewrite the abstract and §1.2 so that Theorem 1.1, Theorem 1.4, and Theorem 1.5 are labeled as background or packaged known results. Present Corollaries 2.5, 2.7, 3.5, and 3.6 as the actual new contributions. Remove the phraseology suggesting that the eventual-sofic exclusion is a deep second theorem unless you strengthen it to a genuinely quantitative statement.

I4. Inconsistent Section 3 narrative.
Either provide the promised self-contained Perron-Frobenius proof of Proposition 3.1, or replace the proof sketch by an exact theorem citation and keep only the specialization needed later. Then change the introduction so it no longer promises a later residue-class asymptotic theorem that never appears.

I5. Theorem 1.5 is disconnected.
Best option: delete it. It is not used in the paper’s main line and currently distracts from the actual contribution. If you keep it, add a short background section with explicit references to Estermann and Bowen-Lanford and give short proofs or exact theorem-number citations. 
Oxford Research Archive
+1

I6. Symmetric-difference notation.
Replace every ambiguous expression by an explicitly parenthesized one:
|(L(A) ∩ Σ_b^m) △ P_m^(b)|
and
|(L(A) ∩ Z_m) △ P_m^(Z)|.
Then check all proofs to ensure they use this exact meaning.

I7. Missing literature.
Add a paragraph after §1.2 explaining how your results sit relative to Hansel-Perrin, Kozik, Bell, Koga, Montoya, and Berthé-Goulet-Ouellet-Perrin. Right now the paper says “classical” and “new” in broad terms, but it does not map those claims accurately onto the literature. 
DROPS
+5
ScienceDirect
+5
ResearchGate
+5

In its present form, I would not recommend acceptance. A substantially shortened, completed, and correctly positioned revision could become a solid note.