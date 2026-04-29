<!-- oracle metadata: {"timestamp": "2026-04-14T02:07:45.774481", "model": "chatgpt-5.4-pro-extended", "response_length": 12047} -->

Referee report on the attached manuscript, Fibonacci Folding and Zeckendorf Normalization: Gauge Anomaly, Sofic Structure, and Spectral Analysis. 

main

1. Overall assessment

Major revision

This is not a reject from me. I do not see an obvious counterexample to the main claims, and the paper contains a potentially publishable core. However, in its current form it is not journal-ready. The two headline contributions, namely the exact four-state bulk model in Section 4 and the conjugacy threshold in Section 5, are not proved at a level of rigor that matches the strength of the claims. In addition, the literature positioning is incomplete, and the manuscript still contains visible revision artifacts. The paper itself also acknowledges that much of the surrounding machinery is standard, and explicitly describes Theorem 6.1 as routine and Theorem 6.3 as not conceptually new, which weakens the case for acceptance unless the genuinely new parts are made watertight. 

main

2. Novelty rating for each theorem

Using the current theorem numbering in the body:

Theorem 4.6. Exact bulk joint law.
MEDIUM. The marginal density 
5
/
18
5/18 and the two-sided normalization/golden-shift viewpoint are already known, but the exact joint law for naive versus fold-aware digits and its anomaly interpretation appear to be the new part. 

main

Theorem 4.11. Autocovariance and power spectral density.
HIGH. The explicit discrepancy-process covariance formula and rational PSD look genuinely model-specific and plausibly new, conditional on the four-state model being rigorously established. 

main

Theorem 5.2. Conjugacy for 
𝑚
≥
3
m≥3.
MEDIUM. The finite-state/sliding-block framework is standard, but the precise threshold 
𝑚
≥
3
m≥3 and existence of a bounded-memory inverse appear new for this fold. The problem is that the proof is too compressed. 

main

Theorem 6.1. Fourth-order recurrence.
LOW. Once the weighted automaton is fixed, this is a standard transfer-matrix extraction, and the manuscript itself essentially says so. 

main

Theorem 6.3. Discriminant factorization.
LOW. Useful algebraic bookkeeping, but not conceptually deep, and again the manuscript itself does not claim major conceptual novelty here. 

main

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Section 4, Appendix B	BLOCKER	The derivation of the four-state bulk process is not proved rigorously enough for the exact constants 
4
/
9
4/9, 
118
/
243
118/243, and the PSD formula. The key synchronized-factor classification is presented with substantial informal carry language.	Add a formal theorem giving a complete equivalence between admissible reversed-pair factors and paths in the Fischer cover, with a full proof or a certified finite-state computation.
B2	Section 5, Appendix C	BLOCKER	The proof of Theorem 5.2 is too compressed. The step “no longer core can occur” is asserted, not established. The whole conjugacy threshold hinges on this.	Replace the current argument by a full fiber-product proof, or by a formal induction/classification theorem on ambiguous cores, plus complete tables or machine-verifiable certificates.
M1	Introduction, Related work	MEDIUM	Important prior work on Erdős measures as sofic/hidden-Markov objects is missing, especially Bezhaeva and Oseledets. This matters directly for the novelty claims in Section 4.	Add and discuss the missing literature, and explain precisely how the present four-state pair/discrepancy process differs from prior 5-state hidden-Markov models.
M2	Introduction, novelty positioning	MEDIUM	The paper currently overstates the novelty of the finite-state viewpoint. Prior work already treats golden-ratio Erdős measures via sofic/Markov representations.	Rewrite the novelty statements so that the genuinely new content is the fold-aware restriction, the anomaly observable, the exact pair/discrepancy laws, and the 
𝑚
≥
3
m≥3 inverse threshold.
M3	Introduction vs body	MEDIUM	The theorem-by-theorem novelty map still refers to Theorems 4.5 and 4.9, while the body uses Theorems 4.6 and 4.11. This is a clear revision artifact.	Do a full numbering and cross-reference audit. Fix theorem numbers, section references, appendix references, and all internal citations.
M4	Section 6	MEDIUM	The paper elevates routine transfer-matrix algebra to theorem-level prominence, even though it admits this material is routine or not conceptually new.	Demote some results to propositions/corollaries or move part of Section 6 to an appendix. Emphasize why these formulas matter structurally, or trim them.
M5	Exposition throughout	MEDIUM	Too much of the paper’s real argument is deferred to appendices with “standard” or “direct inspection” language. This reduces confidence in the main claims.	Bring at least one full proof of the bulk model and one full proof of the decoder/conjugacy argument into the main text. Add a dependency map between propositions, lemmas, and theorems.
L1	Terminology	LOW	“Gauge anomaly” is memorable, but it risks sounding more physical than mathematical. The paper partially addresses this, but the term still feels loaded.	Either keep the term but define it more narrowly up front, or pair it consistently with a neutral synonym such as “restriction discrepancy.”
L2	Introduction	LOW	The introduction is overlong and repetitive, especially on novelty caveats.	Shorten and consolidate the novelty discussion into one subsection.
L3	Notation/conventions	LOW	The LH versus MSD-first convention split is manageable, but still heavy.	Add one schematic example that is followed all the way from raw word to normalized word, pair process, and decoder output.
4. Missing references

These are the most important omissions I see.

Z. I. Bezhaeva and V. I. Oseledets, “Erdős measures, sofic measures, and Markov chains,” J. Math. Sci. 140, 357 to 368 (2007). This is the key missing citation. It explicitly proves that Erdős measures are sofic and states that the corresponding regular Markov chain has 5 states. That is directly relevant to the present manuscript’s Section 4 framing. 
Springer

Z. I. Bezhaeva and V. I. Oseledets, “The Erdős-Vershik problem for the golden ratio,” Funct. Anal. Its Appl. 44, 83 to 91 (2010). This treats properties of the Erdős measure and invariant Erdős measure for the golden ratio, and explicitly situates the topic in hidden-Markov/golden-shift terms. It should be cited in the discussion around the two-sided bulk law. 
Springer

Z. I. Bezhaeva and V. I. Oseledets, “Erdős Measures for the Golden Ratio and 2-step Markov Chains.” Even if the authors decide not to cite this in the main text, they should at least check it when discussing possible Markovian generalizations of the input process. 
ResearchGate

At minimum, item 1 is essential. In my view, omission of item 1 materially weakens the literature review.

5. Specific improvements needed to reach acceptance

The paper needs the following before it is publishable.

First, make the Section 4 finite-state model completely rigorous. The exact constants are only as credible as the automaton from which they are extracted. Right now that automaton is plausible, but the proof is too narrative.

Second, rewrite Section 5 around a complete proof of Theorem 5.2. This theorem is one of the manuscript’s strongest claims, and it cannot rest on a minimality argument that is only sketched.

Third, reposition the novelty more sharply. The paper should stop selling the general sofic/Markov viewpoint as new, and instead sell the genuinely new part, namely the fold-aware restriction, the anomaly observable, the exact joint/discrepancy laws, and the explicit inverse threshold.

Fourth, clean the manuscript editorially. The numbering inconsistency alone is enough to make a referee suspicious that other inconsistencies remain.

Fifth, rebalance Section 6. As written, too much space goes to results the paper itself describes as routine or computational. Either show why this section is indispensable to the main story, or compress it.

6. Concrete fixes for each BLOCKER and MEDIUM issue
B1. Section 4 / Appendix B

Create a standalone theorem of the following form: “The language of interior reversed-pair factors coincides with the label language of the four-state right Fischer cover.” Then prove both inclusions formally. One direction should construct a path from any interior factor. The other should show every path label is realized by an actual folded word. After that, derive the Parry measure, the joint law, the tilted matrices, and the covariance formula as corollaries.

Also include a small supplementary file containing the state graph, adjacency matrix, edge labels, and a short script that reproduces the local factor enumeration. The proof should not rely on the script, but the script should certify that the local classification is complete.

B2. Section 5 / Appendix C

Replace the current “no longer core can occur” paragraph with a formal theorem on ambiguous cores. One acceptable route is:

Define ambiguous core precisely.

Prove a stripping lemma showing passive coordinates can be removed without changing ambiguity.

Prove every minimal ambiguous core has length at most 4.

Enumerate all length-3 and length-4 cores.

Prove the third label resolves every listed core.

An alternative route is a fiber-product argument: explicitly prove that for 
𝑚
≥
3
m≥3 the off-diagonal fiber product has no bi-infinite path, and for 
𝑚
=
2
m=2 it has exactly the stated degenerate cycle. Either route is acceptable, but the present hybrid sketch is not.

M1. Missing Erdős/sofic references

Add a paragraph to the related-work section summarizing Bezhaeva and Oseledets 2007 and 2010. Explicitly say that prior work already treated golden-ratio Erdős measures using sofic/hidden-Markov representations, whereas the present paper studies a different observable, namely the pair/discrepancy process generated by comparing naive restriction with fold-aware restriction. 
Springer
+1

M2. Novelty recalibration

Rewrite the abstract, introduction, and novelty map so that they no longer imply the finite-state perspective itself is new. A safer formulation is:

known: two-sided normalization, golden-shift/Erdős-measure framework, sofic/Markov modeling,

new here: finite-window fold-aware restriction, restriction anomaly, exact pair law, exact discrepancy law, explicit autocovariance/PSD, and the 
𝑚
≥
3
m≥3 decoder threshold.

This change is not cosmetic. It is necessary for credibility.

M3. Numbering inconsistency

Run a full consistency pass. In particular, fix the novelty map so that theorem numbers agree with the body. Right now the introduction refers to Theorems 4.5 and 4.9, while the body uses 4.6 and 4.11. That should be corrected everywhere, including all remarks and cross-references. 

main

M4. Section 6 packaging

Either demote Theorem 6.1 and Theorem 6.3 to proposition-level results, or explicitly justify why they are central. Since the paper itself says the recurrence is routine once the automaton is fixed and the discriminant factorization is an explicit computation rather than a conceptual theorem, these results should not carry the paper’s novelty burden. 

main

A practical fix is to keep the formulas, but compress the prose and move the derivational details into an appendix.

M5. Overreliance on appendices

Move at least one complete proof from Appendix B and one from Appendix C into the main text. Readers should not have to trust the paper’s hardest ideas via appendix summaries. A short “proof architecture” paragraph at the end of the introduction would also help, listing exactly which appendices establish which headline theorems.

Bottom line

The paper has a real core. But the present version asks the reader to grant too much on trust, especially in the two places where the novelty is strongest. My recommendation is therefore Major revision. If the authors fully tighten Sections 4 and 5, add the missing Erdős/sofic references, and clean the editorial inconsistencies, the paper could become publishable.