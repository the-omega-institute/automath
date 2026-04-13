<!-- oracle metadata: {"timestamp": "2026-04-07T11:06:41.645023", "model": "o3-mini-high", "response_length": 12166} -->

Overall assessment: Reject

There is a potentially publishable core here, especially the exact finite-state/statistical formulas in Sections 4 and 6. I spot-checked several of those calculations and found parts of that core internally consistent. But in its current form the manuscript is not journal-ready. The submission still has placeholder citations, an effectively missing bibliography, stale section structure, broken cross-references, and two serious mathematical problems in main claims: the sequence-level conjugacy theorem is incorrect as stated/proved, and the Lee–Yang/branch-point conclusion in Theorem 6.2 is not justified by the displayed discriminant factorization. 

main

Relative to the standard literature on Zeckendorf numeration, automata/normalization, symbolic dynamics, Parry measures, and Markov-chain limit theorems, the fold-specific constructions and exact constants could be new, but the manuscript does not currently document that properly. The classical background it invokes is standard in Zeckendorf/Lekkerkerker, Fraenkel, Frougny, Berstel, Allouche-Shallit, Lind-Marcus, Parry, Walters, Gordin, and the recent Fibonacci-automata paper of Shallit-Shan. 
arXiv
+11
archive.lib.msu.edu
+11
math.ucsd.edu
+11

1. Novelty rating for each theorem

Novelty below is judged independently of correctness.

Theorem	Rating	One-line justification
Theorem 4.4	HIGH	The explicit one-site joint law for the fold-induced bulk process looks genuinely specific to this model, not a standard off-the-shelf result.
Theorem 4.5	MEDIUM	LLN/CLT are standard once the four-state Markov model is in hand, but the exact constants appear fold-specific.
Theorem 4.7	HIGH	Closed-form autocovariances and a rational power spectrum for this discrepancy process are substantial explicit outputs and likely new.
Theorem 5.2	MEDIUM	A sharp invertibility threshold for overlapping folded windows would be interesting, but the theorem is currently wrong/unproved as stated.
Theorem 5.3	LOW	The 
𝑚
=
2
m=2 degeneracy is a small, natural edge-case analysis.
Theorem 6.1	MEDIUM	A fourth-order recurrence for the weighted partition function is natural from transfer-matrix methods, but still useful and probably model-specific.
Theorem 6.2	LOW	The discriminant factorization of a specific quartic is modest by itself, and the physically meaningful branch-point interpretation is currently flawed.
Theorem 6.3	MEDIUM	The LLN/CLT/LDP package is standard transfer-matrix machinery, though the exact constants are new for this observable.
2. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Global / bibliography	BLOCKER	The manuscript still contains many placeholder citations [?, ?], and the reference list is essentially absent. This alone makes novelty and correctness hard to evaluate.	Replace every placeholder with an actual citation, restore the full bibliography, and tie each major standard claim to a specific source.
B2	Section 5 / Appendix C	BLOCKER	Theorem 5.2 and Proposition C.2 are false as stated. For 
𝑚
=
3
m=3, the raw blocks 0001 and 0110 produce the same 2-label block (000,001), so 
𝑚
−
1
m−1 consecutive labels do not determine the claimed vertex/bit.	Reprove the sequence-level result with the correct synchronization length, or weaken the theorem. At minimum, the current 
𝑚
−
1
m−1 decoder claim must be removed.
B3	Appendix C	BLOCKER	The inverse code formula (14) and the proof are index-inconsistent. The “last bit of the terminal vertex” cannot equal 
𝜂
𝑡
η
t
	​

 if the terminal vertex is written as 
𝜂
𝑡
⋯
𝜂
𝑡
+
𝑚
−
2
η
t
	​

⋯η
t+m−2
	​

.	Rewrite the decoder from first principles, with a precise convention for past/future windows and memory/anticipation.
B4	Section 6.3	BLOCKER	Theorem 6.2 overclaims. At 
𝑦
𝐿
𝑌
≈
−
1.13445
y
LY
	​

≈−1.13445, direct root computation shows the repeated root is subdominant, so the discriminant zero does not establish a branch point of the dominant free energy.	Split the theorem. Keep the discriminant factorization, then separately prove any dominant-sheet statement, or drop the Lee–Yang/nearest-branch-point claim.
M1	Section 3 / Appendix A	MEDIUM	The paper silently switches between low-to-high window indexing and MSD-first rewriting/transducer conventions.	Add an explicit lemma translating conventions, including how 011→100 in MSD-first becomes the corresponding rule in the paper’s window order.
M2	Global structure	MEDIUM	The TOC lists Sections 7–8 and Appendix E, but the body jumps from Section 6 to “7 Discussion”, so the compiled manuscript and section structure are out of sync.	Regenerate the TOC from the final source and ensure every listed section/appendix actually exists.
M3	Global references	MEDIUM	There are broken cross-references such as nonexistent “Theorem 4.6”, “Theorem 6.4”, and (??) equation references.	Replace hard-coded numbering with LaTeX labels and compile until all reference warnings are gone.
M4	Global typesetting	MEDIUM	The PDF has encoding/production corruption, for example m ¿= 3, broken ligatures, and section/page-number collisions like 105.3 and 137 Discussion.	Clean the source encoding, rebuild the PDF, and proofread the final output as a publication artifact.
M5	Introduction / related work	MEDIUM	Novelty claims are too broad relative to the standard literature, and the paper does not clearly separate what is standard Markov/transfer-matrix machinery from what is genuinely new.	Add a focused comparison subsection stating exactly which pieces are new: the fold, the anomaly, the exact constants, the corrected sequence-level statement, etc.
L1	Section 6.2	LOW	“Lee–Yang type” is used loosely. The present analysis does not yet support a robust zeros/physical-sheet interpretation.	Either narrow the terminology or add the missing zero-locus/dominant-sheet analysis.
L2	Section 6.2	LOW	“For generic 
𝑦
y” in the Hankel-rank discussion is vague.	Specify the exceptional algebraic locus where rank drops.
3. Missing references

At minimum, the paper should cite the following works it is clearly using or positioning itself against:

Zeckendorf (1972) and Lekkerkerker (1952) for the foundational representation theorem and classical asymptotic background. 
archive.lib.msu.edu
+1

Fraenkel, “Systems of Numeration” (1985) for broad numeration-theoretic context. 
acsel-lab.com

Frougny (1988) on linear numeration systems of order two, and Frougny (1999) on online finite automata/addition in numeration systems. These are closer to the manuscript than a generic numeration survey and are essential for any discussion of finite-state Fibonacci normalization. 
ScienceDirect
+1

Berstel, “Fibonacci words. A survey” (1985) for symbolic/combinatorial Fibonacci background. 
www-igm.univ-mlv.fr

Allouche and Shallit, Automatic Sequences (2003) for automata/numeration background. 
Cambridge University Press & Assessment

Shallit and Shan (2023), which the manuscript abbreviates as SS23, but does not properly integrate into a real bibliography. 
arXiv

Lind and Marcus, An Introduction to Symbolic Dynamics and Coding for sliding block codes, sofic shifts, resolving presentations, and conjugacy arguments. 
Cambridge University Press & Assessment

Parry (1964) for intrinsic Markov chains / Parry measure. 
JSTOR

Walters (1982) for ergodic/thermodynamic formalism background. 
Google Books

Gordin (1969) for the finite-state Markov-chain CLT framework explicitly invoked in the paper. 
Felipe Pérez

4. Specific improvements needed to reach acceptance

The paper would need all of the following before I would reconsider it positively.

First, Section 5 has to be rebuilt. The current theorem about conjugacy and inverse memory is not merely under-explained. It is wrong as stated. The author needs either a corrected theorem with the correct synchronization length and decoder, or a weaker but true statement.

Second, Theorem 6.2 must be narrowed or repaired. The discriminant factorization is fine as an algebraic computation. The jump from that factorization to a statement about the dominant free-energy branch is not justified, and in fact is contradicted by direct root comparison at the quoted negative root.

Third, the paper needs to become a real manuscript rather than a draft export. Placeholder references, broken numbering, stale TOC entries, and corrupted typesetting are not cosmetic in this case. They prevent a reliable reading.

Fourth, the conventions have to be unified. The paper uses one index order for Fibonacci weights and another for rewriting/transducer arguments. That can be repaired, but it must be done explicitly.

Fifth, the introduction should distinguish clearly between the genuinely new fold-specific contributions and the standard consequences of finite-state symbolic dynamics and transfer-matrix theory.

5. Concrete fixes for each BLOCKER and MEDIUM issue

B1. Missing bibliography and placeholders.
Create a complete .bib file, replace every [?, ?], and add citation-level support for: Zeckendorf uniqueness, automata-based Fibonacci normalization, sofic/Parry formalism, and Markov CLT usage. Do not leave any “to our knowledge” sentence unsupported by a targeted comparison paragraph and citations.

B2. Incorrect sequence-level theorem.
Start by inserting the explicit counterexample check into your own notes and recomputing the synchronization problem from the suffix graph. Then state the strongest true version you can prove. My direct check suggests the synchronizing length is not 
𝑚
−
1
m−1. It may be 
𝑚
m, but that needs proof. If only bi-infinite injectivity is true, say that, and separate it from the memory claim.

B3. Broken inverse-code indexing.
Define one convention and stick to it. For example, specify whether label 
𝑦
𝑡
y
t
	​

 comes from the block 
𝜂
𝑡
−
𝑚
+
1
…
𝜂
𝑡
η
t−m+1
	​

…η
t
	​

 or 
𝜂
𝑡
…
𝜂
𝑡
+
𝑚
−
1
η
t
	​

…η
t+m−1
	​

. Then write the decoder with that same convention and verify on a small worked example, say 
𝑚
=
3
m=3, that the decoded coordinate is really the one claimed.

B4. Invalid Lee–Yang/branch-point inference.
Rewrite Theorem 6.2 as two separate statements.
(i) An algebraic statement: the quartic discriminant factors as displayed.
(ii) A physical/dominant-sheet statement, only if you can actually prove it. That second part must compare moduli of all roots and control analytic continuation of the dominant branch. Otherwise, remove it. In the current version, the correct safe statement is only the discriminant factorization.

M1. Convention mismatch.
Add a short lemma right after the definitions that translates between the paper’s low-to-high digit order and the MSD-first normalization rule. Show exactly why the rewrite rule is legitimate under the chosen indexing and how truncation behaves under that translation.

M2. Stale structure / TOC mismatch.
Recompile from a clean source tree. Remove orphan section headings and appendices. The TOC must be auto-generated from the final text, not from an earlier draft.

M3. Broken theorem/equation references.
Use \label and \ref everywhere. Then compile until there are zero unresolved-reference warnings. This will also catch theorem-number typos such as “Theorem 4.6” and “Theorem 6.4”.

M4. Encoding/typesetting corruption.
Move the source to a consistent UTF-8 workflow, eliminate broken ligatures and pasted glyphs, and inspect the final PDF line by line. This matters because some of the current corruption occurs exactly at mathematically meaningful places, such as 
𝑚
≥
3
m≥3.

M5. Overbroad novelty framing.
Add a one-page comparison section near the end of the introduction with three columns mentally, if not literally: standard background, what this paper adds, and what it does not claim. That would make the novelty much easier to judge and reduce overclaiming.

Bottom line

My recommendation is reject in current form, with encouragement to resubmit only after a major mathematical and editorial reconstruction. The potentially strongest salvageable contribution is the fold-specific anomaly/statistical package in Section 4, together with the transfer-matrix recurrence in Section 6, but the current submission does not yet establish its full headline claims.