<!-- oracle metadata: {"timestamp": "2026-04-08T17:18:42.882605", "model": "chatgpt-5.4-pro-extended", "response_length": 10143} -->

1. Overall assessment: Major revision

There is a potentially strong paper here, especially around the fold-aware restriction, the anomaly viewpoint, and the claimed conjugacy threshold. But it is not publishable in its current form. The central problem is proof integrity: Appendix B contains a false lemma and an internally inconsistent derivation of the 4-state transducer, and that proof engine is then used for essentially all of Section 4 and much of Section 6. Appendix C also does not yet give a fully convincing proof of the conjugacy threshold. I would therefore recommend Major revision, not acceptance. 

main

A concrete example of the Appendix B failure is this. In the stated MSD-first setup, Lemma B.1 says that appending one digit can trigger at most two rewrites. But starting from the already-normalized prefix 10101, prepending the paper’s leading 0, and then appending 1 gives 0101011, which rewrites three times:
0101011 -> 0101100 -> 0110000 -> 1000000.
So the lemma is false as stated, and the 4-state machine is not established by the current argument. 

main

That said, several claims look plausible and are consistent with small finite checks, so my recommendation is driven by the current proofs, not by a definite counterexample to the final numerical formulas.

2. Novelty rating for each theorem
Theorem	Rating	One-line justification
Theorem 4.4	MEDIUM	The explicit one-site law and constants look specific to this fold, but once a correct finite-state model exists the Parry-measure computation is standard.
Theorem 4.5	LOW	LLN and CLT are routine Markov-chain consequences; the only new part is the model-specific mean/variance constant.
Theorem 4.7	MEDIUM	The closed-form covariance and rational spectrum seem genuinely new for this model, even though the method is standard after the automaton is fixed.
Theorem 5.2	HIGH	The claimed conjugacy threshold at m >= 3 is model-specific and, if correct, is the paper’s strongest genuinely structural result.
Theorem 5.3	LOW	This is mainly the degenerate companion case to Theorem 5.2.
Theorem 6.1	MEDIUM	The explicit fourth-order recurrence and rational generating function appear new for this fold, though they are transfer-matrix consequences once the correct state model is in hand.
Theorem 6.2	LOW	Mostly an algebraic corollary of Theorem 6.1.
Theorem 6.3	MEDIUM	The explicit discriminant factorization is model-specific and worth recording, but mathematically it is a direct symbolic computation from the quartic.
Theorem 6.5	LOW	LLN/CLT/LDP are standard transfer-matrix consequences; novelty lies only in the specific constants and observable.

The most conceptually novel claims in the manuscript are not theorem-labeled: Proposition 4.1 and Proposition 4.3.

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Appendix B, Lemma B.1	BLOCKER	The bounded-cascade claim is false in the stated MSD-first convention. This breaks the state interpretation used to build the 4-state transducer.	Rebuild the normalization recursion in a correct convention, or construct the finite-state transducer directly from a rigorous normalization automaton.
B2	Appendix B, pp. 18-20	BLOCKER	The state-by-state transition derivation is internally inconsistent. For example, the 01 state discussion first derives an X_t=0 transition and then retracts it because it is not in the advertised table.	Replace the prose derivation with a formal state invariant and a complete transition table proved case-by-case.
B3	Sections 4 and 6	BLOCKER	Theorems 4.4-4.7 and the transfer-matrix claims in Section 6 depend on the unproved 4-state model. As written, this theorem chain is not established.	After correcting Appendix B, rederive the adjacency matrix, Parry measure, tilted matrices, and weighted matrix from the corrected machine.
B4	Appendix C, Theorem 5.2	BLOCKER	The proof of the conjugacy threshold is not rigorous enough. Lemmas C.3-C.4 rely on unsupported claims about minimal connecting chains and potential decrease.	Replace this with either a full fiber-product proof or an explicit inverse decoder for all m >= 3 with a complete proof.
M1	Introduction / Related work	MEDIUM	The paper under-cites foundational work on confluent linear numeration systems, finite-automaton normalization in Pisot/Fibonacci settings, and prior Zeckendorf digit-structure papers. This currently overstates novelty.	Expand related work and narrow the novelty claims to the fold-aware restriction/anomaly, explicit constants, and the m >= 3 threshold.
M2	Sections 2-5, Appendices B-C	MEDIUM	The LH/MSD-first convention switching is too hard to audit. Indexing, carry-slot usage, and the meaning of site t are not stable across proofs.	Add a notation table plus one unifying figure. Keep each appendix in one convention only.
M3	Section 6 / Appendix D	MEDIUM	The transfer-matrix formula for Z_m(y) is not written explicitly as a boundary-vector computation, which makes the recurrence derivation look more magical than it is.	Write Z_m(y) = alpha^T M(y)^m beta explicitly and derive the recurrence and numerator from that formula.
L1	Global presentation	LOW	Several standard corollaries are elevated to theorem status, which makes the novelty profile harder to read.	Consolidate some statements or relabel a few results as corollaries/remarks.
L2	Sections 3-6	LOW	Too few worked examples. The constructions are abstract enough that readers need examples to trust the indexing and state updates.	Add short examples for Fold_4, a worst-case anomaly word, one bulk transition computation, and the m=3 decoder.
4. Missing references

The paper cites some of the right literature, but it omits several papers that are close enough to matter for both positioning and proof style:

Christiane Frougny, Confluent linear numeration systems (1992). This is directly relevant to Appendix A/B because it studies rewriting systems and finite-automaton normalization for confluent linear numeration systems. 
ScienceDirect

Daniel Berend and Christiane Frougny, Computability by finite automata and Pisot bases (1994). Relevant to broad claims about finite-automaton normalization in Pisot/Fibonacci settings. 
Springer

Christiane Frougny, Linear numeration systems of order two (1988). Fibonacci numeration is the order-two case, so this is more directly relevant than the paper acknowledges. 
ScienceDirect

François Blanchard, β-Expansions and symbolic dynamics (1989). Foundational for the numeration/symbolic-dynamics interface used in Section 5. 
ScienceDirect

Clemens Heuberger, Minimal expansions in redundant number systems: Fibonacci bases and Greedy algorithms (2004). Relevant to Fibonacci-base minimal expansions, greedy algorithms, and transducers. 
Springer

P. J. Grabner and R. F. Tichy, Contributions to digit expansions with respect to linear recurrences (1990). Important classical context for digit statistics in linear-recurrence numeration systems. 
ScienceDirect

P. J. Grabner, R. F. Tichy, I. Nemes, A. Pethő, On the Least Significant Digit of Zeckendorf Expansions (1996). Directly relevant to low-order digit behavior and truncation/boundary effects. 
Taylor & Francis Online

Martin Griffiths, Digit Proportions in Zeckendorf Representations (2010), F. Michel Dekking, The structure of Zeckendorf expansions (2021), and F. Michel Dekking, The sum of digits functions of the Zeckendorf and the base phi expansions (2021). All are relevant to digit/block structure and sum-of-digits context. 
FQ Math
+2
Colgate University Math
+2

If the submission is current enough to require 2025 literature, Sungkon Chang, Terminal digits under Zeckendorf expansion (2025) should also be considered, because it is closely related to terminal-digit behavior. 
Mathos

5. Specific improvements needed to reach acceptance

Repair Appendix B completely. This is the main condition for publication.

Provide a genuinely rigorous proof of Theorem 5.2.

Rework the related-work section so the paper no longer appears to claim novelty for standard automata/Markov/transfer-matrix consequences.

Unify the notation and conventions so that a reader can verify each proof without mentally reversing strings every page.

Make Section 6 more explicit, especially the boundary vectors and the exact transfer-matrix representation.

Add short sanity-check examples and, ideally, a computational supplement verifying the state graph and the finite-volume counts.

6. Concrete fixes

B1. Rebuild the transducer from scratch. The cleanest route is to switch to a correct delayed-output formulation in one convention, preferably LH, and define the state invariant precisely. Then derive all state/input updates formally.

B2. Replace the narrative transition discussion with a deterministic update lemma. State exactly what each state means, give the full transition table, and prove each row by a direct value-preservation calculation.

B3. Once the corrected machine is in place, reprove Theorems 4.4-4.7 and Section 6 from that machine. Include the adjacency matrix, primitive/right-resolving check, Parry measure, and the explicit weighted matrix used in Section 6.

B4. For Theorem 5.2, either:

give an explicit inverse sliding block code for general m >= 3, with memory/anticipation bounds and proof, or

give a full fiber-product proof with a rigorously defined invariant and no heuristic statements about minimal chains.

M1. Add the missing references above, then rewrite the novelty paragraph so that the genuinely new content is: fold-aware restriction, gauge anomaly, explicit anomaly constants, and the m >= 3 conjugacy threshold.

M2. Insert a one-page notation guide. It should include: LH vs MSD-first order, the reversal map, where truncation happens, and the role of the carry slot.

M3. Write the partition function in boundary-vector form, then derive the recurrence by Cayley-Hamilton. This will also make the numerator in Theorem 6.1 transparent.

My bottom line is this: the paper has a promising core, but the current proof package is not strong enough for acceptance. The bulk-statistics appendix must be rewritten, and the conjugacy proof must be tightened substantially.