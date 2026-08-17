1. Verdict
Reject.
Single strongest reason: the advertised L0/L1/L2 “non-collapse” is not a coherent mathematical separation theorem. The three levels concern different objects, use different primitives, and impose unrelated structures. What is proved is a collection of independent statements placed under one author-created vocabulary, not a hierarchy whose successive levels are connected by a natural forgetful operation or implication.
This is not a major-revision problem. To repair it, the authors would have to discard the present central theorem and write a different paper around the Zeckendorf moment results.
2. Significance threshold
No. This does not clear the significance threshold of a strong general mathematics journal. It is correct-looking but too small, and the surrounding architecture inflates rather than enlarges the contribution.
There is one respectable specialized result: for each fixed moment degree q, the authors construct a finite signed-Fibonacci carry automaton, prove that the bounded-state truncation is lossless, and obtain a fixed matrix formula for all resolutions m.  The resulting theorem that every fixed-q moment is C-finite is legitimate, and the primitivity argument gives a genuine Perron asymptotic and fixed-degree pressure.  
That core does not support the submitted general-journal package:


The L0 calculator-basis statement is expressly only a cited existence result, not a theorem proved in the paper. 


The L1 arithmetic protocol is decode–perform ordinary integer arithmetic–encode. The manuscript itself observes that any computable bijection transports computable operations in this fashion.  Calling this “Zeckendorf protocol universality” does not create substantive Zeckendorf mathematics.


The one-monogenic-orbit obstruction is an elementary rank-one prime-exponent argument. 


The Richardson theorem is a relative substitution statement: the decisive π- and sine-witness identities are assumed, while only the punctured absolute-value row is established internally. 


The exact maximal-fibre values use the previously published Fibonacci interval-maximum theorem; the new part is the short conversion from ordinary intervals to the shifted fold interval. The manuscript acknowledges this explicitly.  The cited source indeed already proves the two parity formulas for the interval maxima. Numdam


The arbitrary-cover obstruction is obtained by attaching a factorial-size auxiliary fibre. That is a counterexample by definition, not deep structure.


A substantially shortened paper containing the fixed-q carry automata, the primitive transfer result, the exact second-moment recurrence, and a restrained discussion of nonuniformity in q would be right-sized for Discrete Mathematics & Theoretical Computer Science. Its scope expressly includes automata theory and combinatorics of words. 离散数学与理论计算机科学 The EML/Richardson material, the L0/L1/L2 hierarchy language, and the arbitrary-cover construction should not be in that paper.
3. The first point a hostile referee attacks
The vulnerable headline is:

“Theorem 1.5 (Verified-core relative single-primitive hierarchy). With the definitions of L0, L1, and L2 in Sections 2 to 4, the hierarchy does not collapse.” 

The attack is immediate: what hierarchy?
L0 is a statement about existence of terms over the partial analytic operation eml. L1 is a presentation of N by Zeckendorf words, with compiled addition and multiplication computed by first decoding to ordinary integers, applying ordinary + or ×, and greedily encoding again.  Its “single semantic primitive” is composition of endomorphisms, not eml. The paper’s own final L1 theorem calls the construction “value-transported” and disclaims any digit-local arithmetic theorem.  L2 then attaches fibre statistics, and later completely arbitrary auxiliary cover multiplicities, to a finite residue fold.
There is no common system U equipped successively with L0, L1, and L2 structure; no natural forgetful maps
L2⟶L1⟶L0;
and no theorem that one naturally defined level fails to imply the next. The manuscript changes the underlying semantic objects and the meaning of “universality” at every stage, then calls the resulting differences non-collapse.
A hostile referee will therefore say, correctly:

Theorem 1.5 is a taxonomy assembled from unrelated examples, not a hierarchy theorem.

The Richardson obstruction does not repair this. It says that a particular real-function expression fragment cannot have an equality-reflecting finite normalizer. The existence of an unrelated computable protocol for (N,+,×) does not constitute the next level of that same object. Likewise, arbitrary certificate covers over Zeckendorf normal forms do not constitute a further level of the EML expression system.
That is the real weak point because it destroys the paper’s claimed central synthesis even if every individual calculation is correct.
4. Fixed-degree transfer versus the full moment tower
The logical dichotomy is genuine, but the negative half is almost exactly the elementary superexponential-coefficient observation described in the question.
The positive half is real mathematics. For each fixed q, the paper must prove that all relevant signed-Fibonacci carry paths can be retained in the fixed state set
{−1,0,1}q−1×{−1,0,1}q−1,
without discarding an accepting path. That losslessness is not implied by a growth estimate. It is the substantive step behind the matrix Tq​, and the subsequent primitivity argument is also nontrivial.   Thus
∀q∃Tq​
is a genuine theorem about these particular fold fibres.
The all-degree obstruction, however, becomes immediate once the maximal fibre Mm​ is known. Put
Δm​=Smint​(m).
The elementary maximal-term bounds give
Mmm​≤Δm​≤∣Xm​∣Mmm​=Fm+2​Mmm​.
Since
Mm​=Θ(φm/2),
one obtains
logΔm​=21​m2logφ+O(m).
This is already contained in the manuscript’s diagonal squeeze. 
If the bivariate moment series
M(z,w)=m≥1∑​q≥0∑​Sqint​(m)zmwq
were rational as a formal power series at the origin, it would be analytic on some small polydisc. Cauchy estimates would then give
Sqint​(m)≤CRz−m​Rw−q​.
On q=m, this is only exp(O(m)), contradicting the exp(21​m2logφ+O(m)) diagonal. That is precisely the proof printed in Theorem 4.27.  The exclusion of a rational matrix A(w) is then an immediate algebraic corollary, since such a matrix would make the bivariate series rational. 
So the accurate assessment is:


Genuine: the coexistence, for the same intrinsic family, of fixed finite-state transfer separately in every fixed degree and failure of one rational finite-dimensional law uniform in the degree. This is a legitimate quantifier separation:
∀q∃Tq​⇒∃T(w)∀q.


Not deep: once the exact height growth is available, the nonrationality proof is the standard fact that coefficients of a rational bivariate power series cannot have a superexponential diagonal.


Overmarketed: Theorem 4.27 should be presented as a concise corollary of the height theorem, not as an independent major obstruction carrying the conceptual weight of the paper.


The theorem is therefore not false or purely vacuous. But almost all of its mathematical substance lies in constructing the fixed-q automata and establishing the height law. The “no single rational transfer law” half is a one-paragraph consequence of those inputs.
