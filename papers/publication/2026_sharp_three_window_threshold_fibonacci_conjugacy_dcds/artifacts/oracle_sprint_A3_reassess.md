Overall judgment
The core graph theorem is the theorem I had in mind, and the crossing to bounded U-representations of zero is genuine. It is not merely Theorem 2.3 with the nouns changed. The standard object is now the zero-representation relation itself; the manuscript-specific contribution is the aperture-m, one-position-overlap organization and its transient depth.
The priority claim is likely to survive, at roughly 0.82 confidence. The classical literature gives regularity, finite-state recognition, normalization, and various bounded-delay results. I did not find an aperture-linear bound for the longest acyclic transient of these overlap graphs, and that bound does not follow routinely from regularity.
The venue judgment does not change in category. TAMS is now somewhat more defensible as an ambitious first submission; ETDS remains the strong natural alternative. This addition improves the paper materially, but it does not create a tier jump.
There is, however, one necessary correction to the printed statement of Theorem 2.6. The graph formulation is sound, but the following “Equivalently” formulation is too broad under its natural reading.
1. Is Theorem 2.6 the intended theorem?
The core theorem: yes
Lemma 2.5 really has been detached from digit structure. Its hypotheses consist only of the Pisot recurrence, a bounded coefficient alphabet, two adjacent weighted zero relations, and their integer quotients. The proof uses the bounded carries, the contracting embeddings, the finite algebraic separation, and the unchanged dominant-embedding identity. No canonical language or realization of coefficients as digit differences enters. 
Theorem 2.6 then makes exactly the right quantitative statement. For each aperture m, its vertices are bounded coefficient windows, and an edge exists precisely when the corresponding length-m body can be completed by a coefficient of um​ to give zero. In the absence of a reachable cycle, the longest path from a first-coordinate-nonzero state is OU,D​(m), effectively. The fixed cubic example gives the matching linear lower order. 
The proof is both short and substantive. Once two adjacent rows exist, Lemma 2.5 forces every carry after the first to vanish and forces all subsequently appended coefficients, apart from the one determined by the first carry, to vanish. A path of m+1 edges therefore reaches the zero vertex; because that vertex has a loop, this contradicts the no-reachable-cycle hypothesis. The finitely many apertures below m0​(U,D) are covered by exact longest-path computations. 
I see no hidden use of:


the canonical rank bijection;


legality of digit words;


the cyclic fold;


positive/negative realization by raw digits;


the image shift or its decoder.


The manuscript’s logical-boundary remark is accurate on this point. 
The sharpness transfer is also legitimate. Although the words Em​ were first discovered inside the collision problem, in Theorem 2.6 they are used only as bounded coefficient words satisfying the recurrence identities. The proof explicitly discards their realization as differences of raw codewords. 
How narrow is the crossing?
The right formulation is:

The rows are classical bounded U-representations of zero; the aperture-dependent overlap transient is the new quantity.

That is a real standard-object theorem. But it remains narrow because the family of overlap graphs is not itself a classical named invariant of numeration systems. A referee could reasonably describe Theorem 2.6 as a clean abstraction or corollary of the adjacent-collapse mechanism. A referee could not reasonably describe it as merely a restatement of Theorem 2.3, since neither its statement nor its upper-bound proof requires the cyclic code.
In other words, it escapes the paper’s original vocabulary, but it does not establish a new general theory of zero-representation automata. That is exactly the “real but narrow” crossing anticipated earlier.
Two statement repairs
First, the terminal coefficient should be made explicit. In the edge definition, the body coefficients lie in [−D,D], but the coefficient c of um​ is not required by the statement to lie there. The proof establishes the uniform bound
∣c∣=∣kt​∣≤KU,D​.
Thus each edge is indeed a bounded U-representation of zero, but over the fixed mixed alphabet
[−D,D]m×[−KU,D​,KU,D​],
not necessarily with every coefficient bounded by D. I would insert immediately after (2.28):

“The completing coefficient is unique and necessarily satisfies ∣c∣≤KU,D​.”

That removes a predictable terminology objection.
Second, the printed “Equivalently” clause needs anchoring. The theorem currently passes from paths beginning at a vertex with nonzero first coordinate to all overlap chains merely “containing a nonzero exposed coefficient.”  Under the natural unanchored reading, that is false.
Your own nonstandard example already supplies a counterexample. Take
U=(1,2,4,9,…),D=2,m=2.
The graph has vertices −2,−1,0,1,2, and
a⟶b⟺a+2b≡0(mod4).
Hence
0→0,0→2,2→1,
while 1 has no outgoing edge. No directed cycle is reachable from a nonzero vertex: ±2 lead to ±1, and the latter are terminal. Nevertheless, for every N,
N zero loops0→0→⋯→0​​→2→1
is a terminating chain of arbitrarily large total length which eventually contains a nonzero exposed coefficient.
The correct equivalent formulation is:

“After shifting a chain so that its initial exposed coefficient is nonzero, either it reaches a directed cycle, or it has fewer than C(U,D)m further overlaps.”

Alternatively, delete the “Equivalently” sentence and retain the precise graph statement. This is a local statement defect, not a defect in Lemma 2.5 or in the graph theorem.
2. Priority
What the classical literature actually gives
The nearest primary sources establish finite-state recognition at the level of individual zero representations:


Frougny proves finite-automaton normalization and addition in Pisot bases. Springer


Frougny–Pelantová prove finite Büchi recognizability of infinite bounded β-representations of zero in the relevant Pisot regime. arXiv+1


The recent Carton–Sudbery–Yassawi paper states that for a Pisot numeration U and any finite coefficient set B⊂Z, the finite words g∈B∗ with [g]U​=0 form a regular language. arXiv+1


Those results answer:

Is the zero-representation relation recognizable by a finite automaton?

Theorem 2.6 answers a different quantitative question:

As the aperture m varies, how long can an acyclic one-position-overlap chain of length-m zero relations survive?

Regularity alone leaves an order-m context graph with up to (2D+1)m−1 vertices. It supplies a finite row recognizer; it does not collapse the longest acyclic path in that context lift to O(m). A generic pumping argument therefore does not dispose of Theorem 2.6.
The closest recent contraction results also do not subsume it. Carton–Sudbery–Yassawi’s zero-preservation machinery is equivalent to Condition F, and their long-zero-block conclusions are formulated under zero preservation. Theorem 2.6 instead works for every fixed Pisot recurrence in its stated class, including non-Condition-F examples, because it uses the two-adjacent-row separation rather than normalization or zero preservation. arXiv+2arXiv+2
Nor do the decoder-window precedents create a collision. Ashley’s bound is linear in the number of states of a presenting graph; applied directly to the natural aperture-m pair or difference graph, that remains exponential in m. IBM Research Frougny–Sakarovitch study rational relations already assumed to have bounded head delay; they do not infer an O(m) delay or transient from acyclicity of these overlap graphs. Springer
My priority conclusion
I would assign approximately:
0.82​
to the proposition that the precise theorem
no reachable cycle⟹overlap transient OU,D​(m)
will survive a specialist priority audit as genuinely new.
The remaining 0.18 is not because I see a likely collision in the core numeration literature. It is because the same object could have appeared under different automata terminology—de Bruijn powers of a regular constraint, mortal context graphs, nilpotency indices, or finite-delay presentations—without using the phrase “bounded representations of zero.”
A specialist might still say:

“This is a short consequence of your Pisot contraction lemma.”

That would be fair. I do not think a specialist can fairly say:

“This is already a standard consequence of the bounded-zero automaton.”

The manuscript’s existing priority discussion makes the correct distinctions between recognizability, state-count bounds, bounded-delay conversion, and the new m-linear estimate.  The best additional defense would be one explicit sentence—or a small fixed-regular-language example—showing that regularity of the row language alone does not force a linear transient in its order-m overlap lifts.
The computational battery is useful evidence that the generalization was not written around only friendly examples, but the paper correctly treats those computations as falsification and regression tests rather than proof.  
3. Venue effect
The venue label remains unchanged.
The addition improves the TAMS case in one important respect: a referee can no longer accurately summarize the entire manuscript as exact analysis of a newly defined cyclic rank-fold. The paper now contains a quantitative theorem about a standard numeration-theoretic relation, valid for arbitrary bounded coefficient alphabets and independent of the code.
But it does not make TAMS a natural or secure placement, for three reasons.
First, Theorem 2.6 uses the same central contraction as Theorem 2.3. It is a strong abstraction of the mechanism, not a second independent mechanism.
Second, the new quantity is the transient of a particular one-position-overlap organization. That is natural, but it is not yet a widely used invariant or the solution of a recognized named problem.
Third, the paper is still 67 pages with 52 numbered results, and its title and most of its architecture remain centered on the cyclic language-rank recoding. A hostile TAMS referee can therefore continue to ask whether the field-level theorem is large enough, relative to the total package, to support the paper’s length and breadth.
My revised venue description would be:


TAMS: still a defensible ambitious first submission, now less vulnerable to the “entirely bespoke object” objection.


ETDS: still the strong natural alternative and probably the venue at which the whole symbolic-dynamical package is easiest to value on its own terms.


So the addition moves the manuscript within the same band, not into a higher band.
4. Strongest remaining objection
There are two answers, depending on whether one means the current text or the repaired paper.
Strongest objection to the current text
The unanchored “Equivalently” clause in Theorem 2.6 is not valid as written. The U=(1,2,4,9,…), D=2, m=2 calculation above is an explicit boundary counterexample. It must be changed before submission. This is minor in repair cost but not optional.
The terminal coefficient bound should also be stated explicitly so that “bounded representation” cannot be read as asserting ∣c∣≤D.
Strongest objection after those repairs
The strongest remaining objection is proportionality of significance:

The paper’s standard-object theorem is a concise extraction of the same adjacent-collapse lemma, while the bulk of the 67-page manuscript still studies a specially constructed cyclic rank code. Is that one narrow external theorem, together with the exact quadratic and cubic classifications, enough to justify TAMS-level breadth?

That objection is stronger than the remaining priority risk. Theorem 2.6 successfully answers “does the machinery reach an independently recognized object?” It does not by itself answer “is the resulting package broadly important enough for TAMS?”
Bottom line
The work was worth doing. After the anchoring correction, Theorem 2.6 is a genuine theorem about bounded U-representations of zero, not decorative relabeling. Its O(m) transient bound appears likely to be new and is not a routine consequence of classical zero-automaton regularity.
But the standing is unchanged in the sense you asked about:
TAMS remains ambitious and defensible; ETDS remains the strong natural alternative.​
The manuscript is mathematically stronger and less inward-looking than before. It has not become an obvious TAMS paper.
