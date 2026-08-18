1. Significance
Send it out for external review. Do not desk-reject it.
The paper clears the significance threshold of Dynamical Systems, though not comfortably. The publishable point is not merely that a particular finite code happens to be injective. It is the conjunction of:


a uniform conjugacy theorem for every m≥3;


two genuinely different optimal reconstruction scales;


the exact, m-independent inverse radius 2;


the contrast between that bounded symbolic inverse and arbitrarily long Fibonacci carry propagation;


a complete description of the exceptional case m=2.


That package constitutes a recognizable symbolic-dynamics result. In particular, “three labels always suffice although normalization carries are unbounded” is a theorem with conceptual content, provided the four-state mechanism is proved uniformly rather than discovered computationally.
The limitation is narrowness: it is one explicitly constructed family, and the two threshold theorems remain closely tied to that family. Recent papers in Dynamical Systems include broader results on inverse variational principles, entropy representations, Lyapunov-maximizing measures, and invariant curves, so this submission sits near the lower edge of the journal’s theoretical significance level. Taylor & Francis Online+4Taylor & Francis Online+4Taylor & Francis Online+4
My editorial decision would nevertheless be external review, not a scope or significance rejection.
2. Acceptance probability
42%.
That number assumes the uniform proofs are complete and that the exhaustive computations are presented only as audits, not as evidence replacing the proof.
3. Single highest-value change
Add a general finite-carry synchronization theorem from which the Zeckendorf result follows.
The appropriate theorem would say, in substance:

For a sliding block factor represented by a finite carry transducer satisfying an explicit synchronization and boundary-cancellation condition, the factor is conjugate to its image, and the exact memory/anticipation of the inverse is determined by the shortest separating path in the carry-pair graph.

The paper should then verify those hypotheses for the four-state Zeckendorf carry graph and obtain inverse memory 2 as a corollary. Ideally, the same framework should also explain why the whole-block threshold is m, rather than treating the two thresholds through unrelated word calculations.
That change would convert “a sharp analysis of one coding” into “a reusable symbolic-dynamics criterion with a sharp arithmetic application.” It would raise my estimate by roughly 20 percentage points, to about 62%.
Merely adding more computations, more values of m, or a longer discussion of Fibonacci normalization would not materially raise the probability.
4. Weakest load-bearing step
The first target of a hostile referee is the theorem asserting:

Three consecutive folded labels determine the present raw digit uniformly for every m≥3.

This is the load-bearing theorem because it supplies injectivity and continuity of the inverse. The obvious attack is that a four-state carry graph may encode carries internal to a finite normalization window without proving that it captures every carry state induced by arbitrary bi-infinite tails. Unbounded carry cascades make “there are only four relevant states” precisely the point that cannot be accepted informally.
The proof must establish all three of the following without appealing to the m≤9 computations:


every admissible pair of two-sided lifts projects to a path in the stated carry-pair graph;


no additional state can enter through a carry propagated from arbitrarily far outside the displayed window;


the boundary-cancellation identity applies uniformly to all admissible tails, including periodic or eventually extremal configurations.


This is repairable, not fatal, provided the paper already contains the correct invariant and merely compresses its completeness proof. A full transition table plus a lemma proving that the state map is exhaustive would settle it.
It becomes fatal if the four-state claim is inferred from bounded-m enumeration or from finite words with an imposed zero boundary condition. The checks through m=9, even over all 217 words, cannot establish the two-sided uniform theorem.
5. Alternative journal
Journal of Automata, Languages and Combinatorics, following a decline from Dynamical Systems—not replacing the present submission.
Its scope explicitly includes automata and their relations with other subjects, and the carry graph, exact decoding radius, synchronizing behavior, and optimal witness words fit that readership directly. Its recent volumes continue to publish finite-automaton and Fibonacci-related work. Jalc+2DBLP+2
So the submission order I would use is:
Dynamical Systems first; Journal of Automata, Languages and Combinatorics only after a decline.
