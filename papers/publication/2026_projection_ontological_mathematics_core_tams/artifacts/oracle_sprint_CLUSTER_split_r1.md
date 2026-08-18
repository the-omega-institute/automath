Editorial decision: two papers
Three is not defensible. One is unnecessarily unwieldy. But the correct two-paper division is not simply “merge C into A and leave B untouched.” The present boundaries cut across the natural mathematical division.
Paper C is not an independent paper once Paper A exists. Its sequences are the same sequences, its transfer matrices supply machinery for A’s Perron-root conclusions, its q=2 recurrence is an exact instance of A’s moment program, and its maximal-fibre theorem concerns the same endpoint as A’s zero-temperature result. Disclosure would prevent an accusation of concealment, but it would not cure the salami slicing.
Papers A and B contain two defensible theorem-level programs, but A’s pressure, thickness, and zero-temperature material belongs thematically with B’s freezing and large deviations.
1. The two-paper division
Paper I: Fibre spectrum, extremal multiplicities, and freezing
This should be the B-centered paper. It should contain:


The formal equivalence of the different folding conventions, including the exact index shift and equality of fibre multisets.


The partition-difference formula, with its only full proof.


B’s complete multiset identity involving the two consecutive Fibonacci-partition layers.


B’s factorization at even Zeckendorf zero-runs.


The exact second-largest fibre value, all its locations, and eventual degeneracy.


C’s exact maximal-fibre heights.


A’s convexity of the pressure and the two-sided thickness-band estimates.


A’s zero-temperature conclusion
Dm1/m​⟶φ​.


B’s weighted renewal identity.


B’s asymptotically linear critical partition sum and uniform coexistence law.


B’s full large-deviation principle, including the affine coexistence interval and the orbit-filling argument for nonexposed slopes.


B’s power-law limit for the counting measure of fibres whose multiplicity is of order m.


Its headline theorem should be something like:

The fibre multiplicity spectrum of the Fibonacci fold satisfies a full large-deviation principle with a freezing transition: the rate function has an affine coexistence interval, the extremal and second-extremal fibres are determined exactly, and the critical multiplicity counting measure has a power-law limit.

That is a genuine paper-level result. The exact combinatorics, extremal theory, and thermodynamic conclusions reinforce one another.
The fixed-q moment asymptotics from the second paper may be cited as an input where needed. They should not be reproved here.

Paper II: Finite-state moment recurrences and arithmetic
This should merge the moment/arithmetic portion of A with essentially all of C. It should contain:


C’s losslessness theorem for the bounded signed-Fibonacci carry automaton.


The effectively constructible integral transfer matrix for every fixed q.


The resulting rationality of the generating series for each fixed q.


The exact recurrence
S2​(m)=2S2​(m−1)+2S2​(m−2)−2S2​(m−3).


A’s comparison with adjacent windows of Sanna’s Fibonacci-partition power sums.


The exponential asymptotic Sq​(m)∼cq​λqm​, or whatever precise asymptotic the proofs establish.


The identification of λq​ as a Perron root and hence an algebraic integer.


C’s nonrationality of the full bivariate moment series, presented as the contrast:
every fixed-q slice is rational, but there is no single finite rational transfer for the entire moment tower.


A’s certified irreducibility and full symmetric Galois groups for q=9,…,17.


A’s Chebotarev-density consequence.


The partition-difference formula should be cited from Paper I. It may be restated, but not reproved.
Its headline theorem should be:

For every fixed moment degree q, the fibre power sum of the Fibonacci fold is exactly a coefficient of an effectively constructible integral transfer matrix; consequently it satisfies a linear recurrence and has Perron-algebraic exponential growth, while no single rational bivariate generating function encodes the whole moment tower.

The Galois and Chebotarev results are arithmetic consequences of that transfer theory. They belong in this paper, perhaps in a final section or supplement. They are not a third paper.
Why not one paper?
The two headlines are genuinely different:


a global spectrum/freezing/LDP theorem;


a fixed-degree finite-state and arithmetic theorem.


Combining them would likely produce a very long paper with two unrelated culminations. The two-paper split is intellectually intelligible and editorially defensible.
Why not three?
Because C has no independent theorem-level spine after the identity of the sequences is disclosed. Its main contribution is an important method and exact refinement of A’s moment theory. That is material for strengthening Paper II, not grounds for a separate simultaneous publication.
Before either paper is submitted, the authors should prove—not merely computationally observe—the convention equivalence. There should be a short proposition establishing for all m,q the precise relation, for example
SqA​(m+1)=SqC​(m),Dm+1A​=DmC​,
together with the corresponding equality or bijection of complete fibre multisets. A table through m=12 is evidence for finding the equivalence, not an acceptable substitute for stating it.
2. Minimum disclosure
The disclosure must appear inside the manuscripts, not only in cover letters. A referee should not have to infer the identity by comparing tables or conventions.
In Paper I
Place a subsection entitled “Relation to the companion paper” on the first or second page of the introduction. It should say, in substance:

The folding convention used in the companion paper [II] is equivalent to the present one after the reindexing m↦m+1. In particular, the complete fibre multisets agree under this reindexing, so that SqII​(m)=SqI​(m+1) and likewise for the maximal fibre multiplicity. The present paper studies the complete multiplicity spectrum, its extremal fibres, and its freezing and large-deviation behavior. The companion paper studies fixed-degree carry automata, transfer recurrences, Perron algebraicity, and the arithmetic of the resulting recurrence polynomials. The partition-difference formula is proved only in the present paper.

The exact superscripts and shift should match the final conventions. Do not use vague language such as “closely related,” “arising from a similar model,” or “a companion construction.” The point is that it is the same object.
At the first use of a fixed-q moment theorem from Paper II, write:

By [II, Theorem X], for each fixed q the moment sequence has an integral transfer representation and exponential rate λq​.

Then use it. Do not reproduce the automaton proof.
In Paper II
Again, put “Relation to the companion paper” in the introduction, not in the final remarks:

The moment sequences studied here are not different sequences from those of [I]. After the explicit change of indexing described in Proposition 1.1, their complete fibre multisets, power sums, and maximal multiplicities agree exactly. Paper [I] develops the full fibre spectrum, extremal structure, freezing transition, and large-deviation theory. The present paper develops a lossless finite-state representation for each fixed moment degree and derives exact recurrences, Perron-algebraic growth, nonrationality of the full moment series, and arithmetic properties of the recurrence polynomials.

At the partition-difference formula, write:

We use the following identity from [I, Theorem Y]. It is restated solely to fix notation.

Then state the formula and proceed without duplicating its proof.
In both cover letters
Each editor should receive the other manuscript or a stable public preprint, together with a direct disclosure such as:

A companion manuscript by the same authors studies the same Fibonacci-fold fibre multiset under a different indexing convention. The exact relation is given in Section 1.2. The shared input is the partition-difference identity, proved only in Paper I and cited in Paper II. Paper I concerns the full spectrum, extremal fibres, freezing, and large deviations; Paper II concerns fixed-degree transfer matrices, recurrences, and arithmetic. We enclose the companion manuscript for comparison.

Submitting either manuscript while leaving the related one uncited and undisclosed would be a serious editorial error.
Were C nevertheless kept separate
Its first page would have to say:

The sequences considered in this note are exactly those studied in [A], after the reindexing SqC​(m)=SqA​(m+1), and the maximal-fibre sequences agree under the same shift. The contribution of this note is limited to a direct lossless carry-automaton realization, the resulting fixed-degree transfer matrices and recurrences, and the contrast between fixed-degree rationality and bivariate nonrationality.

That disclosure is necessary, but it would also make obvious why most editors would ask for merger with A.
3. Publishability ranking as the manuscripts stand
1. Paper B
B has the strongest independent mathematical endpoint. The full LDP with an affine coexistence interval, especially if the orbit-filling map genuinely supplies the nonexposed slopes, is the clearest paper-level theorem in the package. The exact near-extremal structure and critical counting law give it a coherent narrative rather than a collection of calculations.
Effect of overlap: it lowers B’s chances in its current form. The verbatim theorem shared with A is an immediate problem, and A’s pressure/thickness/zero-temperature sections make the division look artificially engineered. After the re-cut above, the overlap becomes beneficial because Paper II supplies a clean fixed-q input rather than competing for B’s conclusion.
2. Paper A
A contains substantial mathematics, but as presently organized it is diffuse: partition identities, moment asymptotics, thermodynamic selection, zero temperature, finite-window Galois computations, and Chebotarev density do not naturally produce one headline. The Galois section in particular risks looking appended to increase apparent breadth.
Effect of overlap: it materially lowers A’s chances. C shows that the same moments have a direct transfer theory and exact recurrence structure, while B occupies the natural endpoint of A’s pressure and zero-temperature discussion. A becomes much stronger after absorbing C’s finite-state machinery and surrendering the thermodynamic material to the spectrum paper.
3. Paper C
As an isolated note, C has a respectable technical core: the losslessness proof is the real contribution, and the fixed-q rationality versus full bivariate nonrationality is a clean contrast. But in the presence of A, it is not a separate publication.
Effect of overlap: essentially fatal to independent publication. The same Sq​ and maximal-fibre sequences are being presented under conventions that conceal their identity. Exact S2​, exact maxima, and a direct automaton are valuable additions to A’s program, but they do not support a third simultaneous paper.
Thus the ranking is
B>A≫C​
as mathematical manuscripts, while none of the three should be submitted simultaneously in their present undisclosed form.
After the proposed restructuring, the B-centered spectrum/freezing paper would remain the stronger of the two, and the A+C finite-state/arithmetic paper would be a credible, distinct companion.
4. The theorem repeated verbatim
Disclosure alone is not enough.
A mathematical theorem statement may legitimately be restated in a second paper when it is needed for readability, but it must be presented as a cited result. A substantial theorem cannot be presented as an original numbered theorem in two simultaneous submissions, with the same proof and surrounding text, merely because both manuscripts disclose the relationship.
One paper must own the theorem and its proof. Under the proposed division, the B-centered spectrum paper should own the partition-difference theorem because it proceeds to the stronger complete-multiset identity. The finite-state moment paper should say:

We recall [I, Theorem Y].

It may then reproduce the mathematical statement. It should not reproduce the proof word for word, and it should not list the theorem among that paper’s novel contributions.
The workable rule is:


Same statement, explicitly cited and restated for convenience: acceptable.


Same proof or substantial exposition repeated: not acceptable except for a truly trivial lemma.


Same theorem presented as original in both papers: not acceptable.


Both papers require the full theorem and full proof to sustain their claimed novelty: then they have not been separated successfully and should be merged.


The present “word for word, same label, same notation” arrangement would alarm a referee even with a disclosure paragraph. One paper must cite rather than duplicate.
