1. Verdict: minor revision
Strongest reason: Corollary 2.3 is false as written. It drops the anchoring condition that makes Theorem 2.2 correct and thereby permits arbitrarily many initial traversals of the zero loop. The core results—Theorem 2.2, Corollary 3.2, and Theorem 4.1—appear to survive, so I would not demand a mathematical reconstruction. But I would not accept a paper containing a false labeled corollary, especially when the same anchoring issue has plainly been encountered before.
2. ETDS significance threshold
Yes, narrowly. I would not call the paper correct but too small for ETDS.
The case for ETDS is Theorem 2.2, not the aperture-three curiosity. It gives, for every fixed irreducible nonintegral Pisot recurrence and every coefficient bound, an effective eventual coefficient-one linear path bound, together with an effective all-aperture conditional O(m) bound. The passage from that arithmetic statement to an exact collision quotient, eventual injectivity, and a sharp future-only inverse coefficient is coherent rather than a collection of examples. The cubic then proves sharpness while keeping the recurrence and alphabet fixed.   
This is at the lower edge of the journal, because the cyclic-rank recoding is bespoke and the paper does not demonstrate a large external dynamical consequence. An editor could decide that the construction is too self-generated. But ETDS does publish focused papers on particular symbolic and cellular systems at roughly this scale; a recent twenty-page article on elementary cellular automaton 18, for example, centers on an exact partial classification for one fixed automaton and a separation consequence. 剑桥大学出版社
So my answer is: it clears, but it is not secure. A rejection would more likely say “the dynamical object is insufficiently natural” than “the theorem is too small.” I would not redirect it pre-emptively to a lower journal.
3. The point a hostile referee attacks first

Corollary 2.3: “Either some chain with a nonzero coefficient has a finite prefix followed by a periodic bounded zero representation, or every nonzero chain has fewer than (C(U,D)+1)m rows.” 

This is false under the ordinary meaning of “nonzero chain.”
Take the Tribonacci numeration sequence
U=(1,2,4,7,…),un+3​=un+2​+un+1​+un​,
with D=2 and m=2. Its characteristic polynomial
x3−x2−x−1
is irreducible, has one real root β>1, and its conjugate pair has modulus β−1/2<1; hence it is within the paper’s Pisot class.
The graph G2​(U,2) has vertices −2,−1,0,1,2, and
e⟶f⟺e+2f≡0(mod4),
by the paper’s edge definition.  Its nontrivial edges are
0→±2,2→±1,−2→±1,
in addition to the zero loop. The vertices ±1 have no outgoing edge. Thus:


the only directed cycle is the zero loop;


no cycle is reachable from a first-coordinate-nonzero vertex;


there is no nonzero chain with an eventually periodic tail.


Nevertheless, for every N there is a chain consisting of N zero loops followed by
0→2→1.
In terms of bounded zero rows, this is
(0,0,0)N,(0,2,−1),(2,1,−1).
It contains nonzero coefficients and has arbitrarily many rows. This contradicts the second alternative of Corollary 2.3 for every fixed C(U,D).
The precise error is in the proof sentence

“at most m−1 initial shifts pass before a nonzero coordinate occupies the first position.”

That is true only after the first nonzero coefficient has appeared. It does not control an arbitrary number of leading zero rows.
Theorem 2.2 itself avoids this error by explicitly shifting to an “initial exposed coefficient” that is nonzero.  Corollary 2.3 immediately loses that anchor again. Delete the corollary, or restate it as a bound on the portion of the chain beginning with its first nonzero row. Do not try to preserve the present “global” formulation.
4. Is one exceptional aperture enough?
It is enough for the narrow logical claim, and not enough for the broader rhetoric.
Corollary 3.2 has the form
∀U ∃mU​ ∀m≥mU​:ΦU,m​ is injective.
The all-aperture strengthening would be
∀U ∀m≥2:ΦU,m​ is injective.
One witness (Uθ​,3) with noninjectivity is sufficient to refute that universal strengthening. Theorem 4.1 supplies exactly such a witness: aperture two is injective, aperture three is not, and every aperture from four onward is injective. 
So the sentence

“the eventual qualifier in Corollary 3.2 cannot be removed”

is logically correct, provided “removed” means “replaced by injectivity for every m≥2.”
But the introduction says more:

“Theorem C shows that the threshold in Theorem B is intrinsic rather than an artifact of the contraction estimate.” 

That is overstated. The example proves only that a universal theorem cannot start at m=2. It does not show:


failures at arbitrarily large apertures;


that the thresholds mU​ are unbounded as U varies;


any quantitative lower bound on mU​;


that a universal theorem beginning at m=4 is impossible;


that the analytic contraction threshold has the right scale.


In substance, it does show that this particular system has a one-step defect at m=3, and that injectivity is not monotone from aperture two onward. That is enough for the literal counterexample, not enough to make the threshold phenomenon look substantial.
I would replace the introductory claim with:

“Theorem C shows that the all-aperture strengthening of Theorem B is false, even for a fixed cubic system whose aperture-two recoding is injective.”

That says exactly what was proved.
5. Abstract and introduction: hypothesis audit
There are three definite scope defects, plus one under-specified theorem statement.
(a) The abstract states Theorem 2.2 under weaker hypotheses
The abstract says:

“If U=(uj​) is strictly increasing, u0​=1, and its recurrence has a nonintegral Pisot characteristic root…” 

The actual theorem requires a strictly increasing sequence of positive integers satisfying an integral recurrence whose characteristic polynomial is exactly the minimal polynomial of a nonintegral Pisot number. 
“Has a nonintegral Pisot characteristic root” is much weaker. It permits additional characteristic roots that are not algebraic conjugates of the Pisot root and need not lie inside the unit disk. The proof does not cover that situation: its central estimate sums over all roots of the minimal polynomial and uses ∣βi​∣<1 for every nondominant root. 
This is not harmless shorthand. Replace the abstract hypothesis with the theorem’s exact hypothesis.
(b) The abstract drops the reachability anchor
The abstract says:

“At all apertures, the absence of a reachable cycle gives an effective C(U,D)m transient bound.” 

The theorem says that no directed cycle is reachable from a vertex whose first coordinate is nonzero. 
That qualification matters because the zero loop is always present. Without identifying the initial set, “absence of a reachable cycle” is either undefined or vacuous. It should read:

“For every m≥2, if no directed cycle is reachable from a first-coordinate-nonzero vertex, …”

Given the false Corollary 2.3, this is not a stylistic complaint. The anchor is doing real mathematical work.
(c) “Every fixed Pisot system” is broader than Corollary 3.2
The abstract says:

“The recoding of every fixed Pisot system is therefore injective at all sufficiently large apertures…” 

Corollary 3.2 requires a strictly increasing Pisot numeration system, u0​=1, with the canonical greedy digit set and canonical normal words.  The paper’s own definition also separates the Pisot recurrence condition from the additional assumptions of strict increase and u0​=1. 
Write “every such strictly increasing Pisot numeration system” and repeat u0​=1, unless the term is explicitly defined before the abstract—which it cannot be.
(d) Theorem A in the introduction is not self-contained
Theorem A says merely:

“Let U=(uj​) be strictly increasing with u0​=1, and suppose that its integral recurrence has as characteristic polynomial…” 

The formal theorem says “a strictly increasing sequence of positive integers.”  An “integral recurrence” ordinarily describes the recurrence coefficients, not necessarily the values of the sequence. Since integrality of the weights is used for divisibility, integer quotients, and finite graph construction, Theorem A should include “positive integers.”
What does match
Theorem B in the introduction matches Corollary 3.2. Theorem C matches Theorem 4.1. The cubic aperture classification, the formula
ℓcau​(θ,m)=2⌊m/2⌋−1
at the injective apertures, and both sharpness conclusions are stated with the hypotheses actually proved.  
The “threshold is intrinsic” sentence is not a hypothesis mismatch; it is a logical overinterpretation, dealt with in item 4.
