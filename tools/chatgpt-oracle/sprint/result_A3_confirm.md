Confirmation-audit verdict
Theorem A survives the audit. I find (A1) mathematically correct, including the graph-reachability step and the claimed effectivity of CU​. I also find (A2)–(A3) correct and genuinely sharp in growth order. The class is a recognized Pisot-numeration class, not your constructed family in disguise, and I found no published theorem that already gives this particular OU​(m) inverse-depth bound.
There is, however, one material revision I would insist on:

Condition F and zero preservation appear to be unnecessary for (A1).

The proof as written establishes a stronger theorem for every strictly increasing Pisot numeration system of the stated recurrence type. That is good news mathematically, but it means the current scope language and the role assigned to the bounded-zero automaton should be rewritten.
1. Is (A1) correct?
The collision quotient and reachability argument are correct
The passage from output collisions to digit-difference congruences is exact. Because the normal words represent 0,…,um​−1 bijectively, two folded windows are equal exactly when their weighted raw values agree modulo um​. Every coordinate e∈[−dU​,dU​] is realized as the difference of two digits in DU​ by taking its positive and negative parts. Consequently no collision is lost when the pair graph is quotiented by coordinatewise difference. This justifies both the obstruction-set formula and the path-length formula for ℓcau​. 
The role of the first-coordinate-nonzero set BU,m​ is also right. A vector in NU,m,L​ starts with e0​=0, hence starts at such a state; conversely, every path from such a state determines a realizable pair of raw blocks whose first digits differ. Thus
ℓcau​(U,m)=1+sup{edge length of a path from BU,m​}.
The only subtlety is the zero loop. A nonzero reachable cycle immediately gives a periodic collision. The zero cycle would merely give an arbitrarily long one-sided ambiguity unless one proves that it cannot be reached. The manuscript does prove this:


If dU​≥um​, the constant difference sequence et​=um​ is allowed and gives a nonzero loop, so ΦU,m​ is already noninjective.


Hence injectivity forces dU​<um​.


Under that inequality, any edge into the zero vertex has all overlap coordinates zero and satisfies e0​≡0(modum​); since ∣e0​∣≤dU​<um​, it follows that e0​=0. Therefore zero has only itself as predecessor and cannot be reached from BU,m​.


That closes precisely the potential reachability gap. 
The effective Pisot-contraction constant is valid
The Binet decomposition
un​=i∑​ci​βin​,c0​>0,
is valid for the recurrence because the characteristic polynomial is the separable minimal polynomial of the Pisot root. The claimed effective bounds
bU​βn≤un​≤AU​βn
can indeed be produced by isolating the roots, finding an effective point beyond which the contracting-conjugate contribution is at most half the dominant contribution, and checking the remaining finite prefix exactly. 
The carry bound
∣kt​∣≤dU​um​∑j<m​uj​​<bU​(β−1)dU​AU​​
is correct. Once the finite set of possible carries is known, the separation
δU​=min{∣a+k−βl∣:a∈ΔU​, k,l∈KU​, a+k−βl=0}
is positive. For l=0, equality would make the nonintegral algebraic integer β rational; for l=0, the nonzero quantity is an integer. Algebraic-number comparison makes the minimum effective. 
The key adjacent-row identity is also correct:
βm(et+m​+kt​−βkt+1​)=βAt+1,0​−At,0​+et​.
The contracting embeddings uniformly bound the right side. Once
βmδU​>BU​, the parenthesis must vanish; irrationality then separately forces
kt+1​=0,et+m​=−kt​.
I checked the subtraction leading to this identity; there is no missing boundary term. 
For L=m+1, repeated carry collapse makes the terminal difference vertex zero. Under the no-reachable-cycle hypothesis, that is impossible because zero has its loop. Therefore no path from BU,m​ has more than m edges at large apertures, giving
ℓcau​(U,m)≤m+1≤2m.
The finitely many smaller apertures are handled by exact cycle detection and longest-path searches, yielding the stated effective CU​.  
The important strengthening: Condition F is not used
The manuscript currently obtains the finite carry set by intersecting a bounded-zero automaton with a finite terminal alphabet. That is legitimate: for every Pisot numeration and every fixed finite alphabet, the finite zero-representation language is regular. This regularity is not restricted to Condition F systems. arXiv
More decisively, the automaton can be removed altogether. Define
KU∗​=⌈bU​(β−1)dU​AU​​⌉
and take all integers ∣k∣,∣l∣≤KU∗​ in the definition of the separation constant:
δU∗​=min{∣a+k−βl∣:a∈ΔU​, ∣k∣,∣l∣≤KU∗​, a+k−βl=0}.
This is still a finite, effective, positive minimum, and every actual carry is contained in the chosen interval. Replacing KU​ by KU∗​ in MU​, BU​, and mU​ reproduces Lemma 7.2 verbatim.
Therefore my conclusion is stronger than merely “I found no use of Condition F”: the displayed proof gives an explicit replacement that proves (A1) without Condition F, zero preservation, or a zero-normalization automaton.
This does not invalidate the stated theorem. It means the theorem is overhypothesized. I would revise it to:

Let U be any strictly increasing Pisot numeration system with u0​=1, canonical greedy digit set and canonical normal words. Then there is an effectively computable CU​<∞ such that
ΦU,m​ injective⟹ℓcau​(U,m)≤CU​m.

The automaton-derived carry set may remain as an optional sharpening of the numerical value of CU​, not as a hypothesis or logical input.
If the authors retain the current formulation, I would still accept (A1) as correct. The only point requiring a citation or a sentence of construction is exactly which finite zero automaton is being supplied and in which digit-reading orientation. That is an effectivity-presentation issue, not a mathematical gap.
2. Is the quantified class genuine?
It is a genuine standard numeration class, not a disguised family
The manuscript’s definition agrees with the recognized notion of a Pisot numeration: an integer sequence generated by the integral recurrence whose characteristic polynomial is the minimal polynomial of a Pisot number, together with greedy normalization and its canonical bounded digit set. arXiv+1
Representative systems satisfying the hypotheses include:


Ordinary radix systems un​=bn, b≥2.


The standard silver-mean system
1,2,5,12,29,…,un+2​=2un+1​+un​,
associated with x2−2x−1. Its greedy expansion of 1 is 210∞, which lies in the classical Frougny–Solomyak finite-expansion class. 剑桥大学出版社


Shifted Zeckendorf/Fibonacci
1,2,3,5,8,…,
shifted Tribonacci
1,2,4,7,13,…,
and, similarly, shifted k-bonacci systems. These are among the canonical examples of Pisot numeration, and all k-bonacci roots satisfy Condition F. arXiv+1


Standard or nonstandard systems attached to many other Condition F roots, such as the cubic root of x3−x2−2x−1, for which both standard and nonstandard initial-value systems are explicitly studied in the recent Pisot-numeration literature. arXiv


Both the standard system and the manuscript’s language-count system associated with the root of x3−2x2+x−1.


So the class is unquestionably populated outside the manuscript’s specially analyzed Uθ​.
But the abstract’s use of “standard” is terminologically inaccurate
In current Pisot-numeration usage, “standard” commonly has the technical meaning
u−1​=⋯=u−d+1​=0,u0​=1,
rather than merely “a conventional Pisot numeration system.” The manuscript simultaneously says “standard” and allows nonstandard initial values. arXiv
There are two additional qualifications:


Condition F is a real restriction. General Pisot numbers need not have it; for example, the principal root of
x3−3x2+2x−1
is a standard cited example of a Pisot root without the finiteness property. 筑波大学数学系+1


Some iconic systems in the precise standard-initial-condition convention begin 1,1,…, so they fail the manuscript’s strict-increase hypothesis at the first index. The usual shift to 1,2,…, explicitly permitted by the nonstandard-initial-values clause, restores strict increase.


Thus, as presently stated, the sentence “uniform over standard Pisot numeration systems” is broader than the formal theorem. It is not fraudulent—the next sentence gives the zero-preservation qualification—but a hostile referee could reasonably object.
The correct current wording is:

“uniform over every fixed strictly increasing zero-preserving Pisot numeration system, with nonstandard initial values allowed.”

After removing the unused Condition F assumption, the cleaner wording is:

“uniform over every fixed strictly increasing Pisot linear numeration system.”

That version would completely eliminate the concern that the class is artificially selected around your examples.
3. Do (A2) and (A3) give a genuine matching lower bound?
Yes.
The exact obstruction identity
Nθ,m,λm​−1​={Em​,−Em​}=∅,Nθ,m,λm​​=∅
implies, directly from the exact collision criterion,
ℓcau​(θ,m)=λm​=2⌊2m​⌋−1.
Thus
ℓcau​(θ,m)={m−1,m−2,​m even,m odd,​
and the ratio tends to 1. 
The analytic proof is complete:


The effective contraction calculation establishes the carry-collapse mechanism for m≥6.


The suffix-sum identity
Rt​=et​+et+2​+2Rt+1​−Rt+2​+Rt+3​
gives deterministic backward propagation.


The three-, four-, and five-digit terminal equations are exhaustively solved in the bounded alphabet {−1,0,1}.


The cases m=4,5 are separately exhausted exactly.  


As an independent check, I reconstructed the collision graph rather than relying on the supplied verifier. For every 4≤m≤10, the penultimate obstruction set was exactly {±Em​}, and the next set was empty. I also independently enumerated the bounded terminal equations; their solution lists are exactly those used in the proof.
The precise sharpness statement is:

No theorem valid for every fixed system in the A1 class can replace OU​(m) by o(m).

That is genuine fixed-system sharpness, stronger than a varying-base example. It does not claim that the computed CU​ is numerically optimal or that coefficient 1 is universal across all systems. The manuscript states the correct growth-order conclusion. 
The computational batteries are therefore properly relegated to regression testing; the manuscript itself explicitly says they are not certificates for the parameter-uniform theorem. 
4. Is the result new?
My literature-audit conclusion
After searches under the manuscript’s terminology and the closest established terminology—decoder window, look-ahead, synchronization delay, bounded-zero automata, normalization transducers, pair graphs, inverse local codes, Pisot carry propagation—I found no prior theorem covering
ΦU,m​ injective⟹ℓcau​(U,m)≤CU​m
for these cyclic language-rank folds, nor an equivalent theorem giving a linear bound on the length of overlapping bounded-zero strips.
I would therefore sign off on a cautious novelty statement such as:

“To the authors’ knowledge, this is the first aperture-linear inverse-depth bound for cyclic language-rank recodings over fixed Pisot numeration systems.”

I would not write an unqualified “first linear decoder bound,” because several titles in the older literature sound dangerously close.
Close precedents that do not subsume A1
Finite Pisot normalization. Frougny proved finite-automaton realizability of normalization and addition in Pisot bases, and Berend–Frougny characterized finite-automaton normalization in real bases by the Pisot property. These establish finite-state computability, not an aperture-linear optimal inverse window for a prescribed cyclic rank-modulo-um​ map. Springer Link+1
Zero-representation automata. The regularity and finiteness of bounded zero automata are classical or established in later generalizations. They tell one that zero representations can be recognized by a finite automaton; they do not bound the survival time of the manuscript’s overlapping congruence strips by CU​m. arXiv+2ORBi+2
The recent zero-preservation paper. Carton–Sudbery–Yassawi prove the equivalence between preservation of zeros and Condition F and use Pisot contraction to obtain divisibility information for sufficiently shifted bounded zero representations. This is the closest methodological precedent I found. It does not formulate the cyclic rank map, its collision graph, a future-only inverse, or an O(m) survival-depth theorem. arXiv+1
Classical pair/fiber graphs. Reachable-cycle injectivity tests and the existence of finite inverse windows for injective local maps are classical. The manuscript acknowledges this correctly. The generic difference-graph count gives the exponential estimate
(2dU​+1)m−1−1,
not the new aperture-linear estimate.  
Ashley’s “linear bound” papers. These are the most likely source of a mistaken priority objection. Ashley’s bounds concern constructions of finite-state encoders into constrained systems and are linear in the number of states of a presenting graph, together with memory and anticipation parameters. The later paper likewise constructs encoders with look-ahead linear in the size of a smallest presentation. They do not say that an arbitrary prescribed injective sliding code has inverse depth linear in its aperture. In your setting the natural pair/difference presentations have exponentially many aperture-m states, so a state-count-linear theorem would still be exponential in m. IBM Research+1
Bounded-delay synchronization. Frougny–Sakarovitch show that a subsequential automaton already known to have bounded delay can be replaced by an online form after a fixed transient. That is a structural conversion theorem under a bounded-delay hypothesis, not a quantitative deduction of O(m) delay from injectivity. Lip6
The novelty therefore lies in the particular quantitative combination:
exact rank-difference quotient+ Pisot conjugate separation+ adjacent-carry collapse+ finite small-aperture patching.
I recommend adding a dedicated paragraph—rather than scattering the distinctions across the introduction—explicitly comparing A1 with Frougny, Carton–Sudbery–Yassawi, Ashley, and bounded-delay synchronization. Given the manuscript’s previous priority problems, leaving Ashley’s title unanswered would be unnecessarily risky.
No literature search can prove absolute nonexistence, but on the evidence I found, this is not a rediscovery of an existing linear-delay theorem.
5. Does Theorem A still raise the paper’s tier?
Yes. I uphold that judgment on the actual proof, not merely on the earlier commitment.
The reason is now concrete. The paper no longer consists only of exact analyses of specially chosen cyclic folds. It contains:


a fixed-system structural theorem over a recognized Pisot-numeration class;


an effective complexity bound that replaces exponential graph counting by algebraic contraction;


a sharp lower bound in one fixed cubic system, ruling out o(m);


exact quadratic and cubic calculations explaining how the general mechanism manifests in arithmetic examples.


That is the package I had in mind when identifying Theorem A as tier-raising.
The limitation remains important: this is still a theorem about the manuscript’s cyclic language-rank recoding, not a theorem about numerical β-normalization in general, arbitrary β-transformations, or all Pisot symbolic dynamics. The manuscript mostly observes that distinction correctly. Theorem A raises the paper because it is structural across U, not because it turns the fold into classical β-normalization.
Venue assessment
My honest assessment after the audit is:


ETDS is now a strong and natural target, rather than merely a hopeful one.


TAMS is now a defensible ambitious first submission. I would not call acceptance likely or routine: a TAMS referee may still regard the map as specialized and may object to the breadth and length of the surrounding package. But a reject-on-sight verdict is no longer justified.


DCDS-A would now be conservative rather than aspirational.


The result does not move the paper into Annals/JAMS/Inventiones territory.


For a TAMS submission, I would make four changes before sending it:


Remove Condition F from A1 using the finite carry interval argument above, or explicitly explain why the authors decline the stronger theorem.


Replace “standard Pisot numeration systems” by technically exact language.


Add the concentrated priority comparison with Ashley, Frougny, zero automata, and Carton–Sudbery–Yassawi.


Move A1–A3 even more visibly to the front and shorten material that obscures the fixed-system theorem.


Final referee-style ruling: A1–A3 are proved; A2–A3 furnish genuine fixed-system sharpness; the quantified class is substantial and classical rather than bespoke; novelty is defensible after a targeted literature audit; and the addition does raise the manuscript by one real publication tier. The main required correction is strengthening and reframing A1, not repairing a failed proof.