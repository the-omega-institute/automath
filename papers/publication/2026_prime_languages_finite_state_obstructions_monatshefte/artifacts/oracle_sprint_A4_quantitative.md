Definite judgment
Yes. Theorem 3.2 can be made quantitative in the effective-computability sense. Given effective recurrence data and the finite paired-loop covers—or context-free grammars from which those covers are constructed—one can compute:


an upper bound for ∣X∣; and


with a slightly fuller use of Mignotte’s effective argument, an upper bound for the largest element of X.


No step in the architecture is inherently ineffective. The present manuscript stops at qualitative finiteness because it imports only the finiteness conclusion of Mignotte and states the paired-loop classification only qualitatively. The missing strength is therefore unwritten effectivity bookkeeping, not a context-free obstruction.
There is, however, an important distinction:

An algorithmically computable bound from the complete grammar, loop, and recurrence data is reachable.
A clean closed formula in a few size parameters, comparable to Albayrak–Bell’s formula in the numbers of automaton states, is not cheaply available.

That distinction should replace the present unqualified statement that the theorem “supplies no quantitative bound.” The manuscript itself describes exactly the right finite architecture—paired-loop cover, residue recurrences, then common values—and already records that Mignotte’s proof is effective. 
1. The effective bound and where it comes from
Write the two effective paired-loop decompositions as
RepU​(X)=EU​∪i=1⋃a​{ui​vin​wi​xin​yi​:n≥0},
RepV​(X)=EV​∪j=1⋃b​{uj′​(vj′​)mwj′​(xj′​)myj′​:m≥0},
where EU​,EV​ include the zero-pump loops and any finite initial portions separated off to cross recurrence transients.
For every nonconstant U-loop, make Lemma 3.1 effective. It produces:
Ai,r​(t)=valU​(ui​vihi​t+r​wi​xihi​t+r​yi​),0≤r<hi​,
after a computable index shift if necessary. Each Ai,r​ is an integer linear recurrence with a unique positive dominant root
Λi​=αhi​Di​,Di​=∣vi​∣+∣xi​∣>0.
Likewise one obtains recurrences Bj,s​(u) with unique dominant roots
Kj​=βkj​Dj′​.
This is not merely an existence-level reconstruction: the manuscript’s proof gives the actual powering matrix Mvi​T​⊗Mxi​​, obtains the scalar recurrence by Cayley–Hamilton, consolidates the peripheral eigenvalues after an arithmetic restriction, and proves that the dominant spectral coefficient does not vanish.  The greedy length squeeze is used only to certify that the computable dominant coefficient is positive rather than cancelled. 
Now fix one pair A=Ai,r​, B=Bj,s​, with expansions
A(t)=cΛt+O(ρt),B(u)=dKu+O(σu),
where c,d>0, ρ<Λ, and σ<K. Because Λ and K are positive powers of multiplicatively independent α,β, they are themselves multiplicatively independent.
Mignotte’s effective theorem gives a computable threshold MA,B​ such that an equality A(t)=B(u) with t≥MA,B​ forces equality of the dominant terms,
cΛt=dKu.
Apply the same theorem with the two sequences interchanged and obtain NA,B​ for the u-index. The effective-threshold formulation of Mignotte is explicitly recorded in later recurrence literature: beyond a computable threshold, equality of the full terms forces equality of their leading terms. 个人数学网站 Other recurrence work describes Mignotte’s result as providing an effective upper bound for common-value indices under the unique-dominant-root and independence hypotheses. 莱顿大学数学出版社
There can be at most one solution of
cΛt=dKu:
two different solutions would give
Λt1​−t2​=Ku1​−u2​,
contradicting multiplicative independence. Consequently,
#{(t,u):A(t)=B(u)}≤MA,B​NA,B​+1.
Therefore a completely valid effective global bound is
∣X∣≤∣E∣+i,r,j,s∑​(Mi,r,j,s​Ni,r,j,s​+1),​
where E is the finite set represented by the discarded constant loops and pretransient pieces. This overcounts repeated values, which is harmless for an upper bound.
Thus an effective cardinality bound follows particularly cleanly. It requires no search for the possible exceptional large solution of the dominant-term equation.
Bounding the largest element
A largest-element bound takes one additional step.
All solutions inside the finite rectangles
0≤t<Mi,r,j,s​,0≤u<Ni,r,j,s​
can be evaluated directly. Outside such a rectangle there is at most one candidate, governed by
ci,r​Λit​=dj,s​Kju​.
Using Mignotte in its effective index-bound form bounds that pair as well. One can then evaluate all terms up to the resulting index bounds and take their maximum. Hence an integer B satisfying
X⊆[1,B]
is effectively computable.
The cardinality bound is therefore the easier and cleaner theorem to state. The largest-element bound is also reachable, but it forces you to expose more of Mignotte’s effective Diophantine machinery.
A necessary qualification is that the bound depends on the full effective data, not merely on α,β and the total pumped lengths. It uses:


recurrence coefficients, initial values, and recurrence thresholds;


the actual fixed and pumped words, not only their lengths;


the resulting matrices and Binet coefficients;


algebraic degrees, heights, spectral gaps, and Mignotte constants.


Long fixed prefixes alone can move the common values arbitrarily far out, so no bound on the largest element could reasonably depend only on the dominant roots and Di​,Dj′​.
2. Exact audit of effectivity at each step
Paired-loop decomposition: effective, not an obstruction
If finite paired-loop covers are supplied, this step is already complete.
If the inputs are context-free grammars, the required refinement is also known: the constructive slender-language result effectively converts a given slender context-free language into a finite union of paired loops. 科学直通车 Thus the Latteux–Thierrin–Ilie step is not inherently ineffective. Your present Section 3 simply invokes the qualitative finite-union formulation. 
The cost is that the number and lengths of the resulting loops may be enormous and the dependence on grammar size is not organized into a clean formula. That is a complexity and exposition problem, not a computability failure.
Residue-class restriction: effective
The residue period hi​ is computable from the minimal polynomial of α:


compute the conjugates on the spectral circle;


test their quotients for being roots of unity;


compute their finite orders;


take a common multiple.


The recurrence transient and the number of initial loop iterations needed to move every variable block into the stationary recurrence range are also explicit from the recurrence threshold and block lengths.
There is no ineffectivity here.
Dominant-root transfer in Lemma 3.1: effective after bookkeeping
The proof already uses explicit integral matrices and finite-dimensional tensor products. From those matrices one can compute:


a characteristic recurrence by Cayley–Hamilton;


all characteristic roots as algebraic numbers;


the unique dominant root after the residue restriction;


the dominant spectral-projection coefficient;


a spectral-gap estimate;


an index after which the dominant term controls the error.


The current proof states the lower and upper asymptotic comparison qualitatively,
0<liminfΛtZr​(t)​≤limsupΛtZr​(t)​<∞,
and uses it to rule out cancellation.  For a quantitative corollary, that paragraph should be upgraded to an effective transfer package recording a computable shift, recurrence, dominant coefficient, and error bound. Nothing new has to be proved conceptually.
Mignotte: effective, but the constants are the expensive part
The manuscript correctly says that Mignotte’s common-value proof is effective and then explicitly says that only its finiteness conclusion is being used.  This is the point at which the current proof deliberately throws away the quantitative information.
Mignotte is therefore not the obstruction. It is the source of the effective bound. But reconstructing and presenting its constants in terms of your matrices, algebraic heights, coefficients, and spectral gaps is where the resulting formula becomes extremely large and unattractive.
So the exact diagnosis is:

Effectivity does not fail. The manuscript has not propagated effective constants through the constructive paired-loop decomposition, Lemma 3.1, and Mignotte’s threshold.

3. Probability, cost, gain, and venue
Success probability
My probability that you can prove a correct effective cardinality bound from the supplied paired-loop and recurrence data is:
0.94​.
That estimate is not higher only because the precise hypotheses and output format of the Mignotte result must be quoted and matched carefully, and because all finite prefixes and eventual-recurrence shifts must be handled without a hidden uniformity assumption.
For a clean Albayrak–Bell-style closed formula in compact grammar-size parameters, my probability would be only about 0.55. The issue there is not truth but whether a usable formula can be extracted without doing a disproportionate reconstruction of two old effective arguments.
Amount of work
There are three different products:
A one-paragraph remark.
You can say that an effective version follows from the constructive paired-loop theorem, the effective matrix construction in Lemma 3.1, and Mignotte. This is easy, but it does not responsibly replace Theorem 3.2 by a quantitative theorem because it gives no defined input model or bound.
A proper effective theorem.
This is a short section, approximately two to four pages. It should contain:


an effective-presentation hypothesis;


an effective version of Lemma 3.1;


the Mpq​Npq​+1 pair bound;


treatment of constant loops and finite transients;


a corollary bounding ∣X∣, and optionally maxX.


That is the version I recommend.
A displayed closed formula comparable to Albayrak–Bell.
That is a separate project. It would require explicit size bounds for the grammar-to-loop construction and detailed height estimates through the tensor matrices and Mignotte’s Baker-type constants.
Albayrak–Bell do substantially more than merely assert computability: their Theorem 1.1 gives an automaton-data bound, and they provide a closed expression in the bases, dimension, and numbers of minimal-automaton states. They also distinguish this cardinality estimate from actually computing the intersection. arXiv Your route can be effective, but it will not naturally have that finite-state cleanliness.
What it would buy
A proper effective corollary would buy three real things:


It would remove the impression that context-freeness has introduced an intrinsic ineffectivity.


It would sharpen the comparison with Albayrak–Bell: their advantage would correctly be described as a clean uniform state-count formula, not effectivity versus noneffectivity.


It would make the proof architecture look more complete, because every step is finite and constructive.


It would not change the venue judgment. Monatshefte für Mathematik remains the right target. The effective refinement is a worthwhile completion of the theorem, but the deep input remains Mignotte and the principal novelty remains the nonregular slender-context-free transfer already identified in the manuscript. The present proof correctly locates that novelty in the passage from genuinely nonregular paired loops to weak-Perron recurrence sequences. 
Plainly: do not undertake a separate project to produce a polished closed-form bound in the hope of raising the venue. It will not do so. A short effective section is worth adding; a large quantitative reconstruction is not.
4. What the paper should say
Because the bound is reachable, the paper should not say that the context-free case intrinsically resists quantitative treatment. That would overstate the asymmetry and would probably be false.
The accurate limitation is:

The proof is effective from complete grammar, paired-loop, and recurrence data, but the paper does not extract a closed uniform bound in compact grammar-size parameters comparable to the automaton-state bound of Albayrak–Bell.

A suitable replacement for the current disclaimer would be:

Effective refinement. Suppose, in addition, that the two numeration sequences are supplied by effective integral recurrence data and that the two slender context-free representation languages are supplied by context-free grammars, or by finite paired-loop decompositions. Then an upper bound for ∣X∣, and indeed an upper bound for the largest element of X, is effectively computable from these data. The constructive slender-language classification produces the finite paired-loop covers; the matrix construction in Lemma 3.1 effectively produces the finitely many residue recurrence sequences with unique positive dominant roots; and Mignotte’s effective common-value theorem bounds the intersections of every pair. We do not extract a closed formula in terms of grammar size, recurrence heights, and block lengths. Thus the distinction from the quantitative theorem of Albayrak–Bell is one of explicit uniform bounds, not one of effectivity.

I would also change the sentence in Remark 3.3 saying that the present theorem “supplies no quantitative bound” to:

“The present argument does not supply a displayed uniform bound in compact input-size parameters; an effective bound can nevertheless be obtained by retaining the constructive constants in the paired-loop decomposition, Lemma 3.1, and Mignotte’s theorem.”

That is the honest final position: the asymmetry is not intrinsic, an effective version is within reach, a clean Albayrak–Bell-style formula is expensive, and the venue remains Monatshefte either way.
