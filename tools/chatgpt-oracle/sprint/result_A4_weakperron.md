Referee recommendation
Major revision; if the journal does not use that category, reject with an invitation to resubmit.
I do not find a fatal mathematical error in Theorem 2.25. After reconstructing the omitted details, I believe the weak-Perron classification is correct under the stated hypotheses. I also find the removal of (U3) complete for the general recurrent-numeration theorem chain.
I would nevertheless not recommend acceptance of the present version for two reasons:


The proof of the principal new specialization is too compressed at exactly its highest-risk point: the peripheral-spectrum residue analysis.


The priority discussion materially omits Charlier–Kreczman’s December 2025 paper on numeration systems without a dominant root. That paper does not appear to contain the MCFL prime-support classification, but it substantially overlaps the asymptotic mechanism currently presented as the new technical step.


The manuscript’s basic framing is now accurate: unique representations and weak MCFL pumping produce one synchronized orbit, not global language control.  The abstract and conclusion also correctly retain the one-orbit structural ceiling. 
1. Correctness of the weak-Perron classification
Overall judgment
Theorem 2.25 is correct in substance. I can verify all five equivalences once several standard but currently implicit arguments are written out. The theorem is stated at lines 1162–1200, and the delicate implication (ii)⇒(iii) occupies lines 1201–1259.  
I found no counterexample under the exact hypotheses:


U0​=1;


strictly increasing integer place values;


bounded successive quotients;


ordinary greedy positional representations;


minimal tail recurrence polynomial equal to the irreducible minimal polynomial of a weak Perron number.


The proof is not yet referee-proof in exposition, however. The following is the fully expanded audit.
A. Choice of the peripheral period h
From the conjugate-modulus definition of weak Perron, one may choose h≥1 such that
ρ=βh
is a Perron number. Equivalently, every peripheral conjugate has the form
γ=βζγ​,ζγh​=1,
and hence
γh=βh=ρ.
This fact is classical. Brunotte explicitly proves the equivalence between the “almost Perron” condition ∣γ∣≤β and the existence of a positive power that is Perron; his discussion also identifies the root-of-unity structure of the peripheral conjugates. SciSpace
The manuscript’s invocation of “Perron–Frobenius periodicity for irreducible diagonal blocks” is plausible but too abbreviated. In particular, the reader should not have to infer why a conjugate of equal modulus must collapse to βh, rather than merely remain somewhere on the peripheral circle.
Required resolution: insert a lemma stating explicitly:

There exists h≥1 such that ρ=βh is Perron and, for every conjugate γ of β, either γh=ρ or ∣γ∣h<ρ.

Cite Lind and, preferably, Brunotte directly.
B. Tail expansion and Galois covariance of the coefficients
Let Jr​ be a threshold from which the minimal recurrence holds. Since μU​ is irreducible over Q, it is separable. Thus, over a splitting field K, there are unique coefficients Aγ​∈K such that
Un​=γ∑​Aγ​γn(n≥Jr​),
where γ runs over all conjugates of β.
The uniqueness can be justified from any d=degμU​ consecutive tail values and the nonsingularity of the associated Vandermonde matrix. If σ∈Gal(K/Q), rationality of every Un​ gives a second expansion
Un​=γ∑​σ(Aγ​)σ(γ)n.
Uniqueness therefore yields
Aσ(γ)​=σ(Aγ​).
Consequently, if Aβ​=0, transitivity of the Galois action on the roots of an irreducible polynomial forces every Aγ​=0, contradicting the positive, nonzero tail of U. Thus Aβ​=0; indeed, every Aγ​=0.
The manuscript states this correctly but compresses uniqueness, extension of embeddings to the splitting field, and transitivity into one sentence. 
Required resolution: write the displayed covariance identity Aσ(γ)​=σ(Aγ​) and state explicitly that an embedding of Q(β) into the splitting field extends to a splitting-field automorphism.
C. Residue asymptotics and thresholds
For each r∈{0,…,h−1}, put
Nr​=max(0,⌈hJr​−r​⌉).
Then, for n≥Nr​,
Uhn+r​=Cr​ρn+o(ρn),Cr​=∣γ∣=β∑​Aγ​γr.
Because the smaller conjugates have modulus strictly less than β, their contributions are o(ρn). No polynomial factors occur because μU​ is separable.
Each Cr​ is real: either use complex-conjugate pairing, or note directly that
Cr​=n→∞lim​ρnUhn+r​​.
Since Uhn+r​>0, this gives
Cr​≥0.
The displayed asymptotics in the manuscript are correct, but the residue-dependent thresholds and the reality of Cr​ should be explicit. 
D. Vandermonde nonvanishing
Let γ1​,…,γs​ be the peripheral conjugates and write
γj​=βζj​,ζjh​=1.
The ζj​ are distinct and s≤h. If every Cr​ vanished, then
0=β−rCr​=j=1∑s​Aγj​​ζjr​(0≤r<h).
The h×s Fourier–Vandermonde matrix
(ζjr​)0≤r<h1≤j≤s​​
has full column rank. Hence all peripheral coefficients vanish, including Aβ​, a contradiction.
This validates the manuscript’s assertion that at least one Cr​ is nonzero. But “Vandermonde independence” by itself is too compressed: the proof uses the additional observation that the peripheral phases are distinct h-th roots of unity and therefore number at most h.
Required resolution: include the preceding three-line matrix argument.
E. Cyclic propagation of positivity
Suppose Cr​>0.
For r<h−1, if Cr+1​=0, divide
Uhn+r​<Uhn+r+1​
by ρn. The two sides tend respectively to Cr​>0 and 0, a contradiction. Thus Cr+1​>0.
At the wraparound one has
Uhn+h−1​<Uh(n+1)​.
After division by ρn, the limits are
Ch−1​andρC0​,
not C0​. If C0​=0, this again contradicts Ch−1​>0. Therefore positivity propagates cyclically and every Cr​>0.
The manuscript’s “similarly” is logically valid, but it suppresses the factor ρ. 
Required resolution: display
ρ−nUh(n+1)​⟶ρC0​.
This is a small omission, but it occurs at the most delicate point and should not be left implicit.
F. Global root growth
For N=hn+r,
UN​=Cr​ρn(1+o(1)),Cr​>0.
Therefore
NlogUN​​=hn+rnlogρ+O(1)​⟶hlogρ​=logβ,
so
UN1/N​⟶β.
The conclusion in the manuscript is correct. It should, however, be accompanied by this one-line residue-to-global calculation.
G. The greedy-length squeeze
If a canonical greedy word has length m, then its value lies in
[Um−1​,Um​).
Thus, for a synchronized geometric scheme with
∣W(t)∣=L+Dt,D>0,valU​(W(t))=cbt,
one has
UL+Dt−1​≤cbt<UL+Dt​.
The root limit gives
UL+Dt1/t​=(UL+Dt1/(L+Dt)​)(L+Dt)/t⟶βD,
and the lower bound has the same limit. Hence
b=βD.
This step is correct. It does, however, depend on the standard greedy interval property, not merely on “strict increase plus bounded quotients.” The phrase “standard greedy linear numeration basis” carries that information, but the paper should state it as a lemma when first defining this subclass. 
H. The algebraic equivalences
The remaining implications are correct:


βm=B if and only if the minimal polynomial μU​ divides Xm−B.


μU​∣Xm−B if and only if Xm−B annihilates the tail, equivalently
Un+m​=BUn​
eventually.


Eventual scalar periodicity gives the greedy ray
0n0​+mt1,valU​(0n0​+mt1)=Un0​​Bt.


The only exposition issue is that “minimal tail polynomial” should be formally identified as the monic generator of the ideal of rational polynomials annihilating some tail. With that definition, the divisibility assertions are immediate. 
I. Audit of the upstream arithmetic theorem
I also checked the dependence on Theorem 2.16 and Lemma 2.15. I find that chain sound:


The synchronized orbit is a linear recurrence by the tensor-product construction.


Local return times produce an arithmetic subsequence supported on a fixed finite set of primes.


Root-of-unity classes are separated into nondegenerate residue subsequences.


Evertse excludes two or more characteristic roots.


The Hankel-rank argument forces the sole characteristic root to be rational.


Schur’s theorem eliminates a nonconstant polynomial coefficient.


Positivity, integrality and injectivity force an integer ratio b≥2.


The manuscript quotes Evertse in the needed uniform quotient form. Evertse’s Theorem 3 indeed says that, for a nondegenerate recurrence with at least two characteristic roots, the largest prime-ideal norm occurring in ur​/us​ tends to infinity uniformly as r→∞, r>s, us​=0. Numdam The manuscript’s formulation and finite-support contradiction are faithful to that result. 
Bottom line on correctness: I find no fatal gap. I would require the proof expansion above before publication because, in its present compressed form, the principal implication is too easy to misread and too difficult to audit.
2. Nonemptiness and the alternating-radix family
Judgment
Yes, the positive class is substantively nonempty. The pq​ family is not merely a single numerical curiosity.
It supplies:


an infinite parametric family;


genuinely nonintegral weak Perron roots;


an equal-modulus conjugate, so strict Perron dominance genuinely fails;


regular canonical greedy languages;


exact eventual scalar periodicity;


an explicit regular ray realizing bounded support.


The construction and its two numerical instances are correctly verified in the manuscript. 
Moreover, Theorem 2.25 itself says that every positive example must exhibit eventual scalar periodicity. It would therefore be unreasonable to reject the family merely because its positive behavior is visibly built from a periodic radix structure: that structure is not accidental but is exactly what the theorem classifies.
There is nevertheless a presentational limitation. The submitted examples realize only period h=2, with peripheral spectrum {B​,−B​}. They do not visibly exercise:


more than two peripheral conjugates;


nonreal peripheral conjugates;


the full Fourier–Vandermonde residue argument.


A much better illustrative example is obtained from repeating radices 2,3,5:
U3t​=30t,U3t+1​=2⋅30t,U3t+2​=6⋅30t.
Then
Un+3​=30Un​,
the greedy digit bounds repeat as
{0,1},{0,1,2},{0,1,2,3,4},
and the language is regular by tracking position modulo 3. Since X3−30 is Eisenstein, it is the minimal polynomial, and
β=330​
has three equal-modulus conjugates, two of them nonreal. The ray
{03t1:t≥0}
has values 30t.
More generally, for periodic radices r0​,…,rh−1​≥2, put
B=j=0∏h−1​rj​,Rj​=i<j∏​ri​,Uht+j​=Rj​Bt.
When Xh−B is irreducible, this gives a degree-h weak-Perron positive family.
Alternate-base constructions themselves are established numeration-theoretic objects, not a new architecture; Charlier–Kreczman explicitly place them in the prior alternate-base literature. arXiv
Required resolution: the period-3 example is not necessary for correctness, but I strongly recommend adding it. It would demonstrate that the theorem handles the genuinely complex peripheral-spectrum case rather than only the square-root prototype. It should be labeled an illustration of the theorem, not a novel alternate-base construction.
3. Removal of (U3)
Judgment
The removal is complete for the ambient theorem chain as submitted.
The revised Theorem 2.7 now obtains:


pairwise distinct words because their lengths increase by the positive pumped length; and


pairwise distinct values because valU​:RU​→N≥1​ is injective.


No comparison of values of different word lengths occurs there.  The weak pumping lemma used has exactly the fixed synchronized form claimed, while its quantifier is only the existence of one pumpable family. arXiv+1 The fixed-left-quotient construction is also justified by the standard closure of k-MCFLs under regular intersection, homomorphism and inverse homomorphism. arXiv
I checked each downstream use identified in the manuscript’s audit:


Theorem 2.9: only needs a return point distinct from the original point.


Lemma 2.15 and Theorem 2.16: need a pairwise-distinct positive integer recurrence, not monotonicity.


Theorem 2.20: among infinitely many distinct positive values in a return class, some exceed the current value because only finitely many positive integers do not.


Theorem 2.21: the same finite-below-current-value argument supplies every increasing choice.


These are exactly the uses listed by the authors.  The revised quotient-chain and divisibility-tree proofs implement that argument correctly.  
Two length/value comparisons remain elsewhere, but neither is a hidden return of (U3):


The preliminary Zeckendorf theorem uses the specific Zeckendorf interval ordering.


Theorem 2.25 uses the specific greedy interval
[Um−1​,Um​).


These are subclass properties, not assumptions on every canonical eventually recurrent numeration system.
Strict increase of the place values in (U1) is likewise distinct from deleted (U3). Its use in propagating the positivity of the Cr​ is legitimate and essential.
There are two minor revisions I would request:


Replace “the only place where strict ordering by canonical length was used” by “the only place in the general recurrent-numeration theorem chain.” Otherwise the nearby Zeckendorf and standard-greedy uses can make the sentence appear literally false.


In Theorem 2.7, replace the informal “delete the finitely many words” by
L∩A≥J,
noting that this remains a k-MCFL by regular intersection.


Neither point affects the result.
4. Priority audit
Full classification
I did not locate an existing theorem giving the complete equivalence
​bounded outside-prime support on an infinite MCFL⟺synchronized geometric scheme⟺βm∈Z⟺μU​∣Xm−B⟺Un+m​=BUn​ eventually.​
In particular, the searches did not reveal a prior result joining MCFL pumping, fixed-prime-support recurrences, weak Perron spectra and greedy numeration in this five-way form. My present judgment is therefore that the classification as an interface theorem is genuinely new.
That judgment must be qualified sharply: several ingredients, including one now presented as the new technical step, are already in or very near the literature.
Materially omitted paper: Charlier–Kreczman
Émilie Charlier and Savinien Kreczman’s December 2025 preprint, Numeration systems without a dominant root and regularity, gives a full characterization of positional systems with regular numeration language through alternate bases. arXiv
More importantly here:


Proposition 10 derives residue-class quotient limits from the peripheral eigenvalues of an increasing linear numeration sequence. arXiv


Remark 12 states, for an arbitrary linear recurrence, that if its dominating eigenvalues have the same p-th power, then the converse quotient-limit conclusion holds under eventual increase of ∣Un​∣. arXiv


In the present theorem, μU​ is separable, so all peripheral roots have equal multiplicity, and weak-Perron periodicity gives precisely the equality of their h-th powers. Strict increase supplies the eventual-increase hypothesis. Charlier–Kreczman therefore provide, in essentially equivalent form, the growth mechanism
Un−h​Un​​⟶βh,
from which Un1/n​→β follows.
Their paper does not appear to discuss MCFLs, prime support, synchronized schemes or the five-way radical classification. Thus it does not destroy Theorem 2.25. But it prevents the manuscript from safely presenting the residue-growth conclusion as an unanticipated new technical result.
Required resolution:


cite Charlier–Kreczman prominently;


compare their Proposition 10 and Remark 12 with the present residue argument;


describe the current proof as a self-contained coefficient-level specialization adapted to the theorem, unless the authors can identify a genuinely sharper statement;


remove any implication that equal-modulus residue growth for increasing linear numeration sequences is first established here.


Other classical or previously established components
The paper should separate the following clearly:


The equivalence between the conjugate-modulus definition of weak Perron and the existence of a Perron power is classical; Brunotte is a direct citation. SciSpace


The weak MCFL pumping family is Seki–Matsumura–Fujii–Kasami’s theorem. The recent Duncan–Elder–Frenkel–Lyu paper confirms both its exact synchronized form and its one-family limitation. arXiv+1


Evertse’s quotient theorem is classical and is used correctly. Numdam


The implications
βm=B⟺μU​∣Xm−B⟺eventual scalar periodicity
are elementary recurrence algebra, not independently novel.


Alternating or periodic radix systems belong to established alternate-base numeration theory. arXiv


The defensible novelty claim is narrower and, in my view, still substantial:

The new contribution is the passage from bounded outside-prime support on an arbitrary infinite finite-fan-out MCFL to an exact synchronized geometric ray, and the resulting classification of that language-theoretic phenomenon in weak-Perron greedy systems.

That claim is consistent with the manuscript’s use of Evertse in Theorem 2.16. 
Given the project’s history of priority omissions, the absence of Charlier–Kreczman is not a cosmetic bibliographic defect. It is the strongest immediate reason not to accept the current version.
5. Resulting tier
Mathematical effect of the revision
The completed theorem does raise the paper.
The weak-Perron extension is a clean endpoint theorem with a genuine equal-modulus positive regime, rather than a merely formal weakening of “Perron.” The removal of (U3) also makes the ambient theorem chain materially less artificial and confirms that the mechanism uses injectivity, not an accidental length-order hypothesis.
But it does not remove the structural ceiling. The manuscript itself correctly concedes that the method produces only one synchronized orbit and controls neither every sufficiently long word, the whole canonical language, nor simultaneous representations in two systems.  That remains the decisive obstacle to a higher general-theory tier.
The priority overlap with Charlier–Kreczman also reduces the realized impact of the weak-Perron addition: the five-way MCFL classification remains valuable, but the peripheral-growth lemma is not an entirely new technical phenomenon. On the scale used in the earlier discussion, I would now assign the completed addition about 6.5–7/10 tier impact, rather than the full prospective 7.5/10.
Journal range
After the required revision, I would regard the paper as a strong upper-specialized theoretical-computer-science paper, with the following range:


Acta Informatica


Theory of Computing Systems


Theoretical Computer Science


Information and Computation as an ambitious but credible submission


These journals explicitly cover formal-language theory or broad theoretical computer science. Elsevier商店+3Springer Link+3Springer Link+3
I would not regard the current package as competitive for a substantially higher general-theory venue such as JCSS or SICOMP. At that level I would recommend rejection on significance, not correctness: the theorem classifies the exceptional behavior of one extracted orbit, while leaving the global-language quantifiers untouched.
A number-theory journal is possible, but less natural. The deepest arithmetic input is classical, and the new contribution is principally the formal-language/numeration interface.
Final disposition
For an appropriately specialized journal:

Major revision. The main theorem appears correct and publishable, but acceptance should be conditional on a complete peripheral-spectrum proof and a rewritten priority discussion incorporating Charlier–Kreczman and Brunotte.

For a higher generalist theory journal:

Reject. The revised theorem improves the paper and may move it across a nearby editorial boundary, but it does not produce a full-tier jump because the one-synchronized-orbit ceiling remains.

The strongest curable objection is the present priority and exposition failure. The strongest intrinsic objection is the unchanged one-orbit quantifier.