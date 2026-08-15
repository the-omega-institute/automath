Overall verdict
The two principal objections from the preceding round are now resolved.
I find no remaining mathematical gap in the expanded peripheral-spectrum argument, and the manuscript now gives a materially accurate account of the Charlier–Kreczman overlap. The overlap does reduce the independent weight of the weak-Perron specialization, but it does not collapse the paper’s central MCFL/prime-support theorem chain. My referee disposition would now be minor revision rather than rejection.
1. Peripheral-spectrum residue analysis
The rewritten argument is complete and correct at referee standard.
The proof now closes each point that was previously compressed:


Because the minimal tail polynomial is the irreducible minimal polynomial of β, it is separable. The tail therefore has a unique pure exponential expansion
Un​=γ∑​Aγ​γn
with no polynomial factors. The Vandermonde justification is explicit. The Galois covariance
Aσ(γ)​=σ(Aγ​)
is also correctly obtained from uniqueness, and it correctly implies Aβ​=0, indeed Aγ​=0 for every conjugate. 


The residue thresholds
Nr​=max{0,⌈hJr​−r​⌉}
correctly ensure that the tail expansion applies to every Uhn+r​ under consideration. The peripheral terms produce Cr​ρn, while the nonperipheral terms are uniformly O(θn) for some θ<ρ. The special case in which no nonperipheral roots exist is also explicitly handled rather than hidden in the O-notation. 


The proof that Cr​ is real and nonnegative is valid because
Cr​=n→∞lim​ρ−nUhn+r​,
and the place values are positive. The Fourier–Vandermonde argument correctly proves that not all Cr​ vanish: the peripheral phases are distinct h-th roots of unity, and the first s rows give an ordinary nonsingular Vandermonde matrix. 


The cyclic positivity argument is now properly closed. For adjacent residue classes, monotonicity gives Cr​≤Cr+1​; at the wraparound it gives Ch−1​≤ρC0​. Starting from one positive coefficient therefore propagates positivity through every residue class. There is no missing assumption of uniformity here: there are only finitely many residues, and “sufficiently large” may be chosen separately and then maximized. 


Once every Cr​>0, the passage from residue-wise asymptotics to the global limit
UN1/N​⟶β
is correct. The subsequent greedy-length squeeze
UL+Dt−1​≤cbt<UL+Dt​
then gives b=βD without any hidden length-order assumption beyond the standard greedy interval already stated. 


Thus, at the precise point that previously required reconstruction by the referee, the manuscript is now self-contained.
There is one wording refinement, not a proof defect. In the prior-work discussion, “separability gives equal peripheral multiplicities” could be made maximally exact by saying:

Since μU​ is the minimal shift-annihilator and is separable, all characteristic roots have multiplicity one; the covariance argument ensures that the peripheral roots actually occur.

That matches Charlier–Kreczman’s definition of the “dominating eigenvalues” more explicitly.
2. What Remark 12 actually implies
Your revised reading is correct.
Charlier–Kreczman define the dominating eigenvalues as those of maximal multiplicity among the eigenvalues of maximal modulus. Their Remark 12 states that, for p≥2, equality
α1p​=⋯=αkp​
among the p-th powers of the dominating eigenvalues, together with eventual increase of (∣Un​∣), implies the existence of
n→∞lim​Un−p​Un​​,
with that common power as its value. They separately recall the corresponding p=1 Kepler-limit criterion. arXiv
Under Theorem 2.25’s hypotheses:


the sequence’s minimal polynomial is μU​, which is irreducible and separable, so all its characteristic roots are simple;


the manuscript’s covariance argument ensures that the conjugate roots occur in the tail expansion;


the weak-Perron power theorem supplies h such that every peripheral conjugate γ satisfies
γh=βh=ρ;


Un​>0 and is strictly increasing, so (∣Un​∣) is certainly eventually increasing.


Consequently Remark 12 gives
Un−h​Un​​⟶ρ=βh.
For each residue rmodh, applying this to Uqh+r​ and taking logarithmic Cesàro averages gives
Uqh+r1/q​⟶ρ,Uqh+r1/(qh+r)​⟶ρ1/h=β.
The global root limit follows because there are finitely many residues. The greedy-length squeeze then yields b=βD.
So the conclusion needed for (ii)⇒(iii) is genuinely derivable from their result. Your manuscript now says exactly that: the quotient-limit conclusion is available from Charlier–Kreczman, while the retained proof gives the individual residue coefficients and their positivity explicitly.  
One nuance slightly favors you. In the preprint, the p≥2 converse appears as a statement in Remark 12, without a proof at that location. Thus you may legitimately claim that your manuscript supplies a detailed, self-contained coefficient-level proof in this specialization. What you may not claim is that the quotient-limit criterion or the conceptual root-growth mechanism is new. The revised manuscript observes that distinction correctly.
For exact attribution, I would make Remark 12 primary:

“The required lag-h quotient limit follows from Charlier–Kreczman, Remark 12; their Proposition 10 places the same phenomenon in the regular-language setting.”

Proposition 10 itself assumes regularity of the whole numeration language; it is not the logical source needed under your nonregular hypotheses. Remark 12 is.
3. Size of the surviving contribution
You have identified the surviving central contribution correctly:

bounded outside-prime support on an infinite finite-fan-out MCFL
⟺
existence of an exact synchronized geometric ray.

That is Theorem 2.16, and it is not a result about regularity of the whole greedy language. Its difficult direction combines the fixed synchronized MCFL orbit, congruence return, passage to a fixed finite prime set, recurrence closure, Evertse quotient rigidity, and elimination of the remaining polynomial factor by Schur. 
I found no further collapse of that theorem into Charlier–Kreczman. Their preprint’s problem is the regularity of the complete positional numeration language and its characterization through associated alternate real bases. arXiv Its Remark 12 supplies a recurrence-asymptotic criterion; it does not supply the quantifier passage
infinite MCFL sublanguage⟶one synchronized orbit⟶fixed-support recurrence⟶cbt.
The following parts of your paper also remain outside their framework:


the synchronized local-congruence orbit of Theorem 2.7;


the adic no-isolated-point and scattered-set obstruction;


the intrinsic deleted-prime Cantor–Bendixson calculation;


the nonunit escape dichotomy and MCF-immunity conclusions;


the Evertse-based geometric-ray characterization;


the unit-case arbitrarily deep quotient congruences and induced divisibility tree.


The manuscript itself presents these as the main theorem chain before reaching the weak-Perron specialization. 
There is, nevertheless, a necessary sizing correction inside Theorem 2.25 considered in isolation:


(i)⟺(ii) is the genuinely new central input from Theorem 2.16.


(ii)⇒(iii) uses the Charlier–Kreczman mechanism.


(iii)⟺(iv)⟺(v) consists of fairly direct minimal-polynomial and annihilator-ideal reformulations.


(v)⇒(ii) is the explicit one-nonzero-digit ray.


Accordingly, Theorem 2.25 remains a worthwhile exact classification, but its novelty is principally the synthesis of the MCFL/prime-support condition with the scalar-periodicity criterion, not five independently new equivalences. That is a reduction in the independent technical weight of Theorem 2.25, not a reduction of the entire paper to Charlier–Kreczman.
Your current framing largely reflects this already. I would only replace phrases such as “our exact geometric-ray and algebraic classification” by something like:

“our identification of the bounded-support MCFL condition with the resulting geometric-ray and scalar-periodicity conditions.”

This avoids suggesting that the algebraic criterion or quotient asymptotics themselves are newly discovered.
4. Priority discussion
The priority discussion is now sufficient in both placement and substance.
It appears:


in the main-results introduction, where the residue-growth mechanism is expressly called non-new and the paper’s contribution is separated from it; 


in a dedicated prior-work discussion that accurately describes Proposition 10, Remark 12, their applicability under your hypotheses, and the distinction between whole-language regularity and MCFL sublanguages; 


at the statement and proof of Theorem 2.25 itself. 


That is more than enough to prevent a reasonable reader from attributing the quotient-limit mechanism to you.
I do not regard a citation in the abstract as mandatory. The abstract states the entire equivalence involving bounded-support MCFLs, which is not Charlier–Kreczman’s theorem, and it already identifies Evertse as an imported rigidity input.  An abstract-level mention of Charlier–Kreczman would be maximally conservative, but its absence is no longer a priority defect.
The only substantive adjustment I recommend is to distinguish the roles of Proposition 10 and Remark 12 more sharply, as described above.
5. Venue judgment
For Monatshefte für Mathematik, the revised manuscript is now a credible submission. The journal expressly has a broad pure-mathematics remit and accommodates integration with neighboring disciplines, so the number-theory/formal-language interface is not formally outside its scope. Springer Link+1
My present referee-level judgment would be:
Minor revision; publishable thereafter.
I would no longer recommend rejection for either correctness or priority. The revised proof is checkable without reconstruction, and the paper no longer claims the borrowed asymptotic mechanism as its own.
The remaining editorial risk is not a hidden mathematical collapse. It is that an editor or referee may regard the paper as a broad synthesis whose individual ingredients are largely classical—weak MCFL pumping, finite-group recurrence, Broughan, Evertse, Schur, and now Charlier–Kreczman—and therefore ask whether the interface theorem is sufficiently central and conceptually strong. In my judgment, Theorem 2.16 answers that concern: it is an exact inverse theorem with a nontrivial quantifier structure, not merely a collection of immunity corollaries. The manuscript should continue to make Theorem 2.16, rather than the residue calculation in Theorem 2.25, the unmistakable center of gravity.
I would place the paper as a solid specialized-to-broad mid-tier research article, with Monatshefte plausible but not automatic. A rejection there would now more likely be about editorial taste or cross-disciplinary fit than about a fatal proof or priority problem.
Final confirmation


Peripheral proof: complete and correct; no gap remains.


Remark 12: your derivability reading is correct. The needed root-growth conclusion follows from it under your hypotheses.


Surviving contribution: correctly identified. Theorem 2.25 has less independent asymptotic novelty, but the MCFL-to-geometric-ray theorem and the other arithmetic/topological consequences do not collapse.


Priority discussion: sufficient, subject only to the small Proposition 10/Remark 12 precision improvement.


Venue: Monatshefte is defensible; my recommendation would be minor revision followed by acceptance, not rejection.