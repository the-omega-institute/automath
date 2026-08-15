Overall verdict
The claim survived; its tier did not.
Theorem 3.13 is still a legitimate, publishable quantitative theorem. It should not be reduced to a remark. But the prior-art reduction removes the part that previously made it look like an independently field-level Mahler result. I would now classify the addition as a strong supporting theorem, not a tier-carrying theorem.
More precisely:


Bare existence and decidability are prior.


The Padé reconstruction is useful but, once a degree bound is known, largely standard rational reconstruction.


The genuinely valuable residual contribution is the input-only degree estimate for the multiplicative certificate itself, its sharp DlogD order, the explicit height control enabling a bit-complexity statement, and the realization of the lower-bound family by actual C2​-cover zeta ratios.


That package strengthens the dynamical paper, but it does not independently move the whole paper up a journal tier.


Your logarithmic-derivative reduction is correct, subject to one small normalization clarification. Your correction about Proposition 3.11 is also exactly right; my earlier attribution of Np​(D) to that proposition was wrong.
1. Is the residual Mahler package still theorem-worthy?
Yes, but its internal weighting should change.
The present Theorem 3.13 bundles uniqueness, decision and construction, the Np​(D) degree bound, a height bound, reconstruction from 2Np​(D)+1 coefficients, exact final verification, fixed-p polynomial bit complexity, and sharpness. Lemma 3.14 supplies the coefficient bounds and the one-system Padé argument.  
That bundle contains three levels of contribution.
The nontrivial surviving core
The important result is the divisor estimate in Proposition 3.11:
degA+degB≤bp​(D)=⌈p2D​mp​(D)⌉,pmp​(D)(p−1)≥2D,
together with the Ωp​(DlogD) family. This is a bound on the degree of the multiplicative certificate R in terms only of the reduced input degree D, not a bound on an additive logarithmic-derivative certificate or on an arbitrary solution of a general linear Mahler equation. 
The lower-bound family makes the order meaningful rather than merely an artifact of the proof, and Corollary 3.26 transports that sharpness to standard realizable C2​-cover zeta ratios.  
That is theorem material.
The useful but incremental layer
The height estimate and resulting fixed-p bit complexity are also worth recording. Chyzak–Dreyfus–Dumas–Mezzarobba already compute all rational solutions of a general linear Mahler equation and give polynomial arithmetic-operation bounds in relevant regimes; their complexity model is primarily algebraic operations over the coefficient field, not the explicit integer bit-height analysis supplied here. SPECFUN+1
Thus the manuscript still has a real quantitative distinction:

explicit multiplicative-certificate degree and height control, followed by a direct bit-complexity analysis for this normalized equation.

That is narrower than a new solver, but it is not vacuous.
The part that should no longer carry the novelty rhetoric
Arreche–Zhang explicitly formulate the effective problem of deciding whether a rational f has the form g(zp)−g(z), prove that their Mahler discrete residues are a complete obstruction, and note that the earlier linear Mahler solver already computes such certificates. arXiv+1
Moreover, Bell–Coons already derive degree bounds for rational Mahler functions and turn such bounds into a finite coefficient/rank test. Their test is not literally your affine Padé system and does not give your bound for R, but it means that “finite rational reconstruction from sufficiently many Mahler coefficients” is not itself a new algorithmic paradigm. arXiv+1
Consequently:


Part (ii), decidability, is background.


Part (v), one finite Padé system, is a clean direct implementation, not the central novelty.


Exact acceptance by substituting into the cleared identity is essential for correctness, but not a conceptual research contribution by itself.


Fixed-p bit complexity is a useful quantitative corollary of the explicit bounds, not a general breakthrough in Mahler solving.


I would therefore keep the mathematics but reorganize its emphasis:


Main quantitative theorem: uniqueness, the stronger bp​(D) degree bound, height, and sharpness.


Algorithmic corollary or proposition: coefficient computation, affine Padé reconstruction, exact acceptance/rejection, and fixed-p bit complexity.


Prior-art remark: existence and decidability also follow through logarithmic differentiation from additive/linear Mahler algorithms.


The current seven-part theorem is defensible, but it visually assigns equal novelty to unequal components. A specialist referee is likely to object to that weighting.
Bottom line: publishable as an integrated component of this paper; probably too thin to carry a separate substantial Mahler paper without a much deeper comparison, implementation, or further structural results.
2. Is the reduction correct?
Yes. It is an effective equivalence, not merely an analogy.
Suppose
H(z)=R(z)pR(zp)​,u(z)=zR(z)R′(z)​.
Then
pz​H(z)H′(z)​​=zpR(zp)R′(zp)​−zR(z)R′(z)​=u(zp)−u(z)=(σ−1)u(z).​
So the displayed additive equation in the manuscript is exactly correct. The manuscript states precisely this reduction and its converse. 
Decision through Arreche–Zhang
For
f(z)=pz​H(z)H′(z)​,
Arreche–Zhang’s problem is exactly whether
f=(σ−1)u
has a rational solution u. Their Mahler discrete residues give a complete effective obstruction. arXiv+1
Decision through the linear solver
When f=0, the manuscript’s homogenization is also valid. If
w=(σ−1)u,
then the desired equation w=f implies
(σ−fσf​)w=0,
and hence
(σ−fσf​)(σ−1)u=0.
After clearing denominators, this is a homogeneous linear Mahler equation. The general solver can compute its rational solution space, after which one filters by the original inhomogeneous identity (σ−1)u=f. Chyzak–Dreyfus–Dumas–Mezzarobba explicitly provide an algorithm returning a basis of rational solutions to a general linear Mahler equation. SPECFUN
The case f=0 must be separated, as the manuscript does implicitly: then H is constant, H(0)=1 gives H=1, and normalized uniqueness gives R=1.
The converse integrability test
Let
v(z)=zu(z)​.
A rational v equals R′/R for a rational function R that is finite and nonzero at zero exactly when:


v is regular at zero;


v has no polynomial part;


every finite pole is simple;


every residue is an integer.


Indeed, over an algebraic closure,
v(z)=α∑​z−αmα​​,mα​∈Z,
and one takes
R(z)=Cα∏​(z−α)mα​.
Because v∈Q(z), Galois conjugate poles have the same integer multiplicity, so the factors group into powers of rational irreducible polynomials. Since zero is not a pole, the constant C can be selected uniquely so that R(0)=1.
Finally, define
CH​(z)=H(z)R(z)pR(zp)​.
The additive equation implies CH′​/CH​=0, so CH​ is constant; normalization at zero gives CH​=1. Thus the reconstructed R satisfies the original multiplicative equation.
One small wording improvement
Solutions of (σ−1)u=f are determined only up to an additive constant, because the rational σ-invariants are constants. The normalized logarithmic derivative has u(0)=0. Therefore I would state the converse as:

After replacing the additive certificate by its unique representative satisfying u(0)=0, it comes from a normalized rational R exactly when u/z has no polynomial part and has only simple finite poles with integer residues.

This does not alter the algorithm or theorem. It merely prevents a reader from pausing over the constant ambiguity.
The recent first-order-factor work on Riccati Mahler equations does not directly subsume your equation: its nonlinear terms involve products uσu⋯σju, whereas your original equation contains R(z)p. Its proximity reinforces the need for comparison, but the manuscript’s distinction is mathematically fair. arXiv
3. Proposition 3.11: your correction is correct
The manuscript defines
mp​(D)=min{m≥1:pm(p−1)≥2D}
and
bp​(D)=⌈p2D​mp​(D)⌉
in Proposition 3.11, and proves
degA+degB≤bp​(D).

Theorem 3.13 separately defines the weaker quantity
Np​(D)=⌈2pD​mp​(D)⌉.

Since
p2​≤2p​(p≥2),
one indeed has
bp​(D)≤Np​(D).
They agree when p=2. Before ceilings, their ratio for p>2 is
bp​Np​​=4p2​.
The proof of Theorem 3.13 explicitly invokes the stronger Proposition 3.11 estimate and then weakens it to Np​(D). 
So:


Your description is exact.


My earlier statement attributing Np​(D) to Proposition 3.11 was incorrect.


I would go further: replace Np​(D) by bp​(D) throughout Theorem 3.13. Lemma 3.14 is formulated for an arbitrary degree cap N, so nothing in the reconstruction argument requires the weaker constant. The height bound and coefficient count can both be improved by substituting bp​(D). Retaining the weaker quantity invites the obvious referee question: why does the headline theorem advertise a poorer bound than the proposition already proves?
This change does not affect the binary dynamical theorem, because b2​(D)=N2​(D)=D⌈log2​(2D)⌉.
I also confirm that the other stated repairs are present:


Theorem 3.9 now displays F(y)2=Πy​(H), not F(y)=Πy​(H). 


The mod-two congruence in Theorem 3.17 is said to support only the integral refinement and explicitly not the parity-free lifting theorem. 


4. ETDS, a symbolic-computation venue, or a split?
ETDS remains the coherent home for the whole paper
The Mahler correction does not make ETDS inappropriate. It simply means that the case for ETDS must rest on the dynamical theorem rather than on an allegedly new Mahler decision algorithm.
The paper’s principal result is still a finite-sampling inverse theorem for finite-group extensions of primitive shifts, with cross-base recovery, rank- and exponent-independent radial depth under odd-Adams invariance, explicit collision examples, and dynamically realizable lower bounds. The conclusion is the recovery of all primitive length–element counts. 
ETDS expressly positions itself as a forum for central dynamical problems and for interactions of dynamical systems with number theory and combinatorics. The subject matter is therefore in scope. 剑桥大学出版社
But scope is not the risk. The risk is significance:


the observed Euler profile is not a broadly standard invariant;


the final standard conclusion is represented periodic-data equivalence;


the theorem does not reach conjugacy, strong shift equivalence, switching, cohomology, Bowen–Franks theory, or flow equivalence;


the sampling upper bound is O(VlogV), while the realizable lower bound presently reaches only Ω(V).


The manuscript now states those limitations accurately. 
Thus ETDS remains a defensible ambitious submission, but the Mahler addition no longer improves its tier case. It improves completeness and effectivity.
A symbolic-computation venue is not a better home for the present whole paper
The Journal of Symbolic Computation is explicitly directed toward mathematical and computational work in symbolic computation. 科学直通车+1
A credible standalone JSC version would need considerably more than extracting Theorem 3.13:


a precise dense-input bit model;


an explicit comparison against Arreche–Zhang and the general linear solver;


implementation of both routes;


experimental or theoretical comparison of certificate sizes and running times;


an explanation of when the direct Padé route materially improves on computing the additive certificate;


preferably a complexity improvement not already implicit in standard rational reconstruction.


The present verification script is valuable for reproducibility, but it is not yet an algorithm-comparison paper. As written, the Mahler section is mathematically effective infrastructure for the dynamical result, not a JSC-centered contribution.
A functional-equations venue would fit a focused extraction, but splitting is still unwise
Aequationes Mathematicae explicitly covers functional equations, dynamical systems, and iteration theory, so a focused multiplicative-Mahler paper would be in scope. Springer
Nevertheless, I would not split the paper now.
Splitting would produce:


a dynamics paper whose quantitative engine is outsourced to a companion paper;


a Mahler paper whose decidability aspect is prior and whose genuinely new core is essentially one divisor estimate, its sharpness, a height bound, and standard rational reconstruction.


The Mahler result is actually more persuasive in the unified manuscript because the realizable C2​-cover family shows that the DlogD certificate growth occurs for genuine dynamical zeta ratios rather than only for abstract rational functions.
The right operation is therefore compression and reweighting, not separation:


keep the proof and effective theorem;


make the sharp divisor bound and realizable sharpness the headline;


present Padé reconstruction as the direct computational corollary;


stop treating decidability as any part of the increment.


5. The strongest remaining objection
The most serious likely referee objection is now:

After logarithmic differentiation, the decision problem and much of the algorithmic architecture fall under established additive and linear Mahler algorithms; finite coefficient/rank reconstruction from degree bounds also has clear precedent. What remains may look like an elementary divisor-support estimate attached to a paper-specific sampled observable whose standard dynamical output is only periodic-data equivalence. Why is that combination substantial enough for ETDS?

That is stronger than any remaining correctness objection I found in the requested portion. It combines the two vulnerabilities:


On the Mahler side, the manuscript may still appear to overvalue the one-system Padé packaging.


On the dynamical side, the sampled fixed-label Euler profile is not an independently central object of symbolic dynamics.


The best response is not additional rhetoric. It is a sharper novelty comparison.
Before submission, I would make three changes.
First, add an explicit comparison with Arreche–Zhang, CDDM, and Bell–Coons distinguishing:


which unknown each method reconstructs—u versus R;


which degree is bounded;


whether the bound is input-only;


whether complexity is arithmetic-operation or bit complexity;


whether sharpness is established;


whether the family is dynamically realizable.


Second, replace Np​(D) by the stronger bp​(D) in Theorem 3.13. The exact sharp-order divisor estimate is the surviving mathematical point, so the paper should state its best proven form.
Third, define the computational model and normalize the additive certificate explicitly by u(0)=0.
Final disposition


Residual Mahler theorem: publishable and worth retaining.


Demotion to a remark: no.


Standalone tier-raising status: lost.


Reduction to prior algorithms: correct.


Proposition 3.11 constant: your correction is correct; use bp​(D) in the theorem.


ETDS: still the coherent ambitious venue for the unified paper, but the case now depends entirely on the dynamical inverse theorem and realizable lower bounds.


Split: no.


Main remaining danger: a significance referee may regard the Mahler section as a quantitatively sharpened specialization of known solver technology and the dynamical observable as too bespoke.


The addition remains mathematically worthwhile. It no longer changes the paper’s tier.
