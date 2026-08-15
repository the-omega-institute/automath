1. Corrected standard-object list
I have treated the attached manuscript—not the earlier parity-dependent version—as the object under review. Its title and declared subject mix accurately describe a paper combining finite-group extensions of SFTs, twisted determinants, primitive-orbit data, and Mahler functional equations. 
Preliminary corrections to the machinery map
Your map is substantially accurate, with four corrections or qualifications.
First, there is one stale parity sentence in the current PDF. In the proof of Theorem 3.17, after obtaining congruences of character blocks modulo 2, the manuscript says that this is “precisely the parity input in Theorem 3.9.”  But Theorem 3.9, as now correctly formulated, is parity-free; its proof invokes Theorem 3.8 and positivity, while Remark 3.10 explicitly says parity is unnecessary for special-value lifting.  The congruences are true and can support the integral refinement, but they are no longer an input to Theorem 3.9. That sentence should be deleted or rewritten.
Second, at an algebraic positive radius y, the exact normalization is
FH,2​(y)2=Πy​(H).
Thus a vanishing logarithmic coordinate gives Πy​(H)=1; positivity then gives FH,2​(y)=1. The manuscript itself flags this normalization explicitly.  Your summary has the correct logical result but suppresses this square.
Third, the O(DlogD) divisor bound is already valid for arbitrary p≥2, but the printed Padé decision algorithm, height estimate, and bit bound are specialized to p=2.   Consequently, “one affine Padé system reconstructs R” is printed machinery for p=2, not yet a stated general-p algorithm.
Fourth, (OA) should of course be quantified over χ∈G, not χ∈G. The displayed definition in the PDF uses the character group in the surrounding notation, despite some extraction artifacts. 
The corrected inventory of independently standard objects
I would use the following list.


Shifts of finite type, topological conjugacy, strong shift equivalence, shift equivalence, and dimension modules.
For nonnegative integral matrices, strong shift equivalence over Z+​ is the matrix relation corresponding to SFT conjugacy. Williams’s proposed implication “shift equivalence implies strong shift equivalence” is false, including in the irreducible case; what remains open is not that conjecture, but such questions as general decidability of strong shift equivalence. arXiv+1


Artin–Mazur zeta functions and unweighted Ruelle zeta functions of SFTs.
In the SFT setting, the fixed-point exponential definition and the primitive-orbit Euler-product definition are two expansions of the same rational function
ζA​(z)=det(I−zA)−1.
“Ruelle zeta function” should be qualified as unweighted here; weighted or representation-twisted Ruelle/Artin functions are separate objects.


Finite-group extensions of SFTs, G-SFTs, and matrices over Z+​G.
For finite abelian G, conjugacy of the resulting G-extensions is governed by strong shift equivalence over Z+​G, not by determinant or periodic data alone. Boyle–Schmieding show, in particular, that the same dynamical zeta data can be compatible with infinitely many nonconjugate extensions. arXiv


Representation-twisted Artin/Ruelle L-functions and dynamical determinants.
These include det(I−zAρ​), represented trace sequences, and their logarithmic expansions.


Periodic holonomy data, conjugacy-class trace series, represented G-cospectrality, and primitive Frobenius-class orbit counts.
These are standard periodic-data invariants. They are not complete invariants for conjugacy, cocycle cohomology, or switching.


Livšic/cohomological equivalence of cocycles, switching equivalence, voltage/gain graphs, and fundamental-cycle gains.
These concern marked orbitwise or cyclewise information, rather than aggregate counts by length and conjugacy class.


Chebotarev prime-orbit asymptotics and Frobenius-class Mertens products.
This includes the fixed-class Euler product whose logarithm is the manuscript’s −F1C​​. The paper correctly treats this product and its class projection as prior art. 


Bowen–Franks groups, signed Bowen–Franks invariants, and flow equivalence.
For an irreducible nonpermutation SFT, the Bowen–Franks group together with the sign of det(I−A) is the standard complete flow-equivalence invariant; the group alone is not. For reducible SFTs, the complete invariant is substantially more elaborate, involving filtered or K-web-type data. arXiv+1
A further current correction is that shift equivalence is now known to imply flow equivalence for all SFTs; Boyle’s result appeared in journal form in April 2026. arXiv+1


Equivariant flow equivalence of G-SFTs.
This has its own group-ring matrix classification and is standard but remote from the paper’s scalar determinant comparisons. arXiv


Positivity-realization problems for SFT and G-SFT invariants.
These include the Boyle–Schmieding problems of characterizing determinant polynomials, trace series, and conjugacy-class trace series arising from G-primitive matrices. The manuscript itself accurately quotes this boundary. 


Adams operations on representation rings and necklace/Witt transforms.
These are standard algebraic operations. Their use does not by itself establish a new structural theorem about representation rings or λ-rings.


Linear Mahler functions and Mahler special-value theory.
These are functions satisfying a linear relation among f(z),f(zp),…,f(zpr). The manuscript’s quadratic equation is not in that linear class.


Nonlinear algebraic Mahler equations and algebraic-solution rationality.
Keiji Nishioka’s theorem supplies the relevant algebraic-solution rationality implication. Kumiko Nishioka supplies the special-value theorem. Neither belongs in the paper’s novelty ledger. The manuscript now states this correctly. 


Effective rational-solution algorithms for linear Mahler equations and Mahler–Riccati equations.
Current algorithms cover linear Mahler equations and Riccati equations associated with first-order factors of linear Mahler operators. The latter involve products of successive shifts of the unknown; they do not immediately cover
R(zp)=H(z)R(z)p,
where the same unshifted unknown occurs to the p-th power. arXiv+1


The first-order multiplicative Mahler equation
R(zp)=H(z)R(z)p,H∈Q(z)×.
This is a standardly formulable rational functional-equation problem, even though the manuscript’s words “certificate” and “critical product” are its own packaging.


The Dieudonné–Dwork integrality criterion.
This is the standard p-adic power-series integrality tool used in Lemma 3.4. There is no Dieudonné determinant anywhere in the paper. Every determinant in the dynamics is an ordinary determinant of a finite matrix over C, a cyclotomic field, or Z. “Dieudonné determinants” should therefore be struck entirely.


I would not add finite-data rigidity for unimodal or Markov maps to the serious target list. It is a legitimate standard subject but only a remote comparison cited in the introduction; the manuscript has no derivative, kneading, or marked-map rigidity machinery.

2. YES / PARTIALLY / NO inventory
For this table:


YES means the existing machinery contains a substantive result directly formulable with standard objects and standard relations.


PARTIALLY means it controls a real aspect of a standard object but does not reach the standard classification or realization question.


NO means the object is merely an input, output label, or standard translation, or is reached only from hypotheses formulated using the manuscript’s special sampled data.


Standard objectWhere it sits in the fieldVerdictExactly what machinery (i)–(vii) saysExact missing bridge if PARTIALLYStructural reason if NOSFT topological conjugacy and SSE over Z+​Williams theory and matrix classification of SFT conjugacyNONothing beyond producing primitive adjacency matrices and determinant/periodic-data invariants. Proposition B.1 explicitly stops at periodic-data equivalence. —Determinants and aggregate periodic counts discard the positive factorization data carried by an SSE chain. Equal zeta or periodic data can coexist with nonconjugate systems.Shift equivalence and dimension modulesEventual algebraic classification; weaker than SSENOThe paper neither constructs an SE intertwining pair nor computes a dimension module.—Eigenvalue and trace data do not recover the integral module together with its endomorphism. The original SE⇒SSE conjecture is false, while SSE decidability remains open. arXiv+1Artin–Mazur / unweighted Ruelle zeta functionsStandard rational periodic-orbit invariant of an SFTPARTIALLYProposition 2.5 identifies the binary sign-determinant ratio with a ratio of ordinary cover zeta functions. Lemma 3.23 realizes broad prescribed pairs of sign determinants, and Corollary 3.26 realizes O(DlogD)-sharp rational functional equations as zeta ratios.  Convert the relative construction into a precise image theorem characterizing exactly which rational functions occur as ratios of zeta functions of two C2​-extensions, preferably with meaningful control of the common base rather than an arbitrarily enlarged dominating base.—Representation-twisted Artin/Ruelle L-functions and determinantsStandard finite-dimensional transfer-operator/determinant formalismNOLemmas 2.3–2.4 prove the usual spectral-radius bound and trace–determinant logarithm. Theorem 2.6 rewrites fixed-label data using these determinants.  —There is no new meromorphic-continuation, pole, zero, functional-equation, equidistribution, or rigidity theorem for the twisted L-functions themselves. They are finite rational inputs to a different inverse problem.Represented cospectrality and complete finite-group periodic dataPeriodic classification of finite-group extensionsNOProposition B.1 gives the standard equivalence of twisted determinant families, represented traces, conjugacy-class point counts, and primitive class counts. Theorems 3.17 and 3.21 eventually conclude equality of this data, but only from equality of the manuscript’s sampled fixed-label quantities. —The hypothesis doing the work is not a standard periodic-data relation; it is special-value equality of newly packaged Euler coordinates. Once all determinants are equal, the conclusion is the standard dictionary.Finite-group skew products and G-SFT conjugacyPositive K-theory and SSE over Z+​GNOThe paper constructs examples of G-extensions and compares their determinant families. It expressly disclaims conjugacy.—Positive K-theoretic and SSE information is absent. Same zeta data may support infinitely many nonconjugate G-extensions. arXivCocycle cohomology / Livšic equivalenceClassification of cocycles over a fixed dynamical baseNOThe paper records holonomy only after aggregating primitive orbits by length and conjugacy class.—Livšic-type conclusions require marked orbitwise equality—typically every periodic orbit retains its own holonomy—not equality of the number of orbits of each length in each class. The aggregation destroys precisely the information needed.Gain/voltage-graph switching classesGauge classification on a marked graphNOAppendix B gives the standard spanning-tree/fundamental-cycle switching criterion and uses it only to show that one example is not switching-equivalent. —The determinant family does not recover the ordered tuple of fundamental-cycle gains up to simultaneous conjugacy.Chebotarev prime-orbit distribution and Frobenius-class Mertens productsOrbit distribution in finite coversNOThe fixed-class product supplies the coordinate being sampled. No new asymptotic, error term, density, or Mertens constant is proved. The paper correctly attributes the fixed-class product and character projection to prior literature. —The arguments compare exact special values of already-defined products; they do not estimate orbit distributions.Bowen–Franks groups and ordinary flow equivalenceAlgebraic classification coarser than conjugacyNOThe manuscript never forms coker(I−A), its distinguished sign, or the reducible K-web.—A determinant polynomial does not determine the Smith normal form of I−A. Even equality of all traces does not recover the Bowen–Franks group.Equivariant flow equivalence of G-SFTsGroup-ring matrix classification; standard but remoteNONo equivariant flow move, group-ring matrix equivalence, or blocked K-theoretic invariant appears.—Scalar character determinants are only shadows of the relevant group-ring matrix equivalence. arXivBoyle–Schmieding positivity-realization problemsCharacterization of invariants arising from G-primitive matricesPARTIALLYLemma 3.23 is a genuine relative realization result for a pair of binary sign determinants: congruence modulo 2 suffices after choosing a large positive common base. Control the base or characterize the image of the full G-primitive matrix map: prescribed base determinant, prescribed group-ring trace series, or prescribed conjugacy-class trace series. The current construction chooses the base after the fact and does not characterize individual G-primitive invariants.—Adams operations and necklace/Witt transformsRepresentation rings, λ-rings, and combinatorial ghost mapsNOTheorem 2.6 and Lemma 3.20 use standard Adams and Möbius operations to derive formulas and, under (OA), a dyadic cancellation.  —There is no theorem about the representation ring, its Adams eigenspaces, Witt functors, or a new universal transform. The cancellation is a restriction imposed on determinant data.Linear Mahler functions and their special valuesClassical Mahler methodNOThe coefficient-height estimate permits application of Kumiko Nishioka’s theorem. The special-value implication itself is prior.—The function satisfies a nonlinear equation. No new theorem for the standard linear Mahler class is obtained.Nonlinear algebraic Mahler equations and algebraic-solution rationalityAlgebraic functional equations under z↦zpNO as a rationality theoremProposition 3.7 applies Keiji Nishioka’s 1985 theorem and then performs elementary descent from C(z) to Q(z). —The decisive algebraic-solution rationality is exactly the cited prior theorem. The manuscript cannot count that implication as its own theorem about this class.Rational solutions of R(zp)=H(z)R(z)pEffective rational functional equations under a Mahler endomorphismYES, presently strongest at p=2Proposition 3.11 gives a general-p divisor-degree bound. Theorem 3.13 gives, for p=2, uniqueness, explicit degree and height bounds, a finite decision procedure, and reconstruction by one Padé system. Remark 3.14 gives a polynomial bit bound.   ——General algorithms for linear Mahler and Mahler–Riccati equationsSymbolic computation and difference algebraNOThe paper solves one normalized multiplicative equation with repeated unshifted exponent. It does not solve an arbitrary linear Mahler equation or the general Riccati equations associated with linear factors.—The monomial pattern differs: standard factor/Riccati equations involve products of successive shifts, whereas this equation contains R(z)p. Existing algorithms therefore delimit, but do not automatically subsume, the manuscript’s problem. arXiv+1Dieudonné–Dwork integralityp-adic integrality of formal power seriesNOLemma 3.4 invokes the standard criterion to obtain integral coefficients under determinant parity. —It is a direct application. No extension or sharpening of the criterion is proved.
Bottom line of the inventory
The sampled-radius theorem does not become a theorem about SFT zeta functions merely because a ratio of two zeta functions occurs inside its proof. It proves that equality of a paper-specific collection of special values forces equality of standard periodic data. That is a valid inverse theorem, but its independent datum is the newly introduced fixed-label sampling apparatus.
Likewise, it does not reach conjugacy, strong shift equivalence, cocycle cohomology, switching, Bowen–Franks groups, flow equivalence, or full positivity realization. The manuscript is unusually careful about most of these boundaries, especially in Proposition B.1 and the introduction.  
The one place where the machinery already leaves the paper’s vocabulary and addresses an independently standard problem is the effective rational solution of the multiplicative Mahler equation.

3. One constrained theorem about a standard object
The strongest credible redirection is not a new dynamical classification theorem. It is the general-p completion of the effective functional-equation machinery.
The following statement uses no term invented by the manuscript.
Theorem — Effective rational solutions of a first-order multiplicative Mahler equation
Fix an integer p≥2. Let
P0​,P1​∈Z[z]
be coprime polynomials satisfying
P0​(0)=P1​(0)=1,D=degP0​+degP1​>0.
Define
mp​(D)=min{m≥1:pm(p−1)≥2D},Np​(D)=⌈p2Dmp​(D)​⌉.
Then the following assertions hold.


There is at most one rational function R∈Q(z) satisfying
R(0)=1,P0​(z)R(z)p=P1​(z)R(zp).


There is a deterministic algorithm which, from P0​,P1​, decides whether such an R exists and constructs it when it does.


If R=A/B in reduced normalized form, then
degA+degB≤Np​(D).


Put
Lp​=⌊logp​D⌋,Λ=h(P0​)+h(P1​)+21​log((degP0​+1)(degP1​+1)).
The reduced numerator and denominator admit an effective logarithmic-height bound of the form
max{h(A),h(B)}≤Np​(D)log2+D(Lp​+1)Λ.


The algorithm can be implemented by computing the first 2Np​(D)+1 coefficients of the unique formal solution
S(z)∈1+zQ[[z]],P0​(z)S(z)p=P1​(z)S(zp),
solving one affine Padé system, reducing the resulting quotient, and verifying the displayed polynomial identity.


For each fixed p, this gives a deterministic algorithm of polynomial bit complexity in the input size and Np​(D).


The order DlogD cannot in general be replaced by o(DlogD): for each fixed p, there is a sequence of integer inputs for which the unique normalized rational solution has degree
Ωp​(DlogD).


This is a standard functional-equation and symbolic-computation theorem. It contains no reference to radial values, orbit profiles, collision sets, boundary functionals, anchors, or certificates.
What standard problem does this advance?
It advances the effective rational-solvability problem for a nonlinear first-order Mahler equation. Existing general algorithms concern linear Mahler equations or Riccati equations arising from first-order factors of linear Mahler operators. arXiv+1 The proposed theorem isolates a different multiplicative equation and supplies:


an input-only degree bound;


an explicit height bound;


a single-system reconstruction algorithm;


polynomial-time termination for fixed p;


asymptotic sharpness of the degree order.


The theorem does not claim either Nishioka theorem. It begins with the rational-solution question itself. No special-value theorem and no algebraic-solution rationality theorem is needed in its proof.

4. Feasibility audit
4.1 Exact printed ingredients and how they feed the proof
(a) Normalized uniqueness
Proposition 3.3 proves, for p=2, that a rational function U with
U(0)=1,U(z2)=U(z)2
must be 1, by comparing the least nonconstant term.  Proposition 3.7 repeats the same proof for arbitrary p:
U(zp)=U(z)p,U(0)=1⟹U=1.

Applied to the quotient of two prospective solutions, this gives part 1 of the proposed theorem without modification.
(b) General-p divisor recurrence and degree bound
Proposition 3.11 is already stated for every p≥2. Taking orders at α=0 gives
e(α)=r(αp)−pr(α),
followed by the forward-orbit inversion
r(α)=−j≥0∑​p−j−1e(αpj).
The counting argument then yields
degA+degB≤Np​(D).

This proves part 3 exactly as stated.
(c) General-p formal coefficient control
Lemma 3.5 is also already general in p. It shows that the coefficient sn​ is determined linearly from earlier coefficients and obtains
(pq)2n−1sn​∈Z
after clearing the input coefficients by q. 
For integral P0​,P1​, this gives the denominator and coefficient-height control required to compute a finite Taylor jet effectively.
The orientation of P0​,P1​ may need to be interchanged relative to the notation of Lemma 3.5, but that is formal.
(d) Support localization and height
The proof of Theorem 3.13 contains a stronger support observation than the final theorem statement. Before the forward p-power orbit of a zero or pole of R reaches the divisor of P0​/P1​, its multiplicity is multiplied by p at each step. Since all multiplicities are bounded by D, the first hitting time is at most ⌊logp​D⌋.
The printed proof does this for p=2, then places every zero and pole of R among those of
k=0∏L​P0​(z2k)P1​(z2k)
and uses Mahler measure to bound the coefficient heights. 
Replacing 2k by pk gives the displayed general-p height bound because
M(Q(zpk))=M(Q(z))
just as in the binary proof.
(e) Padé reconstruction
Theorem 3.13 computes the unique formal solution through degree 2N, solves one affine Padé system, cancels common factors, and accepts only after verifying a polynomial identity. 
Nothing essentially binary occurs in the Padé uniqueness argument: two rational functions with total numerator-plus-denominator degree at most N and matching through order 2N must coincide. The only change is the formal recurrence used to generate the coefficients.
(f) Bit complexity
Remark 3.14 supplies a deliberately conservative polynomial-time analysis for p=2, using Cauchy estimates and fraction-free elimination. 
For fixed p, Lemma 3.5’s linear-exponent denominator bound substitutes for the binary integrality shortcut. The coefficient bit sizes remain polynomial in Np​(D) and the input height, so the same Bareiss-style analysis should go through.
(g) Sharpness
Remark 3.12 is already valid for arbitrary p. With
RJ​(z)=j=0∏J​Q(zpj)pJ−j,
it gives
RJ​(z)pRJ​(zp)​=Q(z)pJ+1Q(zpJ+1)​,degRJ​=(J+1)pJdegQ.
Hence the solution degree is of order DlogD. 
This proves part 7.
4.2 Single most important missing ingredient
The missing ingredient is:

A complete general-p effective reconstruction lemma proving that the coefficient recurrence for
P0​(z)S(z)p=P1​(z)S(zp)
together with the bound Np​(D) yields a sound and complete one-system Padé algorithm with explicit coefficient-height and polynomial bit-complexity bounds.

This means proving, in one consolidated result, all of the following:


a computable bound for the numerators and denominators of s0​,…,s2Np​(D)​;


uniqueness of the Padé quotient independently of which affine-system solution is chosen;


recovery of every rational solution of total degree at most Np​(D);


rejection when the final polynomial identity fails;


a polynomial bit bound for fixed p.


The mathematical content is not a new transcendence theorem. It is the effective closure of the already printed general-p divisor and coefficient estimates.
4.3 Proof architecture
StepStatusWork requiredNormalize the equation and prove uniquenessAlready presentCite the general-p least-term argument from Proposition 3.7.Derive the divisor recurrenceAlready presentProposition 3.11 is already general in p.Obtain the Np​(D) degree boundAlready presentNo conceptual modification.Construct the unique formal power seriesAlready present in ingredientsRewrite Lemma 3.5 in the orientation P0​Sp=P1​S(zp).Bound coefficient denominators and heightsMostly presentCombine Lemma 3.5 with Cauchy bounds; state constants cleanly.Localize possible irreducible factors of A,BBinary proof presentReplace square orbits by p-power orbits and L=⌊log2​D⌋ by Lp​.Prove the explicit height boundBinary proof presentRepeat the Mahler-measure argument with zpk.Padé reconstructionBinary proof presentReplace only the coefficient recurrence; the rational-approximation uniqueness argument is unchanged.Exact acceptance identityAlready presentVerify P0​ApB(zp)=P1​A(zp)Bp, with the correct numerator/denominator orientation.Polynomial bit complexityRequires a written extensionTrack rational coefficient denominators instead of relying only on binary integrality.DlogD sharpnessAlready presentPromote Remark 3.12 to a theorem/corollary for fixed p.Literature separationGenuinely necessaryCompare carefully with algorithms for linear Mahler equations and Mahler–Riccati equations, and state why the repeated unshifted exponent is outside their exact equation class.
4.4 Classification
(A) Difficult but natural extension of the current proof.
It is not a new dynamical argument, and it is not a major new transcendence argument. Nearly every conceptual component is already printed. The main work is to make the general-p effective section as complete as the current binary section and to establish its exact position relative to existing Mahler algorithms.
4.5 Success probability
75 percent.
The three facts controlling that number are:


Positive: the deepest mathematical estimate needed—the general-p divisor bound—is already proved in Proposition 3.11, and the sharpness family is already general in p.


Positive: the complete p=2 Padé, height, and complexity architecture is printed, so the target does not require inventing a new algorithmic paradigm.


Negative: the principal risk is not proof failure but scope and prior-art collision. Existing Mahler-factor algorithms are broader in some directions and use different Riccati equations. A careful literature comparison might show that the proposed algorithm is already subsumed after a non-obvious transformation, or that only the explicit O(DlogD) bound is new. The manuscript currently asserts a distinction but does not prove a formal non-reducibility theorem. 


Because the probability exceeds 25%, no fallback theorem is formally required. Nevertheless, the strongest immediately available weaker result is the present p=2 theorem stripped of the manuscript’s terminology: a polynomial-time decision and reconstruction algorithm for rational solutions of
P0​(z)R(z)2=P1​(z)R(z2)
with explicit O(DlogD) degree and height bounds. That theorem is essentially already proved by Theorem 3.13 and Remark 3.14.

5. Strongest remaining objection after proving the target theorem
Objection: depth/scope
Even after the general-p algorithm is proved, the strongest remaining objection would be:

The paper would contain a credible standard Mahler-algorithm theorem, but its principal dynamical theorem would still be an inverse theorem for nonstandard special-value data rather than an advance in a standard dynamical equivalence, invariant, or realization problem.

This survives because Theorem 3.21 begins with equality of the paper’s element-indexed Euler values at selected radii and uses (OA) to reduce those values to scalar dyadic equations. Only after that special-value argument has recovered every character determinant does Proposition B.1 convert determinant equality into standard periodic-data equality. 
The standard dynamical conclusion remains no stronger than represented periodic-data equivalence. It still does not provide:


conjugacy or strong shift equivalence over Z+​G;


cocycle cohomology or switching equivalence;


Bowen–Franks or flow-equivalence classification;


a characterization of determinant or trace data arising from G-primitive matrices.


This is not a correctness objection. The conclusions drawn in the manuscript are mathematically delimited. It is not primarily a priority objection either, provided the two Nishioka inputs, fixed-class product, and determinant/periodic-data dictionary remain excluded from the novelty claim. It is a depth/scope objection arising from the mismatch between the standard Mahler theorem and the still paper-specific dynamical headline.
The exact dependency making it survive is the chain
special sampled fixed-label values⟹Hχ​=1⟹standard periodic-data equality.
The first arrow is the paper’s contribution; the second is the standard dictionary. The hypothesis of the first arrow has no established independent role in symbolic dynamics outside this manuscript.

6. Honest-exit statement
The current machinery does not plausibly lead, under a serious but bounded revision, to a theorem about topological conjugacy, strong shift equivalence, cocycle cohomology, switching, Bowen–Franks groups, ordinary or equivariant flow equivalence, or the full Boyle–Schmieding positivity-realization problem.
The structural ceiling has four parts.


Loss of marked-orbit information.
The data retain only the number of primitive length-n orbits in each holonomy class. They forget which orbit has which holonomy. That prevents Livšic, cocycle-cohomology, and switching conclusions.


Loss of positive matrix equivalence information.
Twisted determinants and traces do not encode the elementary positive factorizations required for SSE over Z+​ or Z+​G. Boyle–Schmieding’s examples show that even complete zeta data may coexist with infinitely many nonconjugate finite-group extensions. arXiv


Realization occurs only after the candidate polynomials have been chosen.
Lemma 3.23 embeds a prescribed parity-compatible pair into a sufficiently large positive base. It does not characterize determinant, trace, or conjugacy-class trace data arising from a prescribed G-primitive system, nor does it preserve a prescribed base conjugacy or flow-equivalence class.


The arithmetic reduction is confined to a scalar p-power orbit.
Under (OA), the Adams–Möbius system collapses to dyadic channels. Already for C3​, two determinant ratios remain coupled at infinitely many arithmetically distributed powers; the manuscript correctly identifies the missing coupled special-value and zero theory.  That missing theory would be a major new project, not a bounded extension.


Accordingly, the strongest honest redirection is the effective theorem for the standard multiplicative Mahler equation stated above. A secondary, substantially thinner standard-object corollary could characterize parity-compatible rational functions arising as ratios of zeta functions of two binary SFT covers when the common base is allowed to be chosen freely. That realization statement is already almost contained in Proposition 2.5 plus Lemma 3.23 and is too immediate to serve as the principal tier-raising theorem.
There is no comparably reachable theorem about a standard dynamical classification object in the present machinery.
