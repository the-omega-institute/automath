1. Verdict
Major revision.
Single strongest reason: the manuscript’s front matter is not hypothesis-faithful. It repeatedly advertises results for “general” D-MAPs, “general” local renewal classes, and “general” killed-reset kernels while the corresponding theorems require irreducibility, strict positivity, minimality, compact local parameter classes, exponential tails, separate Hellinger control of the equilibrium law, fixed serial order, and known sampling interval. These are substantive restrictions, not harmless technicalities. The central collision results look defensible, so I would not reject for mathematical failure, but I would not accept a paper whose advertised theorem is materially broader than its proved theorem. 
2. Significance threshold
Yes, it clears Journal of Physics Communications’ significance threshold. It is not too small for that journal.
JPC explicitly says that it does not make a subjective assessment of potential future significance or perceived novelty; it judges validity, methodology, rigour, and contribution to knowledge. IOP’s general review policy likewise identifies JPC as an exception to the usual rejection of technically sound but limited-interest papers. IOPscience - Publishing Support IOPscience - Publishing Support
The genuine venue problem is scope, not significance. The manuscript itself concedes:

“The sampled counter is therefore an interpretation of the constrained kernel, not an independently analysed physical system.”

That is an invitation to a JPC editor to say that this is a probability/statistics paper with detector terminology rather than a contribution to physics.  JPC’s scope is broad, so this is not automatically fatal, but the paper needs a much more convincing account of what a physicist learns that a probabilist does not already see from the renewal experiment. IOPscience - Publishing Support
I would not downshift it on significance grounds. A rejection here would more likely be for physics fit, architecture, or unreliable statement of hypotheses.
3. The first hostile attack
The vulnerable sentence is the abstract’s:

“More generally, we prove local asymptotic equivalence, in Le Cam distance, between a deterministic window of a stationary lattice renewal indicator and an undershot fixed-size i.i.d. sample from its Palm interarrival law.” 

Theorem 4.1 does not establish this for a generic local Hellinger neighbourhood of Palm interarrival laws. It assumes, uniformly over the triangular class,
Ep​ecD≤C,∣μ(p)−μ0​∣≤CN−1/2,
H2(p,p0​)≤C/N,H2(p​,p​0​)≤C/N,
where p​ is the equilibrium forward-recurrence law. 
The last assumption is the weak point. It directly controls the stationary endpoint distribution—the very object that distinguishes the stationary window from a Palm product sample. In the reverse-deficiency construction, the kernel draws the initial delay from p​0​, and the proof couples it to the desired p​ using precisely the separately assumed Hellinger bound. 
So the theorem is valid as a tailored transport result, but its advertised breadth is vulnerable to the charge that it assumes the hard endpoint comparison needed by its proof. A hostile referee will demand one of two things:


derive H2(p​,p​0​)=O(N−1) from a natural weighted-DQM or tangent condition on p; or


stop calling the result an equivalence theorem for a “general local class” and state plainly that both the Palm law and its equilibrium transform must already be locally Hellinger-controlled.


That is the first serious mathematical attack. It is more consequential than any individual algebraic detail in the two-state model.
4. The Bernoulli exception
The Bernoulli phenomenon is genuine. The claim that there are exactly two Bernoulli mechanisms is a two-state artefact.
Conditions
T1​1=ρ1,πT1​=ρπ
remain sufficient in every dimension. What fails beyond dimension two is necessity. The proof in the manuscript uses a specifically two-dimensional argument: because the Bernoulli Hankel matrix has rank one, the two-dimensional reachable and observable spaces cannot both have dimension two, so one of them must have dimension one. That forces one of the two displayed matrix identities. 
In three dimensions, both spaces can have dimension greater than one while their observable pairing still has rank one. There is room for separate invisible left and right directions. Here is an explicit strictly positive three-state counterexample:
T1​=6001​​1136571​5910765​747492​​,T0​=6001​​15785109​91163115​106106148​​.
Then
P=T0​+T1​=​9/201/43/10​1/49/203/10​3/103/102/5​​
is positive and doubly stochastic, so π=(1/3,1/3,1/3). The visible click probability is ρ=2/5, but
T1​1=​41/10041/10019/50​​=52​1,
πT1​=6001​(83,77,80)=6001​(80,80,80)=52​π,
and
detT1​=31254​=0.
Nevertheless, the visible record is i.i.d. Bernoulli(2/5). To see this, take
S=​111​1−10​11−2​​.
In this basis,
S−1T1​S=​2/501/100​1/1002/250​001/25​​,
S−1T0​S=​3/50−1/100​−1/1003/250​003/50​​.
Since πS=e1T​ and S−11=e1​, the probability of a visible word is the (1,1) entry of the corresponding product. The zero pattern prevents either hidden perturbation from feeding back into that entry, so for every word w,
πTw​1=(52​)#1(w)(53​)#0(w).
Thus the record is exactly i.i.d. Bernoulli even though none of the three conditions in the proposed higher-dimensional analogue holds.
There is a second elementary warning: in dimension two, detT1​=0, together with positive row sums, means T1​ has rank one and hence gives a fixed post-click law. In dimension three, detT1​=0 allows rank two and says nothing comparable.
My valuation is therefore:


The existence of Bernoulli hidden-state exceptions is real and survives in all dimensions.


The exact two-mechanism classification is intrinsically DMAP2.


In higher dimensions the Bernoulli representation fibre becomes larger, not smaller.


Theorem 1.3 is a sharp two-state classification lemma. It is not a dimension-robust structural discovery.


5. Abstract/introduction hypothesis audit
Yes. I find four definite mismatches, plus one additional dangerously broad phrase.
(a) “General two-state D-MAP”
The abstract says:

“For a general two-state D-MAP, we also characterize the renewal boundary…” 

Theorem 1.3 assumes:


P=T0​+T1​ is irreducible;


every coordinate of T1​1 is positive;


0<ρ<1.


These conditions exclude reducible kernels, hidden states from which a click is impossible, and degenerate visible laws. They are especially relevant because the “normalized post-click law” is not even defined for a zero row sum. 
The introduction repeats the same overstatement when it says that state-dependent normalized post-click laws can retain renewal only in the Bernoulli case. 
Required correction: “For an irreducible two-state D-MAP with positive click probability from each hidden state and 0<ρ<1…”.
(b) “General local class” of renewal laws
The introduction says the equivalence holds “for a general local class of stationary lattice renewal laws.” 
The actual class has a fixed centre p0​, a common exponential moment, an O(N−1/2) mean restriction, O(N−1) squared Hellinger distance for p, and a separate O(N−1) squared Hellinger restriction for the equilibrium transform p​. 
That is not merely “local.” It is a specifically engineered local class with endpoint-law control. The abstract’s accompanying statement that the all-zero atom is “uniformly negligible” also depends on the omitted uniform tail envelope.
(c) “Sharp recovery boundary”
The introduction asks for and claims a “sharp recovery boundary,” saying that Theorems F and G match the estimation upper bound with a contiguity lower bound. 
The upper result is compact-uniform over bounded local alternatives. The lower result is only:


at a fixed collision base;


against two points v∈{0,v0​};


with the nuisance coordinates held fixed;


under threshold loss;


proving optimality in rate, not an exact local minimax risk or uniform minimax lower bound.


Theorem F states those limitations expressly.  Theorem G does the same. 
The abstract gets this right by saying “pointwise fixed-base two-point threshold lower rate.” The introduction drops those quantifiers. It should copy the abstract’s qualification rather than call the entire recovery boundary sharp.
(d) “For general killed-reset kernels, realization uniqueness identifies a similarity orbit”
That sentence omits minimality. 
Proposition 3.1 applies only to declared subclasses of minimal kernels with full reachability and observability rank.  The paper later admits that for nonminimal representations, equal visible laws need not be connected by an invertible similarity and require a stratified analysis. 
The introduction should say “For minimal killed-reset kernels…”. As printed, it contradicts the paper’s own later caveat.
(e) Additional risky wording: “serial discrete phase-type”
The abstract’s phrase “sampled generalized-Erlang, or serial discrete phase-type” can be read as covering arbitrary serial DPH models. Theorem G covers the special family
Kθ​=eΔτQ(θ)
with a bidiagonal generalized-Erlang generator and deterministic rank-one reset. It expressly excludes unknown order and nonserial phase-type representations. 
I would replace the phrase by “the serial DPH representation induced by a sampled generalized-Erlang law.” Otherwise it invites a broader reading than the theorem supports.
The main F/G sentence is otherwise unusually careful: fixed order, one isolated collision, compact positive rates, separated remaining rates, and known sampling interval are all stated in the abstract. The failures are concentrated in the supposedly “general” surrounding claims.
6. Length and manufactured scale
No, the length is not justified. Yes, scale is being manufactured.
The genuine article is Theorem 4.1 plus Theorems F and G, with Theorem 1.3 as a useful ancillary result. That is a substantial paper. It is not a 72-page paper.
The inflation comes from promoting standard or downstream operations into an elaborate hierarchy:


a regenerative CLT and separated-batch covariance calculation;


an ordinary quotient delta method;


recalled minimal-realization theory;


a finite-coordinate Prony specialization already explicitly attributed to earlier representation theory;


standard chi-bar-square projection mechanics;


multiple diagnostic tests that do not support the central collision theorem;


“total measurable” fallback definitions and operational gates described at disproportionate length.


The manuscript itself says that the minimal-realization material is recalled background and that several calculations are supplementary.  Yet the main text still treats them as part of a twelve-theorem architecture.
The worst example is the appendix. It spends roughly five pages printing 90-digit interval endpoints for a covariance calculation at the single point z=1/2, while simultaneously stating that the calculation supports only a supplementary pointwise projection example and no other diagonal point.  The full decimal transcript then occupies pages of the main article.  That belongs in a machine-readable certificate, not in the paper.
A defensible reconstruction would be approximately:


main theorem and motivation;


stationary-window/Palm equivalence;


collision LAN, information nondegeneracy, test, estimator and lower rate;


a short DMAP2 renewal-boundary section;


everything else compressed into one technical appendix or supplement.


Theorem C and Theorem E should not be paper-level theorems. Proposition 3.1 should be cited, not re-presented as architecture. The pointwise certificate should disappear from the main PDF. The diagnostics should be either one compact section or a separate paper.
JPC formally allows research papers of unlimited length, but that is not an editorial entitlement to unlimited scaffolding. Its own author guidance says the introduction should be concise and that abstracts should normally remain below 300 words; this abstract is roughly 375 words before the paper has even begun. IOPscience - Publishing Support IOPscience - Publishing Support
The present manuscript reads as though every construction encountered during the project was retained and assigned a formal name. The central results deserve publication. The package, at its current scale, does not.
