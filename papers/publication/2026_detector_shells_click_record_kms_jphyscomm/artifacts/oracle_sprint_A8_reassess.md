Overall verdict
The standing has changed mathematically, but less than it has changed editorially.
Theorem 4.1 is, in substance, the experiment-equivalence theorem I had in mind. I find the two deficiency constructions correct, the kernels adequately measurable, and the boundary-cycle conditioning problem genuinely removed rather than displaced. I would put about 0.95 confidence on the core equivalence Δ(EN​,FN​)→0 and about 0.90 on the theorem block including every stated decision-theoretic and efficiency consequence, because one sentence about restrictions to cones should be qualified.
The manuscript’s five other repairs are also real rather than cosmetic: rank-one marked reset is now the regeneration boundary; the observation is explicitly restricted to a stationary binary renewal indicator; and the exact likelihood separates the all-zero atom while claiming negligibility only for increments of endpoint log factors.   
But I have found a significant new prior-art issue. Zhao and Nagaraja’s 2011 paper on window-censored stationary renewal processes already gives the continuous-time analogue of the exact endpoint/complete-gap likelihood and proves that the Fisher information per unit window converges to the interarrival Fisher information divided by the mean interarrival time. 日本统计学会 Theorem 4.1 remains substantially stronger because it proves two-sided Le Cam equivalence, with explicit uniform kernels and bounded-loss, minimax, and semiparametric transport. Nevertheless, the information identity in (LE11) is not itself new, and the omission of this closest predecessor is now the strongest substantive vulnerability.
1. Is Theorem 4.1 proved as intended?
The forward deficiency is correct
The manuscript represents the nonnegative half of the equilibrium process by
A∼ep​,D1​,D2​,…∼iidp,
independently, with renewals at A,A+D1​,A+D1​+D2​,…. It also correctly keeps the all-zero record as the event A>N−1, rather than forcing that atom into the product likelihood. 
The record-to-product kernel outputs the first mN​ observed complete interarrival lengths whenever they exist, and otherwise draws the p0⊗mN​​ fallback. Under the unconditioned equilibrium construction, on
{KN​≥mN​}
those observed lengths are exactly
(D1​,…,DmN​​).
Consequently, coupling the target product observation to this latent vector gives
​RN​PN,p​−p⊗mN​​TV​≤PN,p​(KN​<mN​).
That is precisely the correct argument. 
Most importantly, the target vector is never conditioned on KN​≥mN​. The event is used only to identify a high-probability set on which the kernel output equals an unconditional iid vector. The manuscript explicitly states this distinction. 
There is therefore no hidden “the first mN​ cycles, given that they fit” distribution. The coupling kills exactly the conditioning problem I warned about.
The reverse deficiency is also correct
Given d1​,…,dmN​​, the reverse kernel:


draws A0​∼ep0​​;


uses the supplied interarrivals;


appends iid p0​-interarrivals until the first renewal beyond N−1;


returns the resulting indicator, with the all-zero output when A0​>N−1.


That kernel depends only on p0​,N,γ, not on p, as required. 
For the comparison coupling, use the supplied p-sample as the first mN​ true interarrivals in the target equilibrium process. Then maximally couple
ep​⊗p⊗rN​andep0​​⊗p0⊗rN​​.
The manuscript’s Hellinger tensorization gives
H2(ep​⊗p⊗rN​,ep0​​⊗p0⊗rN​​)≤H2(ep​,ep0​​)+rN​H2(p,p0​)≤NC(1+rN​)​.
If that coupling succeeds and LN​≤mN​+rN​, every random quantity capable of changing the returned window agrees in the two constructions. Thus the two binary records are identical. Total variation is bounded by Hellinger distance, yielding exactly (LE10). 
The coupling used to prove the bound may depend on p. That is harmless: only the Markov kernel must be independent of the unknown parameter. A separate coupling may be selected for each p when bounding the resulting total variation distance.
The uniform renewal-count argument is adequate
The common exponential moment supplies uniform second moments and a uniform exponential tail for the equilibrium delay. Together with
μ(p)=μ0​+O(N−1/2),
this gives
KN​=μ(p)N​+OP​(N​),LN​=μ(p)N​+OP​(N​)
uniformly. Since Nγ/N​→∞, the lower undershoot and upper overshoot probabilities vanish; since γ<1,
N1+rN​​=O(Nγ−1)→0.
The manuscript states these steps in the needed uniform form. 
I do not see a missing concentration ingredient here.
Measurability is sufficient
The record space is finite and the iid sample space is countable. The forward kernel is therefore automatically Borel once its values are defined.
For the reverse kernel, positivity of all interarrivals makes the continuation terminate after finitely many draws. On a countable input space, the probabilities of all output records are countable sums of products of p0​-masses, so the asserted Borel measurability is more than adequate. The all-zero input/output cases are explicitly covered.
A referee-proof presentation could add the words “take a maximal coupling” in the reverse argument and state a convention for LN​ when the initial delay already exceeds the window. Those would be clarifications, not repairs.
One consequence should be narrowed
The sentence saying that all conclusions continue to hold after restriction to a cone or any fixed local subset is too broad if it is intended to include the unmodified canonical-gradient efficiency bound. The Le Cam equivalence and bounded-loss risk transport unquestionably survive parameter restriction. The information matrix also remains the information matrix of the ambient DQM family. But at a boundary or in a tangent cone, the relevant efficiency or minimax bound can be a constrained-experiment bound rather than the ordinary unconstrained canonical-gradient variance.
The safe formulation is:

The equivalence and bounded-loss risk-transfer conclusions remain valid after restriction. Information and efficiency consequences are then interpreted in the corresponding restricted local experiment.

That does not affect (LE7)–(LE10).
2. Bernoulli, SPA, or EJS?
What the new theorem helps
It removes the easiest high-level dismissal of the paper: that all of its machinery is tied to one serial phase-type construction. The paper now contains:


a genuinely general local experiment-transport theorem for stationary lattice renewals; and


a nonregular application in which one must still prove model-specific quadratic collision geometry and sampled pole-order nondegeneracy.


The abstract and discussion correctly distinguish those roles.  
That is a material rise in mathematical value.
What the new theorem hurts
It was added to the omnibus rather than used to simplify it.
The manuscript declares Theorems F and G to be central, but spends roughly the first 34 pages on A–E, physical-image diagnostics, quotient inversion, hidden-realization fibres, and higher-state orbit geometry. The general equivalence begins only in Section 4, and the collision theorems begin in Section 5. The introduction still devotes a substantial theorem inventory to the legacy strands.    
So the result condition for a Bernoulli submission is now met, but the earlier “sharply rebuilt around the central statistical results” condition is not.
Bernoulli describes itself as the Bernoulli Society’s flagship journal and seeks original research of the highest quality across mathematical statistics and probability. 伯努利协会 On mathematical content, submitting there is now defensible: it would not be a category mistake or an unserious reach. On the present architecture, however, I would still regard it as an intentionally high-risk submission rather than the honest modal target.
SPA is specifically devoted to the theory and applications of stochastic processes. 科学直通车 In the current 70-page form—with renewal observation, stationary censoring, D-MAP realization, phase-type structure, and singular inference all retained—SPA is the most honest first target.
EJS publishes theoretical, computational, and applied statistical work. IMStat It becomes at least as natural as SPA if the manuscript is recast around experiment equivalence, LAN, efficient testing, and minimax recovery, with most of the representation and diagnostic material removed from the main article.
SISP is no longer an available alternative: its official journal page now says it is no longer accepting new manuscript submissions. Springer
My venue judgment is therefore:
Bernoulli is now defensible, but the added length has not made it the honest current target. SPA remains the honest target for this manuscript as assembled. The mathematical case for Bernoulli improved; the editorial case did not.
3. Is the broad theorem plus narrow application coherent?
Yes. That pairing is coherent.
A general theorem need not classify every singularity covered by its observation model. Here the division is intelligible:


Theorem 4.1 removes stationary-window censoring, random cycle count, and endpoint-cycle complications.


Theorems F and G analyze the separate question of what the Palm interarrival family does at an isolated double pole.


The paper explicitly acknowledges that the transport theorem does not resolve general phase-type positive realization, residue cancellation, multiple collisions, complex poles, or Markov-renewal observations. 


That is not an inconsistency. It is a broad reduction theorem followed by one deep application.
The difficulty is that the current manuscript does not have only those two components. It also contains the A–E D-MAP inverse, model diagnostics, exact fibre arc, higher-dimensional orbit calculation, and associated supplementary interfaces. The natural indivisible paper is:
Theorem 4.1+Theorems F and G.
The naturally separable material is:
A–E+D-MAP representation/fibre/diagnostic package.
There is a second integration problem. The proof of Theorem G still obtains stationary LAN by applying the direct stationary-likelihood Lemma 5.5, rather than treating Theorem 4.1 as the formal reduction from stationary records to iid Palm gaps.  The direct proof is not pointless: it supplies an explicit record likelihood expansion, a concrete central sequence, and the all-complete-gap score test rather than merely an asymptotically transferred randomized procedure. But the manuscript must say clearly that this is the extra value of the direct proof. Otherwise Theorem 4.1 looks adjacent to, rather than load-bearing for, F and G.
A referee could therefore say “two papers,” but the accurate criticism would be:

The equivalence theorem and the collision application belong together; the legacy population-and-diagnostic package is the third centre preventing the article from reading as one paper.

4. The strongest remaining objection
The strongest substantive objection is the missing comparison with Zhao and Nagaraja.
They study a renewal process observed in a fixed window beginning at a random time, with a forward recurrence variable, iid complete renewal intervals, a right-censored terminal interval, and a separate no-renewal case. Their exact likelihood has precisely that factor structure. 日本统计学会 They then prove, for regular parametric renewal families,
w1​Iwindow​(θ)⟶μ(θ)1​Iinterarrival​(θ).
日本统计学会
This does not subsume Theorem 4.1. Zhao–Nagaraja do not prove two-sided Le Cam deficiency convergence, do not construct the two parameter-free randomizations, do not give the local nonparametric Hellinger class, and do not transfer arbitrary bounded-loss procedures or semiparametric risks. The manuscript’s residual contribution is therefore clear and potentially substantial:
asymptotic Fisher-information identity⟶full local experiment equivalence.
But until that comparison is made explicitly, a referee can reasonably conclude that the paper has presented the known information factor as part of an apparently new field-level package without identifying its closest predecessor. That is a concrete priority objection, not a speculative one.
The strongest editorial objection remains the omnibus architecture. The paper says its centre has moved, but its order and page allocation still make the reader traverse the old centre before reaching the new one.
Final assessment
Theorem 4.1 is proved. The coupling argument is the right solution, and it does not conceal another conditioning step. The mathematical standing of the paper has risen materially.
Bernoulli is now a defensible ambitious submission on results, but not yet the honest target for this 70-page architecture. In its current form, SPA is the honest first destination; EJS is equally plausible after a statistical refocusing. SISP is closed.
The broad theorem and narrow singular application form a coherent paper. The real fragmentation comes from retaining the entire A–E and representation/diagnostic project around them.
The most serious remaining matter is no longer proof failure. It is the combination of an unaddressed direct predecessor for the information consequence and a manuscript structure that has added a new centre without removing the old one.
