Bottom-line valuation
The recast is worth doing. It changes the first-choice venue from SPA to EJS, raises my estimated probability for the best first submission from about 39% to 51%, and does not weaken Theorem G provided that the serial recurrence and pole-order ingredients remain in the main article.
My author-level recommendation is therefore:

Recast the paper around experiment equivalence and singular inference, and submit that article to EJS.

I would not make the high-risk Bernoulli attempt, and I would not submit the present 72-page assembly to SPA before making this recast.

1. The recast, concretely
The new article should no longer present eight comparable headline results. Its hierarchy should be unmistakable:


A general experiment-equivalence theorem for stationary renewal windows.


A singular LAN application to an isolated double pole in sampled serial generalized-Erlang renewals.


Efficient testing and the sharp N−1/4 recovery rate for the unordered colliding rates.


That is already the real mathematical spine of the manuscript: the abstract states the two-sided local equivalence, Gaussian half-space experiment, efficient one-sided test, and matching fourth-root recovery rate; the introduction itself calls F and G the central statistical results.  
Main article: retain and renumber
I would use approximately the following main theorem structure.
Theorem 1: Stationary renewal window–Palm sample equivalence
Retain current Theorem 4.1, including:


both deficiency directions;


the explicit parameter-free Markov kernels;


the Nγ undershoot;


bounded-loss risk transfer;


calendar-time information scaling;


the semiparametric consequence;


the repaired qualification for fixed cones and constrained local experiments.


This should be the first main theorem, not a theorem appearing after thirty-four pages of two-state representation theory. It is the broadest field-facing result in the paper and is logically independent of the special pole calculation. 
Keep its proof in the main article. The record-to-sample coupling is the conceptual innovation: it does not condition Palm gaps on fitting inside the window, but makes the two experiments agree except when the undershot number of cycles is unavailable. That is precisely where the boundary-cycle problem is genuinely removed. 
Proposition 2: Serial sampled-tail coordinates at an isolated double pole
Retain a sharply shortened version of current Corollary 3.3, but only the part required later:


the confluent exponential-polynomial form of the sampled survival tail;


the minimal recurrence polynomial;


invertibility of the leading Hankel matrix;


recovery of the collision multiplicity and the unordered sampled-rate multiset from finitely many tail coordinates.


Do not surround this proposition with the general killed-reset similarity-orbit theory. Its role is not to establish a representation-theoretic programme. Its role is to provide regular quotient coordinates and a root-N estimator for the recurrence coefficients even at a double root. 
Proposition 3: Isolated-double-pole score nondegeneracy
Retain current Lemma 5.6, preferably promoted to a proposition.
Its pole-order argument is one of the paper’s genuinely distinctive calculations:


the collision derivative has an exact fourth-order pole;


the centre derivative has order three;


each separated-rate derivative has its own order-two pole;


after sampling, these produce the distinguishing k3e−λΔτk, k2e−λΔτk, and ke−θj​Δτk components.


This proof should remain in the main article. It is what turns population identifiability into positive statistical information and distinguishes the theorem from a generic invocation of conic LAN. 
Theorem 4: Stationary isolated-double-pole limit experiment
Retain current Theorem G, but split its presentation into three named parts or closely adjacent corollaries:


uniform LAN and convergence to the Gaussian shift on
Rn−1×[0,∞);


the efficient residualized test and its local power envelope;


attainable N−1/4 multiset recovery and the matching two-point threshold lower rate.


This is the application theorem, not a second independent centre competing with the equivalence theorem. Its current hypotheses must remain conspicuous: fixed serial order, one isolated real double pole, all other rates simple and separated, known sampling interval, and the serial positive realization. 
Corollary 5: Two-state collision
Current Theorem F should remain only as the n=2 corollary or worked example.
Do not retain it as a four-part theorem of equal visual status to G. The two-state formulas are useful because they display the fourth-order pole and the squared-separation coordinate transparently, but the fixed-order theorem already contains the substantive statistical statement.
Lemma 6: Two-point lower bound
Retain current Lemma 5.4 in the main text. It is short and essential to the honest formulation of the minimax claim: optimality in rate, witnessed by a fixed-base two-point threshold loss, rather than an exact continuum minimax constant.
Estimator statement
Retain the statement of current Lemma 5.7, because Theorem G must exhibit a measurable, rate-attaining procedure rather than merely assert existence. Move most of the finite-atlas contour construction to the supplement. The main text should explain:


empirical recurrence coefficients are root-N;


the simple roots and the two-root cluster have compatible analytic charts;


(c,δ) are regular cluster coordinates;


projection of δ onto [0,∞) gives the fourth-root rate after taking square roots.


The current proof of G already shows that its real dependencies are the serial renewal law, pole-order nondegeneracy, efficient-score plug-in, finite-atlas estimator, and the two-point lower bound. 

Move to an online supplement
These are necessary supporting results, but they should not determine the main article’s identity.
Move with full proofs


Lemma 5.1: uniform sampled-bin and sampled-tail derivative bounds.


Lemma 5.2: stopped renewal-score CLT and LLN.


Lemma 5.3: efficient-score plug-in equicontinuity.


Lemma 5.5: direct compact-uniform stationary-renewal LAN proof.


Most of the proof of Lemma 5.7: finite contour atlas, chart compatibility, total measurability.


The detailed two-state calculations supporting the shortened corollary derived from Theorem F.


Longer endpoint-tail, measurability, and empirical-information checks.


For the recast, I would use Theorem 1 as the primary conceptual route from the stationary record to the Palm experiment. The direct stationary-likelihood argument in Lemma 5.5 can remain in the supplement as an independent proof and as a check that the exact endpoint likelihood gives the same information. Keeping both full arguments in the main text currently creates duplication rather than additional force.
Optional supplementary model example
A compact version of the current two-state sampled-counter construction may go into the supplement as an example illustrating how a rank-one marked reset produces the renewal observation. This would include only:


Assumption 1.1;


the essential statement of Lemma 1.2;


the rank-one regeneration point from Proposition 1.3;


the Palm gap formula needed to identify the n=2 member of the serial family.


It should not retain the current A–E theorem apparatus.

Cut from the recast submission
Here “cut” means remove from the EJS article and its supplement, rather than moving everything out of sight while still presenting a 70-page package. These results could be retained for a separate representation-and-diagnostics paper.
Theorem A: cut as a headline theorem
The basic renewal reduction can survive as a short lemma or model example, but the hazard, covariance-mode, exact one-dependence, and finite-order-Markov conclusions are not part of the experiment-equivalence/collision-inference argument.
Also cut:


Corollary 1.4;


Proposition 1.5;


the extended observable and threshold discussion in Section 2.


Theorem B: cut
The direct three-inclusion quotient inverse is explicitly described by the manuscript as a “candidate original result pending complete reduction” against canonical DMAP2 coordinates. That is exactly the kind of peripheral priority exposure that a focused EJS submission should not carry.
Cut with it:


Proposition 1.6;


Proposition 1.7;


Corollary 1.8;


Proposition 1.9.


The serial collision article has a cleaner recurrence-coordinate route and does not need the two-state three-inclusion inverse.
Theorems C and E: cut
The retained-cycle inclusion CLT and the quotient delta method are mathematically sound infrastructure, but they answer a different inferential question. They do not advance the limit experiment or the fourth-root collision theorem.
Cut:


Lemma 1.10 in its present specialized batch-estimator role;


Theorem C;


Theorem E;


the sorted two-state root/rate CLTs attached to them.


Generic stopped-renewal CLT material needed by G already remains in the supplement through Lemma 5.2.
Theorem D and all diagnostic testing: cut
Cut:


Theorem 1.11;


Proposition 1.12;


Theorem D;


the physical-image test;


the complete-visible-law specification test;


the preserved-three-inclusion nonrenewal alternative;


the associated local-power analysis.


These results are individually substantial enough to distract from the article’s theorem hierarchy, but not strong enough to serve as a second centre beside equivalence and singular LAN.
General representation/fibre theory: cut
Cut:


Proposition 3.1;


Theorem 3.2;


Theorem 3.4;


the general similarity-orbit and (n−1)2-dimensional fibre discussion.


Keep only the distilled serial recurrence proposition extracted from Corollary 3.3.
The two-state fibre arc and higher-dimensional orbit manifold concern hidden-representation nonuniqueness. Theorem G concerns the statistical experiment generated by a declared serial renewal family. Their proximity in the current article makes the paper look broader, but does not make G stronger.
Appendix A certificate: cut
Cut Lemma A.1 and the long interval-arithmetic transcript. It supports only a supplementary pointwise projection example, not Theorem 4.1, F, or G. The paper itself limits the certificate to that single projection calculation.
Comparison section: reduce drastically
Replace the multi-page comparison table with approximately two pages organized around:


stationary renewal window censoring and Fisher information;


Le Cam equivalence and decision-theoretic transfer;


locally conic/singular experiments;


finite-mixture and Prony collision antecedents;


the distinction from super-resolution observation models.


The current clustered-source comparison is useful, but it should be prose, not part of an encyclopaedic representation table.

2. What the two versions are worth
These are editorial acceptance estimates, conditional on the present mathematical block being correct and on no new priority conflict. I would attach an uncertainty of roughly ±7 percentage points to each number.
Estimated length
VersionMain articleSupplementCurrent assembly72 pagesExisting additional supplementary calculationsStatistics-first recast31–35 pages including references22–30 pagesBernoulli-compliant variant24–25 pages including references30–38 pages
The Bernoulli estimate below assumes the extra compression to its normal length expectation. Bernoulli’s current author instructions say papers should generally be no more than 25 pages including references and that excess material should be placed in supplementary files; noncompliance may cause immediate rejection. 伯努利学会+1
Acceptance probabilities
VenueCurrent 72-page articleRecast articleChangeEJS24%51%+27 pointsSPA39%44%+5 pointsBernoulli7%21%+14 points
For Bernoulli, the 21% assumes the main paper is brought within approximately 25 pages. A 31–35-page version submitted without further compression would be nearer 11–13%, principally because of the length and editorial-fit problem rather than a mathematical defect.
Venue ordering
Current article
SPA (39%)>EJS (24%)>Bernoulli (7%)​
As assembled, the article still reads partly as a stochastic-process/model-structure paper with a major statistical block added to it. SPA expressly accommodates both the theory and applications of stochastic processes, including statistical inference for stochastic processes, so its editorial tolerance for the present mixture is higher. 科学直通车+1
Recast article
EJS (51%)>SPA (44%)>Bernoulli (21%)​
Yes, the recast changes the ordering. That is the principal thing it buys.
EJS becomes the natural first target because the article would then be recognizably about statistical experiments, equivalence, LAN, efficient testing, and minimax recovery, all within EJS’s stated theoretical and methodological statistical scope. IMStat+1
SPA remains entirely credible, but after the recast its comparative advantage decreases: the renewal process is the observation mechanism, while the scientific centre is statistical decision theory.
Bernoulli improves materially but remains a reach. Its theoretical emphasis fits the content, but the article still has a specialized singular application rather than a general classification of collision geometries, and even the focused version must be compressed unusually hard. Bernoulli describes itself as a flagship journal for the highest-quality work across mathematical statistics and probability, with substantial emphasis on theoretical development. 伯努利学会
What the recast buys in practical terms
It is not merely a five-point improvement at the same venue.
It changes the best available first shot from:


39% at SPA for the present article


to:


51% at EJS for the recast article.


That roughly twelve-point improvement in the best-target probability is large enough to justify a serious editorial reconstruction, particularly because the reconstruction does not require a new theorem.

3. Does the recast weaken Theorem G?
No—provided the serial structural inputs are distinguished from the general representation material.
There are two very different things currently described as “representation.”
Material that Theorem G genuinely needs
The main article must retain:


the serial generalized-Erlang construction;


the confluent sampled-tail representation;


the minimal recurrence and Hankel invertibility;


the regular cluster coordinates (c,δ);


the pole-order calculation proving score independence;


the measurable recurrence estimator.


Those are not decorative population results. They supply:


the regular nuisance and collision coordinates;


the positive-definite information matrix;


the root-N recurrence estimator;


the conversion from root-N estimation of δ to N−1/4 estimation of the colliding roots.


Moving those entirely out of the main article would weaken the presentation of G. That is why I would keep the distilled Corollary 3.3 material and the full Lemma 5.6 pole proof in the main text.
Material that Theorem G does not need
Theorem G does not depend on:


the complete two-state similarity arc;


the unrestricted killed-reset fibre;


the (n−1)2-dimensional general orbit calculation;


the three-inclusion inverse;


the physical-image constraints;


the inclusion CLT and delta method;


the specification diagnostics;


the pointwise projection certificate.


The manuscript’s own dependency table identifies G’s inputs as the stationary reduction, sampled pole-order lemma, and finite-tail recurrence estimator—not the general fibre theorems or the A–E diagnostic chain. 
It later says explicitly that A–E remain downstream of the population algebra and that the tangent, coupling, split-experiment, and projection calculations are not being used to replace the stationary likelihood proof of F–G. 
Thus the correct editorial operation is:

Remove general representation theory, but retain the serial algebra needed to construct and analyse the singular experiment.

That operation leaves the proof of G intact. In my judgement, it actually strengthens the case for G, because a reader can see immediately that each retained structural lemma supplies one necessary statistical step. At present, the essential serial algebra is embedded among several independent hidden-representation and diagnostic projects.
There is also no need to oversell what remains. The recast should preserve the present ceiling: experiment equivalence solves stationary-window censoring and random cycle count, but the collision theorem remains restricted to one isolated real double pole in a fixed serial order with the other poles simple and separated, known Δτ, and a special positive realization. 
That qualification is compatible with a strong EJS article. It becomes damaging only when the article’s architecture suggests that it is simultaneously offering a broad phase-type representation theory.

4. My decision as an author
I would recast for EJS.
I would not submit the assembled paper to SPA first. That route is defensible, but it leaves a substantial amount of value unrealized: the broadest theorem is buried on page 35, the principal statistical theorem competes with several unrelated theorem chains, and one of the prominent side results still carries an expressly unresolved priority qualification.
I would not try Bernoulli first. The mathematical content makes that attempt non-frivolous, but the remaining model-specific ceiling and the severe compression needed to meet its ordinary length expectation make the risk disproportionate. A Bernoulli rejection would not establish that the recast was wrong; it would mostly show that Bernoulli wanted a broader singular-experiment theorem than the paper honestly proves.
The EJS recast asks the paper to become exactly what its strongest mathematics already is:

a general equivalence theorem for stationary renewal observation, followed by a complete singular statistical experiment for an isolated sampled serial double pole, including efficient testing and sharp recovery rate.

That is a coherent article, not merely a shortened version of the present one. The work is principally subtraction, reordering, and proof allocation—not another research programme. On the probabilities above, it is worth doing.
