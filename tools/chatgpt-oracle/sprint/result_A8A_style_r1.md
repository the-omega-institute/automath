PART ONE — THE HOUSE STYLE, LEARNED FROM ACTUAL RECENT PAPERS
One limitation should be stated at the outset. I received the 33-page main article, but not the separate 22-page supplement. I can assess the allocation because the main article identifies the supplement’s contents and invokes its results repeatedly, but I cannot assess the supplement’s sentence-level prose or whether its proofs are themselves well paced. The main article says that the supplement contains the derivative bounds, stopped-renewal limit theory, plug-in equicontinuity, a second stationary-likelihood proof, and the finite-atlas construction. 
My calibration set was a group of theoretical and semiparametric EJS papers published in 2023–2025: Chigansky–Kleptsyna’s 43-page LAN paper, Bücher–Staud’s 36-page limit-theorem paper, Moss–Rousseau’s 72-page semiparametric HMM paper, Shetty–Ma–Zhao’s 26-page semiparametric missing-data paper, and Meitz–Shapiro’s 30-page minimax-asymptotics paper. This is a calibration sample rather than a formal census, but it is broad enough to identify the register relevant here. Project Euclid+4Project Euclid+4鲁尔大学数学系+4
1. What recent accepted EJS papers actually do
How they open and where the theorem appears
The modal opening is:


a restrained abstract stating the problem, the principal result, and perhaps one methodological consequence;


an introduction beginning immediately with the statistical model or inferential obstruction;


a short account of the literature and the precise gap;


definitions and assumptions;


the main theorem.


The journal does not have a first-page-theorem convention. Chigansky–Kleptsyna use roughly two pages for the problem and LAN background and state their model-specific main results on page 4. Bücher–Staud identify their principal theorem on page 2 of the introduction, then give the model and conditions before stating it. Moss–Rousseau have a four-page introduction and reach their first theorem around page 10. Meitz–Shapiro do substantial optimization groundwork and reach their first main asymptotic theorem around page 11. arXiv+3arXiv+3arXiv+3
For a theory paper of 30–45 pages, an introduction of roughly 2–5 pages—about 8–15 percent of the main article—is ordinary. Longer introductions occur when a paper has several contributions or straddles distinct literatures.
Your paper fits this convention. The introduction occupies pages 2–6, and Theorem 1 begins on page 7. That is not late for EJS. The opening paragraph also does what an EJS opening should do: it identifies a concrete statistical mismatch—the random number of cycles and the two censored boundary cycles—rather than opening with a general history of renewal theory. 
How much explanatory prose there is
Recent theoretical EJS papers are dense. In result and proof sections, perhaps two thirds to four fifths of the space consists of assumptions, formulas, statements, and proofs. The remaining prose is highly functional:


before a result, it says what obstacle the result removes;


immediately after a result, it interprets the statistical meaning or compares assumptions;


at the beginning of a proof, it identifies the decomposition or external theorem being used;


inside a proof, it is used when the logical reason for a calculation is not apparent from the calculation itself.


What is less customary is a paragraph before every formal statement explaining that the statement is deliberately narrow, followed by another paragraph after it restating what it does not prove.
The prose is uneven on purpose. A genuinely novel coupling may receive a full page of explanation; a standard delta-method consequence may receive one sentence. The paper is not expected to give every assertion equal rhetorical weight.
How proofs are written
EJS accepts short proofs that invoke cited results when the invoked result really discharges the work. Chigansky–Kleptsyna, for example, dispose of a recalled Hájek theorem with a one-line citation. Moss–Rousseau similarly invoke standard parametric HMM results once their model-specific information issue has been handled. arXiv+1
But the readership expects the paper to expose the model-specific argument. A proof may be technical without being line-by-line encyclopedic. The usual pattern is:

identify the novel step → state the auxiliary result precisely → perform the model-specific reduction → cite the standard conclusion.

Routine envelope calculations, repeated moment estimates, empirical-process bookkeeping, lengthy variance formulas, simulation details, and alternative proofs are commonly deferred. Bücher–Staud keep the principal proofs in a proof section and put a strong-mixing extension and variance calculations in a short supplement. Moss–Rousseau retain their most novel proofs in the article and send more standard arguments and simulation details to a nearly article-sized supplement. Shetty–Ma–Zhao use the opposite extreme: their relatively short main article sends theorem and lemma proofs to a very long supplement. arXiv+4arXiv+4arXiv+4
So EJS does not impose a rule that every central proof must be printed in the main article. It does expect the main article to make the chain of dependence intelligible without requiring the reader to reverse-engineer the supplement.
Main text versus supplement
There is no meaningful numerical “house ratio.” In the sample:


some accepted theory papers carry essentially all proofs in the article;


Bücher–Staud have approximately 35 pages of main text and 8 pages of supplement in the author copy;


Moss–Rousseau have approximately 46 pages of main text and 40 pages of supplement in the author copy;


Shetty–Ma–Zhao append a proof supplement many times longer than their short main manuscript.


The customary principle is about kind, not length:
Main article: model, statistical question, exact main results, central construction, novel proof mechanism, enough auxiliary statements to follow the argument, interpretation.
Supplement: lengthy technical bounds, standard-but-long proofs, alternative proofs, measurability edge cases, secondary extensions, additional computations, simulation details, code, and reproducibility material.
Your 33:22 division means that the supplement is two thirds the length of the main article and 40 percent of the combined package. That is entirely normal for EJS. The numerical proportion should not be changed merely for optics.
The allocation is almost right as well. The independent direct stationary-likelihood proof, exhaustive derivative bounds, contour-atlas bookkeeping, exceptional-event fallbacks, and detailed two-state calculations are natural supplementary material. The stopped-score CLT/LLN and plug-in equicontinuity may also remain there, but their exact usable statements should be visible in the main article. At present, the reader is sometimes told only that “Lemma S2 supplies” or “Lemma S3 shows” the required fact.  
I would move one to two pages of statements and proof roadmaps from the supplement into the main article, not the proofs themselves. In the other direction, some of the test-gate and fallback mechanics now embedded in Theorem 4 can move to the supplement or to the proof. The revised package could remain approximately 34–35 pages plus 20–22 pages.
Register
First-person plural is standard:


“we consider”;


“we show”;


“we decompose”;


“we now apply”;


“the following theorem yields.”


Impersonal prose is used where natural, but sustained passive voice is not a house preference. Results are generally signposted once in the introduction and then referred to by number. Motivation may return in the discussion, but in a broadened or interpretive form—not as a second rendition of the introduction.
The style is mathematically direct rather than ceremonial. A typical proof begins with the object to be decomposed, not with “We now proceed to demonstrate the following result.” A typical remark explains a consequence or limitation that a reader might otherwise misunderstand. It does not catalogue every nearby theorem that is not being claimed.
Tells of a poor EJS register fit
The common signs are:


an abstract that functions as a complete theorem inventory;


a long contribution list before the reader knows the model;


an introduction written like a grant proposal or referee-response memorandum;


theorem statements containing implementation safeguards, fallback conventions, and every negative qualification;


recurring paragraphs beginning “This result does not cover…”;


a supplement that contains unnamed indispensable inputs;


a discussion that repeats the contribution statement rather than interpreting it;


mathematical prose in which every assumption and caveat receives the same emphasis as the principal idea.


Your paper exhibits several of these, but not all.

2. Application to the manuscript, section by section
Title
The title is good. It names both the general contribution and the singular application. It is technical, but EJS titles are often technical. I would not change it.
Abstract, pages 1–2
The abstract is about 250 words and tries to carry nearly the entire paper:


two-sided equivalence;


explicit kernels;


risk transfer;


information conversion;


semiparametric efficiency;


fixed-cone restriction;


all principal collision-model assumptions;


the pole-order argument;


LAN;


efficient testing;


attainable recovery;


lower bound;


five separate nonclaims.


The content is accurate, but its hierarchy is flat. The last sentence—listing the absence of an exact minimax constant and exclusions of multiple collisions, unknown order, unknown sampling interval, and nonserial representations—is especially unlike the strongest recent EJS abstracts. 
What to do instead: reduce it to approximately 170–190 words. Keep:


the two-sided local-equivalence theorem and its decision-theoretic consequence;


the isolated-double-pole application;


the nondegenerate collision score, Gaussian half-space limit, efficient test, and N−1/4 multiset rate.


Mention the fixed serial model and isolated collision in one clause. Delete the catalogue of nonclaims. Those belong in the model section and final discussion.
Introduction, pages 2–6
The first three paragraphs are strong. They identify the genuine boundary-cycle problem, explain the two kernels, and say what the equivalence buys statistically. This is exactly the kind of opening EJS uses. 
The application paragraph and the “three ingredients” paragraph are also effective. They explain why the squared half-separation is the regular coordinate and why pole order is a statistical information argument rather than only an identifiability argument. 
The departure begins with:

“The order of the results reflects this logic.”

What follows is an exhaustive ledger of every numbered result and every class of supplementary argument. It reads less like an introduction and more like a document map generated to prove that every dependency has been placed somewhere. 
Replace that paragraph with two sentences:


Section 2 proves the general experiment equivalence.


Sections 3–5 develop the collision coordinates and derive the singular limit experiment, test, and recovery rate.


The literature paragraphs are competent but compressed into a sequence of boundary markers: this paper strengthens that result, specializes this theory, and does not inherit those minimax conclusions. The super-resolution comparison is particularly defensive this early. 
The subsection “Observation model and notation” then introduces Q(θ), Kθ​, the rank-one marked kernel, and matching distance before the general renewal theorem. This interrupts the general-to-specific order.
What to do instead: retain only the scalar description of the sampled generalized-Erlang model in the introduction. Move equations (1.1)–(1.4), especially the matrix realization, to the beginning of the application part, immediately before current Section 3. This will shorten the introduction by about one page and prevent the reader from entering the model algebra and then being pulled back to a general renewal theorem.
Section 2, local equivalence
The sectional opening repeats material already given in the introduction: the observation is a lattice renewal indicator rather than interval counts, and the theorem improves an information comparison to experiment equivalence. 
That can be compressed to one paragraph.
Theorem 1 is mathematically clear but editorially overloaded. Its statement occupies much of pages 7–10 and combines:


hypotheses;


experiment definitions;


qualitative equivalence;


quantitative bounds for both deficiencies;


bounded-loss transfer;


local minimax transfer;


parametric information;


semiparametric canonical-gradient bounds;


vector-valued covariance;


restriction to cones;


a warning about constrained efficiency;


a final nonclaim about global adaptation. 


An EJS reader can follow it, but the central theorem is hard to quote or remember.
Better architecture:


Theorem 1: experiment equivalence and quantitative deficiency bounds.


Corollary 2: bounded-loss transfer, information per calendar unit, and canonical-gradient covariance.


Remark: restriction to a fixed cone and the absence of global adaptive equivalence.


The proof itself is one of the best-written parts of the paper. It explains the construction rather than merely presenting inequalities. In particular, the paragraph explaining that the first mN​ cycles are not conditioned to fit, and that the Nγ undershoot removes the boundary-conditioning problem, gives the reader the conceptual point at the correct location. 
I would not shorten that proof materially.
The final two paragraphs of the section should be reorganized. The paragraph beginning “For the serial models below…” is really a bridge proposition verifying that the application lies within Theorem 1. It should either be a formally stated “Verification lemma for the serial family” or appear at the beginning of the proof of Theorem 4. The following boundary paragraph—excluding Markov-renewal, semi-Markov, and generic MAP observations—is another instance of a limitation repeated too many times. 
Section 3, finite serial coordinates
This section fits EJS very well. Proposition 2 is concise, self-contained, and carries its own proof. It states exactly the finite-coordinate fact that will be used later, rather than developing an unnecessary general theory of phase-type representations. 
The one tonal defect is the opening:

“It is not a statement about general phase-type representations or hidden-realization geometry.”

Begin positively instead:

“The next proposition supplies finite regular coordinates for the sampled survival tail at repeated rates.”

The negative scope sentence can be placed in a short remark after the proof or omitted; the paper has already fixed the serial model.
Section 4, the isolated-double-pole experiment
Proposition 3 and its proof are strong. The progression from exact pole orders to polynomial-exponential components and then to score linear independence is visible and economical. The argument does not merely cite generic singular-model theory; it performs the required model calculation. 
The section’s central presentation problem is Theorem 4. It contains three genuine results:


uniform LAN and the constrained Gaussian experiment;


the locally efficient one-sided test;


attainable and lower recovery rates.


That tripartite structure is defensible. What is not defensible stylistically is placing operational safeguards inside the theorem statement:


the null recurrence fit;


the empirical information;


the fixed score chart;


the singular-block gate;


the nonpositive-Schur-complement gate;


the default nonrejection rule;


the statement that the gate is asymptotically inactive.


These are important for total measurability, but they are not the scientific headline. They make the theorem read like a verified implementation specification. 
There is also a structural inversion: Theorem 4 refers to “Estimator 7” before Estimator 7 has been defined. The estimator appears only after Corollary 5 and Lemma 6.  
What to do instead:


Define the recurrence estimator and the residualized statistic before the theorem.


State only that there exists a total measurable test based on those definitions, with the displayed limiting power.


Put the fallback gates and their inactivity in the proof.


Either divide Theorem 4 into three results or retain parts A–C after the procedures have been defined.


“Estimator 7” is also an unnatural theorem-environment name. Make it a subsection called “A measurable recurrence estimator” and then state a proposition about its rate.
Corollary 5 is too slight in its present position. It essentially says that Theorem 4 applies when the product Bη​ is empty and gives two derivatives. Either turn it into a short worked example before the general n-state statement, or reduce it to a remark and leave the extended two-state formulas in the supplement. 
Lemma 6 belongs in the main article. The lower-bound proof is short, conceptually important, and clarifies exactly what “optimal in rate” means. Keep it.
Section 5, proof of the limit-experiment theorem
The section has the right conceptual route:


verify the DQM/Hellinger hypotheses;


invoke Theorem 1;


transfer the i.i.d. Palm LAN experiment;


construct the efficient score test;


use the recurrence estimator and the two-point argument.


The problem is that a reader encounters a string of external dependencies:


Lemma S1 for relative derivative bounds;


Lemma S4 for the direct stationary likelihood expansion;


Lemma S2 for the stopped Hessian LLN and score CLT;


Lemma S3 for plug-in equicontinuity;


Section 3.1 of the supplement for the estimator.


The main text explains what these inputs do, but not always their exact hypotheses and conclusions.  
This is not an excessive supplement by EJS standards. It is an interface problem.
Add a short proposition or three compact lemmas in the main article giving the exact forms used:


uniform relative derivative/envelope bounds and resulting DQM;


stopped-score CLT and information LLN;


plug-in equicontinuity for the fitted efficient score.


The proofs may remain entirely in the supplement.
The independent direct stationary-likelihood proof is ideal supplementary material. In the main article, call it an independent verification in one sentence; do not allow the principal proof to oscillate between two routes.
Section 6, discussion and prior work
There is good material here, but the section is approximately twice as long as it needs to be.
The first two pages repeat:


why complete gaps are not conditioned to fit;


why the reverse kernel needs a base continuation;


why two deficiencies matter;


why the theorem stops at renewal cycles;


why fixed cones change the decision problem.


Those points have already appeared in the introduction, Theorem 1, its proof, and the bridge to Theorem 4. 
The pole-order interpretation and the explanation of why confluent coordinates avoid labelling the colliding roots are worth retaining. 
The subsection “Why this is not a super-resolution observation model” is the most conspicuously defensive part. A related-work distinction is appropriate, but it should take one paragraph, not a named subsection culminating in another complete list of the paper’s ceiling. 
Reduce Section 6 from about five pages to roughly two and a half or three:


one subsection on the meaning and scope of the equivalence;


one on collision geometry, Prony coordinates, and the fourth-root rate;


one concluding paragraph on extensions.



3. Does it read as machine-assisted?
Yes, in identifiable places. It does not read like a raw machine-generated mathematics paper. It reads like a mathematically competent human paper that has been repeatedly edited under an adversarial checklist, probably with machine assistance.
The tell is not bad grammar or uniformly generic mathematics. The proof of Theorem 1 and the pole-order proof have real mathematical rhythm: some steps are compressed, while the conceptual coupling and score-separation points are allowed to breathe. Those passages read naturally.  
The machine-assisted or checklist-conditioned habits are elsewhere:


The abstract as a complete claim ledger. Every result and almost every limitation appears, with no willingness to leave secondary qualifications to the paper. 


The exhaustive roadmap. The paragraph naming Theorem 1, Proposition 2, Proposition 3, Theorem 4, Corollary 5, Lemma 6, and every supplementary component announces structure rather than advancing the argument. 


Repeated negative triads and quartets. “We do not infer…, allow…, or claim…” and repeated exclusions of multiple collisions, unknown order, unknown sampling interval, and nonserial representations recur in the abstract, model definition, theorem statement, and discussion.  


Equal emphasis on theorem and fail-safe mechanics. Theorem 4 gives the Gaussian power envelope and, in the same rhetorical register, the behavior when an empirical matrix is singular or a fitted chart is exited. 


Transitions that certify completeness. “The mechanism in Estimator 7 is short even though its total construction is technical” is followed by an inventory of every constructional component. 


Assessment language inside the article. “The ceiling of Theorem 4 is therefore substantive” sounds like a response to a referee or a valuation memorandum, not like the conclusion of a research article. 


The prose does not suffer mainly from uniform paragraph length. Its stronger artificial tell is scope saturation: the paper repeatedly proves that it has not overclaimed. That may have been necessary during auditing, but the audit trail should now be removed from the published voice.
A human final pass should delete roughly half of the negative scope sentences. State the model once, state the principal limitations once near the end, and trust the formal hypotheses everywhere else.

PART TWO — YOU ARE THE REFEREE
Recommendation: Accept with minor revisions
To the Editor:
I have read the manuscript Renewal-window equivalence and singular inference at a sampled double pole. My recommendation is acceptance subject to a focused revision of the presentation. I do not recommend a further mathematical round, and I do not regard the paper as a reject-and-resubmit case.
The paper has two connected contributions. First, it establishes two-sided local asymptotic equivalence between a stationary lattice-renewal record observed in a deterministic window and a slightly undersized i.i.d. sample from the Palm interarrival distribution. The equivalence is implemented by parameter-free kernels and is used to transfer bounded-loss risks, information, and constrained local decision theory. Second, the paper applies this result to an isolated collision in a sampled serial generalized-Erlang model, proving a nondegenerate boundary LAN experiment, a locally efficient one-sided test, and an attainable and pointwise rate-optimal N−1/4 recovery rate for the unordered colliding rates. The article’s ordering—general experiment theorem first, singular application second—is appropriate for EJS.
The principal proof in Section 2 is particularly effective. The record-to-sample coupling and reverse continuation kernel are explained clearly, including the reason that the extracted gaps are not being conditioned to fit the observation window. This is the conceptual heart of the equivalence result, and it is carried in the main article rather than hidden in the supplement. The pole-order argument in Proposition 3 is similarly well presented and makes clear why positive information in the collision coordinate is a model-specific fact rather than a consequence of generic locally conic theory.
The manuscript nevertheless needs editorial compression. At present it is excessively defensive. Its abstract, theorem statements, model paragraphs, and discussion repeatedly state what is not being claimed. The same restrictions—one isolated collision, fixed serial order, known sampling interval, and no general phase-type conclusion—are given several times. These qualifications are mathematically appropriate but rhetorically overrepresented. They make the paper sound as though it is answering a sequence of objections rather than presenting one statistical argument.
The most important concrete issue is the organization of Section 4. Theorem 4 refers to Estimator 7 before that estimator has been defined and incorporates the estimator’s fallback gates and measurability safeguards directly into the theorem statement. The estimator and residualized statistic should be defined first. The theorem should then state the limit experiment, power envelope, and recovery conclusion cleanly, leaving gate behavior to the proof. Splitting Theorem 4 into separate limit-experiment, testing, and recovery statements would also be reasonable, although it is not essential if the definitions are reordered.
The division between main text and supplement is acceptable in length and largely acceptable in content. I would not ask the authors to move the long derivative estimates, contour-atlas bookkeeping, or alternative likelihood proof into the main article. I would, however, ask them to print in the main article the exact statements of the supplementary inputs used in the proof of Theorem 4: the DQM/envelope result, the stopped-score CLT and information LLN, and the plug-in equicontinuity result. At present the proof is intelligible conceptually, but the reader must consult the supplement to determine the precise uniform conclusions being invoked.
Finally, the discussion should be shortened substantially. The explanation of the two kernels, the fixed-cone qualification, and several limitations repeat material already stated in the introduction and theorem sections. The comparison with super-resolution models should be reduced to one related-work paragraph. The discussion should emphasize interpretation rather than provide a second catalogue of claims and nonclaims.
The single objection most likely to harm the paper editorially is therefore not the supplement ratio or the location of the first theorem. It is that the manuscript’s over-defensive architecture obscures the hierarchy of the results. A reader may finish with an unusually clear memory of what the authors decline to prove but a less immediate sense of the one general theorem and one singular application that they do prove. This is fully fixable and requires no new mathematics.
Subject to the revisions above, I would accept the paper.

PART THREE — THE EDITOR’S BAR
I would require the following changes before acceptance, in this order.
1. Reorganize the singular-inference section
Required — organization and writing; no new mathematics
In current Section 4:


move the recurrence estimator now called “Estimator 7” before Theorem 4;


define the residualized statistic and its empirical information before stating its power result;


remove the score-chart, singular-block, Schur-complement, fallback, and default-nonrejection mechanics from the theorem statement;


retain those mechanics in the construction and proof, where their role is measurability and total definition;


state the scientific conclusions cleanly.


A satisfactory order would be:


4.1 Model and isolated-collision coordinates


4.2 Score nondegeneracy


4.3 Recurrence estimator and residualized statistic


4.4 Limit experiment and efficient testing


4.5 Recovery rate and lower bound


The current A–C theorem may remain one theorem after this reordering, but I would prefer three results: limit experiment, efficient test, and multiset recovery.
2. Rewrite the abstract and the final half of the introduction
Required — writing; no new mathematics
In the abstract:


reduce the length from about 250 words to approximately 170–190;


state the equivalence result;


state the isolated-collision application and N−1/4 rate;


mention the Gaussian half-space experiment and efficient test;


delete the terminal list of nonclaims.


In the introduction:


retain the opening explanation of the boundary-cycle problem;


retain the paragraph on the three ingredients of the singular application;


replace the exhaustive numbered-result roadmap with a two-sentence organization paragraph;


reduce the super-resolution discussion to one sentence or defer it to the related-work discussion;


remove repeated model limitations already encoded in the theorem hypotheses.


3. Make the main–supplement interface formally complete
Required — organization of existing mathematics; no new result
Insert in the main article exact statements, with proofs deferred, of the three supplementary inputs needed for Theorem 4:


uniform relative derivative/envelope bounds and the resulting DQM/Hellinger conclusions;


the stopped-score CLT and information/Hessian LLN;


plug-in equicontinuity for the fitted residualized score and empirical information.


These may be three short lemmas or one proposition with three parts. Their combined length should be about one to two pages.
Keep in the supplement:


the complete derivative calculations;


the independent direct stationary-likelihood proof;


contour-atlas compatibility and fallback details;


lengthy measurability verifications;


detailed two-state computations;


deterministic verification scripts.


The 33:22 ratio is not a problem. After the transfer above and removal of theorem-level gate mechanics, a package of approximately 34–35 pages main plus 20–22 pages supplement would be entirely normal for EJS.
4. Consolidate all scope limitations
Required — writing; no new mathematics
State the application’s scope in exactly three places:


once in the abstract, very briefly;


once when defining the isolated-collision model;


once in the final discussion.


Delete or compress the other repetitions.
In particular, avoid repeatedly restating that the theorem does not cover multiple collisions, unknown order, unknown sampling interval, or general phase-type representations. The formal assumptions already make those facts true. The reader does not need them recertified in every theorem-adjacent paragraph.
Remove the sentence “The ceiling of Theorem 4 is therefore substantive.” Replace it with an ordinary forward-looking conclusion, such as:

“Multiple collisions and nonserial phase-type realizations require different local coordinates and additional score-separation arguments.”

5. Shorten and refocus Section 6
Required — writing; no new mathematics
Reduce the discussion from approximately five pages to no more than three.
Delete the repeated derivation of:


why the complete gaps are unconditioned;


why the reverse kernel uses a base-law continuation;


why the fixed cone changes the decision problem;


why the result stops at observable renewal cycles.


Retain:


one paragraph interpreting two-sided deficiency rather than information equality;


one paragraph on constrained local decision theory;


one paragraph on pole order and positive efficient information;


one paragraph on confluent coordinates and unordered recovery;


one short paragraph distinguishing the observation model from super-resolution;


one concluding paragraph on future extensions.


6. Remove the “verification memorandum” register throughout
Required — writing; no new mathematics
Conduct a sentence-level pass for:


“No … is claimed”;


“This is not a statement about …”;


“The conclusion is deliberately no broader than …”;


inventories of all exceptional cases;


transitions announcing completeness rather than giving a mathematical reason.


Retain a qualification only when omitting it would cause a competent statistical reader to misread the theorem.
At the same time, preserve the explanatory prose inside the proof of Theorem 1 and the pole-order proof. Those passages have the correct human unevenness and should not be compressed into formulas.
7. Separate Theorem 1 from its decision-theoretic consequences
Discretionary but strongly recommended — organization; no new mathematics
Make the equivalence and quantitative deficiency estimates the theorem proper. Move bounded-loss transfer, calendar information, canonical-gradient covariance, and fixed-cone consequences to a corollary and remark.
This would make the principal general result easier to cite and would allow the reader to distinguish:


the coupling theorem;


standard Le Cam consequences;


the boundary-specific interpretation.


8. Move the detailed application notation out of the introduction
Discretionary — organization; no new mathematics
Move the matrix realization Q(θ), Kθ​, T1,θ​, and matching-distance definition to the beginning of the application part. Retain only a prose description of the sampled serial model in the introduction.
This would make the transition from the introduction to the general renewal theorem much cleaner.

New mathematics required: none.
The gap between the current manuscript and the version I would accept is almost entirely one of rhetorical hierarchy and proof-interface design. The general theorem, model-specific score argument, test, estimator, and lower bound already form an EJS-level mathematical package. After the required revisions above, I would accept the manuscript without asking for an additional theorem or a stronger minimax result.
