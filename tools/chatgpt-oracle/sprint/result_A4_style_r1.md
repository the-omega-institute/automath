PART ONE — THE HOUSE STYLE, LEARNED FROM ACTUAL RECENT PAPERS
Basis of comparison and one limitation
I compared the manuscript with a cross-section of recent Monatshefte für Mathematik papers from 2023–2025, including short number-theory and algebra papers, medium-length analysis papers, and two unusually long papers. The sample includes:


the 16-page “p-elements in profinite groups”;


the 18-page “On the number of lattice points in thin sectors”;


the 20-page “Magic squares, the symmetric group and Möbius randomness”;


the 8-page “On the equivalence of certain quadratic irrationals”;


the 12-page “Weyl multipliers for (Lp,Lq)”;


the 43-page “Almost automorphic and bijective factors of substitution shifts”;


and the 48-page “Sharp density discrepancy for cut and project sets.”


Thus, the comparison is not restricted to short papers, and the conclusion below is not that Monatshefte refuses long articles. It plainly does not. The issue is what long papers do with their length. Springer Link+6Springer Link+6Springer Link+6
The file available for direct inspection here is the 37-page main article. I did not receive the separate 43-page supplement as an inspectable file. My assessment of the supplement’s contents therefore rests on the article’s own description of it, not on a line-by-line reading of the supplement. 
1. How accepted papers open, and where the theorem appears
There is no single compulsory opening formula, but there is a stable family resemblance.
A short algebra or number-theory paper often defines the object, gives one concrete example or obstruction, and states its first principal theorem immediately. “p-elements in profinite groups” defines the probability under study, gives a semidirect-product counterexample, and reaches Theorem 1 on the second printed page. “On the equivalence of certain quadratic irrationals” gives a numerical continued-fraction example and then states Theorem 1 in the introduction. Springer Link+2Springer Link+2
A more technical paper may begin with definitions and formulas rather than motivation. “Weyl multipliers” begins directly with the Weyl transform. “A note on Weyl’s equidistribution theorem” begins with its central definition and states Theorems 1.2 and 1.3 in the introduction; it even says explicitly that the most general version was withheld from the introduction to keep that introduction concise. Springer Link+1
A longer article gets more room, but it still displays its major results early. The 43-page substitution-shifts paper has a roughly three-page introduction and states Theorem 1 on the third printed page and Theorems 2 and 3 on the fourth. The 18-page thin-sectors paper has an unusually long introductory section because that section contains the notation, regime division, and the actual statements of Theorems 1.1 and 1.3; the proofs begin later. Springer Link+3Springer Link+3Springer Link+3
The practical rule is therefore:

A Monatshefte paper need not state its theorem on page one, but it normally lets the reader see the exact principal theorem, as a theorem, within the introduction—usually by pages two to four.

Introductions in the sample are commonly around 10–20% of the article, though there are justified outliers when the introduction doubles as a theorem section. What matters more than the percentage is that the introduction selects and orders the results. It does not usually narrate every numbered lemma, corollary, qualification, failed route, and effective boundary.
Application to this manuscript
The manuscript’s introduction occupies about 2,050 words, roughly 14% of the pre-reference text. That proportion is entirely normal. The problem is not its raw length.
The problem is that §1.1 functions as a complete theorem inventory. It successively discusses Theorem 2.7, Theorem 2.9, Proposition 2.10, Theorem 2.11, Proposition 2.12, Theorem 2.16, Lemma 2.17, Corollary 2.18, Remark 2.19, Theorems 2.20 and 2.21, Theorem 2.25, Theorem 3.2, and Theorem 3.5.  
Yet the central results are not displayed as introductory theorems. Theorem 2.16 is paraphrased in a three-item list, and Theorems 2.25 and 3.2 are summarized in prose. This makes the introduction simultaneously too detailed and not decisive enough.
I would replace §1.1 with three displayed results:


the synchronized-orbit theorem, in a compressed form;


the geometric-ray/weak-Perron classification, preferably presented as the central one-system theorem;


the slender-context-free Cobham theorem, if Section 3 is retained.


Everything else should be described as a consequence or specialization in one or two paragraphs.
The opening two paragraphs themselves are good. They define the value map, pose a clear arithmetic question, and state the ambient assumptions without a long historical preamble. 
2. Prose versus statement and proof
In the recent papers I inspected, approximately 70–85% of the mathematical body is definition, statement, calculation, and proof. The remaining prose explains the problem, locates a theorem, introduces a section, or gives a consequence or example. That ratio varies by subject, but the explanatory prose normally has a local job.
Its usual locations are:


immediately before a theorem, to explain why it is the next statement;


at the beginning of a section, to state the strategy;


after a theorem, to record a consequence, comparison, or example;


occasionally at the beginning of a long proof, to divide the argument into stages.


It is much less common to place a paragraph before and after nearly every major result explaining exactly what the result does not say. The long substitution paper, for example, has substantial introductory prose, but it leads to three displayed theorems and then moves into preliminaries. Its prose identifies the two questions and two toolkits; it does not repeatedly re-audit the novelty boundary throughout the paper. Springer Link+2Springer Link+2
Application to this manuscript
The manuscript contains enough genuine mathematical exposition, but too much of it has become defensive scope management rather than motivation.
The densest instances are:


the extended comparison of the weak MCFL pumping lemma with the newer substitution lemma immediately before Theorem 2.7; 


the freestanding “Length-order audit,” which inventories every downstream use of a formerly stronger hypothesis; 


Remark 2.19, which surveys Skolem, Positivity, orbit hitting, and matrix equations chiefly to say that none closes the decision problem; 


Remark 2.26, which excludes a long catalogue of neighbouring numeration frameworks; 


Remark 3.6, which re-establishes the precise non-overlap with three existing Cobham theories over more than a page; 


and the conclusion, which repeats both effective boundaries and once again explains why the two-system theorem is not an extension of the pumping theorem. 


These passages are not individually wrong. Collectively, they cause the paper to sound as though it is answering an adversarial audit that the reader has not seen. A journal article should incorporate the result of such an audit, not preserve the audit transcript.
The corrective principle is simple: state each boundary once, at the point where a reader might otherwise make the mistaken inference. Do not restate it in the abstract, introduction, theorem preamble, later remark, and conclusion.
3. How proofs are written in this journal
Short citation-driven proofs are completely acceptable when the cited result really performs the work. A recent Monatshefte theorem about Weyl multipliers has a one-sentence proof: a preceding proposition supplies invariance, and a preceding theorem supplies the required representation. Springer Link
Routine verifications may be described as “easily checked” or handled in one sentence. The recent profinite-group paper does this even inside a classification-dependent argument. Springer Link
But the journal expects the article to carry the new mathematical bridge. A paper may invoke a deep external theorem, but it should verify that the hypotheses match and explain how the imported theorem enters the new setting. Recent longer papers carry their substantive constructions and technical appendices in the article itself.
Application to this manuscript
This aspect of the manuscript is mostly strong and already journal-compatible.
The short proofs of Lemmas 2.1 and 2.2 do exactly what short proofs should do: they calculate the matrix action, determinant, and modular consequence without ceremony. 
The paper also correctly carries the genuinely new interfaces:


Theorem 2.7 proves the placement beyond the recurrence transient, finite-group return, and distinctness; 


Lemma 2.15 gives the full recurrence-to-geometric-subsequence argument, including the Evertse and Schur steps; 


Lemma 3.1 carries the dominant-root transfer and cancellation analysis;


Theorem 3.2 is then appropriately short, because the paired-loop classification, Lemma 3.1, and Mignotte have already done the work. 


That last contrast is good. It is exactly the deliberate unevenness expected in a human mathematical article: the hard bridge gets two pages; the terminal theorem gets half a page.
There are, however, places where the manuscript proves standard infrastructure at excessive length. In Theorem 2.7, the explicit fresh-letter construction proving closure under fixed left quotient can probably be replaced by a citation or a single sentence. The closure fact is not where the paper’s value lies. The “Length-order audit” should not be a named textual unit at all; its necessary observations should be inserted in the two or three later proofs that use them.
I would not ask the authors to expand any core proof. I would ask them to remove procedural verification from around those proofs.
4. Main text, appendices, and supplementary material
The customary ratio in the papers I inspected is approximately 90:10 to 100:0 in favour of the article itself. Most papers have no external supplement. When a substantial mathematical appendix is needed, it is normally printed as part of the article.
The 48-page cut-and-project paper is instructive. Its appendix, written by two additional authors, contains lower bounds needed to establish the sharpness advertised in the abstract. It is an in-article appendix, visibly integrated into the theorem narrative. Springer Link+1
By contrast, a recent external supplement attached to a Monatshefte logic article consists of Isabelle/HOL source files. That is the natural kind of external material: formalization files, code, tables, large computational records, or verification artefacts. Springer Link
I would not infer that the journal formally forbids a large mathematical supplement. The point is customary presentation: a second, longer mathematical paper is not normally disguised as an online resource.
Application to this manuscript
The proposed ratio is:


main article: 37 pages;


supplement: 43 pages;


total package: 80 pages;


main share: approximately 46%;


supplementary share: approximately 54%.


That is not the normal Monatshefte shape.
More seriously, the main article describes the supplement as containing:


a density dichotomy;


effective fixed-DFA prime-slice bounds in ordinary bases;


Zeckendorf growth and regular-language results;


analytic comparisons;


explicit comparisons with Shen and Dubbe;


and expressly says that these results are independent and not used in the recurrent-MCFL theorem chain. 
The conclusion repeats that they are “independent fixed-DFA density and regular Zeckendorf results.” 
On that description, Online Resource 1 is not supplementary proof material. It is a second article.
My recommendation is:


remove that 43-page mathematical supplement from this submission;


develop it as a separately titled paper;


retain the deterministic scripts, unit tests, and archived outputs as an online resource;


import into the main article, at most, one concise finite-state theorem or motivating example if it materially improves the opening of Section 2.


Nothing essential to the main theorem chain should be moved out of the article. Conversely, independent theorem streams should not be kept outside merely to make the printed article look shorter.
5. Register and signposting
The common register is ordinary first-person plural:


“We prove…”;


“We first show…”;


“Our main result is…”;


“The following consequence…”;


“By Theorem 2.3…”;


“It remains to prove…”.


Impersonal constructions also occur, but there is no preference for sustained passive voice. Recent papers are comfortable with direct judgments such as “The beauty of this result…” or “Our main goal…”. Springer Link+1
Results are normally referred to by number, with little re-description unless the result is being used in a new conceptual role. Motivation is not usually repeated verbatim in the introduction, a later scope remark, and the conclusion.
Application to this manuscript
The first-person register is fine. The problem is the manuscript’s special vocabulary of certification:


“the promised class of valid presentations”;


“exact algorithmic boundary”;


“exact open interfaces”;


“priority and scope”;


“length-order audit”;


“we audit the actual affine matrices”;


“the full prime-ideal norm bound and all quantifiers … are given”;


“no recognition procedure … is asserted”;


“no reduction in either direction is claimed”.


Some of that language is needed once. Its repetition makes the article read more like a response memorandum or formal assurance document than like a Monatshefte paper.
One conspicuous revision artefact is Definition 2.5. Its assumptions are labelled (U1), (U2), and (U4), followed by the explanation that the label (U4) was retained “to preserve the numbering.” 
That sentence should not survive into a submitted article. Renumber the assumptions. A reader should not be made to see the paper’s revision history.
6. Tells of a paper that does not fit the register
In recent Monatshefte papers, the clearest non-fit tells would be:


an abstract that tries to inventory the whole paper;


a main theorem not stated formally until deep into the article;


extensive defensive priority discussion repeated in several locations;


numerous numbered results of approximately equal rhetorical weight;


a section that announces itself as architecturally separate from the preceding paper;


a mathematical supplement larger than the article and logically independent of it;


visible remnants of previous numbering or referee-response language.


This manuscript presently displays all seven.
Section-by-section application
Title and abstract
The current title is a good title for Section 2:

Prime support and multiple-context-free languages in recurrent numeration.

It does not prepare the reader for a slender-context-free Cobham theorem. The abstract itself calls the two-system result “separate.” 
Either:


retain the title and move the Cobham paper elsewhere; or


retain Section 3 and change the title to something that names both branches, for example
“Context-free rigidity in recurrent numeration: prime support and a Cobham theorem.”


The abstract is approximately 307 words, compared with roughly 40–120 words in several recent papers sampled above. More important than the count, it contains almost every level of the theorem hierarchy: orbit return, adic topology, Cantor–Bendixson rank, prime immunity, quotient chains, divisibility tree, inverse theorem, semidecidability, the missing witness bound, weak-Perron classification, alternating radices, and the Cobham theorem. 
It should be rewritten to about 150–180 words. State:


the one-system prime-support classification;


its weak-Perron consequence;


the two-system slender-context-free finiteness theorem.


The adic and divisibility-tree consequences can be summarized in one clause. The negative decision boundary does not belong in the abstract unless effectivity is the title-level contribution.
Introduction
The opening is good. The main-results section should be rebuilt rather than merely shortened.
The present introduction gives similar emphasis to central theorems, technical inputs, secondary consequences, effective qualifications, and priority boundaries. This produces flat emphasis.
Theorem 2.16 or Theorem 2.25 should be visibly the centre. Theorem 3.2 should be the second principal theorem if retained. Theorems 2.20 and 2.21 are interesting consequences but should not receive equal introductory billing. Proposition 2.12, Lemma 2.17, and Remark 2.19 need not be mentioned individually.
Section 1.2 should be cut by at least half. Retain the indispensable comparisons with:


Hartmanis–Shank and Schützenberger;


the weak MCFL pumping lemma;


Evertse;


the nearest weak-Perron regularity result;


the three relevant Cobham traditions.


Move exact non-overlap discussions to one local remark per topic.
Section 2 opening and the Zeckendorf motivation
The concrete Zeckendorf block action is an effective journal opening. Lemmas 2.1–2.4 are clean, short, and motivating.
But the sentence “We now pass from finite automata to pushdown automata” sounds as though the reader has just read the 43-page finite-state paper. Within the main article, they have not. 
Replace it with something self-contained, such as:

“We begin with the Zeckendorf system, where the recurrent block action and the pumping argument are visible in dimension three.”

Renumber (U1), (U2), (U4). Remove the revision-history explanation.
Theorem 2.7 and its neighbourhood
The theorem itself is a strong structural result. Keep it.
Compress the discussion of the two pumping lemmas before it to one paragraph. The exact comparison can appear in one later remark.
Delete “Length-order audit.” Where pairwise distinctness is used later, say so in the relevant proof.
Shorten the standard closure-property portion of the proof. Preserve the finite-group return argument in full.
Theorems 2.9–2.17
This is the most coherent part of the article. The sequence
orbit return→adic recurrence→scatteredness→escape dichotomy→minimal recurrence→geometric ray
reads like one paper.
The Evertse input is correctly isolated, and Lemma 2.15 is appropriately detailed. I would make only local compression edits here.
Corollary 2.18 and Remark 2.19
The positive semidecision belongs, but the language of “promised presentations” is overused. Define once what input is assumed valid, then use ordinary language such as “Given such an effective presentation…”.
Remark 2.19 should be reduced to one paragraph:


candidate verification is effective;


a uniform witness bound is missing;


no decidability or undecidability statement follows.


The catalogue of adjacent decision problems is not needed in full.
Theorems 2.20–2.23
The deep quotient congruences and the divisibility tree are attractive, but they are downstream ornaments rather than the article’s centre.
I would retain Theorem 2.20, but present Theorem 2.21 as a corollary or application. Theorem 2.22 largely repackages earlier immunity conclusions, and Corollary 2.23 specializes them. These can be merged into one “Consequences for standard greedy systems” subsection.
The current number of headline results contributes to the feeling that the article refuses to rank its own contributions.
Example 2.24
The alternating-radix examples are valuable because they show that the weak-Perron positive case is genuinely nonintegral.
The catalogue is too long. The Fibonacci, Pell, Tribonacci, integer-base, alternating-radix, nonintegral Pisot, and non-Pisot Perron examples do not all need extended treatment. Keep:


one sentence covering the standard unit examples;


the alternating-radix family;


one genuinely non-Pisot example if it is needed to demonstrate the breadth of Theorem 2.25.


Move the rest to a short table or omit it.
Theorem 2.25
This is one of the best-written parts of the paper.
The internal headings—“Peripheral period,” “Tail coefficients and their covariance,” “Residue asymptotics,” “Cyclic propagation of positivity”—are useful because they mark genuine changes of argument. They should remain.
This theorem should be promoted in the introduction and possibly in the title.
Remark 2.26
Reduce it sharply. The manuscript does not need to enumerate Rényi expansions, β-shifts, Parry languages, β-integers, Cantor real bases, abstract numeration, redundant systems, and nonrecurrent systems in one closing exclusion notice.
One sentence can say that the theorem concerns integer-valued greedy linear numeration and not real-base or genealogical-rank numeration.
Section 3
The first paragraph is the single most damaging paragraph in the main article:

“This section has a different architecture … none of the finite-group return, deleted-prime, fixed-support quotient, geometric-subsequence, or divisibility-tree arguments enters the proof.” 

That is an accurate audit statement but a poor article transition. It tells the referee that a second paper has been appended.
There is a better and mathematically honest framing:

“The preceding argument extracts one synchronized orbit from an arbitrary infinite MCFL. Slender context-free languages provide more: their entire language is covered by finitely many paired loops. Combining that global cover with the same affine recurrence evaluation yields a two-system rigidity theorem.”

That states both the distinction and the common spine.
Lemma 3.1 should remain in full. It is the genuine bridge. Theorem 3.2 should remain short. That proof is already in the journal’s normal register.
The effective refinement is mathematically legitimate but over-administered. Definition 3.3 reads like an input contract. Reduce the detailed promises to the minimum necessary hypotheses. Lemma 3.4 may be placed in an in-article appendix if its proof interrupts the qualitative theorem, but it should not be hidden in the independent online supplement because it is essential to Theorem 3.5.
Remark 3.6 should become at most two paragraphs:


one paragraph stating that the regular integer-base specialization lies within existing quantitative Cobham theory;


one paragraph identifying the new nonregular slender-CF and weak-Perron step.


Conclusion
The conclusion is almost two additional pages of theorem summary, decision-boundary qualification, and renewed separation of the two arguments. 
Reduce it to approximately half a page:


one paragraph on the local one-orbit theorem and geometric classification;


one paragraph on the global slender-CF theorem and the remaining witness-bound problem.


Do not repeat the full prior-art defence.
Does it read as machine-assisted?
Bluntly: the proofs do not read like raw machine output, but the editorial superstructure does read as machine-assisted or machine-over-revised.
The positive evidence is important. Paragraph lengths are not mechanically uniform. Proofs are uneven in a mathematically appropriate way. Lemma 2.15 and Theorem 2.25 are allowed to be long; Theorem 3.2 is allowed to be short. The authors do make choices.
The machine-assisted impression comes from a different layer:


exhaustive enumeration rather than selection;


repeated symmetry of “does not X, no Y is claimed, nor is Z asserted”;


headings such as “Length-order audit,” “Exact algorithmic boundary,” “Exact open interfaces,” and “Priority and scope”;


the repeated word “exact” or “exactly” throughout the paper;


the repeated contractual adjective “promised”;


transitions that announce the architecture or list unused machinery rather than move the argument forward;


visible revision residue such as retaining the label (U4) solely to preserve old numbering;


and an abstract, introduction, scope remarks, and conclusion that give nearly every result and every limitation comparable rhetorical weight.


In the pre-reference body, I count roughly forty occurrences of exact or exactly, twelve of promised, and seventeen of does not. No one count proves anything. The clustering accurately describes the reading experience.
The most conspicuous passages are the “Length-order audit,” Remark 2.19, Remark 2.26, the opening of Section 3, and Remark 3.6. Those passages should be rewritten, not merely copyedited.

PART TWO — YOU ARE THE REFEREE
Recommendation: Major revisions
Report to the Editor
The manuscript studies finite-fan-out language restrictions in recurrent numeration systems. Its principal one-system results derive synchronized congruence recurrence from weak MCFL pumping, use this to obtain prime-support and scatteredness obstructions, and characterize bounded prime support through synchronized geometric rays. In the weak-Perron greedy setting, this becomes an algebraic classification by the condition that a positive power of the dominant root be integral. A second part proves a slender-context-free Cobham theorem for two multiplicatively independent weak-Perron systems and gives an effective cardinality refinement.
For the purposes of this report, I am evaluating presentation, coherence, and suitability for Monatshefte für Mathematik, rather than re-auditing the correctness or priority of the mathematical results.
The paper contains substantial mathematics and, after reconstruction, could be suitable for the journal. I do not recommend acceptance in its present form.
The principal difficulty is that the submission does not presently read as one article. It reads as three related packages:


the recurrent-MCFL prime-support and geometric-ray theory in Section 2;


the slender-context-free two-system theorem in Section 3;


an independent 43-page finite-state paper submitted as supplementary information.


The manuscript itself repeatedly confirms this separation. The introduction calls the two-system result “separate”; Section 3 begins by saying that it has a different architecture and enumerates the machinery from Section 2 that it does not use; the supplement is described as containing independent results not used in the main theorem chain.   
Long articles are not out of place in this journal, but the accepted long papers I know have a visibly unified question and theorem hierarchy. Here the total package is approximately 80 pages, with more pages in the supplementary mathematical article than in the main article. I do not regard independent theorem streams as appropriate supplementary material.
The main article also needs a substantial editorial rewrite. The abstract is an exhaustive inventory. The introduction is not excessive as a percentage of the paper, but it gives comparable attention to central theorems, technical inputs, secondary consequences, effective qualifications, failed compression routes, and priority delimitations. The result is a flattened hierarchy. The reader is told about nearly every numbered result but is not given two or three formally displayed introductory theorems around which to organize the paper.
The body contains several passages that read as remnants of a correctness or priority audit rather than finished exposition: “Length-order audit,” “Exact algorithmic boundary,” “Exact open interfaces,” and “Priority and scope.” The explanation that the label (U4) is preserved to retain earlier numbering is an especially clear revision artefact. These passages should not remain in a submitted version.
I do not object to the level of detail in the central proofs. In particular, the proofs of the synchronized-orbit theorem, the recurrence rigidity lemma, the weak-Perron classification, and the dominant-root transfer carry the parts that should be carried in the article. The short proof of the ultimate Cobham theorem is appropriate after those ingredients have been established. The needed revision is not proof expansion. It is selection, hierarchy, and removal of defensive repetition.
I would require the following before publication:


Remove the independent 43-page mathematical supplement from this submission and treat it as a separate paper. Computational scripts and archived verification outputs may remain as an online resource.


Recast the main article around a single conceptual spine. It is possible to retain Section 3: the shared idea is that the affine recurrence evaluation turns language-theoretic loop structure into recurrence sequences, with Section 2 using a single pumped orbit and Section 3 using a finite global paired-loop cover. The current manuscript obscures this relation by emphasizing non-use and separation.


Rewrite the title, abstract, and introduction. The introduction should display the central one-system classification and the two-system theorem. Secondary consequences should be subordinated.


Remove the audit vocabulary and consolidate each scope or priority boundary into one location.


Reduce the number of equally prominent theorem statements by merging or demoting the downstream immunity restatements, divisibility-tree application, and routine specializations.


Shorten the example catalogue, the two long scope remarks, and the conclusion.


The single objection most likely to sink the paper is therefore the absence of a defensible article boundary. An editor or referee can reasonably conclude that the submission packages several papers together while using an online supplement to conceal rather than solve the problem of scale.
This objection is fixable. The preferred repair requires no new mathematics: separate the independent finite-state paper, and rewrite the 37-page article around the common affine-recurrence interface connecting its local and global language results. If the authors insist that all three streams must remain one submission, then the objection is not fixable by prose alone; a genuinely stronger mathematical synthesis would be needed.
Subject to the above major revision, I would be prepared to recommend publication.

PART THREE — THE EDITOR’S BAR
I would issue a major-revision decision with the following acceptance conditions, in this order.
1. Remove the 43-page independent mathematical supplement
Status: Required.
Type: Writing, packaging, and article-boundary work; no new mathematics.
Online Resource 1 should not accompany this paper in its present form. The main article expressly says that its density dichotomy, fixed-DFA prime-slice estimates, Zeckendorf growth results, and analytic comparisons are independent and unused in the main theorem chain. 
Turn that material into a separate article with its own title, abstract, introduction, and references.
For this submission:


retain Online Resource 2 containing scripts, unit tests, and archived outputs;


import from the former supplement no more than one concise finite-state theorem or example, and only if it is needed to motivate the Zeckendorf opening;


do not move any proof essential to the main theorems out of the printed article.


Without this change, I would not accept the submission.
2. Establish one conceptual spine for the 37-page article
Status: Required.
Type: Primarily writing and organization. New mathematics is required only if the authors insist on a stronger unification than the present results support.
My preferred architecture is:


Local rigidity from one synchronized orbit
MCFL pumping, affine recurrence action, local returns, prime-support obstruction, geometric-ray classification.


Global rigidity from a finite paired-loop cover
slender-CF classification, dominant-root transfer, common-value finiteness.


The common idea is not the weak pumping lemma. It is the passage
structured word families⟶affine matrix powers⟶linear recurrence sequences⟶arithmetic rigidity.
Rewrite the final paragraph of the introduction and the opening of Section 3 accordingly. Remove the catalogue of Section 2 tools that Section 3 does not use. 
If the authors cannot explain this common spine convincingly in approximately one introductory page, then Section 3 should become a separate paper titled along the lines of:

A slender context-free Cobham theorem for weak-Perron numeration systems.

No new theorem is needed for the preferred two-branch architecture. A new theorem would be needed only if the authors wished to claim that the global Cobham theorem is itself a consequence of the one-orbit MCFL machinery; the manuscript correctly does not prove that.
3. Change the title
Status: Required if Section 3 remains; otherwise discretionary.
Type: Writing.
If Section 3 remains, the current title understates approximately one fifth of the article and omits one of its principal results.
A suitable title would be:

Context-free rigidity in recurrent numeration: prime support and a Cobham theorem

or

Prime support and slender context-free rigidity in recurrent numeration

If Section 3 is split off, the present title is appropriate.
4. Replace the abstract completely
Status: Required.
Type: Writing.
Target approximately 150–180 words.
The new abstract should contain:


one sentence defining the setting;


one sentence on the synchronized recurrence orbit;


the geometric-ray/weak-Perron classification;


the slender-context-free Cobham theorem, if retained;


at most one sentence on effectivity.


Remove from the abstract:


the complete list of adic and divisibility consequences;


the missing uniform witness bound;


the explanation of why the one-orbit method does not control two systems;


detailed attribution of the Evertse step;


the phrase “Separately”.


Those matters belong in the introduction.
5. Rebuild the introduction around displayed theorems
Status: Required.
Type: Writing and organization.
Keep the opening problem and ambient assumptions.
Then state, in exact but compressed form:


Main Theorem A: synchronized orbit and its prime-support consequence;


Main Theorem B: geometric-ray characterization, followed by the weak-Perron equivalence;


Main Theorem C: slender-context-free Cobham theorem, if retained.


The introduction should then explain the proof architecture in approximately five paragraphs:


affine block action and synchronized pumping;


topology and prime support;


Evertse/Schur rigidity;


weak-Perron length squeeze;


paired-loop cover and Mignotte.


Reduce the present prior-work section by at least 40–50%. Keep exact attribution, but delete repeated statements that neighbouring theorems do not imply the present result. Each such distinction should occur once.
The revised introduction may still be four or five pages. It should no longer mention nearly every numbered result.
6. Rebuild the hierarchy of Section 2
Status: Required.
Type: Writing and organization; no new mathematics.
In §2:


replace “We now pass from finite automata…” with a self-contained Zeckendorf opening;


renumber (U1), (U2), and (U4) consecutively;


delete the statement that old numbering was preserved;


compress the pumping-lemma comparison before Theorem 2.7;


delete “Length-order audit” and incorporate its necessary observations locally;


retain Theorems 2.7, 2.9, 2.11, 2.16, and 2.25 as major landmarks;


present Proposition 2.10 and Lemmas 2.14–2.17 as the structural bridge between them;


demote Theorem 2.21 to a corollary or application of Theorem 2.20;


merge Theorem 2.22 and Corollary 2.23 into one consequences subsection;


shorten Example 2.24;


reduce Remark 2.26 to one paragraph.


Theorem 2.25 and its internal proof headings should remain substantially as written.
7. Streamline the effective statements
Status: Required.
Type: Writing; no new mathematics.
For Corollary 2.18 and Definition 3.3:


define “effective presentation” once;


state that validity, uniqueness, recurrence data, and the relevant minimal polynomial are supplied;


stop repeatedly calling the inputs “promised”;


distinguish clearly between an effective bound from complete data and a closed bound in compact size parameters.


Remark 2.19 should be one paragraph. Definition 3.3 should not read as a software interface contract.
The detailed proof of Lemma 3.4 may remain in Section 3 or move to an in-article appendix. It must remain in the article package because Theorem 3.5 depends on it.
8. Rewrite Section 3’s introduction and priority discussion
Status: Required.
Type: Writing and organization.
Open Section 3 by explaining why slenderness supplies global control that arbitrary MCFL pumping does not. Do not begin by enumerating unused Section 2 machinery.
Keep Lemma 3.1 in full. It is the new mathematical bridge.
Keep the proof of Theorem 3.2 short.
Reduce Remark 3.6 from its current length to two paragraphs:


the regular integer-base overlap with Albayrak–Bell and the fact that their quantitative bound is stronger there;


the genuinely new passage to nonregular slender context-free representation languages in weak-Perron systems.


Durand and abstract numeration can be included in the second paragraph without another complete scope audit.
9. Shorten the conclusion
Status: Required.
Type: Writing.
Maximum target: approximately three-quarters of a page.
The conclusion should not restate the full Evertse argument, the witness-compression obstruction, the neighbouring undecidability problems, and the nonrelation between the two proof mechanisms.
Conclude with:


the local-to-arithmetic rigidity principle;


the weak-Perron classification;


the global paired-loop Cobham consequence;


one sentence identifying the missing effective witness bound.


Delete the renewed defence of the supplement.
10. Remove revision-response vocabulary throughout
Status: Required.
Type: Copyediting and register.
Search globally for:


audit;


exact boundary;


exact interface;


priority and scope;


promised;


no claim is made;


not asserted;


does not imply;


precisely the input;


for completeness.


Retain these expressions only where they add mathematical information. Most should be replaced by direct affirmative statements.
For example:

“No recognition procedure for membership in the promised input class is asserted.”

can become:

“The presentation is assumed valid; recognizing valid presentations is not part of the algorithm.”

That is shorter and carries the same information.
11. Discretionary refinements
Status: Discretionary.
Type: Writing.
I would also encourage:


a one-paragraph roadmap at the start of the long proof of Theorem 2.25;


a small diagram showing the dependence of the principal results;


a compact table of examples replacing part of Example 2.24;


removal of theorem names that simply restate previously proved immunity consequences;


consistent use of either “least eventual recurrence polynomial” or “minimal tail recurrence polynomial,” with the equivalence fixed once.


Mathematics versus craft
Under the preferred revision, no new mathematics is required for acceptance. The necessary work is:


splitting the independent supplement;


selecting the principal theorems;


making the existing common affine-recurrence mechanism visible;


compressing repeated scope and priority language;


and restoring a normal theorem hierarchy.


New mathematics would be required only under one condition: if the authors insist that the one-system pumping theorem and the two-system Cobham theorem must form a single sequential theorem chain. They currently do not, and the manuscript correctly says so. A prose revision cannot manufacture that implication.
With required items 1–10 completed, I would accept the article, subject only to ordinary final checking. Without items 1 and 2—the article boundary and the conceptual spine—I would not.
